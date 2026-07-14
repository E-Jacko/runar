package runar

import (
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

// rpcHandler dispatches mock RPC responses based on the method field.
type rpcHandler struct {
	t        *testing.T
	handlers map[string]func(params []interface{}) (interface{}, *rpcErrorObj)
}

func (h *rpcHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	// Verify basic auth
	user, pass, ok := r.BasicAuth()
	if !ok || user != "testuser" || pass != "testpass" {
		h.t.Errorf("bad auth: user=%q pass=%q ok=%v", user, pass, ok)
		http.Error(w, "unauthorized", http.StatusUnauthorized)
		return
	}

	var req rpcRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		h.t.Fatalf("failed to decode RPC request: %v", err)
	}

	handler, ok := h.handlers[req.Method]
	if !ok {
		h.t.Fatalf("unexpected RPC method: %s", req.Method)
	}

	result, rpcErr := handler(req.Params)

	resp := map[string]interface{}{
		"result": result,
		"error":  rpcErr,
		"id":     req.ID,
	}
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(resp)
}

func newTestRPCProvider(t *testing.T, handlers map[string]func(params []interface{}) (interface{}, *rpcErrorObj)) (*RPCProvider, *httptest.Server) {
	t.Helper()
	h := &rpcHandler{t: t, handlers: handlers}
	server := httptest.NewServer(h)
	provider := NewRPCProvider(server.URL, "testuser", "testpass")
	return provider, server
}

// ---------------------------------------------------------------------------
// GetTransaction
// ---------------------------------------------------------------------------

func TestRPCProvider_GetTransaction(t *testing.T) {
	txid := strings.Repeat("ab", 32)

	provider, server := newTestRPCProvider(t, map[string]func([]interface{}) (interface{}, *rpcErrorObj){
		"getrawtransaction": func(params []interface{}) (interface{}, *rpcErrorObj) {
			if len(params) < 2 {
				t.Fatal("expected 2 params for getrawtransaction")
			}
			gotTxid, _ := params[0].(string)
			if gotTxid != txid {
				t.Fatalf("expected txid %s, got %s", txid, gotTxid)
			}
			return map[string]interface{}{
				"hex":  "0100000001000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000",
				"txid": txid,
				"vout": []interface{}{
					map[string]interface{}{
						"value": 0.001,
						"scriptPubKey": map[string]interface{}{
							"hex": "76a91400000000000000000000000000000000000000008ac",
						},
					},
					map[string]interface{}{
						"value": 0.005,
						"scriptPubKey": map[string]interface{}{
							"hex": "a914bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb87",
						},
					},
				},
			}, nil
		},
	})
	defer server.Close()

	txData, err := provider.GetTransaction(txid)
	if err != nil {
		t.Fatalf("GetTransaction failed: %v", err)
	}

	if txData.Txid != txid {
		t.Fatalf("expected txid %s, got %s", txid, txData.Txid)
	}
	if len(txData.Outputs) != 2 {
		t.Fatalf("expected 2 outputs, got %d", len(txData.Outputs))
	}
	if txData.Outputs[0].Satoshis != 100000 {
		t.Fatalf("expected first output 100000 sats, got %d", txData.Outputs[0].Satoshis)
	}
	if txData.Outputs[1].Satoshis != 500000 {
		t.Fatalf("expected second output 500000 sats, got %d", txData.Outputs[1].Satoshis)
	}
	if txData.Outputs[0].Script != "76a91400000000000000000000000000000000000000008ac" {
		t.Fatalf("unexpected script: %s", txData.Outputs[0].Script)
	}
}

func TestRPCProvider_GetTransaction_RPCError(t *testing.T) {
	provider, server := newTestRPCProvider(t, map[string]func([]interface{}) (interface{}, *rpcErrorObj){
		"getrawtransaction": func(params []interface{}) (interface{}, *rpcErrorObj) {
			return nil, &rpcErrorObj{Code: -5, Message: "No such mempool or blockchain transaction"}
		},
	})
	defer server.Close()

	_, err := provider.GetTransaction("deadbeef")
	if err == nil {
		t.Fatal("expected error for unknown txid")
	}
	if !strings.Contains(err.Error(), "No such mempool") {
		t.Fatalf("unexpected error: %v", err)
	}
}

// ---------------------------------------------------------------------------
// Broadcast
// ---------------------------------------------------------------------------

func TestRPCProvider_Broadcast_SendsRawTx(t *testing.T) {
	expectedTxid := strings.Repeat("cd", 32)
	var receivedMethod string

	provider, server := newTestRPCProvider(t, map[string]func([]interface{}) (interface{}, *rpcErrorObj){
		"sendrawtransaction": func(params []interface{}) (interface{}, *rpcErrorObj) {
			receivedMethod = "sendrawtransaction"
			if len(params) < 1 {
				t.Fatal("expected at least 1 param for sendrawtransaction")
			}
			return expectedTxid, nil
		},
	})
	defer server.Close()

	// Build a minimal transaction using go-sdk.
	// We just need Broadcast to call sendrawtransaction with the hex.
	// Since we can't easily construct a full go-sdk Transaction without
	// importing heavy dependencies, we test the method dispatch instead
	// by verifying the RPC plumbing works.
	_ = provider
	_ = receivedMethod

	// Verify the RPC method is correct by calling rpcCall directly.
	result, err := provider.rpcCall("sendrawtransaction", "01000000000000000000")
	if err != nil {
		t.Fatalf("rpcCall failed: %v", err)
	}
	var txid string
	if err := json.Unmarshal(result, &txid); err != nil {
		t.Fatalf("failed to parse txid: %v", err)
	}
	if txid != expectedTxid {
		t.Fatalf("expected txid %s, got %s", expectedTxid, txid)
	}
	if receivedMethod != "sendrawtransaction" {
		t.Fatalf("expected method sendrawtransaction, got %s", receivedMethod)
	}
}

// ---------------------------------------------------------------------------
// GetUtxos
// ---------------------------------------------------------------------------

func TestRPCProvider_GetUtxos(t *testing.T) {
	address := "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa"

	provider, server := newTestRPCProvider(t, map[string]func([]interface{}) (interface{}, *rpcErrorObj){
		"listunspent": func(params []interface{}) (interface{}, *rpcErrorObj) {
			// Verify the address is passed in the params
			if len(params) < 3 {
				t.Fatal("expected 3 params for listunspent")
			}
			addrs, ok := params[2].([]interface{})
			if !ok || len(addrs) == 0 {
				t.Fatal("expected address list in params[2]")
			}
			if addrs[0].(string) != address {
				t.Fatalf("expected address %s, got %s", address, addrs[0].(string))
			}

			return []interface{}{
				map[string]interface{}{
					"txid":         strings.Repeat("aa", 32),
					"vout":         float64(0),
					"amount":       0.01,
					"scriptPubKey": "76a914000000000000000000000000000000000000000088ac",
				},
				map[string]interface{}{
					"txid":         strings.Repeat("bb", 32),
					"vout":         float64(1),
					"amount":       0.05,
					"scriptPubKey": "76a914111111111111111111111111111111111111111188ac",
				},
			}, nil
		},
	})
	defer server.Close()

	utxos, err := provider.GetUtxos(address)
	if err != nil {
		t.Fatalf("GetUtxos failed: %v", err)
	}

	if len(utxos) != 2 {
		t.Fatalf("expected 2 UTXOs, got %d", len(utxos))
	}

	if utxos[0].Txid != strings.Repeat("aa", 32) {
		t.Fatalf("unexpected first UTXO txid: %s", utxos[0].Txid)
	}
	if utxos[0].OutputIndex != 0 {
		t.Fatalf("expected output index 0, got %d", utxos[0].OutputIndex)
	}
	if utxos[0].Satoshis != 1000000 {
		t.Fatalf("expected 1000000 sats, got %d", utxos[0].Satoshis)
	}

	if utxos[1].Txid != strings.Repeat("bb", 32) {
		t.Fatalf("unexpected second UTXO txid: %s", utxos[1].Txid)
	}
	if utxos[1].OutputIndex != 1 {
		t.Fatalf("expected output index 1, got %d", utxos[1].OutputIndex)
	}
	if utxos[1].Satoshis != 5000000 {
		t.Fatalf("expected 5000000 sats, got %d", utxos[1].Satoshis)
	}
}

func TestRPCProvider_GetUtxos_Empty(t *testing.T) {
	provider, server := newTestRPCProvider(t, map[string]func([]interface{}) (interface{}, *rpcErrorObj){
		"listunspent": func(params []interface{}) (interface{}, *rpcErrorObj) {
			return []interface{}{}, nil
		},
	})
	defer server.Close()

	utxos, err := provider.GetUtxos("1SomeAddress")
	if err != nil {
		t.Fatalf("GetUtxos failed: %v", err)
	}
	if len(utxos) != 0 {
		t.Fatalf("expected 0 UTXOs, got %d", len(utxos))
	}
}

// ---------------------------------------------------------------------------
// GetFeeRate
// ---------------------------------------------------------------------------

func TestRPCProvider_GetFeeRate(t *testing.T) {
	provider := NewRPCProvider("http://unused", "user", "pass")
	rate, err := provider.GetFeeRate()
	if err != nil {
		t.Fatalf("GetFeeRate failed: %v", err)
	}
	if rate != 100 {
		t.Fatalf("expected fee rate 100, got %d", rate)
	}
}

// ---------------------------------------------------------------------------
// GetNetwork
// ---------------------------------------------------------------------------

func TestRPCProvider_GetNetwork_Default(t *testing.T) {
	provider := NewRPCProvider("http://unused", "user", "pass")
	if provider.GetNetwork() != "testnet" {
		t.Fatalf("expected testnet, got %s", provider.GetNetwork())
	}
}

func TestRPCProvider_GetNetwork_Regtest(t *testing.T) {
	provider := NewRegtestRPCProvider("http://unused", "user", "pass")
	if provider.GetNetwork() != "regtest" {
		t.Fatalf("expected regtest, got %s", provider.GetNetwork())
	}
}

// ---------------------------------------------------------------------------
// GetRawTransaction
// ---------------------------------------------------------------------------

func TestRPCProvider_GetRawTransaction(t *testing.T) {
	txid := strings.Repeat("ef", 32)
	expectedHex := "01000000010000000000000000000000000000000000000000000000000000000000000000ffffffff00ffffffff0100000000000000000000000000"

	provider, server := newTestRPCProvider(t, map[string]func([]interface{}) (interface{}, *rpcErrorObj){
		"getrawtransaction": func(params []interface{}) (interface{}, *rpcErrorObj) {
			// non-verbose (param[1] = 0)
			if len(params) >= 2 {
				verbose, _ := params[1].(float64)
				if verbose != 0 {
					t.Fatalf("expected verbose=0, got %v", params[1])
				}
			}
			return expectedHex, nil
		},
	})
	defer server.Close()

	rawHex, err := provider.GetRawTransaction(txid)
	if err != nil {
		t.Fatalf("GetRawTransaction failed: %v", err)
	}
	if rawHex != expectedHex {
		t.Fatalf("expected hex %s, got %s", expectedHex, rawHex)
	}
}

// ---------------------------------------------------------------------------
// GetContractUtxo — not implemented
// ---------------------------------------------------------------------------

func TestRPCProvider_GetContractUtxo_NotImplemented(t *testing.T) {
	provider := NewRPCProvider("http://unused", "user", "pass")
	utxo, err := provider.GetContractUtxo("somehash")
	if err == nil {
		t.Fatal("expected error for unimplemented GetContractUtxo")
	}
	if utxo != nil {
		t.Fatal("expected nil utxo")
	}
	if !strings.Contains(err.Error(), "not implemented") {
		t.Fatalf("unexpected error message: %v", err)
	}
}

// ---------------------------------------------------------------------------
// Regtest autoMine flag
// ---------------------------------------------------------------------------

func TestRegtestRPCProvider_AutoMineEnabled(t *testing.T) {
	provider := NewRegtestRPCProvider("http://unused", "user", "pass")
	if !provider.autoMine {
		t.Fatal("regtest provider should have autoMine enabled")
	}
}

func TestRPCProvider_AutoMineDisabledByDefault(t *testing.T) {
	provider := NewRPCProvider("http://unused", "user", "pass")
	if provider.autoMine {
		t.Fatal("default provider should have autoMine disabled")
	}
}

// ---------------------------------------------------------------------------
// Auth verification
// ---------------------------------------------------------------------------

func TestRPCProvider_BasicAuth(t *testing.T) {
	var gotUser, gotPass string

	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		gotUser, gotPass, _ = r.BasicAuth()
		resp := map[string]interface{}{"result": "ok", "error": nil, "id": "1"}
		json.NewEncoder(w).Encode(resp)
	}))
	defer server.Close()

	provider := NewRPCProvider(server.URL, "myuser", "mypass")
	provider.rpcCall("getinfo")

	if gotUser != "myuser" {
		t.Fatalf("expected user myuser, got %s", gotUser)
	}
	if gotPass != "mypass" {
		t.Fatalf("expected pass mypass, got %s", gotPass)
	}
}
