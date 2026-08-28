//! Phase A residual contracts — deploy+spend (Rust SDK).
//! Gated with feature `regtest`.

use crate::helpers::*;
use runar_lang::sdk::{DeployOptions, RunarContract, SdkValue};

fn deploy_call(
    path: &str,
    ctor: Vec<SdkValue>,
    method: &str,
    args: &[SdkValue],
    sats: i64,
) {
    skip_if_no_node();
    let artifact = compile_contract(path);
    let mut contract = RunarContract::new(artifact, ctor);
    let mut provider = create_provider();
    let (signer, _wallet) = create_funded_wallet(&mut provider);
    let (deploy_txid, _) = contract
        .deploy(
            &mut provider,
            &*signer,
            &DeployOptions {
                satoshis: sats,
                change_address: None,
                ..Default::default()
            },
        )
        .expect("deploy");
    assert_eq!(deploy_txid.len(), 64);
    let (call_txid, _) = contract
        .call(method, args, &mut provider, &*signer, None)
        .expect("call");
    assert!(!call_txid.is_empty());
}

#[test]
#[cfg_attr(not(feature = "regtest"), ignore)]
fn test_branch_merged_locals() {
    deploy_call(
        "integration/contracts/constructs/BranchMergedLocals.runar.ts",
        vec![SdkValue::Int(10), SdkValue::Int(20)],
        "bid",
        &[SdkValue::Int(99), SdkValue::Int(1)],
        50_000,
    );
}

#[test]
#[cfg_attr(not(feature = "regtest"), ignore)]
fn test_cond_write_multi_field() {
    deploy_call(
        "integration/contracts/constructs/CondWriteMultiField.runar.ts",
        vec![SdkValue::Int(1), SdkValue::Int(2)],
        "bump",
        &[SdkValue::Int(1)],
        50_000,
    );
}

#[test]
#[cfg_attr(not(feature = "regtest"), ignore)]
fn test_conditional_data_output() {
    // OP_RETURN "bsvm-test"
    let payload = "6a096273766d2d74657374".to_string();
    deploy_call(
        "integration/contracts/constructs/ConditionalDataOutput.runar.ts",
        vec![SdkValue::Int(0)],
        "pay",
        &[SdkValue::Bool(true), SdkValue::Bytes(payload)],
        20_000,
    );
}

#[test]
#[cfg_attr(not(feature = "regtest"), ignore)]
fn test_state_bytestring_1b() {
    deploy_call(
        "integration/contracts/constructs/StateByteString1B.runar.ts",
        vec![SdkValue::Bytes("05".into())],
        "setTag",
        &[SdkValue::Bytes("ab".into())],
        10_000,
    );
}

#[test]
#[cfg_attr(not(feature = "regtest"), ignore)]
fn test_raw_output() {
    skip_if_no_node();
    let artifact = compile_contract("integration/contracts/outputs/RawOutput.runar.ts");
    let mut contract = RunarContract::new(artifact, vec![SdkValue::Int(0)]);
    let mut provider = create_provider();
    let (signer, wallet) = create_funded_wallet(&mut provider);
    contract
        .deploy(
            &mut provider,
            &*signer,
            &DeployOptions {
                satoshis: 50_000,
                change_address: None,
                ..Default::default()
            },
        )
        .expect("deploy");
    let p2pkh = format!("76a914{}88ac", wallet.pub_key_hash);
    let (txid, _) = contract
        .call(
            "sendToScript",
            &[SdkValue::Bytes(p2pkh)],
            &mut provider,
            &*signer,
            None,
        )
        .expect("call");
    assert_eq!(txid.len(), 64);
}

#[test]
#[cfg_attr(not(feature = "regtest"), ignore)]
fn test_multisig_same_key_sdk() {
    skip_if_no_node();
    let artifact = compile_contract("integration/contracts/crypto/MultiSig2of3.runar.ts");
    let mut provider = create_provider();
    let (signer, wallet) = create_funded_wallet(&mut provider);
    let (_s2, other) = create_funded_wallet(&mut provider);
    let mut contract = RunarContract::new(
        artifact,
        vec![
            SdkValue::Bytes(wallet.pub_key_hex.clone()),
            SdkValue::Bytes(wallet.pub_key_hex.clone()),
            SdkValue::Bytes(other.pub_key_hex.clone()),
        ],
    );
    contract
        .deploy(
            &mut provider,
            &*signer,
            &DeployOptions {
                satoshis: 5000,
                change_address: None,
                ..Default::default()
            },
        )
        .expect("deploy");
    // Auto Sig args — both auto-signed by same signer
    let (txid, _) = contract
        .call(
            "unlock",
            &[SdkValue::Auto, SdkValue::Auto],
            &mut provider,
            &*signer,
            None,
        )
        .expect("unlock");
    assert_eq!(txid.len(), 64);
}
