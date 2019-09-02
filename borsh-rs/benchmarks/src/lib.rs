//! This library contains data structures used for benchmarking.

use borsh::{BorshDeserialize, BorshSerialize};
use rand::distributions::{Alphanumeric, Distribution, Standard};
use rand::{thread_rng, Rng, RngCore};
use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};
#[macro_use]
extern crate speedy_derive;
use speedy::{Context, Readable, Reader, Writable, Writer};

pub trait Generate {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self;
}

#[derive(
    BorshSerialize, BorshDeserialize, Debug, Clone, Eq, PartialEq, SerdeSerialize, SerdeDeserialize,
)]
pub struct CryptoHash([u8; 32]);
impl Generate for CryptoHash {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        let mut res = [0u8; 32];
        rng.fill_bytes(&mut res);
        CryptoHash(res)
    }
}

impl<'a, C> Readable<'a, C> for CryptoHash
where
    C: Context,
{
    fn read_from<R: Reader<'a, C>>(reader: &mut R) -> Result<Self, std::io::Error> {
        let mut data = [0u8; 32];
        reader.read_bytes(&mut data)?;
        Ok(Self(data))
    }
}

impl<C: Context> Writable<C> for CryptoHash {
    fn write_to<'a, T: ?Sized + Writer<'a, C>>(
        &'a self,
        writer: &mut T,
    ) -> Result<(), std::io::Error> {
        writer.write_bytes(&self.0).map(|_| ())
    }
}

#[derive(
    BorshSerialize, BorshDeserialize, Debug, Clone, Eq, PartialEq, SerdeSerialize, SerdeDeserialize,
)]
pub struct MerkleHash([u8; 32]);
impl Generate for MerkleHash {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        let mut res = [0u8; 32];
        rng.fill_bytes(&mut res);
        MerkleHash(res)
    }
}

impl<'a, C> Readable<'a, C> for MerkleHash
where
    C: Context,
{
    fn read_from<R: Reader<'a, C>>(reader: &mut R) -> Result<Self, std::io::Error> {
        let mut data = [0u8; 32];
        reader.read_bytes(&mut data)?;
        Ok(Self(data))
    }
}

impl<C: Context> Writable<C> for MerkleHash {
    fn write_to<'a, T: ?Sized + Writer<'a, C>>(
        &'a self,
        writer: &mut T,
    ) -> Result<(), std::io::Error> {
        writer.write_bytes(&self.0).map(|_| ())
    }
}

#[derive(
    BorshSerialize, BorshDeserialize, Debug, Clone, Eq, PartialEq, SerdeSerialize, SerdeDeserialize,
)]
pub struct Signature([u8; 32]);
impl Generate for Signature {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        let mut res = [0u8; 32];
        rng.fill_bytes(&mut res);
        Signature(res)
    }
}

impl<'a, C> Readable<'a, C> for Signature
where
    C: Context,
{
    fn read_from<R: Reader<'a, C>>(reader: &mut R) -> Result<Self, std::io::Error> {
        let mut data = [0u8; 32];
        reader.read_bytes(&mut data)?;
        Ok(Self(data))
    }
}

impl<C: Context> Writable<C> for Signature {
    fn write_to<'a, T: ?Sized + Writer<'a, C>>(
        &'a self,
        writer: &mut T,
    ) -> Result<(), std::io::Error> {
        writer.write_bytes(&self.0).map(|_| ())
    }
}

#[derive(
    BorshSerialize, BorshDeserialize, Debug, Clone, Eq, PartialEq, SerdeSerialize, SerdeDeserialize,
)]
pub struct PublicKey([u8; 32]);
impl Generate for PublicKey {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        let mut res = [0u8; 32];
        rng.fill_bytes(&mut res);
        PublicKey(res)
    }
}

impl<'a, C> Readable<'a, C> for PublicKey
where
    C: Context,
{
    fn read_from<R: Reader<'a, C>>(reader: &mut R) -> Result<Self, std::io::Error> {
        let mut data = [0u8; 32];
        reader.read_bytes(&mut data)?;
        Ok(Self(data))
    }
}

impl<C: Context> Writable<C> for PublicKey {
    fn write_to<'a, T: ?Sized + Writer<'a, C>>(
        &'a self,
        writer: &mut T,
    ) -> Result<(), std::io::Error> {
        writer.write_bytes(&self.0).map(|_| ())
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct AccountId(String);
impl Generate for String {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        let len: usize = rng.gen_range(5, 200);
        let res = rng
            .sample_iter(&Alphanumeric)
            .take(len)
            .collect::<String>();
        res
    }
}

impl Generate for AccountId {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        AccountId(String::generate(rng))
    }
}

pub type Balance = u64;

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct ValidatorStake {
    pub account_id: AccountId,
    pub public_key: PublicKey,
    pub amount: Balance,
}

impl Generate for ValidatorStake {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            account_id: AccountId::generate(rng),
            public_key: PublicKey::generate(rng),
            amount: u64::generate(rng),
        }
    }
}

pub type BlockIndex = u64;
pub type Weight = u64;

pub fn generate_vec_primitives<T, R>(rng: &mut R, min_number: usize, max_number: usize) -> Vec<T>
where
    Standard: Distribution<T>,
    R: rand::Rng
{
    let num: usize = rng.gen_range(min_number, max_number + 1);
    let mut res = vec![];
    for _ in 0..num {
        res.push(rng.gen());
    }
    res
}

pub fn generate_vec<T: Generate, R: rand::Rng>(rng: &mut R, min_number: usize, max_number: usize) -> Vec<T> {
    let num: usize = rng.gen_range(min_number, max_number + 1);
    let mut res = vec![];
    for _ in 0..num {
        res.push(T::generate(rng));
    }
    res
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct BlockHeaderInner {
    pub height: BlockIndex,
    pub epoch_hash: CryptoHash,
    pub prev_hash: CryptoHash,
    pub prev_state_root: MerkleHash,
    pub tx_root: MerkleHash,
    pub timestamp: u64,
    pub approval_mask: Vec<bool>,
    pub approval_sigs: Vec<Signature>,
    pub total_weight: Weight,
    pub validator_proposals: Vec<ValidatorStake>,
}

impl Generate for BlockHeaderInner {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            height: u64::generate(rng),
            epoch_hash: CryptoHash::generate(rng),
            prev_hash: CryptoHash::generate(rng),
            prev_state_root: MerkleHash::generate(rng),
            tx_root: MerkleHash::generate(rng),
            timestamp: u64::generate(rng),
            approval_mask: generate_vec_primitives(rng, 2, 1000),
            approval_sigs: generate_vec(rng, 2, 1000),
            total_weight: u64::generate(rng),
            validator_proposals: generate_vec(rng, 2, 1000),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct BlockHeader {
    pub inner: BlockHeaderInner,
    pub signature: Signature,
    pub hash: CryptoHash,
}

impl Generate for BlockHeader {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            inner: BlockHeaderInner::generate(rng),
            signature: Signature::generate(rng),
            hash: CryptoHash::generate(rng),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct Block {
    pub header: BlockHeader,
    pub transactions: Vec<SignedTransaction>,
}

impl Generate for Block {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            header: BlockHeader::generate(rng),
            transactions: generate_vec(rng, 0, 1000),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct SignedTransaction {
    transaction: Transaction,
    signature: Signature,
    hash: CryptoHash,
}

impl Generate for SignedTransaction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            transaction: Transaction::generate(rng),
            signature: Signature::generate(rng),
            hash: CryptoHash::generate(rng),
        }
    }
}

pub type Nonce = u64;

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct Transaction {
    signer_id: AccountId,
    public_key: PublicKey,
    nonce: Nonce,
    receiver_id: AccountId,
    actions: Vec<Action>,
}

impl Generate for Transaction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            signer_id: AccountId::generate(rng),
            public_key: PublicKey::generate(rng),
            nonce: u64::generate(rng),
            receiver_id: AccountId::generate(rng),
            actions: generate_vec(rng, 1, 10),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub enum Action {
    CreateAccount(CreateAccountAction),
    DeployContract(DeployContractAction),
    FunctionCall(FunctionCallAction),
    Transfer(TransferAction),
    Stake(StakeAction),
    AddKey(AddKeyAction),
    DeleteKey(DeleteKeyAction),
    DeleteAccount(DeleteAccountAction),
}

impl Generate for Action {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        use Action::*;
        // Deploy contract action is 1000 times less frequent than other actions.
        if u64::generate(rng) % 1000 == 0 {
            DeployContract(DeployContractAction::generate(rng))
        } else {
            match u64::generate(rng) % 7 {
                0 => CreateAccount(CreateAccountAction::generate(rng)),
                1 => FunctionCall(FunctionCallAction::generate(rng)),
                2 => Transfer(TransferAction::generate(rng)),
                3 => Stake(StakeAction::generate(rng)),
                4 => AddKey(AddKeyAction::generate(rng)),
                5 => DeleteKey(DeleteKeyAction::generate(rng)),
                6 => DeleteAccount(DeleteAccountAction::generate(rng)),
                _ => unimplemented!(),
            }
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct CreateAccountAction {}
impl Generate for CreateAccountAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {}
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct DeployContractAction {
    code: Vec<u8>,
}

pub fn generate_vec_u8<R: rand::Rng>(rng: &mut R, min_number: usize, max_number: usize) -> Vec<u8> {
    let num: usize = rng.gen_range(min_number, max_number + 1);
    let mut res = vec![0u8; num];
    rng.fill_bytes(&mut res);
    res
}

impl Generate for DeployContractAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            // Between 20KiB and 1MiB.
            code: generate_vec_u8(rng, 20 * 2usize.pow(10), 2usize.pow(20)),
        }
    }
}

pub type Gas = u64;

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct FunctionCallAction {
    method_name: String,
    args: Vec<u8>,
    gas: Gas,
    deposit: Balance,
}

impl Generate for FunctionCallAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            method_name: String::generate(rng),
            args: generate_vec_u8(rng, 0, 1000),
            gas: u64::generate(rng),
            deposit: u64::generate(rng),
        }
    }
}
#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct TransferAction {
    deposit: Balance,
}
impl Generate for TransferAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            deposit: u64::generate(rng),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct StakeAction {
    stake: Balance,
    public_key: PublicKey,
}

impl Generate for StakeAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            stake: u64::generate(rng),
            public_key: PublicKey::generate(rng),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct AddKeyAction {
    public_key: PublicKey,
    access_key: AccessKey,
}

impl Generate for AddKeyAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            public_key: PublicKey::generate(rng),
            access_key: AccessKey::generate(rng),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct DeleteKeyAction {
    public_key: PublicKey,
}

impl Generate for DeleteKeyAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            public_key: PublicKey::generate(rng),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct DeleteAccountAction {
    beneficiary_id: AccountId,
}

impl Generate for DeleteAccountAction {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            beneficiary_id: AccountId::generate(rng),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct AccessKey {
    nonce: Nonce,
    permission: AccessKeyPermission,
}

impl Generate for AccessKey {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            nonce: u64::generate(rng),
            permission: AccessKeyPermission::generate(rng),
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub enum AccessKeyPermission {
    FunctionCall(FunctionCallPermission),
    FullAccess,
}

impl Generate for AccessKeyPermission {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        if u64::generate(rng) % 2 == 0 {
            AccessKeyPermission::FunctionCall(FunctionCallPermission::generate(rng))
        } else {
            AccessKeyPermission::FullAccess
        }
    }
}

#[derive(
    BorshSerialize,
    BorshDeserialize,
    Debug,
    Clone,
    Eq,
    PartialEq,
    SerdeSerialize,
    SerdeDeserialize,
    Readable,
    Writable,
)]
pub struct FunctionCallPermission {
    allowance: Option<Balance>,
    receiver_id: AccountId,
    method_names: Vec<String>,
}

fn generate_option<T: Generate, R: rand::Rng>(rng: &mut R) -> Option<T> {
    if u64::generate(rng) % 2 == 0 {
        None
    } else {
        Some(T::generate(rng))
    }
}

impl Generate for u64 {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        rng.next_u64()
    }
}

impl Generate for FunctionCallPermission {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            allowance: generate_option(rng),
            receiver_id: AccountId::generate(rng),
            method_names: generate_vec(rng, 0, 10),
        }
    }
}

#[derive(
BorshSerialize,
BorshDeserialize,
Debug,
Clone,
Eq,
PartialEq,
SerdeSerialize,
SerdeDeserialize,
Readable,
Writable,
)]
pub struct Account {
    pub amount: Balance,
    pub staked: Balance,
    pub code_hash: CryptoHash,
    pub storage_usage: u64,
    pub storage_paid_at: u64,
}

impl Generate for Account {
    fn generate<R: rand::Rng>(rng: &mut R) -> Self {
        Self {
            amount: u64::generate(rng),
            staked: u64::generate(rng),
            code_hash: CryptoHash::generate(rng),
            storage_usage: u64::generate(rng),
            storage_paid_at: u64::generate(rng)
        }
    }
}
