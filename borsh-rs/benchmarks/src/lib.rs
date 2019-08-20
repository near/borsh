//! This library contains data structures used for benchmarking.

use borsh::{BorshDeserialize, BorshSerialize};
use rand::distributions::{Alphanumeric, Distribution, Standard};
use rand::{thread_rng, Rng, RngCore};
use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};
#[macro_use]
extern crate speedy_derive;
use speedy::{Context, Readable, Reader, Writable, Writer};

pub trait Generate {
    fn generate() -> Self;
}

#[derive(
    BorshSerialize, BorshDeserialize, Debug, Clone, Eq, PartialEq, SerdeSerialize, SerdeDeserialize,
)]
pub struct CryptoHash([u8; 32]);
impl Generate for CryptoHash {
    fn generate() -> Self {
        let mut res = [0u8; 32];
        thread_rng().fill_bytes(&mut res);
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
    fn generate() -> Self {
        let mut res = [0u8; 32];
        thread_rng().fill_bytes(&mut res);
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
    fn generate() -> Self {
        let mut res = [0u8; 32];
        thread_rng().fill_bytes(&mut res);
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
    fn generate() -> Self {
        let mut res = [0u8; 32];
        thread_rng().fill_bytes(&mut res);
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
impl Generate for AccountId {
    fn generate() -> Self {
        let len: usize = thread_rng().gen_range(5, 200);
        let res = thread_rng()
            .sample_iter(&Alphanumeric)
            .take(len)
            .collect::<String>();
        AccountId(res)
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
    fn generate() -> Self {
        Self {
            account_id: AccountId::generate(),
            public_key: PublicKey::generate(),
            amount: thread_rng().next_u64(),
        }
    }
}

pub type BlockIndex = u64;
pub type Weight = u64;

pub fn generate_vec_primitives<T>(min_number: usize, max_number: usize) -> Vec<T>
where
    Standard: Distribution<T>,
{
    let num: usize = thread_rng().gen_range(min_number, max_number + 1);
    let mut res = vec![];
    for _ in 0..num {
        res.push(thread_rng().gen());
    }
    res
}

pub fn generate_vec<T: Generate>(min_number: usize, max_number: usize) -> Vec<T> {
    let num: usize = thread_rng().gen_range(min_number, max_number + 1);
    let mut res = vec![];
    for _ in 0..num {
        res.push(T::generate());
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
    fn generate() -> Self {
        Self {
            height: thread_rng().next_u64(),
            epoch_hash: CryptoHash::generate(),
            prev_hash: CryptoHash::generate(),
            prev_state_root: MerkleHash::generate(),
            tx_root: MerkleHash::generate(),
            timestamp: thread_rng().next_u64(),
            approval_mask: generate_vec_primitives(2, 1000),
            approval_sigs: generate_vec(2, 1000),
            total_weight: thread_rng().next_u64(),
            validator_proposals: generate_vec(2, 1000),
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
    fn generate() -> Self {
        Self {
            inner: BlockHeaderInner::generate(),
            signature: Signature::generate(),
            hash: CryptoHash::generate(),
        }
    }
}
