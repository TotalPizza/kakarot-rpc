use jsonrpsee::{
    core::{async_trait, RpcResult as Result},
    proc_macros::rpc,
};

use starknet::{
    core::types::FieldElement,
    providers::jsonrpc::models::BroadcastedInvokeTransactionV1,
    macros::selector,
    core::utils::{starknet_keccak,get_selector_from_name}
};

use jsonrpsee::types::error::CallError;
use kakarot_rpc_core::{
    client::{client_api::KakarotClient, constants::CHAIN_ID},
    helpers::{ethers_block_id_to_starknet_block_id,raw_starknet_calldata},
};

use reth_primitives::{
    rpc::transaction::eip2930::AccessListWithGasUsed, TransactionSigned, TransactionKind, Transaction, Address, BlockId, BlockNumberOrTag, Bytes,
    H256, H160, H64, U128, U256, U64,
};

use reth_rlp::Decodable;
use ethabi::{decode, Contract, FunctionOutputDecoder, Token};
use hex::encode;

use reth_rpc_types::{
    CallRequest, EIP1186AccountProofResponse, FeeHistory, Index, RichBlock, SyncStatus,
    Transaction as EtherTransaction, TransactionReceipt, TransactionRequest, Work,
};
use serde_json::Value;

use crate::eth_api::EthApiServer;
use kakarot_rpc_core::client::types::TokenBalances;

/// The RPC module for the Ethereum protocol required by Kakarot.
pub struct KakarotEthRpc {
    pub kakarot_client: Box<dyn KakarotClient>,
}

#[async_trait]
impl EthApiServer for KakarotEthRpc {
    async fn block_number(&self) -> Result<U64> {
        let block_number = self.kakarot_client.block_number().await?;
        Ok(block_number)
    }

    /// Get the protocol version of the Kakarot Starknet RPC.
    ///
    /// # Returns
    /// * `protocol_version(u64)` - The protocol version.
    ///
    /// `Ok(protocol_version)` if the operation was successful.
    /// `Err(KakarotClientError)` if the operation failed.
    fn protocol_version(&self) -> Result<U64> {
        let protocol_version = 1_u64;
        Ok(protocol_version.into())
    }

    async fn syncing(&self) -> Result<SyncStatus> {
        let status = self.kakarot_client.syncing().await?;
        Ok(status)
    }

    async fn author(&self) -> Result<Address> {
        todo!()
    }

    async fn accounts(&self) -> Result<Vec<Address>> {
        Ok(Vec::new())
    }

    async fn chain_id(&self) -> Result<Option<U64>> {
        // CHAIN_ID = KKRT (0x4b4b5254) in ASCII
        Ok(Some(CHAIN_ID.into()))
    }

    async fn block_by_hash(&self, _hash: H256, _full: bool) -> Result<Option<RichBlock>> {
        let block_id = BlockId::Hash(_hash.into());
        let starknet_block_id = ethers_block_id_to_starknet_block_id(block_id)?;
        let block = self
            .kakarot_client
            .get_eth_block_from_starknet_block(starknet_block_id, _full)
            .await?;
        Ok(Some(block))
    }

    async fn block_by_number(
        &self,
        _number: BlockNumberOrTag,
        _full: bool,
    ) -> Result<Option<RichBlock>> {
        let block_id = BlockId::Number(_number);
        let starknet_block_id = ethers_block_id_to_starknet_block_id(block_id)?;
        let block = self
            .kakarot_client
            .get_eth_block_from_starknet_block(starknet_block_id, _full)
            .await?;
        Ok(Some(block))
    }

    async fn block_transaction_count_by_hash(&self, hash: H256) -> Result<U64> {
        let transaction_count = self
            .kakarot_client
            .block_transaction_count_by_hash(hash)
            .await?;
        Ok(transaction_count)
    }

    async fn block_transaction_count_by_number(&self, _number: BlockNumberOrTag) -> Result<U64> {
        let transaction_count = self
            .kakarot_client
            .block_transaction_count_by_number(_number)
            .await?;
        Ok(transaction_count)
    }

    async fn block_uncles_count_by_hash(&self, _hash: H256) -> Result<U256> {
        todo!()
    }

    async fn block_uncles_count_by_number(&self, _number: BlockNumberOrTag) -> Result<U256> {
        todo!()
    }

    async fn uncle_by_block_hash_and_index(
        &self,
        _hash: H256,
        _index: Index,
    ) -> Result<Option<RichBlock>> {
        todo!()
    }

    async fn uncle_by_block_number_and_index(
        &self,
        _number: BlockNumberOrTag,
        _index: Index,
    ) -> Result<Option<RichBlock>> {
        todo!()
    }

    async fn transaction_by_hash(&self, _hash: H256) -> Result<Option<EtherTransaction>> {
        let ether_tx = EtherTransaction::default();

        Ok(Some(ether_tx))
    }

    async fn transaction_by_block_hash_and_index(
        &self,
        _hash: H256,
        _index: Index,
    ) -> Result<Option<EtherTransaction>> {
        let block_id = BlockId::Hash(_hash.into());
        let starknet_block_id = ethers_block_id_to_starknet_block_id(block_id)?;
        let tx = self
            .kakarot_client
            .transaction_by_block_id_and_index(starknet_block_id, _index)
            .await?;
        Ok(Some(tx))
    }

    async fn transaction_by_block_number_and_index(
        &self,
        _number: BlockNumberOrTag,
        _index: Index,
    ) -> Result<Option<EtherTransaction>> {
        let block_id = BlockId::Number(_number);
        let starknet_block_id = ethers_block_id_to_starknet_block_id(block_id)?;
        let tx = self
            .kakarot_client
            .transaction_by_block_id_and_index(starknet_block_id, _index)
            .await?;
        Ok(Some(tx))
    }

    async fn transaction_receipt(&self, _hash: H256) -> Result<Option<TransactionReceipt>> {
        let receipt = self.kakarot_client.transaction_receipt(_hash).await?;
        Ok(receipt)
    }

    async fn balance(&self, _address: Address, _block_number: Option<BlockId>) -> Result<U256> {
        // 1eth balance
        Ok(U256::from(1_000_000_000_000_000_000_u64))
    }

    async fn storage_at(
        &self,
        _address: Address,
        _index: U256,
        _block_number: Option<BlockId>,
    ) -> Result<H256> {
        todo!()
    }

    async fn transaction_count(
        &self,
        _address: Address,
        _block_number: Option<BlockId>,
    ) -> Result<U256> {
        Ok(U256::from(3))
    }

    async fn get_code(&self, _address: Address, _block_number: Option<BlockId>) -> Result<Bytes> {
        let starknet_block_id = ethers_block_id_to_starknet_block_id(_block_number.unwrap())?;

        let code = self
            .kakarot_client
            .get_code(_address, starknet_block_id)
            .await?;
        Ok(code)
    }

    async fn call(&self, _request: CallRequest, _block_number: Option<BlockId>) -> Result<Bytes> {
        // unwrap option or return jsonrpc error
        let to = _request.to.ok_or_else(|| {
            jsonrpsee::core::Error::Call(CallError::InvalidParams(anyhow::anyhow!(
                "CallRequest `to` field is None. Cannot process a Kakarot call",
            )))
        })?;

        let calldata = _request.data.ok_or_else(|| {
            jsonrpsee::core::Error::Call(CallError::InvalidParams(anyhow::anyhow!(
                "CallRequest `data` field is None. Cannot process a Kakarot call",
            )))
        })?;

        let block_id = _block_number.unwrap_or(BlockId::Number(BlockNumberOrTag::Latest));
        let starknet_block_id = ethers_block_id_to_starknet_block_id(block_id)?;
        let result = self
            .kakarot_client
            .call_view(to, Bytes::from(calldata.0), starknet_block_id)
            .await?;

        Ok(result)
    }

    async fn create_access_list(
        &self,
        _request: CallRequest,
        _block_number: Option<BlockId>,
    ) -> Result<AccessListWithGasUsed> {
        todo!()
    }

    async fn estimate_gas(
        &self,
        _request: CallRequest,
        _block_number: Option<BlockId>,
    ) -> Result<U256> {
        Ok(U256::from(1_000_000_000_u64))
    }

    async fn gas_price(&self) -> Result<U256> {
        let gas_price = self.kakarot_client.base_fee_per_gas();
        Ok(gas_price)
    }

    async fn fee_history(
        &self,
        _block_count: U256,
        _newest_block: BlockNumberOrTag,
        _reward_percentiles: Option<Vec<f64>>,
    ) -> Result<FeeHistory> {
        let fee_history = self
            .kakarot_client
            .fee_history(_block_count, _newest_block, _reward_percentiles)
            .await?;

        Ok(fee_history)
    }

    async fn max_priority_fee_per_gas(&self) -> Result<U128> {
        let max_priority_fee = self.kakarot_client.max_priority_fee_per_gas();
        Ok(max_priority_fee)
    }

    async fn is_mining(&self) -> Result<bool> {
        Err(jsonrpsee::core::Error::Custom("Unsupported method: eth_mining. See available methods at https://github.com/sayajin-labs/kakarot-rpc/blob/main/docs/rpc_api_status.md".to_string()))
    }

    async fn hashrate(&self) -> Result<U256> {
        Err(jsonrpsee::core::Error::Custom("Unsupported method: eth_hashrate. See available methods at https://github.com/sayajin-labs/kakarot-rpc/blob/main/docs/rpc_api_status.md".to_string()))
    }

    async fn get_work(&self) -> Result<Work> {
        Err(jsonrpsee::core::Error::Custom("Unsupported method: eth_getWork. See available methods at https://github.com/sayajin-labs/kakarot-rpc/blob/main/docs/rpc_api_status.md".to_string()))
    }

    async fn submit_hashrate(&self, _hashrate: U256, _id: H256) -> Result<bool> {
        todo!()
    }

    async fn submit_work(&self, _nonce: H64, _pow_hash: H256, _mix_digest: H256) -> Result<bool> {
        todo!()
    }

    async fn send_transaction(&self, _request: TransactionRequest) -> Result<H256> {
        todo!()
    }
    
    async fn send_raw_transaction(&self, _bytes: Bytes) -> Result<H256> {
        let mut data = _bytes.as_ref();

        let transaction = TransactionSigned::decode(&mut data).map_err(|_| {
            println!("Kakarot send_transaction: failed to decode transaction");
        }).unwrap();

        println!("transaction: {:?}", transaction);
        
        // match if transaction is Eip1559
        let to = transaction.kind();
        let to: H160 = match to {
            TransactionKind::Call(to) => *to,
            TransactionKind::Create => Address::zero(),
        };
        // transform to to string
        let input = transaction.input();
        if input.len() > 0{
            //Create abi json for erc20 contract
            let contract_abi_json = r#"[{"inputs":[{"internalType":"uint256","name":"to","type":"uint256"},{"internalType":"uint256","name":"selector","type":"uint256"},{"internalType":"uint256[]","name":"calldata","type":"uint256[]"}],"name":"multicall","outputs":[],"stateMutability":"nonpayable","type":"function"}]"#;
            
            //remove the first 4 bytes of input
            let input = &input[4..];
            
            let transaction_data = decode_transaction_input(input,contract_abi_json).unwrap();
            print!("transaction_data: {:?}", transaction_data); 
            
            // Account Address
            let sender_starknet_address = FieldElement::from_hex_be("0x06d324601b008ba0393e541a3b8f4aab5b9c07a2298f5175d316664ae863728f").unwrap();
            // Contract Address
            let to_address: FieldElement = transaction_data[0];
            // Selector
            // Trim zeros and encode selector
            let selector_bytes = transaction_data[1].to_bytes_be();
            let selector = starknet_keccak(&selector_bytes.iter().filter(|&x| *x != 0).cloned().collect::<Vec<u8>>());
            // Calldata
            let calldata_length: FieldElement = FieldElement::from(transaction_data.len());
            let offset: FieldElement = FieldElement::from(0_u64);
            let nr_calls: FieldElement = FieldElement::from(1_u64);
            // Nonce
            let nonce = FieldElement::from(transaction.nonce());
            // We don't utilize this atm....wouldn't be feasible with multiple signers
            //let signature: Vec<FieldElement> = vec![];

            let mut calldata: Vec<FieldElement> = vec![
                nr_calls,
                to_address,
                selector,
                offset,
                calldata_length-FieldElement::from(7_u64),
                calldata_length,
            ];
            
            //signatures
            calldata.push(transaction_data[2]);
            calldata.push(transaction_data[3]);
            calldata.push(transaction_data[4]);
            calldata.push(transaction_data[5]);
            calldata.push(transaction_data[6]);
            //append nonce and chainID
            calldata.push(FieldElement::from(CHAIN_ID));
            calldata.push(FieldElement::from(transaction.nonce()));
            //append contract address and selector
            calldata.push(to_address);
            calldata.push(selector);

            //append payload to calldata
            for i in 7..transaction_data.len() {
                calldata.push(transaction_data[i]);
            }
            println!("calldata: {:?}", calldata);
            // Get estimated_fee from Starknet
            let max_fee = FieldElement::from(1_000_000_000_000_000_u64);

            let signature = vec![];

            let request = BroadcastedInvokeTransactionV1 {
                max_fee,
                signature,
                nonce,
                sender_address: sender_starknet_address,
                calldata,
            };
            //println!("BYTES!: {:?}", bytes_to_felt_vec(&_bytes));        
            //println!("TX HASH: {:?}",transaction.hash());
            
            println!("request: {:?}", request);
            let transaction_result = self.kakarot_client.submit_starknet_transaction(request).await?;
            println!("transaction_hash: {:?}", transaction_result);
            return Ok(transaction_result);
        }
        //let transaction_result = self.kakarot_client.submit_starknet_transaction(request).await?;
        //println!("transaction_hash: {:?}", transaction_result);
        //Ok(transaction_result)

        // return empty hash
        let hash = H256::from_low_u64_be(0);
        Ok(hash)

        //Ok(transaction_result)
    }

    async fn sign(&self, _address: Address, _message: Bytes) -> Result<Bytes> {
        todo!()
    }

    async fn sign_transaction(&self, _transaction: CallRequest) -> Result<Bytes> {
        todo!()
    }

    async fn sign_typed_data(&self, _address: Address, _data: Value) -> Result<Bytes> {
        todo!()
    }

    async fn get_proof(
        &self,
        _address: Address,
        _keys: Vec<H256>,
        _block_number: Option<BlockId>,
    ) -> Result<EIP1186AccountProofResponse> {
        todo!()
    }
}

fn decode_transaction_input(input_data: &[u8], contract_abi_json: &str) -> Result<Vec<FieldElement>> {
    // Parse the ABI
    let contract = Contract::load(contract_abi_json.as_bytes()).unwrap();

    // Decode the function and its inputs
    let function = contract.function("multicall").unwrap();

    let inputs = function.decode_input(input_data).unwrap();
    println!("INPUTS SER: {:?}", inputs);
    let mut transaction_data_uint: Vec<FieldElement> = vec![];
    for (index, input) in inputs.into_iter().enumerate() {
        println!("Input {}: {:?}", index + 1, input);
        // if token is Array
        match input {
            Token::Array(tokens) => {
                for token in tokens {
                    match uint_to_string(token) {
                        Some(value) => {
                            transaction_data_uint.push(FieldElement::from_dec_str(&value).unwrap())
                        }
                        None => eprintln!("Not a Uint token"),
                    }
                }
            }
            Token::Uint(value) => transaction_data_uint.push(FieldElement::from_dec_str(&value.to_string()).unwrap()),
            _ => eprintln!("Not a Uint token"),
        }
    }
    Ok(transaction_data_uint)
}

pub fn bytes_to_felt_vec(bytes: &Bytes) -> Vec<FieldElement> {
    bytes.to_vec().into_iter().map(FieldElement::from).collect()
}

fn uint_to_string(token: Token) -> Option<String> {
    match token {
        Token::Uint(value) => Some(value.to_string()),
        _ => None,
    }
}

#[rpc(server, client)]
trait KakarotCustomApi {
    #[method(name = "kakarot_getTokenBalances")]
    async fn token_balances(
        &self,
        address: Address,
        contract_addresses: Vec<Address>,
    ) -> Result<TokenBalances>;
}

#[async_trait]
impl KakarotCustomApiServer for KakarotEthRpc {
    async fn token_balances(
        &self,
        address: Address,
        contract_addresses: Vec<Address>,
    ) -> Result<TokenBalances> {
        let token_balances = self
            .kakarot_client
            .token_balances(address, contract_addresses)
            .await?;
        Ok(token_balances)
    }
}

impl KakarotEthRpc {
    #[must_use]
    pub fn new(kakarot_client: Box<dyn KakarotClient>) -> Self {
        Self { kakarot_client }
    }
}
