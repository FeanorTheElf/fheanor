
use std::fmt::Display;
use std::fs::File;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Read;
use std::marker::PhantomData;

use feanor_math::integer::*;
use feanor_math::ring::*;
use feanor_math::rings::rust_bigint::RustBigint;
use feanor_math::serialization::*;
use serde::de::DeserializeSeed;
use serde::{Deserialize, Serialize};
use feanor_serde::{impl_deserialize_seed_for_dependent_enum, impl_deserialize_seed_for_dependent_struct};

use crate::{log_time, ZZbig, ZZi64};

pub enum CachedDataKey {
    Integer(String, El<BigIntRing>),
    String(String)
}

impl PartialEq for CachedDataKey {

    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Integer(s_k, s_v), Self::Integer(o_k, o_v)) => s_k == o_k && ZZbig.eq_el(s_v, o_v),
            (Self::String(s), Self::String(o)) => s == o,
            _ => false
        }
    }
}

impl Serialize for CachedDataKey {

    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: serde::Serializer
    {
        #[derive(Serialize)]
        #[serde(rename = "KeyedInt", bound = "")]
        struct SerializableKeyedInteger<'a> {
            key: &'a str,
            value: SerializeWithRing<'a, BigIntRing>
        }

        #[derive(Serialize)]
        #[serde(rename = "Key", bound = "")]
        enum SerializableFilenameKey<'a> {
            Integer(SerializableKeyedInteger<'a>),
            String(&'a str)
        }

        match self {
            Self::Integer(key, value) => SerializableFilenameKey::Integer(SerializableKeyedInteger { key: key.as_str(), value: SerializeWithRing::new(value, ZZbig) }),
            Self::String(val) => SerializableFilenameKey::String(val)
        }.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for CachedDataKey {

    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::Deserializer<'de> 
    {
        struct DeserializeSeedKeyedInt;

        impl_deserialize_seed_for_dependent_struct! {
            pub struct KeyedInt<'de> using DeserializeSeedKeyedInt {
                key: String: |_| PhantomData::<String>,
                value: El<BigIntRing>: |_| DeserializeWithRing::new(ZZbig)
            }
        }

        struct DeserializeSeedKey;

        impl_deserialize_seed_for_dependent_enum! {
            pub enum Key<'de> using DeserializeSeedKey {
                Integer(KeyedInt<'de>): |_| DeserializeSeedKeyedInt,
                String(String): |_| PhantomData::<String>
            }
        }

        DeserializeSeedKey.deserialize(deserializer).map(|x| match x {
            Key::Integer(data) => CachedDataKey::Integer(data.0.key, data.0.value),
            Key::String(data) => CachedDataKey::String(data.0)
        })
    }
}

impl Display for CachedDataKey {
    
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            CachedDataKey::Integer(key, val) if ZZbig.abs_log2_ceil(val).unwrap_or(0) < 20 => write!(f, "{}{}", key, ZZbig.format(val)),
            CachedDataKey::Integer(key, val) => write!(f, "{}{}bits", key, ZZbig.abs_log2_ceil(val).unwrap()),
            CachedDataKey::String(x) => write!(f, "{}", x)
        }
    }
}

impl<'a> From<&'a str> for CachedDataKey {

    fn from(value: &'a str) -> Self {
        Self::String(value.to_owned())
    }
}

impl<'a> From<(&'a str, &'a RustBigint)> for CachedDataKey {

    fn from(value: (&'a str, &'a RustBigint)) -> Self {
        Self::Integer(value.0.to_owned(), ZZbig.clone_el(value.1))
    }
}

impl<'a> From<(&'a str, RustBigint)> for CachedDataKey {

    fn from(value: (&'a str, RustBigint)) -> Self {
        Self::Integer(value.0.to_owned(), value.1)
    }
}

impl<'a> From<(&'a str, i64)> for CachedDataKey {

    fn from(value: (&'a str, i64)) -> Self {
        Self::Integer(value.0.to_owned(), int_cast(value.1, ZZbig, ZZi64))
    }
}

impl<'a> From<(&'a str, i32)> for CachedDataKey {

    fn from(value: (&'a str, i32)) -> Self {
        Self::Integer(value.0.to_owned(), int_cast(value.1 as i64, ZZbig, ZZi64))
    }
}

impl<'a> From<(&'a str, usize)> for CachedDataKey {

    fn from(value: (&'a str, usize)) -> Self {
        Self::from((value.0, TryInto::<i64>::try_into(value.1).unwrap()))
    }
}

impl<'a> From<(&'a str, u64)> for CachedDataKey {

    fn from(value: (&'a str, u64)) -> Self {
        Self::from((value.0, TryInto::<i64>::try_into(value.1).unwrap()))
    }
}

#[macro_export]
macro_rules! filename_keys {
    ($($key:ident $(: $value:expr)?),*) => {
        vec![$(<$crate::cache::CachedDataKey as From<_>>::from((stringify!($key) $(, $value)?))),*]
    };
}

pub trait SerializeDeserializeWith<Data> {

    type SerializeWithData<'a>: Serialize where Self: 'a, Data: 'a;
    type DeserializeWithData<'a>: for<'de> DeserializeSeed<'de, Value = Self> where Self: 'a, Data: 'a;

    fn serialize_with<'a>(&'a self, data: &'a Data) -> Self::SerializeWithData<'a>;
    fn deserialize_with<'a>(data: &'a Data) -> Self::DeserializeWithData<'a>;
}

pub struct RingElSerializeDeserializeWithRing<R: ?Sized + RingBase + SerializableElementRing> {
    value: R::Element,
    ring: PhantomData<Box<R>>
}

impl<R: ?Sized + RingBase + SerializableElementRing> RingElSerializeDeserializeWithRing<R> {

    pub const fn from(value: R::Element) -> Self {
        Self { value: value, ring: PhantomData }
    }

    pub fn into(self) -> R::Element {
        self.value
    }
}

pub struct RingElDeserializeWithRing<R>(DeserializeWithRing<R>)
    where R: RingStore, R::Type: SerializableElementRing;

impl<'de, R> DeserializeSeed<'de> for RingElDeserializeWithRing<R>
    where R: RingStore, R::Type: SerializableElementRing
{
    type Value = RingElSerializeDeserializeWithRing<R::Type>;

    fn deserialize<D: serde::Deserializer<'de>>(self, deserializer: D) -> Result<Self::Value, D::Error> {
        self.0.deserialize(deserializer).map(RingElSerializeDeserializeWithRing::from)
    }
}

impl<R> SerializeDeserializeWith<R> for RingElSerializeDeserializeWithRing<R::Type>
    where R: RingStore,
        R::Type: SerializableElementRing
{
    type SerializeWithData<'a> = SerializeWithRing<'a, &'a R> where Self: 'a, R: 'a;
    type DeserializeWithData<'a> = RingElDeserializeWithRing<&'a R> where Self: 'a, R: 'a;

    fn serialize_with<'a>(&'a self, data: &'a R) -> Self::SerializeWithData<'a> { SerializeWithRing::new(&self.value, data) }
    fn deserialize_with<'a>(data: &'a R) -> Self::DeserializeWithData<'a> { RingElDeserializeWithRing(DeserializeWithRing::new(data)) }
}

#[derive(PartialEq, Eq)]
pub enum StoreAs {
    None,
    AlwaysPostcard,
    AlwaysJson,
    PostcardIfNotJson,
    JsonIfNotPostcard,
    AlwaysBoth
}

pub fn create_cached<T, D, F, const LOG: bool>(data: &D, create_fn: F, keys: &[CachedDataKey], dir: Option<&str>, store_format: StoreAs) -> T
    where T: SerializeDeserializeWith<D>,
        F: FnOnce() -> T
{
    assert!(dir.is_some() || store_format == StoreAs::None);

    #[derive(Serialize)]
    #[serde(rename = "KeyedData", bound = "")]
    struct SerializeKeyedData<'a, T, D>
        where T: 'a + SerializeDeserializeWith<D>,
            D: 'a
    {
        keys: &'a [CachedDataKey],
        data: T::SerializeWithData<'a>,
        ignore: ()
    }
    
    struct DeserializeSeedKeyedData<'a, T, Data>
        where T: 'a + SerializeDeserializeWith<Data>,
            Data: 'a
    {
        data: &'a Data,
        element: PhantomData<T>
    }

    impl_deserialize_seed_for_dependent_struct! {
        <{ 'de, 'a, T, Data }> pub struct KeyedData<{'de, 'a, T, Data}> using DeserializeSeedKeyedData<'a, T, Data> {
            keys: Vec<CachedDataKey>: |_| PhantomData,
            data: T: |seed: &DeserializeSeedKeyedData<'a, T, Data>| T::deserialize_with(seed.data),
            ignore: PhantomData<&'a Data>: |_| PhantomData
        } where T: 'a + SerializeDeserializeWith<Data>,
            Data: 'a
    }

    let identifier_string = keys.iter().map(|key| format!("{}", key)).reduce(|l, r| format!("{}_{}", l, r)).unwrap();
    if let Some(dir) = dir {
        let filename_postcard = format!("{}/{}.pcd", dir, identifier_string);
        let filename_json = format!("{}/{}.json", dir, identifier_string);
        let check_result = |x: KeyedData<T, D>| {
            assert!(x.keys == keys, "filename-key mismatch");
            return x.data;
        };
        let (result, store_json, store_postcard) = if let Ok(mut file) = File::open(filename_postcard.as_str()) {
            log_time::<_, _, LOG, _>(&format!("Reading {} from {}", identifier_string, filename_postcard), |[]| {
                let mut content = Vec::new();
                file.read_to_end(&mut content).unwrap();
                drop(file);
                let reader = postcard::de_flavors::Slice::new(&content);
                let mut deserializer = postcard::Deserializer::from_flavor(reader);
                let result = DeserializeSeedKeyedData { data: data, element: PhantomData }.deserialize(&mut deserializer).map_err(|e| e.to_string()).unwrap();
                (check_result(result), store_format == StoreAs::AlwaysJson || store_format == StoreAs::AlwaysBoth, false)
            })
        } else if let Ok(file) = File::open(filename_json.as_str()) {
            log_time::<_, _, LOG, _>(&format!("Reading {} from {}", identifier_string, filename_json), |[]| {
                let reader = serde_json::de::IoRead::new(BufReader::new(file));
                let mut deserializer = serde_json::Deserializer::new(reader);
                let result = DeserializeSeedKeyedData { data: data, element: PhantomData }.deserialize(&mut deserializer).map_err(|e| e.to_string()).unwrap();
                (check_result(result), false, store_format == StoreAs::AlwaysPostcard || store_format == StoreAs::AlwaysBoth)
            })
        } else {
            let result = log_time::<_, _, LOG, _>(&format!("Creating {}", identifier_string), |[]| create_fn());
            (
                result, 
                store_format == StoreAs::AlwaysJson || store_format == StoreAs::JsonIfNotPostcard || store_format == StoreAs::AlwaysBoth, 
                store_format == StoreAs::AlwaysPostcard || store_format == StoreAs::PostcardIfNotJson || store_format == StoreAs::AlwaysBoth
            )
        };
        if store_json {
            let file = File::create(filename_json).unwrap();
            let mut serializer = serde_json::Serializer::new(BufWriter::new(file));
            SerializeKeyedData::<T, D> {
                data: T::serialize_with(&result, data),
                keys: keys,
                ignore: ()
            }.serialize(&mut serializer).unwrap();
        }
        if store_postcard {
            let file = File::create(filename_postcard).unwrap();
            postcard::to_io(&SerializeKeyedData::<T, D> {
                data: T::serialize_with(&result, data),
                keys: keys,
                ignore: ()
            }, BufWriter::new(file)).unwrap();
        }
        return result;
    } else {
        return log_time::<_, _, LOG, _>(&format!("Creating {}", identifier_string), |[]| create_fn());
    }
}
