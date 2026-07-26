use feanor_math::integer::BigIntRing;
use feanor_math::matrix::{AsPointerToSlice, Submatrix, SubmatrixMut};
use feanor_math::rings::zn::zn_64::*;
use feanor_math::rings::zn::zn_rns;
use feanor_math::seq::VectorView;
use feanor_math::serialization::{DeserializeWithRing, SerializeWithRing};
use serde::de::{DeserializeSeed, Visitor};
use serde::ser::SerializeTuple;
use serde::{Serialize, Serializer, de};

pub fn serialize_rns_data<'a, V>(
    rns_base: &'a zn_rns::Zn<Zn, BigIntRing>,
    data: Submatrix<'a, V, ZnEl>,
) -> impl use<'a, V> + Serialize
where
    V: AsPointerToSlice<ZnEl>,
{
    assert_eq!(rns_base.len(), data.row_count());

    struct SerializeWrapper<'a, V>
    where
        V: AsPointerToSlice<ZnEl>,
    {
        rns_base: &'a zn_rns::Zn<Zn, BigIntRing>,
        data: Submatrix<'a, V, ZnEl>,
    }

    impl<'a, V> Serialize for SerializeWrapper<'a, V>
    where
        V: AsPointerToSlice<ZnEl>,
    {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            let mut tuple = serializer.serialize_tuple(self.data.row_count() * self.data.col_count())?;
            for i in 0..self.data.row_count() {
                for j in 0..self.data.col_count() {
                    tuple.serialize_element(&SerializeWithRing::new(self.data.at(i, j), self.rns_base.at(i)))?;
                }
            }
            return tuple.end();
        }
    }

    return SerializeWrapper { rns_base, data };
}

pub fn deserialize_rns_data<'a, V>(
    rns_base: &'a zn_rns::Zn<Zn, BigIntRing>,
    result: SubmatrixMut<'a, V, ZnEl>,
) -> impl use<'a, V> + for<'de> DeserializeSeed<'de, Value = SubmatrixMut<'a, V, ZnEl>>
where
    V: AsPointerToSlice<ZnEl>,
{
    struct ResultVisitor<'a, V>
    where
        V: AsPointerToSlice<ZnEl>,
    {
        rns_base: &'a zn_rns::Zn<Zn, BigIntRing>,
        result: SubmatrixMut<'a, V, ZnEl>,
    }

    impl<'a, 'de, V> Visitor<'de> for ResultVisitor<'a, V>
    where
        V: AsPointerToSlice<ZnEl>,
    {
        type Value = SubmatrixMut<'a, V, ZnEl>;

        fn expecting(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(
                f,
                "a sequence of {} RNS coefficients",
                self.result.row_count() * self.result.col_count()
            )
        }

        fn visit_seq<S>(mut self, mut seq: S) -> Result<Self::Value, S::Error>
        where
            S: de::SeqAccess<'de>,
        {
            for i in 0..self.result.row_count() {
                for j in 0..self.result.col_count() {
                    if let Some(c) = seq.next_element_seed(DeserializeWithRing::new(self.rns_base.at(i)))? {
                        *self.result.at_mut(i, j) = c;
                    } else {
                        return Err(de::Error::invalid_length(
                            i * self.result.col_count() + j,
                            &format!(
                                "expected a sequence of {} RNS coefficients",
                                self.result.row_count() * self.result.col_count()
                            )
                            .as_str(),
                        ));
                    }
                }
            }
            return Ok(self.result);
        }
    }

    struct DeserializeResult<'a, V>
    where
        V: AsPointerToSlice<ZnEl>,
    {
        rns_base: &'a zn_rns::Zn<Zn, BigIntRing>,
        result: SubmatrixMut<'a, V, ZnEl>,
    }
    impl<'a, 'de, V> DeserializeSeed<'de> for DeserializeResult<'a, V>
    where
        V: AsPointerToSlice<ZnEl>,
    {
        type Value = SubmatrixMut<'a, V, ZnEl>;

        fn deserialize<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            deserializer.deserialize_tuple(
                self.result.col_count() * self.result.row_count(),
                ResultVisitor {
                    rns_base: self.rns_base,
                    result: self.result,
                },
            )
        }
    }

    return DeserializeResult { rns_base, result };
}
