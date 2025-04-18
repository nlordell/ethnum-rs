//! Module containing macros for implementing `core::ops` traits.

macro_rules! impl_cmp {
    (
        impl Cmp for $int:ident ($prim:ident);
    ) => {
        impl ::core::hash::Hash for $int {
            #[inline]
            fn hash<H>(&self, hasher: &mut H)
            where
                H: ::core::hash::Hasher,
            {
                ::core::hash::Hash::hash(&self.0, hasher);
            }
        }

        impl PartialEq for $int {
            #[inline]
            fn eq(&self, other: &Self) -> bool {
                let (ahi, alo) = self.into_words();
                let (bhi, blo) = other.into_words();
                (ahi == bhi) & (alo == blo)
                // bitwise and rather than logical and
                // to make O0 code more effecient.
            }
        }

        impl PartialEq<$prim> for $int {
            #[inline]
            fn eq(&self, other: &$prim) -> bool {
                *self == $int::new(*other)
            }
        }

        impl PartialEq<$int> for $prim {
            #[inline]
            fn eq(&self, other: &$int) -> bool {
                $int::new(*self) == *other
            }
        }

        impl PartialOrd for $int {
            #[inline]
            fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl PartialOrd<$prim> for $int {
            #[inline]
            fn partial_cmp(&self, rhs: &$prim) -> Option<::core::cmp::Ordering> {
                Some(self.cmp(&$int::new(*rhs)))
            }
        }

        impl PartialOrd<$int> for $prim {
            #[inline]
            fn partial_cmp(&self, rhs: &$int) -> Option<::core::cmp::Ordering> {
                Some($int::new(*self).cmp(rhs))
            }
        }
    };
}
