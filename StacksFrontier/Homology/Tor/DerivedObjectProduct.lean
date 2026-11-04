module

public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.GradedAlgebra
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Products on the Tor of a derived object along a ring map

Let `R → A` be a homomorphism of commutative rings and let `K, L ∈ D(R)`. Writing
`Torᴿₙ(K, A) = H⁻ⁿ(K ⊗ᴸ_R A)`, the cocycle pairing on the cohomology of a derived tensor
product over `A`, transported along the base-change identification
`(K ⊗ᴸ_R A) ⊗ᴸ_A (L ⊗ᴸ_R A) ≅ (K ⊗ᴸ_R L) ⊗ᴸ_R A`, gives products

`Torᴿₙ(K, A) ⊗[A] Torᴿₘ(L, A) ⟶ Torᴿₙ₊ₘ(K ⊗ᴸ_R L, A)`.

## Main definitions

* `RingTheory.TorProducts.derivedTor` is `Torᴿₙ(-, A)` on `D(R)`, for a model of derived
  extension of scalars.
* `RingTheory.TorProducts.derivedTensorBaseChangeIso` is the base-change identification for the
  canonical derived tensor products.
* `RingTheory.TorProducts.derivedTensorBaseChangeProduct` is the product in cohomological
  indexing, and `RingTheory.TorProducts.derivedTorProduct` the same product in Tor indexing.

## Main results

* `RingTheory.TorProducts.derivedTorProduct_eq` exhibits the product as the cohomology pairing
  followed by the base-change identification.

## Implementation notes

The cohomology pairing is `RingTheory.TorProducts.cohomologyTensorProduct` and the
identification is `CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso`, for the
canonical derived tensor products `CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` on
`D(R)` and on `D(A)`; the model of derived extension of scalars is a parameter.

The pairing lands in degree `i + j` in cohomological indexing; Tor indexing is obtained from it
by the degree cast along `-n + -m = -(n + m)`.

Ring and module universes agree: the monoidal structure on `ModuleCat.{u} A` requires the module
universe to be the ring universe.

## References

* [The Stacks Project, Tag 068G](https://stacks.math.columbia.edu/tag/068G)
-/

open CategoryTheory MonoidalCategory CochainComplex.DerivedTensor

universe u

namespace RingTheory.TorProducts

attribute [local instance] HasDerivedCategory.standard

variable {R A : Type u} [CommRing R] [CommRing A]

/-- `Torᴿₙ(-, A)` on `D(R)`: the `(-n)`-th cohomology of derived extension of scalars along
`f`, for a model `D` of the latter. -/
public noncomputable def derivedTor (f : R →+* A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f) (n : ℤ) :
    DObj R ⥤ ModuleCat.{u} A :=
  D.functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-n)

/-- The base-change identification
`(K ⊗ᴸ_R A) ⊗ᴸ_A (L ⊗ᴸ_R A) ≅ (K ⊗ᴸ_R L) ⊗ᴸ_R A`, for the canonical derived tensor products of
`R` and of `A` and a model `D` of derived extension of scalars. -/
public noncomputable def derivedTensorBaseChangeIso (f : R →+* A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f)
    (K L : DObj R) :
    ((canonicalDerivedTensorProductFunctor A).obj (D.functor.obj K)).obj (D.functor.obj L) ≅
      D.functor.obj (((canonicalDerivedTensorProductFunctor R).obj K).obj L) :=
  (derivedExtensionScalarsTensorIso f (canonicalDerivedTensorProduct R).toGeneral
    (canonicalDerivedTensorProduct A).toGeneral D).iso.app (K, L)

/-- The product on the cohomology of derived extension of scalars, in cohomological indexing:
the cocycle pairing over `A`, followed by the base-change identification. -/
public noncomputable def derivedTensorBaseChangeProduct (f : R →+* A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f)
    (K L : DObj R) (i j : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (D.functor.obj K) ⊗
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj (D.functor.obj L) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i + j)).obj
        (D.functor.obj (((canonicalDerivedTensorProductFunctor R).obj K).obj L)) :=
  (cohomologyTensorProduct (D.functor.obj K) (D.functor.obj L) i j).map ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i + j)).map
      (derivedTensorBaseChangeIso f D K L).hom

/-- The degree identification reading cohomology in degree `-n + -m` as `Torᴿₙ₊ₘ`. -/
public noncomputable def derivedTorSumIso (f : R →+* A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f)
    (X : DObj R) (n m : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-n + -m)).obj (D.functor.obj X) ≅
      (derivedTor f D (n + m)).obj X :=
  eqToIso (congrArg
    (fun d => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).obj (D.functor.obj X))
    (neg_add n m).symm)

/-- The products
`Torᴿₙ(K, A) ⊗[A] Torᴿₘ(L, A) ⟶ Torᴿₙ₊ₘ(K ⊗ᴸ_R L, A)` on the Tor of derived objects
`K, L ∈ D(R)`: the cocycle pairing over `A` carried along the base-change identification. -/
@[stacks 068G "products on the Tor of derived objects, the last display of the paragraph
  following Equation 15.64.0.2"]
public noncomputable def derivedTorProduct (f : R →+* A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f)
    (K L : DObj R) (n m : ℤ) :
    (derivedTor f D n).obj K ⊗ (derivedTor f D m).obj L ⟶
      (derivedTor f D (n + m)).obj (((canonicalDerivedTensorProductFunctor R).obj K).obj L) :=
  derivedTensorBaseChangeProduct f D K L (-n) (-m) ≫
    (derivedTorSumIso f D (((canonicalDerivedTensorProductFunctor R).obj K).obj L) n m).hom

/-- The product on Tor is the cocycle pairing on the cohomology of the derived tensor product
over `A`, followed by the base-change identification and the degree identification. -/
public lemma derivedTorProduct_eq (f : R →+* A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f)
    (K L : DObj R) (n m : ℤ) :
    derivedTorProduct f D K L n m =
      (cohomologyTensorProduct (D.functor.obj K) (D.functor.obj L) (-n) (-m)).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-n + -m)).map
          (derivedTensorBaseChangeIso f D K L).hom ≫
        (derivedTorSumIso f D (((canonicalDerivedTensorProductFunctor R).obj K).obj L) n m).hom :=
  Category.assoc _ _ _

end RingTheory.TorProducts

/-! ### The remaining content of Section 15.64 -/

add_to_stacks 068G "Equation 15.64.0.1: the pairing `Hⁱ(K) ⊗ Hʲ(L) ⟶ Hⁱ⁺ʲ(K ⊗ᴸ L)` sending the
  classes of cocycles `k, l` to the class of `k ⊗ l`."
  RingTheory.TorProducts.cohomologyTensorProduct

add_to_stacks 068G "Equation 15.64.0.2: the canonical identification
  `(K ⊗ᴸ_R A) ⊗ᴸ_A (L ⊗ᴸ_R A) = (K ⊗ᴸ_R L) ⊗ᴸ_R A` in `D(A)`."
  CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso

add_to_stacks 068G "Equation 15.64.0.3: the products
  `Torᴿₙ(M, A) ⊗[A] Torᴿₘ(N, A) ⟶ Torᴿₙ₊ₘ(M ⊗_R N, A)` for `R`-modules `M` and `N`."
  RingTheory.TorProducts.torProduct

add_to_stacks 068G "The `A`-algebra structure on `Torᴿ_⋆(B, A)` for an `R`-algebra `B`, whose
  multiplication is the product of Equation 15.64.0.3 followed by the map induced by the
  multiplication `B ⊗_R B → B`." GradedTor.existsUnique_algebra

add_to_stacks 068G "The multiplication of the `A`-algebra `Torᴿ_⋆(B, A)` is the product of
  Equation 15.64.0.3 followed by the map induced by multiplication on `B`."
  GradedTor.canonical_mul_ofNat

add_to_stacks 068G "Lemma 15.64.1: for an `R`-algebra map `B → C` the induced map
  `Torᴿ_⋆(B, A) ⟶ Torᴿ_⋆(C, A)` is a homomorphism of `A`-algebras. The source omits the proof."
  GradedTor.torPieceMap_isAlgebraHom

end
