module

public import StacksFrontier.Homology.KFlat.BifunctorTransportEquivalence
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse

/-!
# The derived tensor product along an isomorphism of the base ring

Let `e : R ≃+* S` be an isomorphism of commutative rings. Restriction of scalars along `e` is
an equivalence of abelian categories
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv e : ModuleCat.{u} S ≌ ModuleCat.{u} R`, whose
functor is `ModuleCat.restrictScalars e.toRingHom`, and it carries the tensor product of
`S`-modules to the tensor product of `R`-modules. This file records the resulting comparison of
**derived** tensor products,

`E(x ⊗^𝐋_S y) ≅ E x ⊗^𝐋_R E y`,

as an isomorphism of bifunctors on the unbounded derived categories — on *arbitrary* objects,
and natural in both of them — where `E` is restriction of scalars read on the derived
categories.

The derived tensor product is
`CochainComplex.KFlatBifunctor.derivedBifunctor (MonoidalCategory.curriedTensor (ModuleCat _))`,
the K-flat descent of the total tensor complex of [Stacks, Tag 06YU]; this is the form in which
`CochainComplex.DerivedTensor.OneSided` and `CochainComplex.KFlatMonoidal` state their
comparisons, and `CochainComplex.KFlatMonoidal.derivedMonoidalTensorIso` identifies it with the
tensor product of the monoidal structure of `D(R)`.

## Main definitions

* `CochainComplex.KFlatBifunctor.restrictScalarsCurriedTensorIso`: the abelian-level
  comparison `E(M ⊗_S N) ≅ E M ⊗_R E N`, in the `MonoidalCategory.curriedTensor` spelling that
  the transport engine wants.
* `CochainComplex.KFlatBifunctor.restrictScalarsDerivedTensorIso`: the comparison of derived
  tensor products, as an isomorphism of bifunctors on the derived categories.
* `CochainComplex.KFlatBifunctor.restrictScalarsDerivedTensorObjIso`: the same comparison at a
  pair of objects, `E(x ⊗^𝐋_S y) ≅ E x ⊗^𝐋_R E y`.

## Main results

* `CochainComplex.KFlatBifunctor.restrictScalarsCurriedTensorIso_naturality_left` and
  `restrictScalarsCurriedTensorIso_naturality_right`: the two one-variable naturality squares
  of the abelian comparison. They are exactly the hypotheses `hε₁` and `hε₂` of
  `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`.

## Implementation notes

The comparison is `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`, whose
hypotheses are met as follows:

* the abelian comparison is `CochainComplex.DerivedTensor.restrictScalarsTensorIso`, read
  through the identification of `CochainComplex.DerivedTensor.moduleTensor R` with
  `MonoidalCategory.curriedTensor (ModuleCat.{u} R)`. At module universe equal to the ring
  universe the two bifunctors are *definitionally equal* — both send `(M, N)` to
  `ModuleCat.of R (TensorProduct R M N)` with `LinearMap.lTensor` and `LinearMap.rTensor` for
  the two actions on morphisms — so it applies by `exact`, with no bridge isomorphism, in the
  body of `CochainComplex.KFlatBifunctor.restrictScalarsCurriedTensorIso` and of the two private
  naturality squares;
* additivity of `MonoidalCategory.curriedTensor (ModuleCat.{u} R)` in each slot comes from
  `CategoryTheory.MonoidalPreadditive`, which `ModuleCat` carries, and the existence of the
  total tensor complexes is the `HomologicalComplex.HasMapBifunctor` instance of Mathlib's
  monoidal structure on `CochainComplex (ModuleCat.{u} R) ℤ`;
* the four localization hypotheses are already instances on each of the two sides:
  `CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` and
  `kFlatQLeft_isLocalization_of_hasLeftResolutions`, fed by the K-flat resolutions
  `CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions` and
  `moduleKFlatLocalizerLeft_hasLeftResolutions`;
* additivity of the functor of the equivalence is
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv_additive`, and that of its inverse — which
  is `ModuleCat.restrictScalars e.symm` — is recorded as an instance here, since instance
  search does not unfold the equivalence.

Only the two one-variable naturality squares are proved, and both are checked on pure tensors:
the comparison is the identity map on underlying elements, `e` acting on the scalars alone. In
particular **no monoidal coherence is used**: the transport engine asks for a pairwise
comparison and its two naturality squares, not for a monoidal structure on the functor, so the
associator, the unitors and the braiding of neither tensor product appear anywhere below. This
is why the comparison is available even though restriction of scalars along a ring isomorphism
is not equipped with a `CategoryTheory.Functor.Monoidal` instance, which is what
`CochainComplex.KFlatBifunctor.monoidalDerivedTransportIso` would require.

Everything is at one universe level: `R S : Type u` and modules in `ModuleCat.{u}`. The
monoidal structure on `ModuleCat` needs the module universe to agree with the ring universe, so
this is the level at which the `curriedTensor` spelling is available at all.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace CochainComplex.KFlatBifunctor

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The inverse of the equivalence of `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` is
restriction of scalars along `e.symm`, hence additive. Mathlib records this for the functor
but not for the inverse, and instance search does not unfold the equivalence. -/
instance restrictScalarsEquivalenceOfRingEquiv_inverse_additive (e : R ≃+* S) :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u} e).inverse.Additive :=
  inferInstanceAs (ModuleCat.restrictScalars _).Additive

/-! ### The abelian comparison -/

/-- **Restriction of scalars along a ring isomorphism commutes with the tensor product**, in
the `MonoidalCategory.curriedTensor` spelling: `E(M ⊗_S N) ≅ E M ⊗_R E N`.

This is `CochainComplex.DerivedTensor.restrictScalarsTensorIso`, read backwards. At module
universe equal to the ring universe `CochainComplex.DerivedTensor.moduleTensor R` and
`MonoidalCategory.curriedTensor (ModuleCat.{u} R)` are definitionally the same bifunctor, so
no comparison of the two spellings intervenes. -/
def restrictScalarsCurriedTensorIso (e : R ≃+* S) (M N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj
        (((MonoidalCategory.curriedTensor (ModuleCat.{u} S)).obj M).obj N) ≅
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).obj
          ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
        ((ModuleCat.restrictScalars e.toRingHom).obj N) :=
  (CochainComplex.DerivedTensor.restrictScalarsTensorIso.{u, u} e M N).symm

/-- A commuting square of isomorphisms transposes to one of their inverses. Stated over an
abstract category, so that it applies by `exact` to a goal in which the two spellings of a
tensor product are not interchangeable at reducible transparency. -/
private theorem comp_inv_eq_inv_comp_of_square {C : Type*} [Category C] {X Y X' Y' : C}
    (i : X ≅ Y) (i' : X' ≅ Y') {A : Y ⟶ Y'} {B : X ⟶ X'}
    (h : i.hom ≫ A = B ≫ i'.hom) : A ≫ i'.inv = i.inv ≫ B := by
  rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The abelian comparison is natural in the first variable.** This is the hypothesis `hε₁`
of `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`. -/
theorem restrictScalarsCurriedTensorIso_naturality_left (e : R ≃+* S)
    {M M' : ModuleCat.{u} S} (f : M ⟶ M') (N : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars e.toRingHom).map
          (((MonoidalCategory.curriedTensor (ModuleCat.{u} S)).map f).app N) ≫
        (restrictScalarsCurriedTensorIso e M' N).hom =
      (restrictScalarsCurriedTensorIso e M N).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map
            ((ModuleCat.restrictScalars e.toRingHom).map f)).app
          ((ModuleCat.restrictScalars e.toRingHom).obj N) :=
  comp_inv_eq_inv_comp_of_square _ _ (by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

/-- **The abelian comparison is natural in the second variable.** This is the hypothesis `hε₂`
of `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence`. -/
theorem restrictScalarsCurriedTensorIso_naturality_right (e : R ≃+* S)
    (M : ModuleCat.{u} S) {N N' : ModuleCat.{u} S} (g : N ⟶ N') :
    (ModuleCat.restrictScalars e.toRingHom).map
          (((MonoidalCategory.curriedTensor (ModuleCat.{u} S)).obj M).map g) ≫
        (restrictScalarsCurriedTensorIso e M N').hom =
      (restrictScalarsCurriedTensorIso e M N).hom ≫
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).obj
            ((ModuleCat.restrictScalars e.toRingHom).obj M)).map
          ((ModuleCat.restrictScalars e.toRingHom).map g) :=
  comp_inv_eq_inv_comp_of_square _ _ (by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)

/-! ### The derived comparison -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor product commutes with restriction of scalars along a ring
isomorphism**, as an isomorphism of bifunctors on the derived categories:

`E(x ⊗^𝐋_S y) ≅ E x ⊗^𝐋_R E y`

on arbitrary objects of `D(S)`, natural in both variables.

This is `CochainComplex.KFlatBifunctor.derivedTransportIsoOfEquivalence` at
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv e`, with
`CochainComplex.KFlatBifunctor.restrictScalarsCurriedTensorIso` for the abelian comparison. -/
def restrictScalarsDerivedTensorIso (e : R ≃+* S) :
    derivedTransportSource (MonoidalCategory.curriedTensor (ModuleCat.{u} S))
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor ≅
      derivedTransportTarget (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor :=
  derivedTransportIsoOfEquivalence (MonoidalCategory.curriedTensor (ModuleCat.{u} S))
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e)
    (restrictScalarsCurriedTensorIso e)
    (fun f N => restrictScalarsCurriedTensorIso_naturality_left e f N)
    (fun M {_ _} g => restrictScalarsCurriedTensorIso_naturality_right e M g)

/-- **The derived tensor product commutes with restriction of scalars along a ring
isomorphism**, at a pair of objects of the derived category: `E(x ⊗^𝐋_S y) ≅ E x ⊗^𝐋_R E y`,
read off `CochainComplex.KFlatBifunctor.restrictScalarsDerivedTensorIso`. -/
def restrictScalarsDerivedTensorObjIso (e : R ≃+* S)
    (x y : DerivedCategory (ModuleCat.{u} S)) :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory.obj
        (((derivedBifunctor (MonoidalCategory.curriedTensor (ModuleCat.{u} S))).obj x).obj y) ≅
      ((derivedBifunctor (MonoidalCategory.curriedTensor (ModuleCat.{u} R))).obj
            ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory.obj
              x)).obj
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.mapDerivedCategory.obj y) :=
  derivedTransportObjIsoOfEquivalence (MonoidalCategory.curriedTensor (ModuleCat.{u} S))
    (MonoidalCategory.curriedTensor (ModuleCat.{u} R))
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e)
    (restrictScalarsCurriedTensorIso e)
    (fun f N => restrictScalarsCurriedTensorIso_naturality_left e f N)
    (fun M {_ _} g => restrictScalarsCurriedTensorIso_naturality_right e M g) x y

end Derived

end CochainComplex.KFlatBifunctor

end
