module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimension

/-!
# Tor amplitude depends only on the underived tensor product

`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` carries both an underived tensor
product `- ⊗_{𝒪_X} -` and a derived one `- ⊗^{L}_{𝒪_X} -`, together with the
`CategoryTheory.Functor.IsLeftDerivedFunctor` certificate tying the second to the first. Since a
total left derived functor is unique up to canonical isomorphism, the derived half is determined
by the underived half, and so is every predicate defined from it.

This file proves that, for the predicates of Stacks 08CG: two certificates with the same
underived tensor product define the same Tor amplitude, the same finite Tor dimension and the
same Tor dimension of a module, and two families of certificates with the same underived tensor
products define the same locally finite Tor dimension.

## Main results

* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasTorAmplitudeIn_congr`
* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasFiniteTorDimension_congr`
* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasTorDimensionLE_congr`
* `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_congr`

## Implementation notes

The content is `CategoryTheory.Functor.leftDerivedUnique`: for a fixed `𝒪_X`-module `ℱ`, both
certificates exhibit their `- ⊗^{L} ℱ[0]` as a total left derived functor of the *same* functor
`(- ⊗ ℱ)` read on complexes, along the *same* localization `DerivedCategory.Q` at the *same*
class of quasi-isomorphisms. Hence the two are isomorphic as functors, and `CategoryTheory.IsZero`
transports along the isomorphism obtained by evaluating at `E` and applying `H^i`.

The equality hypothesis is on the `tensor` field alone. The `additive` field is then forced:
`CategoryTheory.Functor.Additive` is a `Prop`, so the two certificates' additivity proofs are
definitionally equal and the two functors being derived are literally the same functor. This is
why the statement does not need, and does not assume, any compatibility between the two
`comparison` fields — the isomorphism is constructed, not supplied.

These lemmas are what makes it legitimate to state a theorem "at the genuine derived tensor
product" of Stacks 06YU, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Perfect.TorDimension` and
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimension` require: the resulting predicate
depends on the genuine underived tensor product `Stacks.SheafOfModules.Tensor.sheafTensor` only,
  and not on
which total left derived functor of it is chosen. Without that, naming the genuine certificate
would still leave the predicate depending on an arbitrary choice.

No `@[stacks]` attribute is placed: no tag of the Stacks project states this. It is the
well-definedness of the predicates of Stacks 08CG under the hypothesis form this development
states them in.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace

section Congr

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

namespace CertifiedDerivedSheafTensoring

/-- **Two total left derived functors of one functor have the same vanishing cohomology.**

The abstract step behind every `_congr` lemma in this file: `LF₁` and `LF₂` are both total left
derived functors of `G` along `DerivedCategory.Q`, so they are isomorphic, so `H^i(LF₁ E)`
vanishes exactly when `H^i(LF₂ E)` does. -/
public theorem isZero_homology_iff_of_isLeftDerived
    {G : CochainComplex (OXMod.{u, u} X) ℤ ⥤ DerivedCategory (OXMod.{u, u} X)}
    (LF₁ LF₂ : DerivedCategory (OXMod.{u, u} X) ⥤ DerivedCategory (OXMod.{u, u} X))
    (α₁ : DerivedCategory.Q ⋙ LF₁ ⟶ G) (α₂ : DerivedCategory.Q ⋙ LF₂ ⟶ G)
    [LF₁.IsLeftDerivedFunctor α₁
      (HomologicalComplex.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ))]
    [LF₂.IsLeftDerivedFunctor α₂
      (HomologicalComplex.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ))]
    (E : DerivedCategory (OXMod.{u, u} X)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj (LF₁.obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj (LF₂.obj E)) := by
  have e : LF₁ ≅ LF₂ :=
    Functor.leftDerivedUnique LF₂ LF₁ α₁ α₂
      (HomologicalComplex.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ))
  exact ⟨fun h => h.of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso (e.app E).symm),
    fun h => h.of_iso
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).mapIso (e.app E))⟩

/-- **Stacks 08CG (1) depends only on the underived tensor product.** Two certificates with the
same underived tensor product `- ⊗_{𝒪_X} -` define the same Tor amplitude. -/
public theorem hasTorAmplitudeIn_congr (D₁ D₂ : CertifiedDerivedSheafTensoring.{d, u} X)
    (h : D₁.tensor = D₂.tensor) (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    D₁.HasTorAmplitudeIn E a b ↔ D₂.HasTorAmplitudeIn E a b := by
  obtain ⟨t₁, add₁, dt₁, c₁, il₁⟩ := D₁
  obtain ⟨t₂, add₂, dt₂, c₂, il₂⟩ := D₂
  dsimp only at h
  subst h
  have hadd : add₁ = add₂ := funext fun _ => rfl
  subst hadd
  refine forall_congr' fun F => forall_congr' fun i => imp_congr_right fun _ => ?_
  let _ := add₁ F
  exact isZero_homology_iff_of_isLeftDerived
    (dt₁.flip.obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F))
    (dt₂.flip.obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F))
    (c₁ F) (c₂ F) E i

/-- **Stacks 08CG (2) depends only on the underived tensor product.** -/
public theorem hasFiniteTorDimension_congr (D₁ D₂ : CertifiedDerivedSheafTensoring.{d, u} X)
    (h : D₁.tensor = D₂.tensor) (E : DerivedCategory (OXMod.{u, u} X)) :
    D₁.HasFiniteTorDimension E ↔ D₂.HasFiniteTorDimension E :=
  exists_congr fun a => exists_congr fun b => hasTorAmplitudeIn_congr D₁ D₂ h E a b

/-- **The last sentence of Stacks 08CG depends only on the underived tensor product.** -/
public theorem hasTorDimensionLE_congr (D₁ D₂ : CertifiedDerivedSheafTensoring.{d, u} X)
    (h : D₁.tensor = D₂.tensor) (F : OXMod.{u, u} X) (n : ℤ) :
    D₁.HasTorDimensionLE F n ↔ D₂.HasTorDimensionLE F n :=
  hasTorAmplitudeIn_congr D₁ D₂ h
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) (-n) 0

end CertifiedDerivedSheafTensoring

end Congr

section CongrLocal

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ U : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **Stacks 08CG (3) depends only on the underived tensor products.** Two families of
certificates whose underived tensor products agree on every open subspace define the same
locally finite Tor dimension. -/
public theorem locallyHasFiniteTorDimension_congr
    (D₁ D₂ : ∀ U : Opens X.carrier,
      CertifiedDerivedSheafTensoring.{d', u} (X.restrict U.isOpenEmbedding))
    (h : ∀ U : Opens X.carrier, (D₁ U).tensor = (D₂ U).tensor)
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X D₁ E ↔ LocallyHasFiniteTorDimension X D₂ E :=
  exists_congr fun _ => exists_congr fun U => and_congr_right fun _ =>
    forall_congr' fun i =>
      CertifiedDerivedSheafTensoring.hasFiniteTorDimension_congr (D₁ (U i)) (D₂ (U i)) (h (U i))
        ((derivedRestrictModules X (U i)).obj E)

end CongrLocal

end AlgebraicGeometry.RingedSpace

end
