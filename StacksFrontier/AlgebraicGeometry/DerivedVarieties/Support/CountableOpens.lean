module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover

/-!
# Countability for open subschemes of affine schemes of finite type

Over a countable Noetherian ring `R`, an affine scheme of finite type over `Spec R` has only
countably many open subschemes, and between any two open subschemes of affine schemes of finite
type over `Spec R` there are only countably many morphisms over the base.

## Main results

* `AlgebraicGeometry.countable_opens_of_affine_finiteType`: countability of the open subschemes of
  an affine scheme of finite type over a countable Noetherian ring.
* `AlgebraicGeometry.countable_open_hom_of_affine_finiteType`: countability of the
  base-preserving morphisms between two such open subschemes.

## Implementation notes

A scheme of finite type over the base is represented by an object of the over category whose
structure morphism is both `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact`. An open subscheme is an element of `Scheme.Opens`, and its
structure morphism is the composite of its open immersion with the ambient structure morphism, so
that morphisms over the base are homomorphisms in the corresponding over category.

## References

* [Stacks Project, Tag 0G0U](https://stacks.math.columbia.edu/tag/0G0U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Over a countable ring, a finite-type algebra has only countably many algebra maps into a
countable algebra: such a map is determined by its values on a finite generating set. -/
private lemma countable_algHom_of_finiteType
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] [Countable B] :
    Countable (A →ₐ[R] B) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  exact Function.Injective.countable (f := fun f : A →ₐ[R] B => fun x : s => f x.1)
    fun f g h => AlgHom.ext_of_adjoin_eq_top hs fun x hx => congrFun h ⟨x, hx⟩

/-- An affine scheme of finite type over a countable Noetherian ring has countably many open
subschemes, and countably many sections over each of them. -/
private lemma countable_sections_and_opens
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X : Over (Spec (.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    Countable X.left.Opens ∧ ∀ U : X.left.Opens, Countable Γ((↑U : Scheme.{u}), ⊤) := by
  have hft := LocallyOfFiniteType.finiteType_appLE X.hom
    (isAffineOpen_top (Spec (.of R))) (isAffineOpen_top X.left) le_top
  let : Algebra Γ(Spec (.of R), ⊤) Γ(X.left, ⊤) :=
    (X.hom.appLE ⊤ ⊤ le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of R), ⊤) Γ(X.left, ⊤) := hft
  have hbase : Cardinal.mk Γ(Spec (.of R), ⊤) ≤ Cardinal.aleph0 := by
    rw [Cardinal.mk_congr (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.toEquiv]
    exact Cardinal.mk_le_aleph0
  have hΓ : Cardinal.mk Γ(X.left, ⊤) ≤ Cardinal.aleph0 :=
    (Cardinal.mk_le_of_algebra_finiteType Γ(Spec (.of R), ⊤) Γ(X.left, ⊤)).trans <| by
      simpa using hbase
  have hsize : X.left.size ≤ Cardinal.aleph0 := by
    rw [Scheme.size_of_isAffine X.left]
    exact max_le le_rfl hΓ
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  have key (U : X.left.Opens) : ∃ s : Finset X.left.affineOpens, U = ⨆ W ∈ s, W.1 := by
    obtain ⟨s, hs, hU⟩ :=
      (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X.left)).mp
        (TopologicalSpace.NoetherianSpace.isCompact (U : Set X.left))
    exact ⟨hs.toFinset, by rw [hU]; simp⟩
  constructor
  · have : Countable X.left.affineOpens := Cardinal.mk_le_aleph0_iff.mp <|
      (Scheme.mk_affineOpens_le_size X.left).trans hsize
    exact Function.Surjective.countable
      (f := fun s : Finset X.left.affineOpens => ⨆ W ∈ s, W.1)
      fun U => (key U).imp fun _ h => h.symm
  · intro U
    obtain ⟨s, hU'⟩ := key U
    have (W : s) : Countable Γ(X.left, W.1.1) :=
      Cardinal.mk_le_aleph0_iff.mp ((Scheme.mk_sections_le_size X.left W.1).trans hsize)
    have : Countable Γ(X.left, U) :=
      (X.left.sections_restrict_injective_of_iSup s (·.1) U hU').countable
    exact (Scheme.restrictFunctorΓ.app
      (Opposite.op U)).commRingCatIsoToRingEquiv.toEquiv.injective.countable

/-- The two countability statements for a pair of affine schemes of finite type over a countable
Noetherian ring, proved together so that the sections of the opens of the source are available
when counting morphisms. -/
private lemma countable_both
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] :
    Countable X.left.Opens ∧ ∀ (U : X.left.Opens) (V : Y.left.Opens),
      Countable
        ((Over.mk (U.ι ≫ X.hom) : Over (Spec (.of R))) ⟶
          (Over.mk (V.ι ≫ Y.hom) : Over (Spec (.of R)))) := by
  obtain ⟨hopens, hsections⟩ := countable_sections_and_opens X
  refine ⟨hopens, fun U V => ?_⟩
  have : Countable Γ((↑U : Scheme.{u}), ⊤) := hsections U
  let : Algebra Γ(Spec (.of R), ⊤) Γ(Y.left, ⊤) := Y.hom.appTop.hom.toAlgebra
  let : Algebra Γ(Spec (.of R), ⊤) Γ((↑U : Scheme.{u}), ⊤) :=
    (U.ι ≫ X.hom).appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of R), ⊤) Γ(Y.left, ⊤) := by
    rw [← RingHom.finiteType_algebraMap, RingHom.algebraMap_toAlgebra]
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      LocallyOfFiniteType.finiteType_appLE Y.hom
        (isAffineOpen_top (Spec (.of R))) (isAffineOpen_top Y.left) le_top
  let code :
      ((Over.mk (U.ι ≫ X.hom) : Over (Spec (.of R))) ⟶
        (Over.mk (V.ι ≫ Y.hom) : Over (Spec (.of R)))) →
        (Γ(Y.left, ⊤) →ₐ[Γ(Spec (.of R), ⊤)] Γ((↑U : Scheme.{u}), ⊤)) := fun f =>
    { (f.left ≫ V.ι).appTop.hom with
      commutes' := fun r => by
        change (Y.hom.appTop ≫ (f.left ≫ V.ι).appTop).hom r =
          (U.ι ≫ X.hom).appTop.hom r
        rw [← Scheme.Hom.comp_appTop]
        have hw : (f.left ≫ V.ι) ≫ Y.hom = U.ι ≫ X.hom := by
          have hw' := f.w
          change f.left ≫ (V.ι ≫ Y.hom) = U.ι ≫ X.hom at hw'
          simpa only [Category.assoc] using hw'
        rw [hw] }
  have : Countable
      (Γ(Y.left, ⊤) →ₐ[Γ(Spec (.of R), ⊤)] Γ((↑U : Scheme.{u}), ⊤)) :=
    countable_algHom_of_finiteType
  refine Function.Injective.countable (f := code) fun f g h => ?_
  apply Over.OverMorphism.ext
  apply (cancel_mono V.ι).mp
  apply ext_of_isAffine
  exact congrArg (fun q : Γ(Y.left, ⊤) →ₐ[Γ(Spec (.of R), ⊤)]
    Γ((↑U : Scheme.{u}), ⊤) => CommRingCat.ofHom q.toRingHom) h

/-- An affine scheme of finite type over a countable Noetherian ring has countably many open
subschemes. -/
public theorem countable_opens_of_affine_finiteType
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X : Over (Spec (.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    Countable X.left.Opens :=
  (countable_both X X).1

/-- Given two affine schemes of finite type over a countable Noetherian ring, the type of
morphisms over the base between any two of their open subschemes is countable. -/
public theorem countable_open_hom_of_affine_finiteType
    {R : Type u} [CommRing R] [Countable R] [IsNoetherianRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (U : X.left.Opens) (V : Y.left.Opens) :
    Countable
      ((Over.mk (U.ι ≫ X.hom) : Over (Spec (.of R))) ⟶
        (Over.mk (V.ι ≫ Y.hom) : Over (Spec (.of R)))) :=
  (countable_both X Y).2 U V

end AlgebraicGeometry

end
