module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Closed immersions into affine space over the base

A morphism of affine schemes that is locally of finite type factors through a closed immersion
into an affine space over the target. Consequently, for a morphism `f : X ⟶ S` locally of finite
type and affine opens `V` of `S` and `U` of `X` with `f(U) ⊆ V`, there is a closed immersion
`U ⟶ 𝔸ⁿ_V` over `V`.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_resLE`: a morphism locally of finite type stays locally
  of finite type after restricting both source and target to opens.
* `AlgebraicGeometry.exists_isClosedImmersion_affineSpace`: a morphism of affine schemes that is
  locally of finite type factors as a closed immersion into an affine space over the target
  followed by the structure morphism of that affine space.
* `AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`: the same for the restriction of
  a morphism locally of finite type to a compatible pair of affine opens.
* `AlgebraicGeometry.flat_affineSpace`: the structure morphism of an affine space over a base is
  flat.

## References

* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 29.15.3 (01T2)](https://stacks.math.columbia.edu/tag/01T2)
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- Restricting both the source and the target of a morphism locally of finite type to opens
leaves it locally of finite type. -/
public theorem locallyOfFiniteType_resLE {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (V : S.Opens) (U : X.Opens) (h : U ≤ f ⁻¹ᵁ V) : LocallyOfFiniteType (f.resLE V U h) :=
  let : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FiniteType)
  let : IsZariskiLocalAtTarget (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := @RingHom.FiniteType)
  IsZariskiLocalAtSource.resLE _ ‹_›

/-- A morphism of affine schemes locally of finite type admits a closed immersion into an affine
space over the target through which it factors. -/
public theorem exists_isClosedImmersion_affineSpace {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (i : X ⟶ AffineSpace (ULift.{u} (Fin n)) S),
      IsClosedImmersion i ∧ i ≫ (AffineSpace.over (ULift.{u} (Fin n)) S).hom = f := by
  have hft : RingHom.FiniteType (f.appTop).hom :=
    HasRingHomProperty.appTop @LocallyOfFiniteType f ‹_›
  let _ : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra Γ(S, ⊤) Γ(X, ⊤)).FG := hft.out
  classical
  set v : ULift.{u} (Fin s.card) → Γ(X, ⊤) := fun i => (s.equivFin.symm i.down : Γ(X, ⊤))
    with hv
  have hrange : Set.range v = (s : Set Γ(X, ⊤)) := by
    ext x
    simp only [hv, Set.mem_range, Finset.mem_coe]
    refine ⟨?_, fun hx => ⟨⟨s.equivFin ⟨x, hx⟩⟩, by simp⟩⟩
    rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i.down).2
  have hsurj : Function.Surjective (MvPolynomial.aeval v (R := Γ(S, ⊤))) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hrange, hs]
  have hover : AffineSpace.homOfVector f v ≫
      (AffineSpace.over (ULift.{u} (Fin s.card)) S).hom = f :=
    AffineSpace.homOfVector_over _ _
  refine ⟨s.card, AffineSpace.homOfVector f v, ?_, hover⟩
  have key : ((AffineSpace.homOfVector f v).appTop).hom.comp
      (MvPolynomial.eval₂Hom ((AffineSpace.over (ULift.{u} (Fin s.card)) S).hom.appTop).hom
        (AffineSpace.coord S)) = (MvPolynomial.aeval v (R := Γ(S, ⊤))).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_C]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hover]
      rfl
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.aeval_X]
      exact AffineSpace.homOfVector_appTop_coord _ _ _
  refine IsClosedImmersion.of_surjective_of_isAffine _ (Function.Surjective.of_comp
    (g := MvPolynomial.eval₂Hom ((AffineSpace.over (ULift.{u} (Fin s.card)) S).hom.appTop).hom
      (AffineSpace.coord S)) ?_)
  rw [← RingHom.coe_comp, key]
  exact hsurj

/-- For a morphism locally of finite type and a pair of affine opens `U` of the source and `V`
of the target with `U ⊆ f⁻¹(V)`, the induced morphism `U ⟶ V` factors as a closed immersion into
an affine space over `V` followed by the structure morphism of that affine space. -/
public theorem exists_isClosedImmersion_affineSpace_resLE {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (V : S.affineOpens) (U : X.affineOpens) (h : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ (n : ℕ) (i : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})),
      IsClosedImmersion i ∧
        i ≫ (AffineSpace.over (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).hom =
          f.resLE V.1 U.1 h :=
  let : IsAffine (U.1 : Scheme.{u}) := U.2
  let : IsAffine (V.1 : Scheme.{u}) := V.2
  let := locallyOfFiniteType_resLE f V.1 U.1 h
  exists_isClosedImmersion_affineSpace (f.resLE V.1 U.1 h)

/-- The structure morphism `𝔸(I; Y) ⟶ Y` of an affine space over a scheme `Y`, on an arbitrary
index type `I`, is flat. -/
public theorem flat_affineSpace (I : Type u) (Y : Scheme.{u}) :
    Flat (AffineSpace.over I Y).hom := by
  let R := ULift.{u} ℤ
  let F : CommRingCat.of R ⟶ CommRingCat.of (MvPolynomial I R) :=
    CommRingCat.ofHom (algebraMap R (MvPolynomial I R))
  have hF : Flat (Spec.map F) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let e := specULiftZIsTerminal.uniqueUpToIso Limits.terminalIsTerminal
  have hterm : Flat (Limits.terminal.from (Spec (.of (MvPolynomial I R)))) := by
    rw [Limits.terminal.hom_ext (Limits.terminal.from _) (Spec.map F ≫ e.hom)]
    infer_instance
  show Flat (Limits.pullback.fst _ _)
  infer_instance

end AlgebraicGeometry

end
