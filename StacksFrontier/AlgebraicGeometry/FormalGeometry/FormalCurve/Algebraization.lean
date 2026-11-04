module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.Ample
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SectionLifting
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemEmbeddedTuple
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemLifting
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AmpleFormalSystemSections
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnit
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ProjectiveClosedSubschemeAlgebraization

/-!
# Algebraization of a formal curve over a complete base

Let `A` be a Noetherian ring complete with respect to an ideal `I`, write `S = Spec A` and
`Sₙ = Spec (A / I ^ (n + 1))`, and let `X₀ ⟶ X₁ ⟶ ⋯` be schemes over `S₀ ⟶ S₁ ⟶ ⋯` with cartesian
squares. If `X₀ ⟶ S₀` is proper and the underlying space of `X₀` has dimension at most one, then
there are an H-projective morphism `X ⟶ S` and morphisms `kₙ : Xₙ ⟶ X`, compatible with the
transition maps, exhibiting every `Xₙ` as `X ×_S Sₙ`. This is the scheme form of
[Stacks, Tag 0E7R]; the tag itself, for algebraic spaces, is
`AlgebraicGeometry.Space.exists_isProjective_algebraization_of_dimension_le_one`.

## The proof

This is the source's proof.

* `X₀` carries an ample invertible module `ℒ₀`
  (`Stacks.FormalCurve.exists_isAmple_of_isProper_of_topologicalKrullDim_le_one`; the source
  cites [Stacks, Tag 0A26]).
* It lifts to a compatible system `(ℒₙ, θₙ)` on the tower
  (`Stacks.FormalCurve.exists_invertibleTower`); the source's obstruction lies in an `H²` that
  vanishes in dimension one, and [Stacks, Tag 09NY] is that statement.
* Grothendieck's algebraization theorem ([Stacks, Tag 089A]) is then run for this tower. By the
  embedding step, for every large `d` a tuple of sections of `ℒ₀ ^⊗ d` embeds `X₀` in `ℙᴺ_{S₀}`
  (`Stacks.AmpleFormalSystemEmbeddedTuple.exists_generatingTuple_isClosedImmersion_of_isAmple`).
  Choosing `d` also beyond the Serre vanishing bound for `H¹(X₀, ℒ₀ ^⊗ d)`
  ([Stacks, Tag 0B5T]), the sections lift compatibly up the tower
  (`Stacks.FormalCurve.surjective_transitionSections_of_isZero_rightDerived_one`, which is where
  the dimension bound is used once more). The lifted tuples give a cartesian tower of closed
  subschemes of `ℙᴺ_{Sₙ}`, and these algebraize to a closed subscheme of `ℙᴺ_S`
  (`AlgebraicGeometry.exists_closedImmersion_algebraization_of_isProjective`, [Stacks, Tag 0899]
  for `ℙᴺ_S`, from Grothendieck's existence theorem [Stacks, Tag 0885]).

The index is shifted by one from the source's: `n` here is the source's `n + 1`.

## Main results

* `Stacks.FormalCurve.exists_isProjectiveMorphism_of_topologicalKrullDim_le_one`.

## References

* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 0899](https://stacks.math.columbia.edu/tag/0899)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ProjectiveSpaceModuli Stacks.Ample
open Stacks.AmpleFormalSystemAmbient Stacks.AmpleFormalSystemSections

universe u

namespace Stacks.FormalCurve

section Tower

variable {A : Type u} [CommRing A] {I : Ideal A} {Xn : ℕ → Scheme.{u}}
  (q : ∀ n, Xn n ⟶ adicThickening A I n) (i : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
include hcart

/-- The transition maps of a cartesian tower over the adic thickenings are closed immersions:
they are base changes of the closed immersions `Sₙ ⟶ Sₙ₊₁`. -/
theorem isClosedImmersion_transition (n : ℕ) : IsClosedImmersion (i n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance

/-- The transition maps of a cartesian tower over the adic thickenings are surjective. -/
theorem surjective_transition (n : ℕ) : AlgebraicGeometry.Surjective (i n) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance

/-- The transition maps of a cartesian tower over the adic thickenings are homeomorphisms on
underlying spaces: closed embeddings which are surjective. -/
theorem isHomeomorph_transition (n : ℕ) : IsHomeomorph (i n).base := by
  have := isClosedImmersion_transition q i hcart n
  have := surjective_transition q i hcart n
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(i n).isClosedEmbedding.isEmbedding, (i n).surjective⟩

/-- Every member of the tower has the underlying space of the bottom member, up to
homeomorphism; in particular they share Noetherianity and dimension. -/
theorem noetherianSpace_and_topologicalKrullDim_eq [NoetherianSpace (Xn 0)] (n : ℕ) :
    NoetherianSpace (Xn n) ∧ topologicalKrullDim (Xn n : Type u) = topologicalKrullDim (Xn 0) := by
  induction n with
  | zero => exact ⟨inferInstance, rfl⟩
  | succ n ih =>
    obtain ⟨h₁, h₂⟩ := ih
    have hh := isHomeomorph_transition q i hcart n
    exact ⟨noetherianSpace_of_surjective _ (i n).base.hom.continuous hh.surjective,
      (IsHomeomorph.topologicalKrullDim_eq _ hh).symm.trans h₂⟩

end Tower

/-- Tensor powers of a compatible system of invertible modules are again compatible. -/
def powTransitionIso {Xn : ℕ → Scheme.{u}} (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (L : ∀ n, (Xn n).Modules) (hL : ∀ n, IsInvertibleModule (Xn n) (L n))
    (θ : ∀ n, (Scheme.Modules.pullback (i n)).obj (L (n + 1)) ≅ L n) (d n : ℕ) :
    (Scheme.Modules.pullback (i n)).obj
        (letI := hL (n + 1); tensorPowModule (Xn (n + 1)) (L (n + 1)) (d : ℤ)) ≅
      (letI := hL n; tensorPowModule (Xn n) (L n) (d : ℤ)) :=
  letI := hL n
  letI := hL (n + 1)
  letI : IsInvertibleModule (Xn n) ((Scheme.Modules.pullback (i n)).obj (L (n + 1))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (i n) (L (n + 1))
  Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (i n) (L (n + 1)) d ≪≫
    Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso (Xn n)
      ((Scheme.Modules.pullback (i n)).obj (L (n + 1))) (L n) (θ n) d

/-- **The algebraization of a formal curve, for schemes.** Let `A` be a Noetherian ring complete
with respect to `I`, and let `Xₙ ⟶ Sₙ = Spec (A / I ^ (n + 1))` be a tower of schemes with
cartesian squares over the thickenings, with `X₀ ⟶ S₀` proper and `dim X₀ ≤ 1`. Then there are an
H-projective `fX : X ⟶ Spec A` and morphisms `kₙ : Xₙ ⟶ X` with `iₙ ≫ kₙ₊₁ = kₙ`, every square
`Xₙ ⟶ X` over `Sₙ ⟶ Spec A` being cartesian. -/
theorem exists_isProjectiveMorphism_of_topologicalKrullDim_le_one (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {Xn : ℕ → Scheme.{u}} (q : ∀ n, Xn n ⟶ adicThickening A I n)
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))
    (hq : IsProper (q 0)) (hdim : topologicalKrullDim (Xn 0 : Type u) ≤ 1) :
    ∃ (X : Scheme.{u}) (fX : X ⟶ Spec (.of A)), IsProjectiveMorphism fX ∧
      ∃ k : ∀ n, Xn n ⟶ X, (∀ n, i n ≫ k (n + 1) = k n) ∧
        ∀ n, IsPullback (k n) (q n) fX (adicThickeningι A I n) := by
  have : IsLocallyNoetherian (Xn 0) := LocallyOfFiniteType.isLocallyNoetherian (q 0)
  have : CompactSpace (Xn 0) := QuasiCompact.compactSpace_of_compactSpace (q 0)
  have : AlgebraicGeometry.IsNoetherian (Xn 0) := ⟨⟩
  have : NoetherianSpace (Xn 0) := AlgebraicGeometry.IsNoetherian.noetherianSpace
  have hnoeth : ∀ n, NoetherianSpace (Xn n) := fun n =>
    (noetherianSpace_and_topologicalKrullDim_eq q i hcart n).1
  have hdimn : ∀ n, topologicalKrullDim (Xn n : Type u) ≤ 1 := fun n =>
    (noetherianSpace_and_topologicalKrullDim_eq q i hcart n).2.le.trans hdim
  have hsurj : ∀ n, Function.Surjective (i n).base := fun n =>
    (isHomeomorph_transition q i hcart n).surjective
  have : ∀ n, IsClosedImmersion (i n) := isClosedImmersion_transition q i hcart
  obtain ⟨L₀, hL₀, hample⟩ := exists_isAmple_of_isProper_of_topologicalKrullDim_le_one (q 0) hdim
  obtain ⟨L, hL, rfl, ⟨θ⟩⟩ := exists_invertibleTower i hdimn L₀
  obtain ⟨d₀, -, hemb⟩ :=
    Stacks.AmpleFormalSystemEmbeddedTuple.exists_generatingTuple_isClosedImmersion_of_isAmple
    (q 0) (L 0) hample
  have : _root_.SheafOfModules.IsCoherent (unitModule (Xn 0)) :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  obtain ⟨d₁, hd₁⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist (q 0)
      (unitModule (Xn 0)) (L 0) hample
  obtain ⟨d, hd₀d, hd₁d⟩ : ∃ d, d₀ ≤ d ∧ d₁ ≤ d := ⟨max d₀ d₁, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨N, s₀, hs₀, hclosed⟩ := hemb d hd₀d
  let M : ∀ n, (Xn n).Modules := fun n => let := hL n; tensorPowModule (Xn n) (L n) (d : ℤ)
  have hM : ∀ n, IsInvertibleModule (Xn n) (M n) := fun n => by
    let := hL n
    infer_instance
  have hvan : IsZero (((AlgebraicGeometry.moduleGlobalSections (Xn 0)).rightDerived 1).obj
      (M 0)) :=
    Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
      (Xn 0).ringCatSheaf ⊤ 1 (M 0) ((hd₁ d 1 hd₁d one_pos).of_iso
        ((Hfunctor (Xn 0).ringCatSheaf ⊤ 1).mapIso
          (Stacks.Algebraization.unitTensorModulesIso (Xn 0) (M 0))).symm)
  obtain ⟨t, ht, ht0⟩ := Stacks.AmpleFormalSystemLifting.exists_generatingTupleTower i M
    (powTransitionIso i L hL θ d) hsurj hM
    (surjective_transitionSections_of_isZero_rightDerived_one A I q i hcart hnoeth hdimn M hM
      (powTransitionIso i L hL θ d) hvan) N s₀ hs₀
  have hclosed0 : IsClosedImmersion (adicLift (A := A) (I := I) (N := N) (q 0)
      (tupleHom (t 0))) :=
    isClosedImmersion_adicLift 0 (q 0) _ (by rwa [tupleHom_congr ht0])
  obtain ⟨W, g, k, hg, hk, -, hkt⟩ :=
    exists_closedImmersion_algebraization_of_isProjective A I (ambientHom A N)
    (IsProjectiveMorphism.isProjective (isProjectiveMorphism_ambientHom A N)) Xn
    (fun n => adicLift (q n) (tupleHom (t n))) i
    (isPullback_adicLift_tupleHom N A I q i hcart t ht) hclosed0
  refine ⟨W, g ≫ ambientHom A N, ⟨N, g, hg, rfl⟩, k, hkt, fun n => ?_⟩
  have h := hk n
  rwa [adicLift_snd] at h

end Stacks.FormalCurve

end
