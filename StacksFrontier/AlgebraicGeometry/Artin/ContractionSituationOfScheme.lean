module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionArtinTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituationOfSchemeCompletion

/-!
# The situation of Artin's contraction for a scheme and a local ring

Let `S` be a locally Noetherian scheme in a big fppf site `B`, let `Z` be a scheme locally of
finite type over `S`, `C ⊆ Z` a closed subset, and `A` a Noetherian local ring with an
`S`-scheme structure `σ : Spec A ⟶ S` whose closed point `Spec κ ⟶ Spec A ⟶ S` is locally of
finite type. A formal modification `g : Z_{/C} ⟶ (Spec A)_{/\{𝔪\}}` then completes the data of
Situation 0GH8 (`AlgebraicGeometry.Artin.ContractionSituation.ofScheme`), with `X' = h_Z`,
`T' = |C|`, `W = (Spec A)_{/\{𝔪\}}` and `W_red` the reduced closed point of `Spec A`. If `Z` is
moreover separated over `S` and the local rings of `S` at finite type points are G-rings, Stacks
0GIB applies (`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_ofScheme`): there is a
solution `(f : X' ⟶ X, T, a)` with `|U| = |X| ∖ T`. When `S` is the spectrum of an algebra of
finite type over a field, the G-ring hypothesis holds
(`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_ofScheme_spec`).

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.ofScheme`: the situation.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_ofScheme`: Stacks 0GIB for it.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_solution_ofScheme_spec`: the same over the
  spectrum of an algebra of finite type over a field.

## References

* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The situation of Stacks 0GH8 for a scheme and a local ring.** Over a locally Noetherian
`S`: the algebraic space `X' = h_Z` of a scheme `Z` locally of finite type over `S`, the closed
subset `T' = |C|` over a closed subset `C ⊆ Z`, the completion `W = (Spec A)_{/\{𝔪\}}` of a local
scheme over `S` whose closed point is locally of finite type over `S`, the reduced closed point
of `Spec A` as `W_red`, and a formal modification `g : X'_{/T'} ⟶ W`. -/
def ofScheme (hSN : _root_.AlgebraicGeometry.IsLocallyNoetherian S) (Zo : BigFppfOver B S hS)
    (hZ : LocallyOfFiniteType (B.inclusion.map Zo.hom))
    (C : Set ((BigFppfOver.toScheme B S hS).obj Zo)) (hC : IsClosed C)
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : B.Contains (Spec (.of A)))
    (σ : Spec (.of A) ⟶ S)
    (hκ : LocallyOfFiniteType
      ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) ≫ σ))
    (g : Space.completionSheaf B S hS (yoneda.obj Zo) (Space.pointsToScheme B S hS Zo ⁻¹' C) ⟶
      FormalSpace.completionAtClosedPoint hA σ)
    (hg : FormalSpace.IsFormalModification B S hS g) :
    ContractionSituation B S hS where
  isLocallyNoetherian_base := hSN
  X' := yoneda.obj Zo
  isAlgebraicSpace_X' := isAlgebraicSpace_yoneda B S hS Zo
  isLocallyOfFiniteType_X' :=
    Space.isLocallyOfFiniteType_terminal_from_yoneda_of_structureMap Zo hZ
  T' := Space.pointsToScheme B S hS Zo ⁻¹' C
  isClosed_T' := Space.isClosed_preimage_pointsToScheme hC
  W := FormalSpace.completionAtClosedPoint hA σ
  isLocallyNoetherian_W := hg.isLocallyNoetherian_target
  Wred := FormalSpace.reductionAtClosedPoint hA σ
  WredInclusion := FormalSpace.reductionAtClosedPointInclusion hA σ
  isReduction_WredInclusion := FormalSpace.isReduction_reductionAtClosedPointInclusion hA σ
  isLocallyOfFiniteType_Wred :=
    FormalSpace.isLocallyOfFiniteTypeULift_terminal_from_reductionAtClosedPoint hA σ hκ
  g := g
  isFormalModification_g := hg

section ofScheme

variable (hSN : _root_.AlgebraicGeometry.IsLocallyNoetherian S) (Zo : BigFppfOver B S hS)
    (hZ : LocallyOfFiniteType (B.inclusion.map Zo.hom))
    (C : Set ((BigFppfOver.toScheme B S hS).obj Zo)) (hC : IsClosed C)
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : B.Contains (Spec (.of A)))
    (σ : Spec (.of A) ⟶ S)
    (hκ : LocallyOfFiniteType
      ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) ≫ σ))
    (g : Space.completionSheaf B S hS (yoneda.obj Zo) (Space.pointsToScheme B S hS Zo ⁻¹' C) ⟶
      FormalSpace.completionAtClosedPoint hA σ)
    (hg : FormalSpace.IsFormalModification B S hS g)

/-- The algebraic space of `AlgebraicGeometry.Artin.ContractionSituation.ofScheme` is `h_Z`. -/
@[simp]
theorem ofScheme_X' : (ofScheme hSN Zo hZ C hC hA σ hκ g hg).X' = yoneda.obj Zo := rfl

/-- The closed subset of `AlgebraicGeometry.Artin.ContractionSituation.ofScheme` is `|C|`. -/
@[simp]
theorem ofScheme_T' :
    (ofScheme hSN Zo hZ C hC hA σ hκ g hg).T' = Space.pointsToScheme B S hS Zo ⁻¹' C := rfl

/-- The formal algebraic space of `AlgebraicGeometry.Artin.ContractionSituation.ofScheme` is
the completion of `Spec A` at its closed point. -/
@[simp]
theorem ofScheme_W :
    (ofScheme hSN Zo hZ C hC hA σ hκ g hg).W = FormalSpace.completionAtClosedPoint hA σ := rfl

/-- The formal modification of `AlgebraicGeometry.Artin.ContractionSituation.ofScheme` is `g`. -/
theorem ofScheme_g : (ofScheme hSN Zo hZ C hC hA σ hκ g hg).g = g := rfl

/-- **Stacks 0GIB for a scheme and a local ring.** In the situation
`AlgebraicGeometry.Artin.ContractionSituation.ofScheme`, if `Z` is separated over `S` and the
local rings of `S` at finite type points are G-rings, there is an algebraic space `X` with a
solution `(f : X' ⟶ X, T, a)` whose open subspace `U` has point set `|X| ∖ T`. The
separatedness of `W` over `S` is automatic, `W` being an affine formal algebraic space. -/
theorem exists_solution_ofScheme
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hZs : AlgebraicGeometry.IsSeparated (B.inclusion.map Zo.hom)) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution (ofScheme hSN Zo hZ C hC hA σ hκ g hg) X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ :=
  exists_solution_of_isSeparated _ hG (Space.isSeparated_terminal_from_yoneda Zo hZs)
    (FormalSpace.isSeparatedMorphism_terminal_from_completionAtClosedPoint hA σ)

end ofScheme

/-- The spectrum of an algebra of finite type over a field is locally Noetherian. -/
theorem isLocallyNoetherian_spec_of_finiteType (k : Type u) [Field k] (R : Type u) [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] :
    _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)) := by
  have := Algebra.FiniteType.isNoetherianRing k R
  infer_instance

/-- **Stacks 0GIB over the spectrum of an algebra of finite type over a field.** Let `R` be an
algebra of finite type over a field `k`, `S = Spec R`, and let the data of
`AlgebraicGeometry.Artin.ContractionSituation.ofScheme` be given with `Z` separated over `S`.
Then there is an algebraic space `X` with a solution `(f : X' ⟶ X, T, a)` whose open subspace
`U` has point set `|X| ∖ T`: `S` is Noetherian and its local rings are G-rings
(`AlgebraicGeometry.isGRing_stalk_spec_of_finiteType`). -/
theorem exists_solution_ofScheme_spec (k : Type u) [Field k] {R : Type u} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {hS : B.Contains (Spec (.of R))}
    (Zo : BigFppfOver B (Spec (.of R)) hS) (hZ : LocallyOfFiniteType (B.inclusion.map Zo.hom))
    (hZs : AlgebraicGeometry.IsSeparated (B.inclusion.map Zo.hom))
    (C : Set ((BigFppfOver.toScheme B (Spec (.of R)) hS).obj Zo)) (hC : IsClosed C)
    {A : Type u} [CommRing A] [IsLocalRing A] (hA : B.Contains (Spec (.of A)))
    (σ : Spec (.of A) ⟶ Spec (.of R))
    (hκ : LocallyOfFiniteType
      ((Spec (.of A)).fromSpecResidueField (IsLocalRing.closedPoint A) ≫ σ))
    (g : Space.completionSheaf B (Spec (.of R)) hS (yoneda.obj Zo)
        (Space.pointsToScheme B (Spec (.of R)) hS Zo ⁻¹' C) ⟶
      FormalSpace.completionAtClosedPoint hA σ)
    (hg : FormalSpace.IsFormalModification B (Spec (.of R)) hS g) :
    ∃ (X : (BigFppfOver B (Spec (.of R)) hS)ᵒᵖ ⥤ Type u)
      (s : Solution
        (ofScheme (isLocallyNoetherian_spec_of_finiteType k R) Zo hZ C hC hA σ hκ g hg) X),
      Set.range (Space.pointsMap B (Spec (.of R)) hS s.U.toFunctor s.U.ι) = s.Tᶜ :=
  exists_solution_ofScheme (isLocallyNoetherian_spec_of_finiteType k R) Zo hZ C hC hA σ hκ g hg
    (isGRing_stalk_of_isFiniteTypePoint_spec k R) hZs

end AlgebraicGeometry.Artin.ContractionSituation

end
