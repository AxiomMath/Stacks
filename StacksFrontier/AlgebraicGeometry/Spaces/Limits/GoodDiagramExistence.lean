module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AllChartLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DominantNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentOfLimitBridges
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageConeLimitOfAlgebraicLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemPropertiesOfAlgebraicLimit

/-!
# Existence of the diagrams of Stacks 0CP8

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces over
`S` with affine transition morphisms, an `AlgebraicGeometry.Space.NoetherianLimitSystem`
(Situation 0CP6), and let `X ⟶ B` be quasi-separated and of finite type. Stacks 0CP7 produces a
diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

with `W ⟶ B_i` of finite type and `X ⟶ B ×_{B_i} W` a closed immersion, an
`AlgebraicGeometry.Space.GoodDiagram`. The source embeds `X` into an algebraic space `X'` of
finite presentation over `B` (Stacks 0872) and descends `X'` to a stage (Stacks 07SK).

The descent of Stacks 07SK is used here in the form which needs no bound on the size of the
index set, for a system with limit bridges. The system `(B_i)` itself need not have them: the
limit of the `B_i` in the big fppf site may be much smaller than the limit of their charts. The
system `(B'_i)` of scheme-theoretic images of the projections `B ⟶ B_i` has the same limit
`B` and scheme-theoretically dominant projections, hence limit bridges; its stages are closed
subspaces of the `B_i`, so they are quasi-compact and quasi-separated and its transition
morphisms are affine. A model `X'_k ⟶ B'_k` of `X'` then gives `W = X'_k` with
`W ⟶ B'_k ⟶ B_k`, of finite type, and `B ×_{B_k} W = B ×_{B'_k} W = X'` because
`B'_k ⟶ B_k` is a monomorphism.

## Main definitions

* `AlgebraicGeometry.Space.NoetherianLimitSystem.dominantSystem`: the system of
  scheme-theoretic images of the projections of the limit.

## Main results

* `AlgebraicGeometry.Space.NoetherianLimitSystem.hasAllChartLimitBridges_dominantSystem`: that
  system has limit bridges along all affine points, with no condition on the size of the index
  set.
* `AlgebraicGeometry.Space.GoodDiagram.nonempty_goodDiagram_of_noetherianApproximation`:
  Stacks 0CP7, from the inputs of the staged Stacks 0872.

## References

* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP7](https://stacks.math.columbia.edu/tag/0CP7)
* [Stacks Project, Tag 0872](https://stacks.math.columbia.edu/tag/0872)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace NoetherianLimitSystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  (D : NoetherianLimitSystem B S hS hZ I)

/-- The members of the system are algebraic spaces, indexed by the opposite of the index set. -/
lemma system_isAlgebraicSpace' (j : Iᵒᵖ) : IsAlgebraicSpace B S hS (D.system.obj j) :=
  D.system_isAlgebraicSpace j.unop

/-- **The dominant system** `(B'_i)` of a Noetherian limit system: the scheme-theoretic images of
the projections `B ⟶ B_i` of its limit. -/
noncomputable abbrev dominantSystem : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  coneImageDiagram D.system_isAlgebraicSpace' D.limitCone

/-- The limit `B` is the limit of the dominant system. -/
noncomputable def isLimitDominantCone :
    IsLimit (coneImageCone D.system_isAlgebraicSpace' D.limitCone) :=
  isLimitConeImageCone D.system_isAlgebraicSpace' D.isLimit

/-- The comparison of `B` with the chosen limit of the dominant system. -/
noncomputable def dominantLimitIso : D.limitCone.pt ≅ limit D.dominantSystem :=
  D.isLimitDominantCone.conePointUniqueUpToIso (limit.isLimit _)

/-- The comparison `dominantLimitIso` followed by a limit projection of the dominant system is the
corresponding projection of the cone of images. -/
@[reassoc (attr := simp)]
lemma dominantLimitIso_hom_π (j : Iᵒᵖ) :
    D.dominantLimitIso.hom ≫ limit.π D.dominantSystem j =
      (coneImageCone D.system_isAlgebraicSpace' D.limitCone).π.app j :=
  D.isLimitDominantCone.conePointUniqueUpToIso_hom_comp (limit.isLimit _) j

/-- The inverse of `dominantLimitIso` followed by a projection of the cone of images is the
corresponding limit projection of the dominant system. -/
@[reassoc (attr := simp)]
lemma dominantLimitIso_inv_π (j : Iᵒᵖ) :
    D.dominantLimitIso.inv ≫ (coneImageCone D.system_isAlgebraicSpace' D.limitCone).π.app j =
      limit.π D.dominantSystem j :=
  D.isLimitDominantCone.conePointUniqueUpToIso_inv_comp (limit.isLimit _) j

/-- The limit projections, factored through the dominant system. -/
@[reassoc]
lemma limitCone_π_eq (j : Iᵒᵖ) :
    D.limitCone.π.app j = D.dominantLimitIso.hom ≫ limit.π D.dominantSystem j ≫
      (coneImageStage D.limitCone j).ι := by
  rw [dominantLimitIso_hom_π_assoc, coneImageCone_π_ι]

/-- The members of the dominant system are algebraic spaces. -/
lemma dominantSystem_isAlgebraicSpace (j : Iᵒᵖ) :
    IsAlgebraicSpace B S hS (D.dominantSystem.obj j) :=
  (isClosedSubspace_coneImageStage D.system_isAlgebraicSpace' D.limitCone j).1

/-- The transition morphisms of the dominant system are affine. -/
lemma dominantSystem_isAffineHom {j j' : Iᵒᵖ} (g : j ⟶ j') :
    IsAffineHom B S hS (D.dominantSystem.map g) :=
  isAffineHom_coneImageMap D.system_isAlgebraicSpace' D.limitCone D.transition_affine g

/-- The members of the dominant system are quasi-compact. -/
lemma dominantSystem_isQuasiCompactSpace (j : Iᵒᵖ) :
    IsQuasiCompactSpace B S hS (D.dominantSystem.obj j) :=
  isQuasiCompactSpace_of_isClosedImmersion B S hS (D.noetherian j.unop).1 _
    (isClosedSubspace_coneImageStage D.system_isAlgebraicSpace' D.limitCone j).2

/-- The members of the dominant system are absolutely quasi-separated. -/
lemma dominantSystem_isAbsolutelyQuasiSeparated (j : Iᵒᵖ) :
    IsAbsolutelyQuasiSeparated B S hS hZ (D.dominantSystem.obj j) :=
  isAbsolutelyQuasiSeparated_coneImageStage D.system_isAlgebraicSpace' D.limitCone
    (D.noetherian j.unop).2.1

/-- The limit of the dominant system is an algebraic space. -/
lemma isAlgebraicSpace_limit_dominantSystem : IsAlgebraicSpace B S hS (limit D.dominantSystem) :=
  isAlgebraicSpace_of_iso B S hS D.dominantLimitIso D.limit_isAlgebraicSpace

/-- The limit projections of the dominant system are scheme-theoretically dominant: the
scheme-theoretic image of each is the whole stage. -/
lemma schemeTheoreticImageSubfunctor_limit_π_dominantSystem (j : Iᵒᵖ) :
    schemeTheoreticImageSubfunctor B S hS (limit.π D.dominantSystem j) = ⊤ := by
  rw [← dominantLimitIso_inv_π,
    @schemeTheoreticImageSubfunctor_comp_of_epi _ _ _ _ _ _ _ (IsIso.epi_of_iso _)]
  exact schemeTheoreticImageSubfunctor_coneImageCone_π _ _ j

/-- **The dominant system has limit bridges** along all affine points, with no condition on the
size of the index set. -/
theorem hasAllChartLimitBridges_dominantSystem : HasAllChartLimitBridges D.dominantSystem :=
  hasAllChartLimitBridges_of_dominant (hZ := hZ) D.dominantSystem_isAlgebraicSpace
    D.dominantSystem_isAffineHom D.isAlgebraicSpace_limit_dominantSystem
    D.dominantSystem_isQuasiCompactSpace D.dominantSystem_isAbsolutelyQuasiSeparated
    D.schemeTheoreticImageSubfunctor_limit_π_dominantSystem

/-- The limit of a Noetherian limit system is quasi-compact: its projection to a stage is affine
and that stage is Noetherian. -/
lemma isQuasiCompactSpace_limitCone_pt : IsQuasiCompactSpace B S hS D.limitCone.pt := by
  obtain ⟨i⟩ : Nonempty I := inferInstance
  exact isQuasiCompactSpace_source_of_isQuasiCompact B S hS (D.system_isAlgebraicSpace i)
    (D.noetherian i).1 (isQuasiCompact_of_isAffineHom' B S hS _ D.limit_isAlgebraicSpace
      (D.system_isAlgebraicSpace i) (isAffineHom_limitCone_π_of_algebraicLimit B S hS D (op i)))

end NoetherianLimitSystem

namespace GoodDiagram

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- **Stacks 0CP7**, granted the held statement `h07SU`, the one input of the staged Stacks
0872. In Situation 0CP6, a quasi-separated
morphism of finite type `f : X ⟶ B` from an algebraic space has a diagram as in Stacks 0CP8:
some stage `B_i`, a model `W ⟶ B_i` of finite type and `X ⟶ W` over `B ⟶ B_i` such that
`X ⟶ B ×_{B_i} W` is a closed immersion. No bound on the size of the index set is assumed. -/
theorem nonempty_goodDiagram_of_noetherianApproximation
    (D : NoetherianLimitSystem B S hS B.contains_terminal I)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ D.limitCone.pt)
    (hX : IsAlgebraicSpace B S hS X)
    (hfqs : IsQuasiSeparated B S hS f) (hfft : IsFiniteType B S hS f)
    (h07SU : ∀ Z : (BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsQuasiCompactSpace B (⊤_ Scheme.{u}) B.contains_terminal Z →
        IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z →
          HasNoetherianApproximation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal Z) :
    Nonempty (GoodDiagram B S hS B.contains_terminal D f) := by
  classical
  have hB := D.limit_isAlgebraicSpace
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hB D.isQuasiCompactSpace_limitCone_pt
      hfft.2
  -- Stacks 0872: a closed immersion `X ⟶ X'` into a space of finite presentation over `B`
  obtain ⟨X', f', ι, hX', hf'fp, hι, hιf⟩ :=
   exists_isFinitePresentation_isClosedImmersion_of_isLocallyOfFiniteType_of_noetherianApproximation
      B S hS f hX hB hfft.1 hXqc
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone_of_algebraicLimit hX hfqs)
      D.isQuasiCompactSpace_limitCone_pt
      (isAbsolutelyQuasiSeparated_limitCone_pt_of_algebraicLimit D) h07SU
  -- Stacks 07SK for the dominant system: `X'` descends to a stage `B'_k`
  let e := D.dominantLimitIso
  have hfp : IsFinitePresentation B S hS (Over.mk (f' ≫ e.hom)).hom :=
    isFinitePresentation_of_arrowIso B S hS f' (f' ≫ e.hom) (𝟙 X') e.hom (by simp) hf'fp
  obtain ⟨k, Yk, hYk, hYkfp, ⟨φ⟩⟩ := exists_model_of_finitePresentation_of_limitBridges B S hS
    B.contains_terminal D.dominantSystem D.isAlgebraicSpace_limit_dominantSystem
    D.hasAllChartLimitBridges_dominantSystem
    (fun i => isAffineHom_π_of_isAlgebraicSpace B S hS _ D.dominantSystem_isAffineHom
      (limit.isLimit _) D.isAlgebraicSpace_limit_dominantSystem i
      (D.dominantSystem_isAlgebraicSpace i))
    D.dominantSystem_isAlgebraicSpace
    D.dominantSystem_isAffineHom D.dominantSystem_isQuasiCompactSpace
    D.dominantSystem_isAbsolutelyQuasiSeparated (Over.mk (f' ≫ e.hom)) hX' hfp
  let ιk := (coneImageStage D.limitCone k).ι
  let φl : X' ≅ pullback Yk.hom (limit.π D.dominantSystem k) := (Over.forget _).mapIso φ
  have hφ : φl.hom ≫ pullback.snd Yk.hom (limit.π D.dominantSystem k) = f' ≫ e.hom :=
    Over.w φ.hom
  -- `X' = B ×_{B_k} W`, because `B'_k ⟶ B_k` is a monomorphism
  have h₀ := IsPullback.of_hasPullback Yk.hom (limit.π D.dominantSystem k)
  have h₁ : IsPullback (pullback.fst Yk.hom (limit.π D.dominantSystem k))
      (pullback.snd Yk.hom (limit.π D.dominantSystem k)) (Yk.hom ≫ ιk)
      (limit.π D.dominantSystem k ≫ ιk) :=
    IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ ιk _ h₀.isLimit)
  have hP : IsPullback f' (φl.hom ≫ pullback.fst _ _) (D.limitCone.π.app k) (Yk.hom ≫ ιk) := by
    refine h₁.flip.of_iso φl.symm e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [← Iso.cancel_iso_hom_left φl, ← Category.assoc, hφ, Iso.symm_hom, Iso.symm_hom,
        Category.assoc, e.hom_inv_id, Category.comp_id, φl.hom_inv_id_assoc]
    · simp
    · simp [D.limitCone_π_eq k, e, ιk]
    · simp
  have hcomm : f ≫ D.limitCone.π.app k = (ι ≫ φl.hom ≫ pullback.fst _ _) ≫ (Yk.hom ≫ ιk) := by
    rw [← hιf, Category.assoc, hP.w]
    simp only [Category.assoc]
  have hlift : pullback.lift f (ι ≫ φl.hom ≫ pullback.fst _ _) hcomm = ι ≫ hP.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst, hιf]
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd]
  refine ⟨{ index := k.unop
            model := Yk.left
            model_isAlgebraicSpace := hYk
            modelMap := Yk.hom ≫ ιk
            toModel := ι ≫ φl.hom ≫ pullback.fst _ _
            commutes := hcomm
            isFiniteType := ?_
            isClosedImmersion := ?_ }⟩
  · exact isFiniteType_comp B S hS hYk (D.dominantSystem_isAlgebraicSpace k)
      (D.system_isAlgebraicSpace' k) _ _ (isFiniteType_of_isFinitePresentation B S hS hYkfp)
      (isFiniteType_of_isClosedImmersion B S hS _
        (isClosedSubspace_coneImageStage D.system_isAlgebraicSpace' D.limitCone k).2)
  · rw [hlift]
    exact isClosedImmersion_comp B S hS _ _ hι (isClosedImmersion_of_isIso B S hS _)

end GoodDiagram

end AlgebraicGeometry.Space

end
