module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentedNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Stages of a Noetherian approximation presented by atlases

An algebraic space over `Spec ℤ` with a surjective étale atlas `V` which is a quasi-compact and
quasi-separated scheme of finite type over `Spec ℤ`, and whose kernel pair `R` is quasi-compact,
is quasi-separated and of finite type over `Spec ℤ` (Stacks 07S4, 040W and 040Y). These are the
stage conditions of a Noetherian approximation for the quotients `X_i = V_i / R_i` of the proof
of absolute Noetherian approximation.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_atlas`: quasi-separatedness.
* `AlgebraicGeometry.Space.isFiniteType_viewOverIntegers_of_atlas`: finite type over
  `Spec ℤ`.

## References

* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  {X : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B _ hZ X)
  {V R : BigFppfOver B (⊤_ Scheme.{u}) hZ} (q : yoneda.obj V ⟶ X)
  (hq_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B _ hZ)).presheaf q)
  (hq_et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B _ hZ)).presheaf q)
  {s t : R ⟶ V} (hker : IsPullback (yoneda.map s) (yoneda.map t) q q)

local notation "𝕋" => BigFppfOver.toScheme B (⊤_ Scheme) hZ

include hX hq_surj hq_et hker in
/-- **An algebraic space with a quasi-separated étale atlas whose kernel pair is quasi-compact over
the atlas is quasi-separated** (Stacks 07S4). -/
theorem isAbsolutelyQuasiSeparated_of_atlas [QuasiSeparatedSpace ((𝕋).obj V)]
    (hs : QuasiCompact ((𝕋).map s)) :
    IsAbsolutelyQuasiSeparated B _ hZ hZ X := by
  refine isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B _ hZ hZ X hX
    ⟨V, q, inferInstance, hq_surj, hq_et, Or.inl ?_⟩
  have h : pullback.fst q q = hker.isoPullback.inv ≫ yoneda.map s :=
    hker.isoPullback_inv_fst.symm
  rw [h]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    ((presheaf_yoneda_map_iff B _ hZ (P := @QuasiCompact.{u}) inferInstance s).mpr hs)

include hX hq_surj hq_et in
/-- **An algebraic space over `Spec ℤ` with a quasi-compact étale atlas of finite type over
`Spec ℤ` is of finite type over `Spec ℤ`** (Stacks 040W and 040Y). -/
theorem isFiniteType_viewOverIntegers_of_atlas [CompactSpace ((𝕋).obj V)]
    (hV : LocallyOfFiniteType (terminal.from ((𝕋).obj V))) :
    IsFiniteType B _ hZ (terminal.from (viewOverIntegers B _ hZ hZ X)) := by
  let T₀ : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (𝟙 (B.obj hZ))
  have hT : IsAlgebraicSpace B _ hZ (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_terminal B _ hZ
  have hq_isEt : IsEtale B _ hZ q := (isEtale_iff_presheaf_of_yoneda B _ hZ q).mpr hq_et
  have hXqc : IsQuasiCompactSpace B _ hZ X := ⟨V, q, inferInstance, hq_surj, hq_isEt⟩
  have hlft : IsLocallyOfFiniteType B _ hZ (terminal.from X) := by
    have _ : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine (holdsOnEveryEtaleChart_iff_surjectiveChart B _ hZ _
      isEtaleLocalOnSourceAndTarget_locallyOfFiniteType hX hT _).mpr
      ⟨V, T₀, q, (terminalPresheafIso B hZ).hom, (Over.mkIdTerminal (X := B.obj hZ)).from V,
        hq_et, presheaf_inverseImage_of_isIso' B hZ _ _, hq_surj, terminal.hom_ext _ _, ?_⟩
    have h : (𝕋).map ((Over.mkIdTerminal (X := B.obj hZ)).from V) =
        terminal.from ((𝕋).obj V) := terminal.hom_ext _ _
    change LocallyOfFiniteType ((𝕋).map _)
    rw [h]
    exact hV
  have hTqs : IsAbsolutelyQuasiSeparated B _ hZ hZ
      (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) := by
    have : IsAffine ((𝕋).obj T₀) :=
      IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
    exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B _ hZ _ hZ
      ⟨T₀, inferInstance,
        ⟨(Functor.RepresentableBy.yoneda T₀).ofIso (terminalPresheafIso B hZ)⟩⟩
  have e := viewOverIntegersTerminalIso B hZ X
  exact ⟨(isLocallyOfFiniteType_terminal_iff_of_iso B _ hZ e).mpr hlft,
    isQuasiCompact_of_isQuasiCompactSpace B _ hZ hZ hT hTqs
      (isQuasiCompactSpace_of_iso B _ hZ e.symm hXqc) _⟩

end AlgebraicGeometry.Space

end
