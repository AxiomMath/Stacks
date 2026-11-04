module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.MapToFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOverIntegersTerminal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Spaces affine over a quasi-compact quasi-separated space, and Noetherian spaces over `Spec ℤ`

Two facts the proofs of Stacks 07UW and Stacks 07V9 use without comment.

* An algebraic space which is affine over a quasi-compact and quasi-separated algebraic space is
  itself quasi-compact and quasi-separated: an affine morphism is quasi-compact and separated, and
  both properties pass from the target to the source. In particular this holds over a Noetherian
  algebraic space, which is the form the proof of Stacks 07UW applies Stacks 07U7 in.
* A quasi-separated algebraic space of finite type over `Spec ℤ` is Noetherian. It is quasi-compact
  because its view over `Spec ℤ` is quasi-compact over the quasi-compact space `Spec ℤ`, and it is
  locally Noetherian because every étale chart of it is a scheme locally of finite type over the
  Noetherian scheme `Spec ℤ`. This is how the proof of Stacks 07V9 sees that the stages of an
  absolute Noetherian approximation are Noetherian.

## Main results

* `isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_source_of_isAffineHom`: a space affine over a
  quasi-compact quasi-separated space is quasi-compact and quasi-separated.
* `isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom_of_isNoetherian`: the same
  over a Noetherian space, for morphisms of algebraic spaces.
* `isNoetherian_of_isFiniteType_viewOverIntegers`: a quasi-separated algebraic space of finite type
  over `Spec ℤ` is Noetherian.

## References

* [Stacks Project, Tag 07UW](https://stacks.math.columbia.edu/tag/07UW)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 04ZL](https://stacks.math.columbia.edu/tag/04ZL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- An algebraic space affine over a quasi-compact and quasi-separated algebraic space is
quasi-compact and quasi-separated. -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_source_of_isAffineHom
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsAffineHom B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) :
    IsQuasiCompactSpace B S hS X ∧ IsAbsolutelyQuasiSeparated B S hS hZ X :=
  ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS hY hYqc
      (isQuasiCompact_of_isAffineHom' B S hS f hX hY hf),
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hYqs
      (isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isAffineHom B S hS f hX hY hf))⟩

/-- An algebraic space admitting an affine morphism of algebraic spaces to a Noetherian algebraic
space is quasi-compact and quasi-separated. -/
theorem isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isAffineHom_of_isNoetherian
    (Z W : AlgebraicSpaces B S hS) (g : Z ⟶ W) (hg : IsAffineHom B S hS g.hom)
    (hW : IsNoetherian B S hS hZ W.1) :
    IsQuasiCompactSpace B S hS Z.1 ∧ IsAbsolutelyQuasiSeparated B S hS hZ Z.1 :=
  isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_source_of_isAffineHom B S hS hZ Z.2 W.2 g.hom
    hg hW.1 hW.2.1

/-- A quasi-separated algebraic space whose view over `Spec ℤ` is of finite type over `Spec ℤ` is
Noetherian. -/
theorem isNoetherian_of_isFiniteType_viewOverIntegers
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hft : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B S hS hZ X))) :
    IsNoetherian B S hS hZ X := by
  let h : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  refine ⟨isQuasiCompactSpace_of_relocalize B S (⊤_ Scheme.{u}) hS hZ h X
    (isQuasiCompactSpace_source_of_isQuasiCompact B (⊤_ Scheme.{u}) hZ
      (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ)
      (isQuasiCompactSpace_terminal_of_isAffine B _ hZ) hft.2), hqs, ?_⟩
  obtain ⟨U, c, hsurj, hetale⟩ := hX.exists_atlas
  have _ : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨U, c, hsurj, hetale, ?_⟩
  let V : BigFppfOver B (⊤_ Scheme.{u}) hZ := Over.mk (𝟙 (B.obj hZ))
  let b : yoneda.obj V ⟶ ⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
    (((Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _).uniqueUpToIso
      terminalIsTerminal).hom
  have hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf b :=
    presheaf_of_isIso B (⊤_ Scheme.{u}) hZ (MorphismProperty.RespectsIso.inverseImage _ _)
      (fun W => by
        show Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (𝟙 W))
        rw [CategoryTheory.Functor.map_id]
        exact MorphismProperty.id_mem _ _) b
  let k : (Over.map h).obj U ⟶ V := Over.homMk ((Over.map h).obj U).hom (Category.comp_id _)
  have hk : LocallyOfFiniteType ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map k) :=
    hft.1 _ _ _ b k ((presheaf_relocalizeChart_iff B S (⊤_ Scheme.{u}) hS hZ h _ c).2 hetale) hb
      (terminal.hom_ext _ _)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj V) :=
    isLocallyNoetherian_terminal
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map k)

end AlgebraicGeometry.Space

end
