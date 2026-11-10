module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionClosedImmersionSolution
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalModification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocallyNoetherianSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleBaseChangeCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothRigSurjectiveClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothRigSurjectiveDescentCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal

/-!
# The scheme-theoretic image of `X' → S` in a contraction situation

In the situation of Stacks 0GH8 let `X' → S` be proper and let `Z ⊆ S` be closed with inverse
image `T'`, such that `U' → S ∖ Z` is a closed immersion. Let `Y ⊆ S` be the scheme-theoretic
image of `X' → S`. Then `Y ∩ (S ∖ Z)` is the image of `U'` (scheme-theoretic images of
quasi-compact morphisms commute with étale base change, Stacks 082Z).

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.imageY`: the scheme-theoretic image `Y ⊆ S` of
  `X' → S`.
* `AlgebraicGeometry.Artin.ContractionSituation.toImageY`: the factorization `X' ⟶ Y`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.imageY_inf_compl`: `Y ∩ (S ∖ Z)` is the image of
  `U'`.

## References

* [Stacks Project, Tag 0GHE](https://stacks.math.columbia.edu/tag/0GHE)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Presheaves of types on the big fppf site have fibre products. -/
theorem presheafHasPullback
    {X Y W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ W) (g : Y ⟶ W) : HasPullback f g :=
  @HasLimitsOfShape.has_limit _ _ _ _ Limits.functorCategoryHasLimitsOfShape _

attribute [local instance 10000] presheafHasPullback

section Image

variable (c : ContractionSituation B S hS)

/-- The scheme-theoretic image `Y ⊆ S` of `X' → S`, a subfunctor of the terminal presheaf. -/
noncomputable def imageY : Subfunctor (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  Space.schemeTheoreticImageSubfunctor B S hS (terminal.from c.X')

/-- The scheme-theoretic image `Y` is a closed subspace of `S`. -/
theorem isClosedSubspace_imageY : Space.IsClosedSubspace B S hS c.imageY :=
  Space.isClosedSubspace_schemeTheoreticImageSubfunctor B S hS _
    (Space.isAlgebraicSpace_terminal B S hS)

/-- The factorization `p : X' ⟶ Y`. -/
noncomputable def toImageY : c.X' ⟶ c.imageY.toFunctor :=
  Space.toSchemeTheoreticImage B S hS (terminal.from c.X')

/-- The factorization `p : X' ⟶ Y` followed by the inclusion `Y ⊆ S` is `X' ⟶ S`. -/
@[simp]
theorem toImageY_ι : c.toImageY ≫ c.imageY.ι = terminal.from c.X' :=
  Space.toSchemeTheoreticImage_ι B S hS _

/-- Every value of a subfunctor of the terminal presheaf is a subsingleton. -/
theorem subsingleton_subfunctor_terminal_obj
    (G : Subfunctor (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))) (V : (BigFppfOver B S hS)ᵒᵖ) :
    Subsingleton (G.toFunctor.obj V) := by
  have := subsingleton_terminal_obj (B := B) (S := S) (hS := hS) V
  exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩

variable {c}

/-- A section of `X'` over an object whose points avoid `Z` lies in `U'`. -/
theorem mem_U'_of_mem_compl
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    {V : BigFppfOver B S hS} (x : c.X'.obj (Opposite.op V))
    (s : (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).obj
      (Opposite.op V)) :
    x ∈ c.U'.obj (Opposite.op V) := by
  have hs := s.2
  change Set.range (Space.pointsMap B S hS (yoneda.obj V) (yonedaEquiv.symm x)) ⊆ c.T'ᶜ
  have hxs : yonedaEquiv.symm x ≫ terminal.from c.X' =
      yonedaEquiv.symm (s.1 : (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).obj (Opposite.op V)) :=
    terminal.hom_ext _ _
  rintro _ ⟨p, rfl⟩ hz
  rw [← hT'] at hz
  exact hs ⟨p, rfl⟩ (by rw [← hxs, Space.pointsMap_comp]; exact hz)

/-- The base change of `X' → S` to `S ∖ Z` has the same range as `u`. -/
theorem range_pullback_snd_eq_range_u
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor) :
    Subfunctor.range (pullback.snd (terminal.from c.X')
        (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).ι) =
      Subfunctor.range u := by
  ext V s
  induction V using Opposite.rec with
  | op V =>
  have hsub := subsingleton_subfunctor_terminal_obj
    (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ)
    (Opposite.op V)
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨⟨(pullback.fst (terminal.from c.X') _).app _ q, mem_U'_of_mem_compl Z hT' _
      ((pullback.snd (terminal.from c.X') _).app _ q)⟩, Subsingleton.elim _ _⟩
  · rintro ⟨x, rfl⟩
    exact ⟨yonedaEquiv (pullback.lift (yonedaEquiv.symm x.1)
      (yonedaEquiv.symm (u.app _ x)) (terminal.hom_ext _ _)), Subsingleton.elim _ _⟩

/-- The scheme-theoretic image of the base change of `X' → S` to `S ∖ Z` is the range of the
closed immersion `u`. -/
theorem schemeTheoreticImage_pullback_snd_eq_range_u
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u) :
    Space.schemeTheoreticImageSubfunctor B S hS (pullback.snd (terminal.from c.X')
        (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).ι) =
      Subfunctor.range u := by
  have h1 : Space.schemeTheoreticImageSubfunctor B S hS (pullback.snd (terminal.from c.X')
        (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).ι) =
      Space.schemeTheoreticImageSubfunctor B S hS u := by
    simp only [Space.schemeTheoreticImageSubfunctor, range_pullback_snd_eq_range_u Z hT' u]
  rw [h1]
  exact le_antisymm
    (Space.schemeTheoreticImageSubfunctor_le B S hS u
      (Space.isClosedSubspace_range_of_isClosedImmersion B S hS u c.isOpenSubspace_U'.1 hu)
      le_rfl)
    (Space.range_le_schemeTheoreticImageSubfunctor B S hS u)

variable (c)

/-- **`Y ∩ (S ∖ Z)` is the image of `U'`**, for `X' → S` proper and `U' → S ∖ Z` a closed
immersion. -/
theorem imageY_inf_compl
    (hproper : Space.IsProper B S hS (terminal.from c.X'))
    (Z : Set (Space.points B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))))
    (hZ : IsClosed Z)
    (hT' : Space.pointsMap B S hS c.X' (terminal.from c.X') ⁻¹' Z = c.T')
    (u : c.U'.toFunctor ⟶
      (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor)
    (hu : Space.IsClosedImmersion B S hS u) :
    c.imageY ⊓ Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ =
      Subfunctor.range
        (u ≫ (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).ι) := by
  have hone := Space.isAlgebraicSpace_terminal B S hS
  have hO := Space.isOpenSubspace_openSubspaceOfPoints B S hS hone Zᶜ hZ.isOpen_compl
  have hbc := Space.schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact'
    B S hS (terminal.from c.X')
    (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).ι
    c.isAlgebraicSpace_X' hone hO.1 hproper.2.1.2
    (Space.isEtale_of_isOpenImmersion B S hS hO.2)
  rw [schemeTheoreticImage_pullback_snd_eq_range_u Z hT' u hu] at hbc
  ext V t
  constructor
  · rintro ⟨htY, htO⟩
    have hmem : (⟨t, htO⟩ :
        (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).toFunctor.obj
          V) ∈
        ((Space.schemeTheoreticImageSubfunctor B S hS (terminal.from c.X')).preimage
          (Space.openSubspaceOfPoints B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) Zᶜ).ι).obj V :=
      htY
    rw [← hbc] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, by rw [NatTrans.comp_app_apply, hx]; rfl⟩
  · rintro ⟨x, rfl⟩
    have hmem : u.app V x ∈ (Subfunctor.range u).obj V := ⟨x, rfl⟩
    rw [hbc] at hmem
    exact ⟨hmem, (u.app V x).2⟩

end Image

end AlgebraicGeometry.Artin.ContractionSituation
