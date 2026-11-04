module

public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ProperRefinedValuative
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The formal hypotheses of the refined valuative criterion for the cover of Stacks 089J

Let `X'` be an object of the big fppf site over `S` which is H-quasi-projective over the base,
and `p : X' ⟶ X` a morphism to a presheaf on the site. Then `p` is separated and
quasi-separated, it is locally of finite type when `X` is an algebraic space, it is
quasi-compact when `X` is separated over the base, and every valuative square for `p` has at
most one lift. These are the hypotheses `hqs`, `hlft`, `hf` and `hunique` of
`AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`.

## Main results

* `AlgebraicGeometry.Space.isSeparated_toBase_yoneda_of_isHQuasiProjective` and
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_toBase_yoneda_of_isHQuasiProjective`: the
  structure morphism of the presheaf represented by an H-quasi-projective object of the site is
  separated and locally of finite type.
* `AlgebraicGeometry.Space.isSeparated_of_isHQuasiProjective_source`: every morphism from such
  a presheaf to a presheaf on the site is separated.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_isHQuasiProjective_source`,
  `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isHQuasiProjective_source` and
  `AlgebraicGeometry.Space.isQuasiCompact_of_isHQuasiProjective_source`: the hypotheses
  `hqs`, `hlft` and `hf` of
  `AlgebraicGeometry.Space.isProper_of_refinedValuativeCriterion`.
* `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map_of_compactSpace`: its hypothesis `hh`, for
  a morphism of the site out of a compact scheme into a quasi-separated one.
* `AlgebraicGeometry.Space.subsingleton_lift_of_isHQuasiProjective_source`: its hypothesis
  `hunique`.

## References

* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 03KU](https://stacks.math.columbia.edu/tag/03KU)
* [Stacks Project, Tag 0AGC](https://stacks.math.columbia.edu/tag/0AGC)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (X' : BigFppfOver B S hS)

/-- The morphism of schemes underlying the unique morphism to the terminal object of the big
fppf category over `S` is the structure morphism of the scheme. -/
private theorem toScheme_map_terminalFrom_eq_hom :
    (BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from X') =
      B.inclusion.map X'.hom := by
  have h : (Over.mkIdTerminal.from X' : X' ⟶ Over.mk (𝟙 (B.obj hS))).left = X'.hom := by
    simp
  exact congrArg B.inclusion.map h

/-- The morphism from a represented presheaf to the terminal presheaf is the image of the morphism
to the terminal object of the site. -/
private theorem from_yoneda_obj_eq_yoneda_map :
    (isTerminal_yoneda_obj_base B S hS).from (yoneda.obj X') =
      yoneda.map (Over.mkIdTerminal.from X') :=
  (isTerminal_yoneda_obj_base B S hS).hom_ext _ _

/-- The structure morphism of the presheaf represented by an H-quasi-projective object of the
site is separated. -/
theorem isSeparated_toBase_yoneda_of_isHQuasiProjective
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from (yoneda.obj X')) := by
  rw [from_yoneda_obj_eq_yoneda_map]
  refine (isSeparated_yoneda_map_iff B S hS _).2 ?_
  rw [toScheme_map_terminalFrom_eq_hom]
  exact h.isSeparated

/-- The structure morphism of the presheaf represented by an H-quasi-projective object of the
site is locally of finite type. -/
theorem isLocallyOfFiniteType_toBase_yoneda_of_isHQuasiProjective
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    IsLocallyOfFiniteType B S hS
      ((isTerminal_yoneda_obj_base B S hS).from (yoneda.obj X')) := by
  rw [from_yoneda_obj_eq_yoneda_map]
  refine (isLocallyOfFiniteType_yoneda_map_iff B S hS _).2 ?_
  rw [toScheme_map_terminalFrom_eq_hom]
  exact h.locallyOfFiniteType

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : yoneda.obj X' ⟶ X)

/-- A morphism out of a represented presheaf followed by the map to the terminal presheaf is the
map to the terminal presheaf. -/
private theorem comp_from_eq_from :
    p ≫ (isTerminal_yoneda_obj_base B S hS).from X =
      (isTerminal_yoneda_obj_base B S hS).from (yoneda.obj X') :=
  (isTerminal_yoneda_obj_base B S hS).hom_ext _ _

/-- A morphism from an H-quasi-projective object of the site into a presheaf over the base is
separated. -/
theorem isSeparated_of_isHQuasiProjective_source
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    IsSeparated B S hS p := by
  refine isSeparated_of_comp B S hS p ((isTerminal_yoneda_obj_base B S hS).from X) ?_
  rw [comp_from_eq_from]
  exact isSeparated_toBase_yoneda_of_isHQuasiProjective B S hS X' h

/-- A morphism from an H-quasi-projective object of the site into a presheaf over the base is
quasi-separated. -/
theorem isQuasiSeparated_of_isHQuasiProjective_source
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    IsQuasiSeparated B S hS p :=
  isQuasiSeparated_of_isSeparated B S hS
    (isSeparated_of_isHQuasiProjective_source B S hS X' p h)

/-- A morphism from an H-quasi-projective object of the site into an algebraic space over the base
is locally of finite type. -/
theorem isLocallyOfFiniteType_of_isHQuasiProjective_source
    (hX : IsAlgebraicSpace B S hS X)
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    IsLocallyOfFiniteType B S hS p := by
  refine isLocallyOfFiniteType_of_comp B S hS (isAlgebraicSpace_yoneda B S hS X') hX
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))) p
    ((isTerminal_yoneda_obj_base B S hS).from X) ?_
  rw [comp_from_eq_from]
  exact isLocallyOfFiniteType_toBase_yoneda_of_isHQuasiProjective B S hS X' h

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- A quasi-compact morphism of the big fppf category over `S` represents a quasi-compact
morphism of algebraic spaces. -/
private theorem isQuasiCompact_yonedaMap_of_quasiCompact_toScheme
    {A T : BigFppfOver B S hS} (f : A ⟶ T)
    (hf : QuasiCompact ((BigFppfOver.toScheme B S hS).map f)) :
    IsQuasiCompact B S hS (yoneda.map f) := by
  have hstab : (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := ⟨by
    intro _ _ _ _ _ _ _ _ hs hg
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @QuasiCompact) (hs.map (BigFppfOver.toScheme B S hS)) hg⟩
  exact isQuasiCompact_of_presheaf_quasiCompact B S hS (MorphismProperty.relative_map hf)

/-- The structure morphism of the presheaf represented by an H-quasi-projective object of the
site is quasi-compact. -/
theorem isQuasiCompact_toBase_yoneda_of_isHQuasiProjective
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    IsQuasiCompact B S hS ((isTerminal_yoneda_obj_base B S hS).from (yoneda.obj X')) := by
  rw [from_yoneda_obj_eq_yoneda_map]
  refine isQuasiCompact_yonedaMap_of_quasiCompact_toScheme B S hS _ ?_
  rw [toScheme_map_terminalFrom_eq_hom]
  exact h.quasiCompact

/-- A morphism from an H-quasi-projective object of the site into a presheaf which is separated
over the base is quasi-compact. -/
theorem isQuasiCompact_of_isHQuasiProjective_source
    (hXsep : IsSeparated B S hS ((isTerminal_yoneda_obj_base B S hS).from X))
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) :
    IsQuasiCompact B S hS p := by
  refine isQuasiCompact_of_comp_of_isQuasiSeparated B S hS p
    ((isTerminal_yoneda_obj_base B S hS).from X) (isAlgebraicSpace_yoneda B S hS X')
    (isAlgebraicSpace_yoneda B S hS (Over.mk (𝟙 (B.obj hS)))) ?_
    (isQuasiSeparated_of_isSeparated B S hS hXsep)
  rw [comp_from_eq_from]
  exact isQuasiCompact_toBase_yoneda_of_isHQuasiProjective B S hS X' h

/-- A morphism of the site whose source has compact underlying scheme and whose target has
quasi-separated underlying scheme represents a quasi-compact morphism of algebraic spaces. -/
theorem isQuasiCompact_yoneda_map_of_compactSpace {A T : BigFppfOver B S hS} (f : A ⟶ T)
    (hA : CompactSpace ((BigFppfOver.toScheme B S hS).obj A))
    (hT : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiCompact B S hS (yoneda.map f) :=
  isQuasiCompact_yonedaMap_of_quasiCompact_toScheme B S hS f
    (quasiCompact_of_compactSpace ((BigFppfOver.toScheme B S hS).map f))

/-- Every valuative square for a morphism from an H-quasi-projective object of the site into a
presheaf over the base has at most one lift. -/
theorem subsingleton_lift_of_isHQuasiProjective_source
    (h : IsHQuasiProjective (B.inclusion.map X'.hom)) (q : ValuativeSquare p) :
    Subsingleton q.Lift :=
  valuativeCriterion_uniqueness_of_isSeparated p
    (isSeparated_of_isHQuasiProjective_source B S hS X' p h) q

end AlgebraicGeometry.Space

end
