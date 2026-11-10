module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.RelativeMapKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceChartEq
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityRange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Space
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuotientSituation

/-!
# Closed subspaces of a relative Proj

In Situation 0849 let `ℐ ⊆ 𝒜` be a quasi-coherent graded ideal and `ψ : 𝒜 ⟶ 𝒜 ⧸ ℐ` the quotient
map. By Stacks 085H the morphism `r_ψ` of Stacks 085F is defined on all of `Proj_X(𝒜 ⧸ ℐ)` and is
a closed immersion `Proj_X(𝒜 ⧸ ℐ) ⟶ Proj_X(𝒜)`. This file compares it with a closed subspace
`i : Z ⟶ Proj_X(𝒜)` over a surjective étale scheme chart `T ⟶ X` of the base, where both become
closed subschemes of `Proj_T(𝒜|_T)` and the scheme case Stacks 0801 applies.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.quotientHomPoints`: the quotient map
  read over the scheme points of the base.
* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.quotientProjHom`: the closed
  immersion `Proj_X(𝒜 ⧸ ℐ) ⟶ Proj_X(𝒜)`.
* `AlgebraicGeometry.Space.RelativeProjSituation.chartClosedSubscheme`: the base change of a
  closed subspace of `Proj_X(𝒜)` to a scheme point, as a closed subscheme of `Proj_T(𝒜|_T)`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.GradedIdeal.isClosedImmersion_quotientProjHom`.
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_iso_quotientProjHom_of_chart`: `Z` is
  `Proj_X(𝒜 ⧸ ℐ)` over `Proj_X(𝒜)` as soon as, on one surjective étale scheme chart of the base,
  the graded ideal of Stacks 0801 of the base change of `Z` has the sections of `ℐ`.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 085H](https://stacks.math.columbia.edu/tag/085H)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

universe u

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable {s : RelativeProjSituation.{u, u}} (J : s.GradedIdeal)

namespace GradedIdeal

/-- The quotient map `𝒜 ⟶ 𝒜 ⧸ ℐ`, read over the scheme points of the base. -/
def quotientHomPoints :
    RelativeProjHomPoints s.relativeProjPoints J.quotientSituation.relativeProjPoints :=
  homPoints s.mul_comm s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT
    J.quotientSituation.mul_comm J.quotientSituation.negative_isZero
    J.quotientSituation.isQuasicoherent J.quotientSituation.sections_hasCardinalLT J.quotientMap

/-- For all sufficiently large `d`, the degree-`d` component of the quotient map `𝒜 ⟶ 𝒜 ⧸ ℐ` is
locally surjective as a map of presheaves on the small étale site of the base. -/
theorem eventually_isLocallySurjective_quotientMap :
    ∀ᶠ d : ℕ in Filter.atTop, Presheaf.IsLocallySurjective
      (SmallEtale.topology s.site s.base s.containsBase s.space.1)
      ((PresheafOfModules.toPresheaf _).map (J.quotientMap.app (d : ℤ)).val) :=
  Filter.Eventually.of_forall fun d =>
    (Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective _).1
      (J.toIdeal.epi_quotientMapApp d)

/-- The domain of definition of the morphism induced by the quotient map `𝒜 ⟶ 𝒜 ⧸ ℐ` is all of
`Proj_X(𝒜 ⧸ ℐ)`. -/
theorem relativeMapSubfunctor_quotientHomPoints_eq_top :
    J.quotientHomPoints.relativeMapSubfunctor = (⊤ : CategoryTheory.Subfunctor _) :=
  relativeMapSubfunctor_homPoints_eq_top _ _ _ _ _ _ _ _ _
    J.eventually_isLocallySurjective_quotientMap

/-- The morphism from the domain of definition to `Proj_X(𝒜)` induced by the quotient map
`𝒜 ⟶ 𝒜 ⧸ ℐ` is a closed immersion. -/
theorem isClosedImmersion_relativeMapSpaceHom_quotientHomPoints :
    IsClosedImmersion s.site s.base s.containsBase J.quotientHomPoints.relativeMapSpaceHom :=
  isClosedImmersion_relativeMapSpaceHom_homPoints _ _ _ _ _ _ _ _ _
    J.eventually_isLocallySurjective_quotientMap

/-- At every scheme point of the base the quotient map is surjective on the sections over the
affine opens, in every degree. -/
theorem surjectiveOnAffineSections_quotientHomPoints (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    Stacks.AlgebraicGeometry.ProjBundleSurjection.SurjectiveOnAffineSections
      (J.quotientHomPoints.hom T f) := by
  intro W hW n
  have : Epi ((J.quotientHomPoints.hom T f).app (n : ℤ)) :=
    epi_restrictHom_app s.mul_comm s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT
      J.quotientSituation.mul_comm J.quotientSituation.negative_isZero
      J.quotientSituation.isQuasicoherent J.quotientSituation.sections_hasCardinalLT J.quotientMap
      (n : ℤ) ((Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective _).1
        (J.toIdeal.epi_quotientMapApp n)) T f
  exact Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen _
    ((J.quotientHomPoints.hom T f).app (n : ℤ)) W hW

/-- A section killed by `φ` is killed by any morphism factoring through `φ`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.Hom.app_eq_zero_of_eq_comp {X : Scheme.{u}}
    {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (χ : M ⟶ K) (h : χ = φ ≫ ψ) (W : X.Opens)
    (a : Γ(M, W)) (ha : φ.app W a = 0) : χ.app W a = 0 := by
  subst h
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ha, map_zero]

/-- **The kernel of the restricted quotient map is monotone in the ideal.** For graded ideals
`J ⊆ I`, at every scheme point of the base a local section of `𝒜|_T` killed by the restriction of
`𝒜 ⟶ 𝒜 ⧸ J` is killed by the restriction of `𝒜 ⟶ 𝒜 ⧸ I`. -/
theorem quotientHomPoints_app_eq_zero_of_le {I : s.GradedIdeal}
    (h : ∀ n, J.piece n ≤ I.piece n) (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W))
    (ha : ((J.quotientHomPoints.hom T f).app n).app W a = 0) :
    ((I.quotientHomPoints.hom T f).app n).app W a = 0 := by
  have key := restrictHom_comp_app s.mul_comm s.negative_isZero s.isQuasicoherent
    s.sections_hasCardinalLT J.quotientSituation.mul_comm J.quotientSituation.negative_isZero
    J.quotientSituation.isQuasicoherent J.quotientSituation.sections_hasCardinalLT
    I.quotientSituation.mul_comm I.quotientSituation.negative_isZero
    I.quotientSituation.isQuasicoherent I.quotientSituation.sections_hasCardinalLT
    J.quotientMap (I.toIdeal.quotientMapOfLE h) T f n
  rw [I.toIdeal.quotientMap_comp_quotientMapOfLE h, SheafGradedAlgebraHom.comp_app] at key
  change ((restrictHom s.mul_comm s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT
    I.quotientSituation.mul_comm I.quotientSituation.negative_isZero
    I.quotientSituation.isQuasicoherent I.quotientSituation.sections_hasCardinalLT
    I.quotientMap T f).app n).app W a = 0
  change ((restrictHom s.mul_comm s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT
    J.quotientSituation.mul_comm J.quotientSituation.negative_isZero
    J.quotientSituation.isQuasicoherent J.quotientSituation.sections_hasCardinalLT
    J.quotientMap T f).app n).app W a = 0 at ha
  exact Scheme.Modules.Hom.app_eq_zero_of_eq_comp _ _ _ key W a ha

/-- The quotient map `𝒜 ⟶ 𝒜 ⧸ ℐ` induces an isomorphism of `Proj_X(𝒜 ⧸ ℐ)` with the domain of
definition `U(ψ)` of Tag 085F, which is everything. -/
def quotientDomainIso :
    J.quotientSituation.relativeProjFunctor ≅ J.quotientHomPoints.relativeMapSubfunctor.toFunctor :=
  have h : Subfunctor.range (𝟙 J.quotientSituation.relativeProjFunctor) ≤
      J.quotientHomPoints.relativeMapSubfunctor := by
    rw [J.relativeMapSubfunctor_quotientHomPoints_eq_top]
    exact le_top
  { hom := Subfunctor.lift (𝟙 _) h
    inv := J.quotientHomPoints.relativeMapSubfunctor.ι
    hom_inv_id := Subfunctor.lift_ι _ _
    inv_hom_id := by
      ext Y x
      exact Subtype.ext rfl }

/-- **The closed immersion `Proj_X(𝒜 ⧸ ℐ) ⟶ Proj_X(𝒜)`** of Tag 085H, for the quotient map. -/
def quotientProjHom : J.quotientSituation.Proj ⟶ s.Proj :=
  ObjectProperty.homMk (J.quotientDomainIso.hom ≫ J.quotientHomPoints.relativeMapSpaceHom)

/-- The morphism `quotientProjHom : Proj_X(𝒜 ⧸ ℐ) ⟶ Proj_X(𝒜)` is a closed immersion. -/
theorem isClosedImmersion_quotientProjHom :
    IsClosedImmersion s.site s.base s.containsBase J.quotientProjHom.hom :=
  MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase))) J.quotientDomainIso.hom _
    J.isClosedImmersion_relativeMapSpaceHom_quotientHomPoints

/-- The image of `quotientProjHom` equals the image of the morphism induced by the quotient map
on its domain of definition. -/
theorem range_quotientProjHom :
    Subfunctor.range J.quotientProjHom.hom =
      Subfunctor.range J.quotientHomPoints.relativeMapSpaceHom := by
  ext Y x
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨J.quotientDomainIso.inv.app Y y, rfl⟩

end GradedIdeal

/-! ### Quasi-compactness at a scheme point -/

/-- **A quasi-compact relative Proj is quasi-compact at every scheme point of the base**: if
`π : Proj_X(𝒜) ⟶ X` is quasi-compact, so is `Proj_T(𝒜|_T) ⟶ T` for every scheme point `T ⟶ X`,
being a base change of `π` (Stacks 084B). -/
theorem quasiCompact_relativeProj_toBase
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1) :
    QuasiCompact (relativeProj (s.relativeProjPoints.algebra T f)).toBase := by
  have h := (presheaf_quasiCompact_of_isQuasiCompact _ _ _
    s.relativeProjPoints.relativelyRepresentable hπ).property f
      (s.relativeProjPoints.fibreToSpace T f) (s.relativeProjPoints.fibreHom T f)
      (s.relativeProjPoints.isPullback T f)
  change QuasiCompact ((BigFppfOver.toScheme s.site s.base s.containsBase).map
    (s.relativeProjPoints.fibreHom T f)) at h
  rw [s.relativeProjPoints.fibreHom_comp] at h
  rw [← Iso.inv_hom_id_assoc (s.relativeProjPoints.fibreIso T f)
    (relativeProj (s.relativeProjPoints.algebra T f)).toBase]
  infer_instance

/-! ### Comparing two closed subspaces on a chart -/

/-- Composing two closed immersions with an isomorphism of their target preserves the inclusion
of their ideal sheaves. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.ker_comp_le_ker_comp_of_isIso {Y₁ Y₂ W W' : Scheme.{u}}
    (a : Y₁ ⟶ W) (b : Y₂ ⟶ W) (e : W ⟶ W') [AlgebraicGeometry.IsClosedImmersion a]
    (h : a.ker ≤ b.ker) : (a ≫ e).ker ≤ (b ≫ e).ker := by
  rw [← AlgebraicGeometry.IsClosedImmersion.lift_fac a b h, Category.assoc]
  exact Scheme.Hom.le_ker_comp _ _

variable {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

/-- The base change of a closed subspace `i : Z ⟶ Proj_X(𝒜)` to a scheme point `f : T ⟶ X`,
as a closed subscheme of `Proj_T(𝒜|_T)`. -/
def chartClosedSubscheme (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).obj
        ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.pullback
          (s.relativeProjPoints.fibreToSpace T f)) ⟶
      (relativeProj (s.relativeProjPoints.algebra T f)).scheme :=
  (BigFppfOver.toScheme s.site s.base s.containsBase).map
      ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
        (s.relativeProjPoints.fibreToSpace T f)) ≫
    (s.relativeProjPoints.fibreIso T f).hom

/-- The base change `chartClosedSubscheme i hi T f` of a closed subspace to a scheme point is a
closed immersion into `Proj_T(𝒜|_T)`. -/
instance isClosedImmersion_chartClosedSubscheme (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    AlgebraicGeometry.IsClosedImmersion (chartClosedSubscheme i hi T f) := by
  have : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map
      ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.snd
        (s.relativeProjPoints.fibreToSpace T f))) :=
    (closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.property _ _ _
      ((closedSubspaceOfIsClosedImmersion _ _ _ i hi).2.2.rep.isPullback _)
  unfold chartClosedSubscheme
  infer_instance

/-- **The identification `Z = Proj_X(𝒜 ⧸ ℐ)`, granted that it holds on one chart.** Let
`f : T ⟶ X` be a surjective étale scheme chart. If the closed immersion `r_{ψ|_T}` of Tag 07ZG for
the restriction of `ψ : 𝒜 ⟶ 𝒜 ⧸ ℐ` and the base change `Z ×_X T ⊆ Proj_T(𝒜|_T)` have the same
ideal sheaf, then `Z` is isomorphic to `Proj_X(𝒜 ⧸ ℐ)` over `Proj_X(𝒜)`. -/
theorem exists_iso_quotientProjHom_of_chart_ker (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1)
    (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase))) f)
    (hfS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase))) f)
    (hrel : (Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom
      (J.quotientHomPoints.hom T f)).ker = (chartClosedSubscheme i hi T f).ker) :
    ∃ e : Z ≅ J.quotientSituation.Proj, e.hom ≫ J.quotientProjHom = i := by
  set g := s.relativeProjPoints.fibreToSpace T f
  have hg : ∀ P : MorphismProperty Scheme.{u},
      (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme s.site s.base s.containsBase))) f →
      (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme s.site s.base s.containsBase))) g := fun P hf =>
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (s.relativeProjPoints.isPullback T f).flip hf
  have hgE := hg _ hfE
  have hgS := hg _ hfS
  let W : SmallEtale s.site s.base s.containsBase s.Proj.1 := ⟨CostructuredArrow.mk g, hgE⟩
  let Z₁ := closedSubspaceOfIsClosedImmersion _ _ _ i hi
  let Z₂ := closedSubspaceOfIsClosedImmersion _ _ _ J.quotientProjHom
    J.isClosedImmersion_quotientProjHom
  set ψ := J.quotientHomPoints.hom T f
  have := isClosedImmersion_relativeMapHom_of_surjective ψ
    (J.surjectiveOnAffineSections_quotientHomPoints T f)
  -- the chart of `Z₂`
  have h₂ : ((BigFppfOver.toScheme s.site s.base s.containsBase).map (Z₂.2.2.rep.snd g)).ker =
      (Stacks.AlgebraicGeometry.Tag07ZGMorphism.relativeMapHom ψ ≫
        (s.relativeProjPoints.fibreIso T f).inv).ker := by
    refine ker_snd_eq_of_mem_iff _ _ _ s.Proj Z₂ W _ fun {a} k => ?_
    change g.app (op a) k ∈ (Subfunctor.range J.quotientProjHom.hom).obj (op a) ↔ _
    rw [J.range_quotientProjHom]
    refine (J.quotientHomPoints.mem_range_relativeMapSpaceHom_iff T f k).trans
      (exists_congr fun τ => ?_)
    rw [← Category.assoc, Iso.comp_inv_eq]
  -- the chart of `Z₁`
  have h₁ : (BigFppfOver.toScheme s.site s.base s.containsBase).map (Z₁.2.2.rep.snd g) =
      chartClosedSubscheme i hi T f ≫ (s.relativeProjPoints.fibreIso T f).inv := by
    rw [chartClosedSubscheme, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hk : ((BigFppfOver.toScheme s.site s.base s.containsBase).map (Z₂.2.2.rep.snd g)).ker =
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (Z₁.2.2.rep.snd g)).ker := by
    rw [h₂, h₁]
    exact le_antisymm (Scheme.Hom.ker_comp_le_ker_comp_of_isIso _ _ _ hrel.le)
      (Scheme.Hom.ker_comp_le_ker_comp_of_isIso _ _ _ hrel.ge)
  exact exists_iso_comp_eq_of_range_eq _ _ _ i J.quotientProjHom hi
    J.isClosedImmersion_quotientProjHom <| le_antisymm
      (closedSubspace_le_of_ker_le_chart _ _ _ s.Proj Z₁ Z₂ g hgE hgS hk.le)
      (closedSubspace_le_of_ker_le_chart _ _ _ s.Proj Z₂ Z₁ g hgE hgS hk.ge)

/-- **The identification `Z = Proj_X(𝒜 ⧸ ℐ)`, granted the comparison of ideals on one chart.**
Let `f : T ⟶ X` be a surjective étale scheme chart. If the graded ideal of Stacks 0801 of the
base change `Z ×_X T ⊆ Proj_T(𝒜|_T)` has the sections of the kernel of `𝒜|_T ⟶ (𝒜 ⧸ ℐ)|_T`, then
`Z` is isomorphic to `Proj_X(𝒜 ⧸ ℐ)` over `Proj_X(𝒜)`. -/
theorem exists_iso_quotientProjHom_of_chart (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1)
    (hfE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase))) f)
    (hfS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase))) f)
    [QuasiCompact (relativeProj (s.relativeProjPoints.algebra T f)).toBase]
    (hker : ∀ (n : ℤ) (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
      (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)),
      a ∈ ((twistKerGradedIdeal (s.relativeProjPoints.algebra T f)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (chartClosedSubscheme i hi T f)).piece n).toSubmodule.obj (op W) ↔
        ((J.quotientHomPoints.hom T f).app n).app W a = 0) :
    ∃ e : Z ≅ J.quotientSituation.Proj, e.hom ≫ J.quotientProjHom = i :=
  exists_iso_quotientProjHom_of_chart_ker J i hi T f hfE hfS
    ((ker_relativeMapHom_eq_ker_projQuotientHom _
        (J.surjectiveOnAffineSections_quotientHomPoints T f) _ hker).trans
      (ker_eq_ker_projQuotientHom_twistKer _ _ _).symm)

end AlgebraicGeometry.Space.RelativeProjSituation
