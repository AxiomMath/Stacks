module

public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.DegreeSandwichPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceGlobalEquations
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDegreeIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuotientFibrePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# A closed subspace of the relative Proj cut out in a single degree

Let `X` be a quasi-compact and quasi-separated algebraic space, `𝒜` a quasi-coherent graded
`𝒪_X`-algebra (Situation 0849) and `π : P = Proj_X(𝒜) ⟶ X` the relative homogeneous spectrum
constructed in Stacks 084A–084B.  This file proves Stacks 085N on this `P`: for a closed
immersion `i : Z ⟶ P` of finite presentation, `π` quasi-compact, `U ⊆ |X|` a quasi-compact open
missing the image of `Z`, and every `𝒜_n` of finite type, there are `d > 0` and a quasi-coherent
`𝒪_X`-submodule of finite type `ℱ ⊆ 𝒜_d` with

* (a) `Z = Proj_X(𝒜/ℱ𝒜)` as closed subspaces of `P`: the range of `i` is the range of the closed
  immersion `Proj_X(𝒜/ℱ𝒜) ⟶ P` of the quotient situation
  (`AlgebraicGeometry.Space.RelativeProjSituation.quotientProjHom`, for the graded ideal
  `ℱ𝒜 = AlgebraicGeometry.Space.RelativeProjSituation.degreeIdeal ℱ`);
* (b) the support of `𝒜_d/ℱ` is disjoint from `U`.

The proof is the source's.  An affine étale chart `w : W ⟶ X` surjective on points is taken
from Stacks 03H6.  On `W`, Stacks 0803 gives `d > 0` and a quasi-coherent finite type
`ℱ' ⊆ (w^*𝒜)_d` of equations of `Z_W` cutting it out, with quotient supported away from `U`
(`AlgebraicGeometry.Space.RelativeProjSituation.exists_chart_finiteType_cutsOut_supp`).  The
globalization of Stacks 0829 inside the degree `d` part of the graded ideal of `Z`
(`AlgebraicGeometry.Space.RelativeProjSituation.exists_finiteType_le_pointZariskiImageSubmodule`)
gives `ℱ` with `ℱ' ⊆ 𝒢 ⊆ ℐ_d(Z_W)`, `𝒢` the image of `w^*ℱ`.  Then `𝒢` presents `Z_W`
(`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.degreeQuotientPresentation_of_le_twistKer`),
`w^*(𝒜/ℱ𝒜) = w^*𝒜/𝒢(w^*𝒜)`
(`RelativeProjSituation.isQuotientByDegreeSubmodule_pointZariskiImageSubmodule`),
so `Z ×_X W = Proj_W(w^*(𝒜/ℱ𝒜))` inside `P ×_X W`
(`AlgebraicGeometry.Space.RelativeProjSituation.range_eq_range_quotientFibreMap`), which descends
to (a) (`AlgebraicGeometry.Space.RelativeProjSituation.range_eq_range_quotientProjHom_of_fibre`);
(b) descends from `W` along the chart
(`AlgebraicGeometry.Space.RelativeProjSituation.disjoint_supportOfSheaf_cokernel_of_le`).

## Main results

* `RelativeProjSituation.exists_finiteType_degreeSubmodule_range_eq_quotientProj`:
  **Stacks 085N**.
* `RelativeProjSituation.nonempty_closedSubspaceDegreeQuotientPresentation_of_range_eq`:
  the two encodings of clause (a) agree.  The range equality above gives the structure
  `AlgebraicGeometry.Space.ClosedSubspaceDegreeQuotientPresentation`, with its space and its
  closed immersion taken from `Proj_X(𝒜/ℱ𝒜)`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

universe u

namespace AlgebraicGeometry.Space

/-- **Two monomorphisms into one algebraic space with the same range are identified over it.**
A monomorphism of presheaves identifies its source with its range subfunctor
(`CategoryTheory.Subfunctor.toRange`), so two monomorphisms with the same range — for instance two
closed subspaces cutting out the same subfunctor — differ by a unique isomorphism of their sources
over the common target.  Only monomorphy of the two maps is assumed, and the second subobject is
an unbundled monomorphism of presheaves together with a witness that its source is an algebraic
space. -/
theorem exists_iso_comp_eq_of_range_eq_of_mono {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {P Z : AlgebraicSpaces B S hS} (i : Z ⟶ P) (hi : Mono i.hom)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hQ : IsAlgebraicSpace B S hS Q) (q : Q ⟶ P.obj)
    (hq : Mono q) (h : Subfunctor.range i.hom = Subfunctor.range q) :
    ∃ e : Z ≅ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS),
      e.hom ≫ ObjectProperty.homMk q = i := by
  have := hi
  have := hq
  have key : ∀ {A A' : Subfunctor P.obj} (hA : A = A'),
      ∃ k : A.toFunctor ≅ A'.toFunctor, k.hom ≫ A'.ι = A.ι := by
    intro A A' hA
    subst hA
    exact ⟨Iso.refl _, Category.id_comp _⟩
  obtain ⟨k, hk⟩ := key h
  have hinv : (asIso (Subfunctor.toRange q)).inv ≫ q = (Subfunctor.range q).ι :=
    (asIso (Subfunctor.toRange q)).inv_comp_eq.2 (Subfunctor.toRange_ι q).symm
  have hfun : (asIso (Subfunctor.toRange i.hom) ≪≫ k ≪≫
      (asIso (Subfunctor.toRange q)).symm).hom ≫ q = i.hom := by
    change (Subfunctor.toRange i.hom ≫ k.hom ≫ (asIso (Subfunctor.toRange q)).inv) ≫ q = i.hom
    rw [Category.assoc, Category.assoc, hinv, hk, Subfunctor.toRange_ι]
  exact ⟨ObjectProperty.isoMk _ (asIso (Subfunctor.toRange i.hom) ≪≫ k ≪≫
    (asIso (Subfunctor.toRange q)).symm), InducedCategory.hom_ext hfun⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, u})

/-- **Clause (a) of Stacks 085N from a chart.**  Let `w : W ⟶ X` be an affine étale chart
surjective on points, `ℱ ⊆ 𝒜_d` quasi-coherent with image `𝒢 ⊆ (w^*𝒜)_d` of `w^*ℱ`, and
`ℱ' ⊆ 𝒢 ⊆ ℐ_d(Z_W)` with `ℱ'` cutting out the fibre `Z_W` on the charts of Tag 0801's
presentation.  Then `Z = Proj_X(𝒜/ℱ𝒜)` as closed subspaces of `P`: on `W`, `𝒢` presents `Z_W`
and `w^*(𝒜/ℱ𝒜) = w^*𝒜/𝒢(w^*𝒜)`, so `Z ×_X W = Proj_W(w^*(𝒜/ℱ𝒜))`, which descends along the
étale surjective `w`. -/
theorem range_eq_range_quotientProjHom_of_chart
    {Z : AlgebraicSpaces s.site s.base s.containsBase} {i : Z.1 ⟶ s.relativeProjFunctor}
    (hi : IsClosedImmersion s.site s.base s.containsBase i)
    {T : BigFppfOver s.site s.base s.containsBase} {f : yoneda.obj T ⟶ s.space.1}
    [_root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)]
    [QuasiCompact (relativeProj (s.shrink.pointAlgebra T f)).toBase]
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    (hfs : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    {d : ℕ} (hd : 0 < d) (ℱ : (s.algebra.piece (d : ℤ)).Submodule)
    (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite)
    {ℱ' : ((s.shrink.pointAlgebra T f).piece (d : ℤ)).Submodule}
    (hle₁ : ℱ' ≤ s.pointZariskiImageSubmodule f ℱ)
    (hcut : CutsOutOnCharts (s.shrink.pointAlgebra T f) ℱ'
      (quotHom (s.shrink.pointAlgebra T f) (twistKerGradedIdeal (s.shrink.pointAlgebra T f)
        (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
        (s.fibreClosedImmersion hi T f))))
    (hle₂ : s.pointZariskiImageSubmodule f ℱ ≤ (twistKerGradedIdeal (s.shrink.pointAlgebra T f)
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
      (s.fibreClosedImmersion hi T f)).piece (d : ℤ)) :
    Subfunctor.range i = Subfunctor.range (s.quotientProjHom (s.degreeIdeal ℱ)
      (s.isQuasicoherentOnSite_degreeIdeal_piece ℱ hℱ)) := by
  obtain ⟨p⟩ := degreeQuotientPresentation_of_le_twistKer (s.shrink.pointAlgebra T f)
    (s.fibreClosedImmersion hi T f) hd hle₁ hcut
    (s.isQuasicoherent_pointZariskiImageSubmodule f ℱ hℱ) hle₂
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map (s.fibreClosedSubspaceHom hi T f) ≫
        (s.relativeProjPoints.fibreIso T f).hom) :=
    s.isClosedImmersion_fibreClosedImmersion hi T f
  have hfib := s.range_eq_range_quotientFibreMap (s.degreeIdeal ℱ)
    (s.isQuasicoherentOnSite_degreeIdeal_piece ℱ hℱ) T f (s.fibreClosedSubspaceHom hi T f)
    (s.isQuasicoherent_pointZariskiImageSubmodule f ℱ hℱ) p
    (s.isQuotientByDegreeSubmodule_pointZariskiImageSubmodule f ℱ hℱ)
  have : Mono i := mono_of_isClosedImmersion s.site s.base s.containsBase i hi
  exact s.range_eq_range_quotientProjHom_of_fibre (s.degreeIdeal ℱ)
    (s.isQuasicoherentOnSite_degreeIdeal_piece ℱ hℱ) i Z.2.isSheaf f hf hfs
    ((Subfunctor.preimage_range_of_isPullback (s.isPullback_fibreClosedSubspace hi T f)).trans
      hfib)

attribute [local instance] pointTopology in
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **Stacks 085N from an affine étale chart surjective on points.**  The statement of
`RelativeProjSituation.exists_finiteType_degreeSubmodule_range_eq_quotientProj`
for a given affine étale chart `W` of `X` whose structure morphism is surjective: Stacks 0803 on
`W`, the globalization of Stacks 0829, then clauses (a) and (b) descend from `W`. -/
theorem exists_finiteType_degreeSubmodule_range_eq_quotientProj_of_chart
    (hX : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
    (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase s.site.contains_terminal
      s.space.1)
    {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z.1 ⟶ s.relativeProjFunctor)
    (hi : IsClosedImmersion s.site s.base s.containsBase i)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    (hfp : IsFinitePresentation s.site s.base s.containsBase i)
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.relativeProjFunctor s.relativeProjπ
        (pointsMap s.site s.base s.containsBase Z.1 i z)))
    (hU : IsOpen U) (hUc : IsCompact U)
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteType (s.algebra.piece n))
    (W : SmallEtale s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space.1)
    (hWaff : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W.1.left))
    (hWs : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf W.1.hom) :
    ∃ (d : ℕ) (_ : 0 < d) (ℱ : (s.algebra.piece (d : ℤ)).Submodule)
      (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite),
      SheafOfModules.IsFiniteType ℱ.toSheafOfModules ∧
        Subfunctor.range i = Subfunctor.range (s.quotientProjHom (s.degreeIdeal ℱ)
          (s.isQuasicoherentOnSite_degreeIdeal_piece ℱ hℱ)) ∧
        Disjoint (supportOfSheaf s.site s.base s.containsBase s.space.1
          ((SheafOfModules.toSheaf (structureRingSheaf s.site s.base s.containsBase
            s.space)).obj (cokernel ℱ.ι))) U := by
  have hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf W.1.hom := W.2
  have hsurj := (surjective_iff_surjective_pointsMap s.site s.base s.containsBase s.space.1
    s.space.2 W.1.left W.1.hom).1 hWs
  have : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W.1.left) := hWaff
  have hqT : QuasiCompact (relativeProj (s.shrink.pointAlgebra W.1.left W.1.hom)).toBase :=
    s.quasiCompact_fibre_toBase W.1.left W.1.hom hπ hWaff
  have hiT : _root_.AlgebraicGeometry.IsClosedImmersion
      (s.fibreClosedImmersion hi W.1.left W.1.hom) :=
    s.isClosedImmersion_fibreClosedImmersion hi W.1.left W.1.hom
  obtain ⟨V, -, hUV, d, hd, ℱ', hℱ'q, hℱ'f, hV, heq, hcut⟩ :=
    s.exists_chart_finiteType_cutsOut_supp hi hWaff hf hsurj hfp hZU hU hUc hA
  have hℱ'K : ℱ' ≤ (twistKerGradedIdeal (s.shrink.pointAlgebra W.1.left W.1.hom)
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
      (s.fibreClosedImmersion hi W.1.left W.1.hom)).piece (d : ℤ) :=
    SheafOfModules.Submodule.le_iff.mpr fun O a ha =>
      (quotProj_app_eq_zero_iff (s.shrink.pointAlgebra W.1.left W.1.hom)
        (twistKerGradedIdeal (s.shrink.pointAlgebra W.1.left W.1.hom)
          (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
          (s.fibreClosedImmersion hi W.1.left W.1.hom)) (d : ℤ) O.unop a).1 (heq O.unop a ha)
  obtain ⟨ℱ, hℱ, hℱf, hle₁, hle₂⟩ := s.exists_finiteType_le_pointZariskiImageSubmodule hX hXqs hi
    hπ W hWaff ℱ' hℱ'q hℱ'f hℱ'K
  exact ⟨d, hd, ℱ, hℱ, hℱf, s.range_eq_range_quotientProjHom_of_chart hi hf hWs hd ℱ hℱ hle₁
    hcut hle₂, s.disjoint_supportOfSheaf_cokernel_of_le hf ℱ hℱ ℱ' hle₁ V hV hUV⟩

attribute [local instance] pointTopology in
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- **Stacks 085N.**  Let `X` be a quasi-compact and quasi-separated algebraic space over `S`,
`𝒜` a quasi-coherent graded `𝒪_X`-algebra and `π : P = Proj_X(𝒜) ⟶ X` its relative Proj
(Stacks 084A–084B).  Let `i : Z ⟶ P` be a closed subspace and `U ⊆ |X|` open.  Assume
(1) `π` quasi-compact, (2) `i` of finite presentation, (3) `|U| ∩ |π|(|i|(|Z|)) = ∅`,
(4) `U` quasi-compact and (5) every `𝒜_n` of finite type.  Then there are `d > 0` and a
quasi-coherent `𝒪_X`-submodule of finite type `ℱ ⊆ 𝒜_d` with (a) `Z = Proj_X(𝒜/ℱ𝒜)` and
(b) the support of `𝒜_d/ℱ` disjoint from `U`.

Clause (a) says that `Z` and the closed subspace `Proj_X(𝒜/ℱ𝒜) ⟶ P`
(`AlgebraicGeometry.Space.RelativeProjSituation.quotientProjHom` of the graded ideal `ℱ𝒜`,
`AlgebraicGeometry.Space.RelativeProjSituation.degreeIdeal`) have the same range in `P`; clause
(b) is disjointness from `U` of the support (Stacks 04KA) of the cokernel of `ℱ ⊆ 𝒜_d`.
"`X` quasi-separated" is `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` (Stacks 03BS).
The source writes the closed subspace as `i : Z → X`; its hypothesis (3) and conclusion (a) place
`Z` in `P`, and it is formalized as `i : Z ⟶ P`. -/
@[stacks 085N "the relative Proj P = Proj_X(𝒜) of Stacks 084A-084B; clause (a) is the equality \
of the ranges of i : Z ⟶ P and of the closed immersion Proj_X(𝒜/ℱ𝒜) ⟶ P, clause (b) the \
disjointness from U of the support of 𝒜_d/ℱ; the closed subspace written i : Z → X in the source \
is i : Z ⟶ P, which condition (3) and clause (a) require"]
theorem exists_finiteType_degreeSubmodule_range_eq_quotientProj
    (hX : IsQuasiCompactSpace s.site s.base s.containsBase s.space.1)
    (hXqs : IsAbsolutelyQuasiSeparated s.site s.base s.containsBase s.site.contains_terminal
      s.space.1)
    {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z.1 ⟶ s.relativeProjFunctor)
    (hi : IsClosedImmersion s.site s.base s.containsBase i)
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.relativeProjπ)
    (hfp : IsFinitePresentation s.site s.base s.containsBase i)
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hZU : Disjoint U (Set.range fun z ↦
      pointsMap s.site s.base s.containsBase s.relativeProjFunctor s.relativeProjπ
        (pointsMap s.site s.base s.containsBase Z.1 i z)))
    (hU : IsOpen U) (hUc : IsCompact U)
    (hA : ∀ n : ℤ, SheafOfModules.IsFiniteType (s.algebra.piece n)) :
    ∃ (d : ℕ) (_ : 0 < d) (ℱ : (s.algebra.piece (d : ℤ)).Submodule)
      (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite),
      SheafOfModules.IsFiniteType ℱ.toSheafOfModules ∧
        Subfunctor.range i = Subfunctor.range (s.quotientProjHom (s.degreeIdeal ℱ)
          (s.isQuasicoherentOnSite_degreeIdeal_piece ℱ hℱ)) ∧
        Disjoint (supportOfSheaf s.site s.base s.containsBase s.space.1
          ((SheafOfModules.toSheaf (structureRingSheaf s.site s.base s.containsBase
            s.space)).obj (cokernel ℱ.ι))) U := by
  obtain ⟨T, f, hTaff, hTsurj, hTetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover s.site s.base s.containsBase
      s.space.1 s.space.2).1 hX
  have hid : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf (yoneda.map (𝟙 T)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff s.site s.base s.containsBase
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 T)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f := by
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using
      hTetale T (yoneda.map (𝟙 T)) hid
  exact s.exists_finiteType_degreeSubmodule_range_eq_quotientProj_of_chart hX hXqs i hi hπ hfp hZU
    hU hUc hA ⟨CostructuredArrow.mk f, hf⟩ hTaff hTsurj

/-! ### Clause (a) in its other encoding -/

/-- **The two encodings of the clause `Z = Proj_X(𝒜/ℱ𝒜)` agree.**

The clause is written here as the equality of the ranges of `i : Z ⟶ Proj_X(𝒜)` and of the closed
immersion `Proj_X(𝒜/ℱ𝒜) ⟶ Proj_X(𝒜)`
(`AlgebraicGeometry.Space.RelativeProjSituation.quotientProjHom` of
`AlgebraicGeometry.Space.RelativeProjSituation.degreeIdeal`), and as the structure
`AlgebraicGeometry.Space.ClosedSubspaceDegreeQuotientPresentation`.  This produces the second
from the first, for a closed subspace `i`: the graded algebra and its degreewise surjection are
`𝒜 ⟶ 𝒜/ℱ𝒜` (`…quotientAlgebra`, `…quotientMkApp`), whose kernel in degree `d + e` is the graded
ideal `ℱ𝒜` of Stacks 085M by
`RelativeProjSituation.generatedByDegree_add_eq_closedSubspaceDegreeProducts`;
the structure's space is `Proj_X(𝒜/ℱ𝒜)` with the closed immersion `…quotientProjHom`; and the
identification of `Z` with it over `Proj_X(𝒜)` is the isomorphism of two monomorphisms with equal
range, `AlgebraicGeometry.Space.exists_iso_comp_eq_of_range_eq_of_mono`. -/
theorem nonempty_closedSubspaceDegreeQuotientPresentation_of_range_eq
    {Z : AlgebraicSpaces s.site s.base s.containsBase}
    (i : Z ⟶ (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase))
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
    {d : ℕ} (hd : 0 < d) (ℱ : (s.algebra.piece (d : ℤ)).Submodule)
    (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite)
    (hrange : Subfunctor.range i.hom = Subfunctor.range (s.quotientProjHom (s.degreeIdeal ℱ)
      (s.isQuasicoherentOnSite_degreeIdeal_piece ℱ hℱ))) :
    Nonempty (ClosedSubspaceDegreeQuotientPresentation i hd ℱ) := by
  have hqc : ∀ n : ℤ, ((s.degreeIdeal ℱ).piece n).toSheafOfModules.IsQuasicoherentOnSite :=
    s.isQuasicoherentOnSite_degreeIdeal_piece ℱ hℱ
  have hker : ∀ e : ℤ, Stacks.SheafOfModules.kerSubmodule
      (s.quotientMkApp (s.degreeIdeal ℱ) ((d : ℤ) + e)) =
        closedSubspaceDegreeProducts s (d : ℤ) e ℱ := by
    intro e
    rw [← s.generatedByDegree_add_eq_closedSubspaceDegreeProducts ℱ e]
    exact le_antisymm
      (SheafOfModules.Submodule.le_iff.mpr fun U x hx =>
        mem_of_quotientMkApp_eq_zero s (s.degreeIdeal ℱ) ((d : ℤ) + e) U x hx)
      (SheafOfModules.Submodule.le_iff.mpr fun U x hx =>
        ι_app_mem_quotientMkApp_eq_zero s (s.degreeIdeal ℱ) ((d : ℤ) + e) U x hx)
  have hspace : IsAlgebraicSpace s.site s.base s.containsBase
      (s.quotient (s.degreeIdeal ℱ) hqc).relativeProjFunctor :=
    (s.quotient (s.degreeIdeal ℱ) hqc).isAlgebraicSpace_relativeProjFunctor
  obtain ⟨eZ, heZ⟩ := exists_iso_comp_eq_of_range_eq_of_mono i
    (mono_of_isClosedImmersion s.site s.base s.containsBase i.hom hi) hspace
    (s.quotientProjHom (s.degreeIdeal ℱ) hqc)
    (s.mono_quotientProjHom (s.degreeIdeal ℱ) hqc) hrange
  exact ⟨{ quotient := s.quotientAlgebra (s.degreeIdeal ℱ)
           quotientMap n := s.quotientMkApp (s.degreeIdeal ℱ) n
           epi n := s.epi_quotientMkApp (s.degreeIdeal ℱ) n
           map_mul e U a b := (s.quotientHom (s.degreeIdeal ℱ)).map_mul (d : ℤ) e U a b
           ker_eq := hker
           space := ⟨(s.quotient (s.degreeIdeal ℱ) hqc).relativeProjFunctor, hspace⟩
           toAmbient := ObjectProperty.homMk (s.quotientProjHom (s.degreeIdeal ℱ) hqc)
           isClosedImmersion := s.isClosedImmersion_quotientProjHom (s.degreeIdeal ℱ) hqc
           iso := eZ
           iso_comp := heZ }⟩

end AlgebraicGeometry.Space.RelativeProjSituation

end
