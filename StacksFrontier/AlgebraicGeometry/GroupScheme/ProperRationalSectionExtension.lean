module

public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContraction
public import StacksFrontier.AlgebraicGeometry.F6Rank89.CoheightOfSurface
public import StacksFrontier.AlgebraicGeometry.F6Rank89.ExtendRationalMap
public import StacksFrontier.AlgebraicGeometry.GroupScheme.BaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ProjectiveLineConstant
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMapDimTwo
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveLocus
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalSquareChain
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMapsUnconditional
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupFactorizationStep
import all
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMapDimTwo

/-!
# Rational sections of proper group schemes over regular surfaces

Let `X` be an integral Noetherian regular scheme of dimension at most two and let `G` be a proper
group scheme over `X`. This file proves that every section of `G` over the generic point of `X`
extends to a section of `G ⟶ X`, granted that morphisms from the projective line over a field
to a group scheme over that field are constant ([Stacks, Tag 0AEN]), which
`AlgebraicGeometry.exists_section_eq_comp_of_projectiveLineProj` proves. This is the core of the
sketch of the proof of [Stacks, Tag 0AF9].

The section over the generic point spreads out to a rational map `X ⇢ G` over `X`. In dimension
at most one the indeterminacy locus consists of points with discrete valuation rings for local
rings, and the valuative criterion extends the map across them. In dimension two
[Stacks, Tag 0C5H] resolves the rational map by a chain of blowups at closed points. Going down
the chain, the exceptional curve of each blowup is a projective line over the residue field of
the blown up point, which the morphism to `G` sends into the fibre of `G` over a point; by
rigidity it is constant on that curve, and the contraction of [Stacks, Tag 0C5J] factors it
through the blowup.

## Main results

* `AlgebraicGeometry.GroupScheme.exists_eq_projToSpecCoeff_comp_of_range_subset` — a morphism
  from `𝐏¹_k` whose image lies in an affine open factors through the structure morphism
  `𝐏¹_k ⟶ Spec k`.
* `AlgebraicGeometry.GroupScheme.exists_comp_eq_of_pointBlowupChain_of_rigid` — a morphism over
  `X` from the top of a chain of blowups at closed points of an integral regular surface to a
  proper group scheme over `X` comes from a section.
* `AlgebraicGeometry.GroupScheme.exists_section_extending_of_isRegular_of_rigid` — the
  extension of a generic section, granted rigidity.
* `AlgebraicGeometry.GroupScheme.exists_section_extending_of_isRegular` — the extension of a
  generic section, unconditionally.

## References

* [Stacks Project, Tag 0AF9](https://stacks.math.columbia.edu/tag/0AF9)
* [Stacks Project, Tag 0AEN](https://stacks.math.columbia.edu/tag/0AEN)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace AlgebraicGeometry.GroupScheme

/-! ### Morphisms out of the projective line with image in an affine open -/

/-- The structure morphism `𝐏¹_k ⟶ Spec k` induces an isomorphism on global sections. -/
theorem isIso_appTop_projToSpecCoeff (k : Type u) [Field k] :
    IsIso (projToSpecCoeff k 1).appTop := by
  have hbij := Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections k 1
  have : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (projToSpecCoeff k 1).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _

/-- **A morphism from `𝐏¹_k` with image in an affine open factors through `Spec k`.** The
global functions on `𝐏¹_k` are `k`, so a morphism to an affine scheme factors through the
structure morphism. -/
theorem exists_eq_projToSpecCoeff_comp_of_range_subset (k : Type u) [Field k] {Y : Scheme.{u}}
    (g : projectiveLineProj k ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (hg : Set.range g.base ⊆ U) :
    ∃ t : Spec (CommRingCat.of k) ⟶ Y, g = projToSpecCoeff k 1 ≫ t := by
  have : IsAffine U := hU
  have := isIso_appTop_projToSpecCoeff k
  let g' : projectiveLineProj k ⟶ U := IsOpenImmersion.lift U.ι g (by simpa using hg)
  have hg' : g' ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  refine ⟨(Spec (CommRingCat.of k)).isoSpec.hom ≫ Spec.map (inv (projToSpecCoeff k 1).appTop) ≫
    Spec.map g'.appTop ≫ (U : Scheme.{u}).isoSpec.inv ≫ U.ι, ?_⟩
  have h1 : projToSpecCoeff k 1 ≫ (Spec (CommRingCat.of k)).isoSpec.hom =
      (projectiveLineProj k).toSpecΓ ≫ Spec.map (projToSpecCoeff k 1).appTop :=
    Scheme.toSpecΓ_naturality _
  have h2 : g' ≫ (U : Scheme.{u}).isoSpec.hom =
      (projectiveLineProj k).toSpecΓ ≫ Spec.map g'.appTop :=
    Scheme.toSpecΓ_naturality _
  rw [reassoc_of% h1, ← Spec.map_comp_assoc, IsIso.inv_hom_id, Spec.map_id, Category.id_comp,
    ← reassoc_of% h2, Iso.hom_inv_id_assoc, hg']

/-! ### Rigidity on the exceptional curve -/

/-- The rigidity input, [Stacks, Tag 0AEN] for schemes: a morphism over `k` from the projective
line over a field `k` to a separated group scheme locally of finite type over `k` factors through
the structure morphism and a `k`-point. -/
def ProjectiveLineRigidity : Prop :=
  ∀ (k : Type u) [Field k] (H : Over (Spec (CommRingCat.of k))) [GrpObj H] [IsSeparated H.hom]
    [LocallyOfFiniteType H.hom] (f : projectiveLineProj k ⟶ H.left),
    f ≫ H.hom = projToSpecCoeff k 1 →
      ∃ c : Spec (CommRingCat.of k) ⟶ H.left, c ≫ H.hom = 𝟙 _ ∧ f = projToSpecCoeff k 1 ≫ c

variable {X : Scheme.{u}}

/-- **The exceptional curve goes to a point.** Let `V` be an integral regular surface with a
morphism `q : V ⟶ X`, let `w ∈ V` be a closed point with two-dimensional local ring, and let
`h` be a morphism from the blowup of `V` at `w` to a proper group scheme `G` over `X`, over `X`.
Granted rigidity, `h` is constant on the exceptional curve. -/
theorem exists_const_on_exceptionalCurve_of_rigid (hrigid : ProjectiveLineRigidity.{u})
    {V : Scheme.{u}} (hV : IsIntegralRegularSurface V) {w : V} (hw : IsClosed ({w} : Set V))
    (hdim : ringKrullDim (V.presheaf.stalk w) = 2) (G : Over X) [GrpObj G] [IsProper G.hom]
    (q : V ⟶ X) (h : pointBlowUp hw ⟶ G.left) (hh : h ≫ G.hom = pointBlowUpToBase hw ≫ q) :
    ∃ y : G.left, ∀ z : (exceptionalIdeal
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))).subscheme,
      h ((exceptionalIdeal
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))).subschemeι z) = y := by
  set E := exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds V))
  set k := IsLocalRing.ResidueField (V.presheaf.stalk w)
  obtain ⟨e, -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal w hw
      (IsRegular.isRegularLocalRing_stalk hV.isRegular w) hdim
  let j : projectiveLineProj k ⟶ pointBlowUp hw := e.hom ≫ E.subschemeι
  -- The curve lies over `w`, hence over the single point `q w` of `X`.
  have hjw : ∀ a, (j ≫ pointBlowUpToBase hw) a = w := by
    intro a
    have hmem : E.subschemeι (e.hom a) ∈ (E.support : Set (pointBlowUp hw)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
    exact hmem
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (q w)) isOpen_univ
  have hrange : Set.range (j ≫ h ≫ G.hom).base ⊆ (U : Set X) := by
    rintro _ ⟨a, rfl⟩
    rw [hh, ← Category.assoc, Scheme.Hom.comp_apply, hjw a]
    exact hxU
  obtain ⟨t, ht⟩ := exists_eq_projToSpecCoeff_comp_of_range_subset k _ hU hrange
  -- The base change of `G` to `Spec k` is a group scheme over `k`.
  let H := (Over.pullback t).obj G
  have : IsSeparated H.hom := by
    change IsSeparated (pullback.snd G.hom t)
    infer_instance
  have : LocallyOfFiniteType H.hom := by
    change LocallyOfFiniteType (pullback.snd G.hom t)
    infer_instance
  let f : projectiveLineProj k ⟶ H.left :=
    pullback.lift (j ≫ h) (projToSpecCoeff k 1) (by rw [Category.assoc, ht])
  obtain ⟨c, -, hc⟩ := hrigid k H f (pullback.lift_snd _ _ _)
  have hf : f ≫ pullback.fst G.hom t = j ≫ h := pullback.lift_fst _ _ _
  refine ⟨(c ≫ pullback.fst G.hom t) (default : Spec (CommRingCat.of k)), fun z => ?_⟩
  have hz : E.subschemeι z = j (e.inv z) := by
    change _ = (e.inv ≫ e.hom ≫ E.subschemeι) z
    rw [Iso.inv_hom_id_assoc]
  rw [hz, ← Scheme.Hom.comp_apply, ← hf, hc, Category.assoc, Scheme.Hom.comp_apply,
    Subsingleton.elim (projToSpecCoeff k 1 (e.inv z)) default]

/-! ### Contracting a chain of blowups -/

/-- **A morphism out of a chain of point blowups into a proper group scheme comes from a
section.** Let `X` be an integral regular surface, `G` a proper group scheme over `X`, and
`p : Z ⟶ X` a chain of blowups at closed points. Granted rigidity, every morphism
`h : Z ⟶ G` over `X` is `p ≫ g` for a section `g` of `G ⟶ X`. -/
theorem exists_comp_eq_of_pointBlowupChain_of_rigid (hrigid : ProjectiveLineRigidity.{u})
    (hX : IsIntegralRegularSurface X) (G : Over X) [GrpObj G] [IsProper G.hom] {T : Set X}
    {Z : Scheme.{u}} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p) :
    ∀ h : Z ⟶ G.left, h ≫ G.hom = p → ∃ g : X ⟶ G.left, g ≫ G.hom = 𝟙 X ∧ p ≫ g = h := by
  induction hp with
  | refl => exact fun h hh => ⟨h, hh, Category.id_comp h⟩
  | @step V qV hqV w hw hwT ih =>
    intro h hh
    obtain ⟨hVsurf, -⟩ := isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional
      hqV hX
    have := hVsurf.isNoetherian
    have hh' : h ≫ G.hom = pointBlowUpToBase hw ≫ qV := hh
    rcases isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two hVsurf w hw with hiso | hdim2
    · obtain ⟨g, hg1, hg2⟩ := ih (inv (pointBlowUpToBase hw) ≫ h)
        (by rw [Category.assoc, hh', IsIso.inv_hom_id_assoc])
      refine ⟨g, hg1, ?_⟩
      change pointBlowUpToBase hw ≫ qV ≫ g = h
      rw [hg2, IsIso.hom_inv_id_assoc]
    · have hconst := exists_const_on_exceptionalCurve_of_rigid hrigid hVsurf hw hdim2 G qV h hh'
      obtain ⟨ψ, hψ1, hψ2⟩ := exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve
        (isContractionOfExceptionalCurve_blowUpToBase w hw
          (IsRegular.isRegularLocalRing_stalk hVsurf.isRegular w) hdim2) qV G.hom h hh' hconst
      obtain ⟨g, hg1, hg2⟩ := ih ψ hψ2
      refine ⟨g, hg1, ?_⟩
      change pointBlowUpToBase hw ≫ qV ≫ g = h
      rw [hg2, hψ1]

/-! ### Extending a generic section -/

/-- On an integral Noetherian scheme of dimension at most two which is not two, a point outside
a dense open has coheight one. -/
theorem coheight_eq_one_of_notMem_of_ne_two [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 2)
    (hne : topologicalKrullDim X ≠ 2) {U : X.Opens} (hU : Dense (U : Set X)) {x : X}
    (hx : x ∉ U) : Order.coheight x = 1 := by
  rcases coheight_eq_one_or_two_of_notMem_dense hdim hU hx with h1 | h2
  · exact h1
  · refine absurd (le_antisymm hdim ?_) hne
    have := coheight_le_topologicalKrullDim x
    rw [h2] at this
    exact this

/-- **The extension in dimension at most one.** -/
theorem exists_extension_of_ne_two [IsIntegral X] [IsNoetherian X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 2) (hne : topologicalKrullDim X ≠ 2) (G : Over X)
    [IsProper G.hom] (f : X.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι) :
    ∃ g : X ⟶ G.left, g ≫ G.hom = 𝟙 X ∧ f.domain.ι ≫ g = f.hom := by
  classical
  let : X.Over X := ⟨𝟙 X⟩
  let : G.left.Over X := ⟨G.hom⟩
  have : IsProper (G.left ↘ X) := ‹IsProper G.hom›
  have hco : ∀ x : X, x ∉ f.domain → Order.coheight x = 1 :=
    fun x hx => coheight_eq_one_of_notMem_of_ne_two hdim hne f.dense_domain hx
  have hpt : ∀ x ∈ ((f.domain : Set X)ᶜ), IsClosed ({x} : Set X) := by
    intro x hx
    refine closure_subset_iff_isClosed.mp fun z hz => ?_
    have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hz
    have hzU : z ∉ f.domain := fun hzU => hx (hxz.mem_open f.domain.2 hzU)
    by_contra hzx
    have hlt : z < x := lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxz) fun hxz' =>
      hzx (inseparable_iff_specializes_and.mpr
        ⟨Scheme.le_iff_specializes.mp hxz', hxz⟩).eq
    have := Order.coheight_add_one_le hlt
    rw [hco z hzU, hco x hx] at this
    exact absurd this (by norm_num)
  have hfin : ((f.domain : Set X)ᶜ).Finite :=
    Stacks.ResolutionOfSurfaces.finite_of_forall_isClosed_singleton f.domain.2.isClosed_compl hpt
  obtain ⟨f₁, hff₁, hf₁base, hres, hF⟩ :=
    Scheme.PartialMap.exists_extension_of_finset_ringKrullDim_eq_one (S := X) f
      (by change f.hom ≫ G.hom = f.domain.ι ≫ 𝟙 X; rw [Category.comp_id]; exact hf)
      (fun x => hreg.isRegularLocalRing_stalk x) hfin.toFinset
      (fun x hx => by
        rw [ringKrullDim_stalk_eq_coheight, hco x (hfin.mem_toFinset.mp hx)]
        rfl)
  have htop : ⊤ ≤ f₁.domain := by
    intro x _
    by_cases hx : x ∈ f.domain
    · exact hff₁ hx
    · exact hF x (hfin.mem_toFinset.mpr hx)
  have hf₁ : f₁.hom ≫ G.hom = f₁.domain.ι := by
    have h := hf₁base
    change f₁.hom ≫ G.hom = f₁.domain.ι ≫ 𝟙 X at h
    rwa [Category.comp_id] at h
  refine ⟨X.topIso.inv ≫ X.homOfLE htop ≫ f₁.hom, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hf₁, Scheme.homOfLE_ι, Scheme.toIso_inv_ι]
  · rw [← hres]
    simp only [← Category.assoc]
    congr 1
    rw [← cancel_mono f₁.domain.ι]
    simp [Scheme.homOfLE_ι, Scheme.toIso_inv_ι]

/-- **The extension in dimension two.** -/
theorem exists_extension_of_eq_two_of_rigid (hrigid : ProjectiveLineRigidity.{u}) [IsIntegral X]
    [IsNoetherian X] (hreg : IsRegular X) (hdim : topologicalKrullDim X = 2) (G : Over X)
    [GrpObj G] [IsProper G.hom] (f : X.PartialMap G.left) (hf : f.hom ≫ G.hom = f.domain.ι) :
    ∃ g : X ⟶ G.left, g ≫ G.hom = 𝟙 X ∧ f.domain.ι ≫ g = f.hom := by
  let : X.Over X := ⟨𝟙 X⟩
  let : G.left.Over X := ⟨G.hom⟩
  have : IsProper (G.left ↘ X) := ‹IsProper G.hom›
  have : f.IsOver X := Scheme.PartialMap.isOver_iff.mpr
    (by change f.hom ≫ G.hom = f.domain.ι ≫ 𝟙 X; rw [Category.comp_id]; exact hf)
  obtain ⟨Z, p, h, hp, hhS, hagree⟩ := exists_pointBlowupChain_resolving_partialMap_of_dim_two
    (S := X) (fun x => hreg.isRegularLocalRing_stalk x) hdim f
  have hXs : IsIntegralRegularSurface X := ⟨inferInstance, inferInstance, hreg, hdim⟩
  have hhS' : h ≫ G.hom = p := by
    change h ≫ G.hom = p ≫ 𝟙 X at hhS
    rwa [Category.comp_id] at hhS
  obtain ⟨g, hg1, hg2⟩ := exists_comp_eq_of_pointBlowupChain_of_rigid hrigid hXs G hp h hhS'
  refine ⟨g, hg1, ?_⟩
  have : Surjective p := ⟨surjective_of_pointBlowupChain_of_isIntegralRegularSurface hp hXs⟩
  refine ext_of_isDominant_of_isSeparated G.hom (by rw [Category.assoc, hg1, hf, Category.comp_id])
    (pullback.snd p f.domain.ι) ?_
  rw [← pullback.condition_assoc, hg2, hagree]

/-- **A rational section of a proper group scheme over a regular surface extends.** Let `X` be an
integral Noetherian regular scheme of dimension at most two and let `G` be a proper group scheme
over `X`. Granted that morphisms from the projective line over a field to a group scheme over
that field are constant ([Stacks, Tag 0AEN]), every section `σ` of `G` over the generic point of
`X` is the restriction of a section of `G ⟶ X`.

This is the core of the sketch of the proof of [Stacks, Tag 0AF9]: the closure of the generic
section is resolved by blowups at closed points, and the exceptional curves are contracted. -/
theorem exists_section_extending_of_isRegular_of_rigid (hrigid : ProjectiveLineRigidity.{u})
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X ≤ 2) (G : Over X) [GrpObj G] [IsProper G.hom]
    (σ : Spec X.functionField ⟶ G.left) (hσ : σ ≫ G.hom = X.fromSpecStalk (genericPoint X)) :
    ∃ g : X ⟶ G.left, g ≫ G.hom = 𝟙 X ∧ X.fromSpecStalk (genericPoint X) ≫ g = σ := by
  have hσ' : σ ≫ G.hom = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := by rw [hσ, Category.comp_id]
  let f := Scheme.PartialMap.ofFromSpecStalk (𝟙 X) G.hom (x := genericPoint X) σ hσ'
  have hf : f.hom ≫ G.hom = f.domain.ι := by
    simpa using Scheme.PartialMap.ofFromSpecStalk_comp (𝟙 X) G.hom (x := genericPoint X) σ hσ'
  have hη := Scheme.PartialMap.mem_domain_ofFromSpecStalk (𝟙 X) G.hom (x := genericPoint X) σ hσ'
  have hσf : f.domain.fromSpecStalkOfMem _ hη ≫ f.hom = σ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (𝟙 X) G.hom (x := genericPoint X) σ hσ'
  obtain ⟨g, hg1, hg2⟩ : ∃ g : X ⟶ G.left, g ≫ G.hom = 𝟙 X ∧ f.domain.ι ≫ g = f.hom := by
    by_cases h2 : topologicalKrullDim X = 2
    · exact exists_extension_of_eq_two_of_rigid hrigid hreg h2 G f hf
    · exact exists_extension_of_ne_two hreg hdim h2 G f hf
  refine ⟨g, hg1, ?_⟩
  rw [← Scheme.Opens.fromSpecStalkOfMem_ι f.domain _ hη, Category.assoc, hg2, hσf]

/-- Rigidity holds: [Stacks, Tag 0AEN] for schemes,
`AlgebraicGeometry.exists_section_eq_comp_of_projectiveLineProj`. -/
theorem projectiveLineRigidity : ProjectiveLineRigidity.{u} :=
  fun _ _ H _ _ _ f hf => exists_section_eq_comp_of_projectiveLineProj H f hf

/-- **A rational section of a proper group scheme over a regular surface extends.** Let `X` be an
integral Noetherian regular scheme of dimension at most two and let `G` be a proper group scheme
over `X`. Every section `σ` of `G` over the generic point of `X` is the restriction of a section
of `G ⟶ X`.

This is the core of the sketch of the proof of [Stacks, Tag 0AF9]. -/
theorem exists_section_extending_of_isRegular (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 2) (G : Over X) [GrpObj G]
    [IsProper G.hom] (σ : Spec X.functionField ⟶ G.left)
    (hσ : σ ≫ G.hom = X.fromSpecStalk (genericPoint X)) :
    ∃ g : X ⟶ G.left, g ≫ G.hom = 𝟙 X ∧ X.fromSpecStalk (genericPoint X) ≫ g = σ :=
  exists_section_extending_of_isRegular_of_rigid projectiveLineRigidity X hreg hdim G σ hσ

end AlgebraicGeometry.GroupScheme

end
