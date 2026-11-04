module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperBaseChangeClause
import StacksCore.Tactic.StacksAttribute

/-!
# The germ-model sections presheaf is a sheaf for the quasi-compact topology

Let `X'` be an object of the locally quasi-compact site and let `F` be a sheaf of sets on its
space. The germ-model sections presheaf `germSectionsPresheaf S X' F` assigns to an object
`h : W ⟶ X'` the global sections `Γ(W, h^{-1}F)` of the germ-model inverse image, and its
restriction maps are precomposition. It is a sheaf for the *Zariski* topology
(`isSheaf_germSectionsPresheaf`); this file proves that it is a sheaf for the finer
*quasi-compact* topology as well. Consequently the quasi-compact sheafification of
`π_{X'}^{-1}F` is `π_{X'}^{-1}F` itself, which identifies the sections formula with
`ε_{X'}^{-1}π_{X'}^{-1}F`, where `ε_{X'}` compares the two topologies on the slice.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcGermSectionsSheaf`: the germ-model
  sections presheaf, as a sheaf of sets on the localized quasi-compact site.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcInverseImageGermSectionsIso`: the
  quasi-compact sheafification of `π_{X'}^{-1}F` is the germ-model sections presheaf.

## Main results

* `Stacks.Topology.exists_apply_eq_of_isQcCovering`: a quasi-compact covering is jointly
  surjective.
* `Stacks.Topology.mem_nhds_of_isQcCovering`: a subset of a Hausdorff space whose preimage in each
  member of a quasi-compact covering is open is a neighbourhood of each of its points.
* `GermPullback.exists_germSections_of_isQcCovering`: a function to the total space of germs which
  pulls back to a germ-model section on each member of a quasi-compact covering of a Hausdorff
  space is itself a germ-model section.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isSheaf_qc_germSectionsPresheaf`: the
  germ-model sections presheaf is a sheaf for the localized quasi-compact topology.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isIso_toSheafify_comparisonInverseImage`:
  quasi-compact sheafification does not change the comparison inverse image `π_{X'}^{-1}F`.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 09X0](https://stacks.math.columbia.edu/tag/09X0)
* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w t

namespace Stacks.Topology

/-- A quasi-compact covering is jointly surjective. -/
theorem exists_apply_eq_of_isQcCovering {ι : Type*} {X : ι → Type*} {Y : Type*}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y] {f : ∀ i, X i → Y}
    (hcov : _root_.IsQcCovering f) (y : Y) : ∃ (i : ι) (z : X i), f i z = y := by
  obtain ⟨s, E, -, hN⟩ := hcov y
  obtain ⟨i, -, z, -, hz⟩ := Set.mem_iUnion₂.1 (mem_of_mem_nhds hN)
  exact ⟨i, z, hz⟩

/-- Let `f i : X i → Y` be a quasi-compact covering of a Hausdorff space and let `D ⊆ Y` be a
subset whose preimage in each `X i` is open. Then `D` is a neighbourhood of every one of its
points. -/
theorem mem_nhds_of_isQcCovering {ι : Type*} {X : ι → Type*} {Y : Type*}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y] [T2Space Y] {f : ∀ i, X i → Y}
    (hf : ∀ i, Continuous (f i)) (hcov : _root_.IsQcCovering f)
    {D : Set Y} (hD : ∀ i, IsOpen (f i ⁻¹' D)) {y : Y} (hy : y ∈ D) :
    D ∈ nhds y := by
  classical
  obtain ⟨s, E, hE, hN⟩ := hcov y
  set K : Set Y := ⋃ i ∈ s, f i '' (E i \ f i ⁻¹' D) with hK
  have hKclosed : IsClosed K :=
    s.finite_toSet.isClosed_biUnion fun i hi => (((hE i hi).diff (hD i)).image (hf i)).isClosed
  have hyK : y ∉ K := by
    simp only [hK, Set.mem_iUnion, Set.mem_image, Set.mem_sdiff, Set.mem_preimage, not_exists]
    intro i _ z hz
    exact hz.1.2 (hz.2 ▸ hy)
  refine Filter.mem_of_superset
    (Filter.inter_mem hN (hKclosed.isOpen_compl.mem_nhds hyK)) ?_
  rintro z ⟨hzN, hzK⟩
  simp only [Set.mem_iUnion, Set.mem_image] at hzN
  obtain ⟨i, hi, p, hp, rfl⟩ := hzN
  by_contra hn
  refine hzK ?_
  simp only [hK, Set.mem_iUnion, Set.mem_image, Set.mem_sdiff, Set.mem_preimage]
  exact ⟨i, hi, p, ⟨hp, hn⟩, rfl⟩

end Stacks.Topology

namespace GermPullback

/-- Let `q : Y → X` and `e : Z → Y` be continuous and let `q' : Z → X` agree pointwise with
`q ∘ e`. Given a section `t` of `q^{-1}𝒢` over an open `B ⊆ Y` and a section `σ` of `q'^{-1}𝒢`
over all of `Z`, the set of points of `Z` which `e` maps into `B` and at which `σ` and `t` have
the same germ is open. -/
lemma isOpen_germAgree_comap {X Y Z : TopCat.{u}} {𝒢 : X.Presheaf (Type (max u t))}
    {q : Y → X} {e : Z → Y} {q' : Z → X}
    (he : Continuous e) (hq' : Continuous q') (hcomp : ∀ z, q' z = q (e z))
    {B : Opens Y} (t : (sheaf q 𝒢).presheaf.obj (op B))
    (σ : (sheaf q' 𝒢).presheaf.obj (op ⊤)) :
    IsOpen {z : Z | ∃ hz : e z ∈ B, σ.1 ⟨z, trivial⟩ = t.1 ⟨e z, hz⟩} :=
  isOpen_agreeSet hq'
    ((sheaf q' 𝒢).presheaf.map
      (homOfLE le_top : (⟨e ⁻¹' (B : Set Y), B.isOpen.preimage he⟩ : Opens Z) ⟶ ⊤).op σ)
    (comap he hcomp (fun z => z.2) t)

/-- Let `q : Y → X` be a continuous map with `Y` Hausdorff, let `e i : Z i → Y` be a
quasi-compact covering by continuous maps, and let `q' i : Z i → X` agree pointwise with
`q ∘ e i`. If a function `ρ : Y → Germs 𝒢` pulls back along each `e i` to a section `σ i` of
`q' i ^{-1}𝒢` over all of `Z i`, then `ρ` is itself a section of `q^{-1}𝒢` over all of `Y`. -/
lemma exists_germSections_of_isQcCovering {X Y : TopCat.{u}} {𝒢 : X.Presheaf (Type (max u t))}
    [T2Space Y] {q : Y → X} (hq : Continuous q)
    {ι : Type*} {Z : ι → TopCat.{u}} {e : ∀ i, Z i → Y} {q' : ∀ i, Z i → X}
    (he : ∀ i, Continuous (e i)) (hq' : ∀ i, Continuous (q' i))
    (hcomp : ∀ (i : ι) (z : Z i), q' i z = q (e i z))
    (hcov : _root_.IsQcCovering e) (ρ : Y → Germs 𝒢)
    (σ : ∀ i, (sheaf (q' i) 𝒢).presheaf.obj (op ⊤))
    (hσ : ∀ (i : ι) (z : Z i), (σ i).1 ⟨z, trivial⟩ = ρ (e i z)) :
    ∃ τ : (sheaf q 𝒢).presheaf.obj (op ⊤), ∀ y : Y, τ.1 ⟨y, trivial⟩ = ρ y := by
  classical
  refine ⟨⟨fun y => ρ y.1, fun y₀ => ?_⟩, fun _ => rfl⟩
  obtain ⟨i₀, z₀, hz₀⟩ := Stacks.Topology.exists_apply_eq_of_isQcCovering hcov y₀.1
  obtain ⟨A₀, hA₀, incl, V₀, hV₀, s₀, hs₀⟩ :=
    exists_repr (σ i₀) (show z₀ ∈ (⊤ : Opens (Z i₀)) from trivial)
  have hy₀V : q y₀.1 ∈ V₀ := by
    have h := hV₀ ⟨z₀, hA₀⟩
    rwa [hcomp i₀ z₀, hz₀] at h
  set B : Opens Y := ⟨q ⁻¹' (V₀ : Set X), V₀.isOpen.preimage hq⟩ with hB
  have hy₀B : y₀.1 ∈ B := hy₀V
  set t : (sheaf q 𝒢).presheaf.obj (op B) := ofSection (fun z => z.2) s₀ with ht
  have hy₀ : ρ y₀.1 = t.1 ⟨y₀.1, hy₀B⟩ :=
    (congrArg ρ hz₀.symm).trans
      ((((hσ i₀ z₀).symm.trans
        (congrArg (fun v => (σ i₀).1 v) (Subtype.ext rfl))).trans
          (hs₀ ⟨z₀, hA₀⟩)).trans
        (Germs.mk_eq_mk s₀ ((hcomp i₀ z₀).trans (congrArg q hz₀)) _ _))
  have hDopen : ∀ i, IsOpen (e i ⁻¹' {y : Y | ∃ hy : y ∈ B, ρ y = t.1 ⟨y, hy⟩}) := by
    intro i
    have hset : e i ⁻¹' {y : Y | ∃ hy : y ∈ B, ρ y = t.1 ⟨y, hy⟩} =
        {z : Z i | ∃ hz : e i z ∈ B, (σ i).1 ⟨z, trivial⟩ = t.1 ⟨e i z, hz⟩} :=
      Set.ext fun z => ⟨fun ⟨hz, hh⟩ => ⟨hz, (hσ i z).trans hh⟩,
        fun ⟨hz, hh⟩ => ⟨hz, (hσ i z).symm.trans hh⟩⟩
    rw [hset]
    exact isOpen_germAgree_comap (he i) (hq' i) (hcomp i) t (σ i)
  obtain ⟨A, hAD, hAopen, hy₀A⟩ := mem_nhds_iff.mp
    (Stacks.Topology.mem_nhds_of_isQcCovering he hcov hDopen ⟨hy₀B, hy₀⟩)
  exact ⟨⟨A, hAopen⟩, hy₀A, homOfLE le_top, V₀,
    fun z => (hAD z.2).elim fun hb _ => hb, s₀,
    fun z => (hAD z.2).elim fun _ hh => hh⟩

end GermPullback

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

attribute [local instance] boundedSiteInclusionCreatesPullbacks

/-- The map of underlying spaces induced by a morphism of the site is that morphism read as a
function. -/
lemma siteToTop_map_apply (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    {A B : S.category} (k : A ⟶ B) (z : (siteToTop S).obj A) :
    ((siteToTop S).map k) z = (k : A.obj → B.obj) z := rfl

/-- If `k₁ : W₁ ⟶ W` and `k₂ : W₂ ⟶ W` belong to a sieve on `W` and points `z₁` of `W₁` and
`z₂` of `W₂` have the same image in `W`, then the two corresponding members of a compatible
family of germ-model sections have the same germ at `z₁` and at `z₂`. -/
lemma germSections_eq_of_map_eq
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t)))
    {W : Over X'} {R : Sieve W}
    {x : Presieve.FamilyOfElements (germSectionsPresheaf S X' F) (R : Presieve W)}
    (hx : x.Compatible)
    {W₁ W₂ : Over X'} (k₁ : W₁ ⟶ W) (k₂ : W₂ ⟶ W) (h₁ : R k₁) (h₂ : R k₂)
    (z₁ : (siteToTop S).obj W₁.left) (z₂ : (siteToTop S).obj W₂.left)
    (hz : ((siteToTop S).map k₁.left) z₁ = ((siteToTop S).map k₂.left) z₂) :
    (x k₁ h₁).1 ⟨z₁, trivial⟩ = (x k₂ h₂).1 ⟨z₂, trivial⟩ := by
  have hz' : (k₁.left : W₁.left.obj → W.left.obj) z₁ =
      (k₂.left : W₂.left.obj → W.left.obj) z₂ := hz
  set p : (pullback k₁.left k₂.left).obj :=
    (zariskiPullbackHomeo S k₂.left k₁.left).symm ⟨(z₁, z₂), hz'⟩ with hp
  have hfst : ((siteToTop S).map (pullback.fst k₁.left k₂.left)) p = z₁ := by
    rw [siteToTop_map_apply, ← zariskiPullbackHomeo_fst S k₂.left k₁.left p, hp,
      Homeomorph.apply_symm_apply]
    rfl
  have hsnd : ((siteToTop S).map (pullback.snd k₁.left k₂.left)) p = z₂ := by
    rw [siteToTop_map_apply, ← zariskiPullbackHomeo_snd S k₂.left k₁.left p, hp,
      Homeomorph.apply_symm_apply]
    rfl
  have hw : pullback.snd k₁.left k₂.left ≫ W₂.hom =
      pullback.fst k₁.left k₂.left ≫ W₁.hom := by
    rw [← Over.w k₂, ← Over.w k₁, ← Category.assoc, ← Category.assoc, pullback.condition]
  have h1 := congrArg (fun σ : (germSectionsPresheaf S X' F).obj
      (op (Over.mk (pullback.fst k₁.left k₂.left ≫ W₁.hom))) => σ.1 ⟨p, trivial⟩)
    (hx (Over.homMk (pullback.fst k₁.left k₂.left) :
        Over.mk (pullback.fst k₁.left k₂.left ≫ W₁.hom) ⟶ W₁)
      (Over.homMk (pullback.snd k₁.left k₂.left) hw :
        Over.mk (pullback.fst k₁.left k₂.left ≫ W₁.hom) ⟶ W₂)
      h₁ h₂ (Over.OverMorphism.ext pullback.condition))
  simp only [germSectionsPresheaf_map_val, unop_op] at h1
  rw [← hfst, ← hsnd]
  exact h1

/-- The presheaf on the localized quasi-compact site `LC_qc/X'` whose sections over
`h : W ⟶ X'` are the global sections of the germ-model inverse image `h^{-1}F` is a sheaf. -/
@[stacks 09X3 "the qc sheaf condition"]
theorem isSheaf_qc_germSectionsPresheaf
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    Presheaf.IsSheaf (S.qcSite.grothendieckTopology.over X')
      (germSectionsPresheaf S X' F) := by
  classical
  rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  intro W R hR x hx
  obtain ⟨R₀, hR₀, hR₀le⟩ := (S.qcSite.grothendieckTopology.mem_over_iff R).mp hR
  let ZZ : R₀.preZeroHypercover.I₀ → S.category := R₀.preZeroHypercover.X
  let gg : ∀ i, ZZ i ⟶ W.left := R₀.preZeroHypercover.f
  let kk : ∀ i, Over.mk (gg i ≫ W.hom) ⟶ W := fun i => Over.homMk (gg i)
  have hmem : ∀ i, R₀ (gg i) := fun i => by
    simpa only [R₀.presieve₀_preZeroHypercover] using R₀.preZeroHypercover.presieve₀_f i
  have hRg : ∀ i, R (kk i) := fun i =>
    (Sieve.overEquiv_iff R (gg i)).mp (hR₀le _ _ (hmem i))
  have hqc : _root_.IsQcCovering (fun i => ⇑((siteToTop S).map (gg i))) :=
    S.qcSite.covering_is_qc R₀ hR₀
  have hc : ∀ {A B : S.category} (f : A ⟶ B), Continuous ⇑((siteToTop S).map f) := fun f =>
    (ConcreteCategory.hom ((siteToTop S).map f)).continuous
  have hcompat : ∀ (i : R₀.preZeroHypercover.I₀) (z : (siteToTop S).obj (ZZ i)),
      ((siteToTop S).map (Over.mk (gg i ≫ W.hom)).hom) z =
        ((siteToTop S).map W.hom) (((siteToTop S).map (gg i)) z) :=
    fun i => siteToTop_hom_apply S (kk i)
  have : T2Space ((siteToTop S).obj W.left) := inferInstanceAs (T2Space W.left.obj)
  choose idx pt hpt using fun y => exists_apply_eq_of_isQcCovering hqc y
  have key : ∀ (W₁ : Over X') (k : W₁ ⟶ W) (hk : R k) (z : (siteToTop S).obj W₁.left),
      (x (kk (idx (((siteToTop S).map k.left) z)))
            (hRg (idx (((siteToTop S).map k.left) z)))).1
          ⟨pt (((siteToTop S).map k.left) z), trivial⟩ =
        (x k hk).1 ⟨z, trivial⟩ := fun W₁ k hk z =>
    germSections_eq_of_map_eq S X' F hx _ k (hRg _) hk _ z
      (hpt (((siteToTop S).map k.left) z))
  obtain ⟨ρ, hρval⟩ := GermPullback.exists_germSections_of_isQcCovering (𝒢 := F.1)
    (hc W.hom) (fun i => hc (gg i)) (fun i => hc (Over.mk (gg i ≫ W.hom)).hom)
    hcompat hqc
    (fun y => (x (kk (idx y)) (hRg (idx y))).1 ⟨pt y, trivial⟩)
    (fun i => x (kk i) (hRg i))
    (fun i z => (key _ (kk i) (hRg i) z).symm)
  have hamalg : x.IsAmalgamation (ρ : (germSectionsPresheaf S X' F).obj (op W)) :=
    fun W'' k hk => GermPullback.ext fun z =>
      (hρval (((siteToTop S).map k.left) z.1)).trans (key W'' k hk z.1)
  refine ⟨ρ, hamalg, fun ρ' hρ' => ?_⟩
  refine GermPullback.ext fun z => ?_
  have hgen : ∀ ρ₀ : (germSectionsPresheaf S X' F).obj (op W),
      (germSectionsPresheaf S X' F).map (kk (idx z.1)).op ρ₀ = x (kk (idx z.1)) (hRg (idx z.1)) →
      ρ₀.1 z = (x (kk (idx z.1)) (hRg (idx z.1))).1 ⟨pt z.1, trivial⟩ := by
    intro ρ₀ h
    refine Eq.trans ?_ (congrArg (fun σ : (germSectionsPresheaf S X' F).obj
      (op (Over.mk (gg (idx z.1) ≫ W.hom))) => σ.1 ⟨pt z.1, trivial⟩) h)
    exact congrArg (fun v => ρ₀.1 v) (Subtype.ext (hpt z.1).symm)
  exact (hgen ρ' (hρ' _ (hRg (idx z.1)))).trans (hgen ρ (hamalg _ (hRg (idx z.1)))).symm

/-- For a sheaf of sets `F` on the space of an object `X'` of the site, the presheaf
`(h : W ⟶ X') ↦ Γ(W, h^{-1}F)` on the localized quasi-compact site `LC_qc/X'`, as a sheaf. -/
def qcGermSectionsSheaf
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    Sheaf (S.qcSite.grothendieckTopology.over X') (Type (max u t)) :=
  ⟨germSectionsPresheaf S X' F, isSheaf_qc_germSectionsPresheaf S X' F⟩

/-- The underlying presheaf of `qcGermSectionsSheaf` is `germSectionsPresheaf`. -/
@[simp]
lemma qcGermSectionsSheaf_obj
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    (qcGermSectionsSheaf S X' F).1 = germSectionsPresheaf S X' F := rfl

/-- Presheaves of types on the localized quasi-compact site can be sheafified, for coefficients in
any universe containing the universe of the spaces. -/
instance hasSheafify_qcTopology_over
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    HasSheafify (S.qcSite.grothendieckTopology.over X) (Type (max u t)) :=
  have := essentiallySmall_over.{u, w, t} S X
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max u t} _ _

/-- The unit of quasi-compact sheafification is an isomorphism on the germ-model sections
presheaf. -/
theorem isIso_toSheafify_germSectionsPresheaf
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    IsIso (toSheafify (S.qcSite.grothendieckTopology.over X')
      (germSectionsPresheaf S X' F)) :=
  CategoryTheory.isIso_toSheafify _ (isSheaf_qc_germSectionsPresheaf S X' F)

/-- The unit of quasi-compact sheafification is an isomorphism on the comparison inverse image
`π_{X'}^{-1}F`: `ε_{X'}^{-1}π_{X'}^{-1}F` is `π_{X'}^{-1}F`. -/
@[stacks 09X3 "the composite inverse image"]
theorem isIso_toSheafify_comparisonInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    IsIso (toSheafify (S.qcSite.grothendieckTopology.over X')
      ((comparisonInverseImage.{u, w, t} S X').obj F).obj) :=
  CategoryTheory.isIso_toSheafify _
    ((Presheaf.isSheaf_of_iso_iff (germSectionsPresheafIso S X' F)).mpr
      (isSheaf_qc_germSectionsPresheaf S X' F))

/-- The quasi-compact sheafification of the comparison inverse image `π_{X'}^{-1}F`, that is
`ε_{X'}^{-1}π_{X'}^{-1}F`, is the germ-model sections presheaf `(h : W ⟶ X') ↦ Γ(W, h^{-1}F)`
on the localized quasi-compact site `LC_qc/X'`. -/
def qcInverseImageGermSectionsIso
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    sheafify (S.qcSite.grothendieckTopology.over X')
        ((comparisonInverseImage.{u, w, t} S X').obj F).obj ≅
      germSectionsPresheaf S X' F :=
  haveI := isIso_toSheafify_comparisonInverseImage S X' F
  (asIso (toSheafify (S.qcSite.grothendieckTopology.over X')
    ((comparisonInverseImage.{u, w, t} S X').obj F).obj)).symm ≪≫
      germSectionsPresheafIso S X' F

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
