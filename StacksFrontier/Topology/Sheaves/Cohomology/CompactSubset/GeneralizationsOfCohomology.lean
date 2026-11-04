module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ClosedMapIso
public import StacksFrontier.Topology.Spectral.CompactOpenNeighborhood
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.VanishingFromSurjectiveRestrictions
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.VanishingFromCechAcyclicity

/-!
# Cohomology along the generalizations of a quasi-compact subset of a spectral space

Let `X` be a spectral space, let `F` be a sheaf of abelian groups on `X`, let `E ⊆ X` be
quasi-compact and let `W` be the set of points of `X` which specialize to a point of `E`. Then the
canonical map

`colim_{E ⊆ U quasi-compact open} H^p(U, F) ⟶ H^p(W, F|_W)`

is an isomorphism in every degree. More generally, the comparison map of [Stacks, Tag 09V3] is an
isomorphism in every degree along any subset `K ⊆ X` which is quasi-compact and stable under
generalization.

## Main results

* `Stacks.Topology.exists_ambientSection_eq_of_isStableCompact`: a section of `F|_S` over an open
  of `S` whose image in `X` is quasi-compact and stable under generalization comes from a section
  of `F` on an open neighbourhood of that image.
* `Stacks.Topology.surjective_subsetSectionsMap_of_isStableCompact`: the degree-zero comparison
  `colim_{U ⊇ K open} F(U) ⟶ Γ(K, F|_K)` is surjective.
* `Stacks.Topology.isZero_cohomologyPresheaf_pullback_of_injective_of_isStableCompact`:
  `H^p(K, I|_K) = 0` for `p > 0` and `I` injective.
* `Stacks.Topology.isIso_cohomologyOfClosedMap_of_isStableCompact`: the comparison map of
  [Stacks, Tag 09V3] is an isomorphism in every degree along such a `K`.
* `Stacks.Topology.initial_compactOpenNhdsFunctor`: the quasi-compact open neighbourhoods of a
  quasi-compact `E` are cofinal among the open neighbourhoods of `W`.
* `Stacks.Topology.isIso_cohomologyOfGeneralizationsMap`: the canonical map
  `colim_{E ⊆ U quasi-compact open} H^p(U, F) ⟶ H^p(W, F|_W)` is an isomorphism.

## References

* [Stacks Project, Tag 0A3D](https://stacks.math.columbia.edu/tag/0A3D)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 0A36](https://stacks.math.columbia.edu/tag/0A36)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat Abelian
open Stacks.Cohomology.FreeYoneda

namespace Stacks.Topology

universe v u

noncomputable section

/-! ### The quasi-compact open neighbourhoods of a stable-compact subset -/

namespace StableCompact

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

/-- A quasi-compact subset stable under generalization is the intersection of its quasi-compact
open neighbourhoods. -/
theorem eq_iInter (K : Set X) (hK : SpectralSubset.IsStableCompact K) :
    K = ⋂ U : SpectralSubset.CompactOpenNeighborhood K, (U : Set X) := by
  have hKgen : K = SpectralSubset.generalizationsOf K := by
    ext x
    exact ⟨fun hx ↦ ⟨x, hx, specializes_refl x⟩, fun ⟨_, hy, hxy⟩ ↦ hK.2 hxy hy⟩
  exact hKgen.trans
    (SpectralSubset.generalizationsOf_eq_iInter_compactOpenNeighborhood K hK.1)

/-- Membership in a quasi-compact subset stable under generalization is membership in all of its
quasi-compact open neighbourhoods. -/
theorem mem_iff (K : Set X) (hK : SpectralSubset.IsStableCompact K) (x : X) :
    x ∈ K ↔ ∀ U : SpectralSubset.CompactOpenNeighborhood K, x ∈ (U : Set X) :=
  (Set.ext_iff.1 (eq_iInter K hK) x).trans Set.mem_iInter

/-- The quasi-compact open neighbourhoods of a subset of a spectral space are codirected. -/
theorem directed (K : Set X) :
    Directed (· ⊇ ·) fun U : SpectralSubset.CompactOpenNeighborhood K ↦ (U : Set X) := fun U V ↦
  (directed_of (· ≥ ·) U V).imp fun _ h ↦ ⟨h.1, h.2⟩

/-- Every open subset containing a quasi-compact subset stable under generalization already
contains one of its quasi-compact open neighbourhoods. -/
theorem exists_subset (K : Set X) (hK : SpectralSubset.IsStableCompact K) {A : Set X}
    (hA : IsOpen A) (hKA : K ⊆ A) :
    ∃ U : SpectralSubset.CompactOpenNeighborhood K, (U : Set X) ⊆ A :=
  SpectralSubset.exists_subset_of_subset_isOpen
    (fun U : SpectralSubset.CompactOpenNeighborhood K ↦ (U : Set X))
    (fun U ↦ ⟨U.2.1, U.2.2.1⟩)
    (fun U V ↦ (directed K U V).imp fun _ h ↦ Set.subset_inter h.1 h.2) K
    (eq_iInter K hK) A hA hKA

/-- If an open set contains the part of a quasi-compact subset `K` stable under generalization
lying in two quasi-compact opens `N₁` and `N₂`, then it already contains the part of one
quasi-compact open neighbourhood of `K` lying in `N₁` and `N₂`. -/
theorem exists_inter_subset (K : Set X) (hK : SpectralSubset.IsStableCompact K) {N₁ N₂ : Set X}
    (hN₁ : IsOpen N₁) (hc₁ : IsCompact N₁) (hN₂ : IsOpen N₂) (hc₂ : IsCompact N₂) {A : Set X}
    (hA : IsOpen A) (hKA : K ∩ N₁ ∩ N₂ ⊆ A) :
    ∃ U : SpectralSubset.CompactOpenNeighborhood K, (U : Set X) ∩ N₁ ∩ N₂ ⊆ A := by
  refine SpectralSubset.exists_subset_of_subset_isOpen
    (fun U : SpectralSubset.CompactOpenNeighborhood K ↦ (U : Set X) ∩ N₁ ∩ N₂)
    (fun U ↦ ⟨(U.2.1.inter hN₁).inter hN₂,
      QuasiSeparatedSpace.inter_isCompact _ _ (U.2.1.inter hN₁)
        (QuasiSeparatedSpace.inter_isCompact _ _ U.2.1 U.2.2.1 hN₁ hc₁) hN₂ hc₂⟩)
    (fun U V ↦ (directed K U V).imp fun _ h ↦ fun x hx ↦
      ⟨⟨⟨h.1 hx.1.1, hx.1.2⟩, hx.2⟩, ⟨⟨h.2 hx.1.1, hx.1.2⟩, hx.2⟩⟩)
    _ ?_ A hA hKA
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff]
  refine ⟨fun hx U ↦ ⟨⟨(mem_iff K hK x).1 hx.1.1 U, hx.1.2⟩, hx.2⟩, fun hx ↦ ?_⟩
  exact ⟨⟨(mem_iff K hK x).2 fun U ↦ (hx U).1.1, (hx (Classical.arbitrary _)).1.2⟩,
    (hx (Classical.arbitrary _)).2⟩

end StableCompact

/-! ### Sections along a stable-compact subset -/

section Sections

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X : TopCat.{v}} [SpectralSpace X]

omit [SpectralSpace X] in
/-- The image in `X` of a quasi-compact open of a quasi-compact, generalization-stable subset is
again quasi-compact and stable under generalization. -/
theorem isStableCompact_image_of_isCompact {K : Set X}
    (hK : SpectralSubset.IsStableCompact K) {V : Opens (TopCat.of K)}
    (hV : IsCompact (V : Set (TopCat.of K))) :
    SpectralSubset.IsStableCompact (Subtype.val '' (V : Set (TopCat.of K))) := by
  obtain ⟨Ω, hΩ, hVΩ⟩ := isOpen_induced_iff.1 V.isOpen
  have himg : Subtype.val '' (V : Set (TopCat.of K)) = K ∩ Ω := by
    rw [← hVΩ]
    exact Subtype.image_preimage_coe K Ω
  refine ⟨hV.image continuous_subtype_val, ?_⟩
  rw [himg]
  exact fun x y hxy hy ↦ ⟨hK.2 hxy hy.1, hxy.mem_open hΩ hy.2⟩

/-- Let `X` be a spectral space, `S ⊆ X` a subset and `V` an open of `S` whose image in `X`
is quasi-compact and stable under generalization. Then every section over `V` of the restriction
of a sheaf `F` on `X` to `S` is induced by a section of `F` on an open neighbourhood of that
image. -/
theorem exists_ambientSection_eq_of_isStableCompact (F : X.Sheaf C) (S : Set X)
    {V : Opens (TopCat.of S)}
    (hV : SpectralSubset.IsStableCompact (Subtype.val '' (V : Set (TopCat.of S))))
    (σ : ToType (((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X S)).obj F).presheaf.obj
      (op V))) :
    ∃ (O : Opens X) (h : V ≤ (Opens.map (Stacks.subsetInclusion X S)).obj O)
      (s : ToType (F.presheaf.obj (op O))),
      ambientSection (Stacks.subsetInclusion X S) F h s = σ := by
  classical
  set K : Set X := Subtype.val '' (V : Set (TopCat.of S)) with hKdef
  have hKS : K ⊆ S := by rintro w ⟨z, -, rfl⟩; exact z.2
  have hrep : ∀ z : {z : TopCat.of S // z ∈ V}, ∃ (N : Opens X) (_ : IsCompact (N : Set X))
      (_ : ((z : TopCat.of S) : X) ∈ N)
      (hNV : (Opens.map (Stacks.subsetInclusion X S)).obj N ≤ V)
      (a : ToType (F.presheaf.obj (op N))),
      ∀ (w : X) (hwS : w ∈ S) (hwN : w ∈ N),
        ambientStalkHom (Stacks.subsetInclusion X S) F ⟨w, hwS⟩
            (F.presheaf.germ N w hwN a) =
          ((TopCat.Sheaf.pullback C (Stacks.subsetInclusion X S)).obj F).presheaf.germ V
            ⟨w, hwS⟩ (hNV hwN) σ := by
    intro z
    obtain ⟨N₀, hzN₀, hN₀V, a₀, ha₀⟩ := exists_ambient_repr_of_subset F S σ z.1 z.2
    obtain ⟨P, ⟨hPo, hPc⟩, hzP, hPN⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hzN₀ N₀.isOpen
    have hPN' : (⟨P, hPo⟩ : Opens X) ≤ N₀ := hPN
    refine ⟨⟨P, hPo⟩, hPc, hzP, fun x hx ↦ hN₀V (hPN' hx),
      F.presheaf.map (homOfLE hPN').op a₀, fun w hwS hwP ↦ ?_⟩
    rw [F.presheaf.germ_res_apply (homOfLE hPN') w hwP a₀]
    exact ha₀ w hwS (hPN' hwP)
  choose N hNc hzN hNV a ha using hrep
  have hcov : K ⊆ ⋃ z : {z : TopCat.of S // z ∈ V}, (N z : Set X) := by
    rintro w ⟨z, hzV, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨z, hzV⟩, hzN ⟨z, hzV⟩⟩
  obtain ⟨T, hT⟩ :=
    hV.1.elim_finite_subcover (fun z ↦ (N z : Set X)) (fun z ↦ (N z).isOpen) hcov
  obtain ⟨U₀, hU₀⟩ :=
    StableCompact.exists_subset K hV (isOpen_biUnion fun z _ ↦ (N z).isOpen) hT
  have hpair : ∀ p q : {z : TopCat.of S // z ∈ V},
      ∃ (A : Opens X) (iAp : A ⟶ N p) (iAq : A ⟶ N q),
        K ∩ (N p : Set X) ∩ (N q : Set X) ⊆ (A : Set X) ∧
          F.presheaf.map iAp.op (a p) = F.presheaf.map iAq.op (a q) := by
    intro p q
    obtain ⟨A, hKA, iAp, iAq, hA⟩ :=
      exists_opens_restrict_eq_of_germ_eqOn F (a p) (a q)
        (T := K ∩ (N p : Set X) ∩ (N q : Set X)) (fun _ hx ↦ hx.1.2) (fun _ hx ↦ hx.2)
        (fun w hw ↦ ambientStalkHom_injective (Stacks.subsetInclusion X S) F ⟨w, hKS hw.1.1⟩
          ((ha p w (hKS hw.1.1) hw.1.2).trans (ha q w (hKS hw.1.1) hw.2).symm))
    exact ⟨A, iAp, iAq, hKA, hA⟩
  choose A iAp iAq hKA hA using hpair
  have hstage : ∀ p q : {z : TopCat.of S // z ∈ V},
      ∃ U : SpectralSubset.CompactOpenNeighborhood K,
        (U : Set X) ∩ (N p : Set X) ∩ (N q : Set X) ⊆ (A p q : Set X) := fun p q ↦
    StableCompact.exists_inter_subset K hV (N p).isOpen (hNc p) (N q).isOpen (hNc q)
      (A p q).isOpen (hKA p q)
  choose St hSt using hstage
  obtain ⟨m, hm⟩ := (StableCompact.directed K).finset_le
    (insert U₀ (Finset.image
      (fun pq : {x : {z : TopCat.of S // z ∈ V} // x ∈ T} ×
          {x : {z : TopCat.of S // z ∈ V} // x ∈ T} ↦ St pq.1.1 pq.2.1)
      Finset.univ))
  have hmU₀ : (m : Set X) ⊆ (U₀ : Set X) := hm U₀ (Finset.mem_insert_self _ _)
  have hmSt : ∀ p q : {x : {z : TopCat.of S // z ∈ V} // x ∈ T},
      (m : Set X) ⊆ (St p.1 q.1 : Set X) := fun p q ↦
    hm _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ (p, q))))
  set M : Opens X := ⟨(m : Set X), m.2.1⟩ with hMdef
  set W : {x : {z : TopCat.of S // z ∈ V} // x ∈ T} → Opens X := fun t ↦ M ⊓ N t.1 with hWdef
  set r : ∀ t, ToType (F.presheaf.obj (op (W t))) := fun t ↦
    F.presheaf.map (homOfLE (inf_le_right : M ⊓ N t.1 ≤ N t.1)).op (a t.1) with hrdef
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf W r := by
    intro t t'
    have hD : W t ⊓ W t' ≤ A t.1 t'.1 := fun x hx ↦
      hSt t.1 t'.1 ⟨⟨hmSt t t' hx.1.1, hx.1.2⟩, hx.2.2⟩
    have hres : ∀ {B C D E : Opens X} (f : B ⟶ C) (g : C ⟶ D) (f' : B ⟶ E) (g' : E ⟶ D)
        (x : ToType (F.presheaf.obj (op D))),
        F.presheaf.map f.op (F.presheaf.map g.op x) =
          F.presheaf.map f'.op (F.presheaf.map g'.op x) := fun f g f' g' x ↦
      (map_op_comp_apply F.presheaf f g (f ≫ g) x).trans
        (map_op_comp_apply F.presheaf f' g' (f ≫ g) x).symm
    calc F.presheaf.map (Opens.infLELeft (W t) (W t')).op (r t)
        = F.presheaf.map (homOfLE hD).op (F.presheaf.map (iAp t.1 t'.1).op (a t.1)) := hres ..
      _ = F.presheaf.map (homOfLE hD).op (F.presheaf.map (iAq t.1 t'.1).op (a t'.1)) := by
          rw [hA t.1 t'.1]
      _ = F.presheaf.map (Opens.infLERight (W t) (W t')).op (r t') := hres ..
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing W r hcompat
  have hKW : ∀ w ∈ K, ∃ t, w ∈ W t := by
    intro w hw
    obtain ⟨t, htT, hwt⟩ := Set.mem_iUnion₂.1 (hT hw)
    exact ⟨⟨t, htT⟩, ⟨(StableCompact.mem_iff K hV w).1 hw m, hwt⟩⟩
  have hKO : K ⊆ ((⨆ t, W t : Opens X) : Set X) := fun w hw ↦ Opens.mem_iSup.2 (hKW w hw)
  have hVO : V ≤ (Opens.map (Stacks.subsetInclusion X S)).obj (⨆ t, W t) := fun z hz ↦
    hKO ⟨z, hz, rfl⟩
  refine ⟨⨆ t, W t, hVO, s, ?_⟩
  refine TopCat.Presheaf.section_ext ((TopCat.Sheaf.pullback C
    (Stacks.subsetInclusion X S)).obj F) V _ _ fun z hz ↦ ?_
  obtain ⟨t, hzt⟩ := hKW ((z : X)) ⟨z, hz, rfl⟩
  have hgerm : F.presheaf.germ (⨆ t, W t) (Stacks.subsetInclusion X S z) (hVO hz) s =
      F.presheaf.germ (N t.1) (Stacks.subsetInclusion X S z) hzt.2 (a t.1) := by
    rw [← F.presheaf.germ_res_apply (Opens.leSupr W t)
      (Stacks.subsetInclusion X S z) hzt s, hs t]
    exact F.presheaf.germ_res_apply (homOfLE (inf_le_right : M ⊓ N t.1 ≤ N t.1))
      (Stacks.subsetInclusion X S z) hzt (a t.1)
  exact (germ_ambientSection (Stacks.subsetInclusion X S) F hVO z hz s).trans
    ((congrArg (ambientStalkHom (Stacks.subsetInclusion X S) F z) hgerm).trans
      (ha t.1 ((z : X)) z.2 hzt.2))

/-- Along a quasi-compact subset `K` stable under generalization, every global section of the
restriction of `F` to `K` comes from a section of `F` on an open neighbourhood of `K`. -/
theorem surjective_subsetSectionsMap_of_isStableCompact (F : X.Sheaf C) {K : Set X}
    (hK : SpectralSubset.IsStableCompact K) :
    Function.Surjective (subsetSectionsMap F K) := by
  intro σ
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK.1
  have htop := isStableCompact_image_of_isCompact hK (V := ⊤)
    (by rw [Opens.coe_top]; exact isCompact_univ)
  obtain ⟨O, h, s, hs⟩ := exists_ambientSection_eq_of_isStableCompact F K htop σ
  have hKO : K ⊆ (O : Set X) := fun w hw ↦ h (show (⟨w, hw⟩ : TopCat.of K) ∈ ⊤ from trivial)
  exact ⟨colimit.ι (neighborhoodSections F K) (op (⟨O, hKO⟩ : OpenNhdsSet K)) s,
    (subsetSectionsMap_ι F K (op (⟨O, hKO⟩ : OpenNhdsSet K)) s).trans hs⟩

end Sections

/-! ### Vanishing of the higher cohomology of the restriction of an injective sheaf -/

section Vanishing

variable {X : TopCat.{u}} [SpectralSpace X]

/-- The restriction of a flasque abelian sheaf to a quasi-compact, generalization-stable subset of
a spectral space has surjective restriction maps between quasi-compact opens. -/
theorem surjective_restriction_pullback_of_isFlasque (I : X.Sheaf AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque I] {K : Set X} (hK : SpectralSubset.IsStableCompact K)
    {V V₀ : Opens (TopCat.of K)} (hVV₀ : V ≤ V₀)
    (hV : IsCompact (V : Set (TopCat.of K))) :
    Function.Surjective (((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X K)).obj I).presheaf.map (homOfLE hVV₀).op) := by
  intro σ
  obtain ⟨O, hO, s, hs⟩ :=
    exists_ambientSection_eq_of_isStableCompact I K (isStableCompact_image_of_isCompact hK hV) σ
  obtain ⟨s', hs'⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (TopCat.Presheaf.IsFlasque.epi (F := I.presheaf) (homOfLE (le_top : O ≤ ⊤)).op) s
  have htop : V₀ ≤ (Opens.map (Stacks.subsetInclusion X K)).obj ⊤ := fun _ _ ↦ trivial
  refine ⟨ambientSection (Stacks.subsetInclusion X K) I htop s', ?_⟩
  refine TopCat.Presheaf.section_ext ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
    (Stacks.subsetInclusion X K)).obj I) V _ _ fun z hz ↦ ?_
  have h1 := ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X K)).obj I).presheaf.germ_res_apply (homOfLE hVV₀) z hz
      (ambientSection (Stacks.subsetInclusion X K) I htop s')
  have h2 := germ_ambientSection (Stacks.subsetInclusion X K) I htop z (hVV₀ hz) s'
  have h3 := germ_ambientSection (Stacks.subsetInclusion X K) I hO z hz s
  have key : I.presheaf.germ O (Stacks.subsetInclusion X K z) (hO hz) s =
      I.presheaf.germ (⊤ : Opens X) (Stacks.subsetInclusion X K z) trivial s' := by
    rw [← hs']
    exact I.presheaf.germ_res_apply (homOfLE (le_top : O ≤ ⊤)) _ (hO hz) s'
  rw [h1, h2, ← hs, h3]
  exact congrArg (ambientStalkHom (Stacks.subsetInclusion X K) I z) key.symm

/-- The positive-degree cohomology of the restriction of a flasque abelian sheaf to a
quasi-compact, generalization-stable subset of a spectral space vanishes. -/
theorem isZero_cohomologyPresheaf_pullback_of_isFlasque_of_isStableCompact
    (I : X.Sheaf AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque I] {K : Set X} (hK : SpectralSubset.IsStableCompact K)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of K)) AddCommGrpCat.{u})]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X K)).obj I).cohomologyPresheaf p).obj (op ⊤)) := by
  classical
  have hspec : SpectralSpace (TopCat.of K) := SpectralSubset.spectralSpace_of_isStableCompact K hK
  have hInter : QuasiSeparatedSpace (TopCat.of K : Type u) := inferInstance
  refine Stacks.Cohomology.AbelianBasis.isZero_H'_of_cechAcyclic inferInstance hInter _
    ?_ ⊤ (by rw [Opens.coe_top]; exact isCompact_univ) p hp
  intro Wc hWc n hn
  refine Stacks.Cohomology.RaviCech.isZero_cechCohomology_of_surjective_restrictions Wc.obj _
    Wc.carrier Wc.iSup_eq.symm ?_ n hn
  rintro V hVU ⟨S, hS, rfl⟩
  have hιfin : Finite Wc.ι := hWc.1
  have : Fintype Wc.ι := Fintype.ofFinite Wc.ι
  have : Finite (Finset Wc.ι) := inferInstance
  have hSfin : Finite (S : Type u) := Subtype.finite
  refine surjective_restriction_pullback_of_isFlasque I hK hVU ?_
  rw [Opens.coe_iSup]
  refine isCompact_iUnion fun sq ↦ ?_
  have heq : (⨅ k : ((sq : Finset Wc.ι) : Finset Wc.ι), Wc.obj k) =
      (sq : Finset Wc.ι).inf Wc.obj :=
    (Stacks.Cohomology.RaviCech.interF_eq_biInf Wc.obj _).trans (Finset.inf_eq_iInf _ _).symm
  rw [heq]
  exact Stacks.Cohomology.Vanishing.isCompact_coe_finsetInf hInter Wc.obj hWc.2.2 (hS _ sq.2)

/-- The positive-degree cohomology of the restriction of an injective abelian sheaf to a
quasi-compact, generalization-stable subset of a spectral space vanishes. -/
theorem isZero_cohomologyPresheaf_pullback_of_injective_of_isStableCompact
    (I : X.Sheaf AddCommGrpCat.{u})
    [Injective I] {K : Set X} (hK : SpectralSubset.IsStableCompact K)
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of K)) AddCommGrpCat.{u})]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (Stacks.subsetInclusion X K)).obj I).cohomologyPresheaf p).obj (op ⊤)) :=
  have : TopCat.Sheaf.IsFlasque I := isFlasque_of_injective I
  isZero_cohomologyPresheaf_pullback_of_isFlasque_of_isStableCompact I hK p hp

end Vanishing

/-! ### The comparison map of Stacks 09V3 along the generalizations of a quasi-compact set -/

section Main

variable {X : TopCat.{u}} [SpectralSpace X] (K : Set X)
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology (TopCat.of K)) AddCommGrpCat.{u})]

/-- Along a quasi-compact subset stable under generalization the comparison map of
[Stacks, Tag 09V3] is an isomorphism in degree zero. -/
theorem isIso_cohomologyOfClosedMap_zero_of_isStableCompact
    (hK : SpectralSubset.IsStableCompact K)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsIso (cohomologyOfClosedMap K F 0) := by
  have hκ : Function.Bijective
      (HasColimit.isoOfNatIso (openNeighborhoodCohomologyZeroIso K F)).hom :=
    ConcreteCategory.bijective_of_isIso _
  have hσ : Function.Bijective (subsetSectionsMap F K) :=
    ⟨injective_subsetSectionsMap F K, surjective_subsetSectionsMap_of_isStableCompact F hK⟩
  have hρ := (extSectionsAddEquiv (⊤ : Opens (TopCat.of K))
    ((restrictionFunctor X K).obj F)).bijective
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun c c' hcc ↦ hκ.1 (hσ.1 ?_), fun t ↦ ?_⟩
  · exact ((extSectionsAddEquiv_cohomologyOfClosedMap_zero K F c).symm.trans
      (congrArg _ hcc)).trans (extSectionsAddEquiv_cohomologyOfClosedMap_zero K F c')
  · obtain ⟨w, hw⟩ := hσ.2 (extSectionsAddEquiv ⊤ ((restrictionFunctor X K).obj F) t)
    obtain ⟨c, hc⟩ := hκ.2 w
    exact ⟨c, hρ.1 ((extSectionsAddEquiv_cohomologyOfClosedMap_zero K F c).trans
      ((congrArg _ hc).trans hw))⟩

omit [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
/-- The positive-degree `Ext`-groups out of the free abelian sheaf on `K` into the restriction of
an injective abelian sheaf vanish, on elements. -/
theorem ext_eq_zero_of_injective_restriction_of_isStableCompact
    (hK : SpectralSubset.IsStableCompact K)
    (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I]
    (p : ℕ) (hp : 0 < p)
    (y : Ext.{u} ((freeYoneda (Opens.grothendieckTopology (TopCat.of K))).obj ⊤)
      ((restrictionFunctor X K).obj I) p) :
    y = 0 :=
  have hinj : Injective (C := TopCat.Sheaf AddCommGrpCat.{u} X) I := ‹Injective I›
  (AddCommGrpCat.subsingleton_of_isZero
    (isZero_cohomologyPresheaf_pullback_of_injective_of_isStableCompact I hK p hp)).elim y 0

variable (hK : SpectralSubset.IsStableCompact K) (p : ℕ)
  (ih : ∀ G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
    Function.Bijective (cohomologyOfClosedMap K G p))
  (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
  (hS : S.ShortExact) (hinj : Injective S.X₂)

include hK ih hS hinj in
/-- Let `K` be a quasi-compact subset stable under generalization and suppose the comparison map
along `K` is bijective in degree `p` for every abelian sheaf. Then for a short exact sequence
`S` with injective middle term, the comparison map of `S.X₁` is surjective in degree `p + 1`. -/
theorem surjective_cohomologyOfClosedMap_succ_of_isStableCompact :
    Function.Surjective (cohomologyOfClosedMap K S.X₁ (p + 1)) := by
  have := hinj
  have hLS : (S.map (restrictionFunctor X K)).ShortExact :=
    hS.map_of_exact (restrictionFunctor X K)
  intro y
  have hy0 : Ext.comp y (Ext.mk₀ (S.map (restrictionFunctor X K)).f) (add_zero (p + 1)) = 0 :=
    ext_eq_zero_of_injective_restriction_of_isStableCompact K hK S.X₂ (p + 1) p.succ_pos _
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁
    ((freeYoneda (Opens.grothendieckTopology (TopCat.of K))).obj ⊤) hLS y hy0 rfl
  obtain ⟨c, hc⟩ := (ih S.X₃).2 x₃
  obtain ⟨U, xU, rfl⟩ := exists_colimit_ι_ext K S.X₃ p c
  refine ⟨colimit.ι (openNeighborhoodCohomology K S.X₁ (p + 1)) U
    (Ext.comp xU hS.extClass rfl), ?_⟩
  refine (cohomologyOfClosedMap_ι_comp K hS.extClass p (p + 1) rfl U xU).trans ?_
  rw [hc, Ext.mapExactFunctor_extClass]
  exact hx₃

/-- The comparison map of [Stacks, Tag 09V3] is bijective in every degree along a quasi-compact
subset stable under generalization. -/
theorem bijective_cohomologyOfClosedMap_of_isStableCompact
    (hK : SpectralSubset.IsStableCompact K) (p : ℕ) :
    ∀ F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      Function.Bijective (cohomologyOfClosedMap K F p) := by
  induction p with
  | zero =>
    intro F
    have := isIso_cohomologyOfClosedMap_zero_of_isStableCompact K hK F
    exact ConcreteCategory.bijective_of_isIso _
  | succ p ih =>
    intro F
    obtain ⟨S, hS, hinjF, rfl⟩ :
        ∃ (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
          (_ : S.ShortExact) (_ : Injective S.X₂), S.X₁ = F :=
      ⟨ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F)),
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F)) },
        Injective.injective_under F, rfl⟩
    exact ⟨injective_cohomologyOfClosedMap_succ K p ih S hS hinjF,
      surjective_cohomologyOfClosedMap_succ_of_isStableCompact K hK p ih S hS hinjF⟩

/-- The comparison map of [Stacks, Tag 09V3] is an isomorphism in every degree along a
quasi-compact subset stable under generalization. -/
theorem isIso_cohomologyOfClosedMap_of_isStableCompact
    (hK : SpectralSubset.IsStableCompact K)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (cohomologyOfClosedMap K F p) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (bijective_cohomologyOfClosedMap_of_isStableCompact K hK p F)

end Main

/-! ### Cohomology along the generalizations of a quasi-compact subset -/

section Generalizations

variable {X : TopCat.{u}} [SpectralSpace X]

/-- The set of points specializing to a point of a quasi-compact subset of a spectral space is
quasi-compact and stable under generalization. -/
theorem isStableCompact_generalizationsOf {E : Set X} (hE : IsCompact E) :
    SpectralSubset.IsStableCompact (SpectralSubset.generalizationsOf E) :=
  (SpectralSubset.characterizations_equiv
    (SpectralSubset.generalizationsOf E)).2.1.2 ⟨E, hE, rfl⟩

/-- A quasi-compact open neighbourhood of `E` is an open neighbourhood of the set of points
specializing to a point of `E`, functorially in the inclusion. -/
def compactOpenNhdsFunctor (E : Set X) :
    SpectralSubset.CompactOpenNeighborhood E ⥤
      OpenNhdsSet (SpectralSubset.generalizationsOf E) where
  obj U := ⟨⟨(U : Set X), U.2.1⟩, by
    rintro x ⟨y, hyE, hxy⟩
    exact hxy.mem_open U.2.1 (U.2.2.2 hyE)⟩
  map {U V} f := ObjectProperty.homMk (homOfLE (leOfHom f))
  map_id _ := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)
  map_comp _ _ := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)

/-- An inclusion between two quasi-compact open neighbourhoods of `E` is the same thing as an
inclusion between the corresponding open neighbourhoods of the generalizations of `E`. -/
instance compactOpenNhdsFunctor_full (E : Set X) : (compactOpenNhdsFunctor E).Full where
  map_surjective f :=
    ⟨homOfLE (leOfHom ((openNhdsSetInclusion (SpectralSubset.generalizationsOf E)).map f)),
      ObjectProperty.hom_ext _ (Subsingleton.elim _ _)⟩

/-- The functor `compactOpenNhdsFunctor E` is faithful. -/
instance compactOpenNhdsFunctor_faithful (E : Set X) : (compactOpenNhdsFunctor E).Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The quasi-compact open neighbourhoods of a quasi-compact `E` are cofinal among the open
neighbourhoods of the set of points specializing to `E`. -/
theorem initial_compactOpenNhdsFunctor {E : Set X} (hE : IsCompact E) :
    (compactOpenNhdsFunctor E).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun V ↦ by
    obtain ⟨U, hU⟩ := StableCompact.exists_subset (SpectralSubset.generalizationsOf E)
      (isStableCompact_generalizationsOf hE) V.obj.isOpen V.property
    exact ⟨⟨(U : Set X), U.2.1, U.2.2.1, fun x hx ↦ U.2.2.2 ⟨x, hx, specializes_refl x⟩⟩,
      ⟨ObjectProperty.homMk (homOfLE hU)⟩⟩

variable (E : Set X) [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology
    (TopCat.of (SpectralSubset.generalizationsOf E))) AddCommGrpCat.{u})]

/-- The diagram `U ↦ H^p(U, F)` over the quasi-compact open neighbourhoods of `E`. -/
abbrev compactNeighborhoodCohomology
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    (SpectralSubset.CompactOpenNeighborhood E)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (compactOpenNhdsFunctor E).op ⋙
    openNeighborhoodCohomology (SpectralSubset.generalizationsOf E) F p

/-- The comparison map from the colimit of the cohomology of `F`
over the quasi-compact open neighbourhoods of `E` to the cohomology of the restriction of `F` to
the set of points specializing to a point of `E`. It is the comparison map of
[Stacks, Tag 09V3] precomposed with the passage from the colimit over the quasi-compact open
neighbourhoods of `E` to the colimit over all open neighbourhoods of that set. -/
def cohomologyOfGeneralizationsMap
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    colimit (compactNeighborhoodCohomology E F p) ⟶
      (((restrictionFunctor X (SpectralSubset.generalizationsOf E)).obj
        F).cohomologyPresheaf p).obj (op ⊤) :=
  colimit.pre (openNeighborhoodCohomology (SpectralSubset.generalizationsOf E) F p)
      (compactOpenNhdsFunctor E).op ≫
    cohomologyOfClosedMap (SpectralSubset.generalizationsOf E) F p

/-- Let `X` be a spectral space, let `F` be an abelian sheaf on `X`,
let `E ⊆ X` be quasi-compact and let `W` be the set of points of `X` which specialize to a point
of `E`. Then for every `p` the canonical map

`colim_{E ⊆ U quasi-compact open} H^p(U, F) ⟶ H^p(W, F|_W)`

is an isomorphism. -/
@[stacks 0A3D "cohomology_of_neighbourhoods"]
theorem isIso_cohomologyOfGeneralizationsMap (hE : IsCompact E)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (cohomologyOfGeneralizationsMap E F p) := by
  have : (compactOpenNhdsFunctor E).Initial := initial_compactOpenNhdsFunctor hE
  have := isIso_cohomologyOfClosedMap_of_isStableCompact
    (SpectralSubset.generalizationsOf E) (isStableCompact_generalizationsOf hE) F p
  exact IsIso.comp_isIso

end Generalizations

end

end Stacks.Topology

end
