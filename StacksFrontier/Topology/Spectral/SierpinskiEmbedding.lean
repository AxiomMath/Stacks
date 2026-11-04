module

public import StacksFrontier.Topology.Spectral.ConstructibleTopology

/-!
# Spectral spaces as constructibly closed subspaces of Sierpinski products

A topological space `X` is spectral if and only if it is homeomorphic to a subset of a product of
copies of the Sierpinski space `Prop` that is closed for the constructible topology of the
product. The constructible topology of such a product is the product of the discrete topologies
on the factors.

## Main definitions

* `Topology.SierpinskiProduct`: the product `I → Prop` of copies of the Sierpinski space.
* `Topology.piDiscreteTopology`: the product of the discrete topologies on the factors of
  `SierpinskiProduct I`.
* `Topology.memCompactOpens`: the map `x ↦ (U ↦ x ∈ U)` from `X` into the Sierpinski product
  indexed by the quasi-compact opens of `X`.

## Main results

* `Topology.constructibleTopology_sierpinskiProduct`: the constructible topology of
  `SierpinskiProduct I` is `piDiscreteTopology I`.
* `Topology.quasiSober_of_finite`: a finite topological space is quasi-sober.
* `Topology.spectralSpace_of_isClosed_withConstructibleTopology`: a constructibly closed subset of
  a Sierpinski product is spectral.
* `Topology.exists_isClosed_withConstructibleTopology_of_spectralSpace`: a spectral space is
  homeomorphic to a constructibly closed subset of a Sierpinski product.
* `Topology.spectralSpace_iff_exists_isClosed_withConstructibleTopology`: the characterization of
  spectral spaces as constructibly closed subspaces of Sierpinski products.
-/

@[expose] public section

universe u

open TopologicalSpace Topology

/-- Spectrality is a homeomorphism invariant. -/
theorem Homeomorph.spectralSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) [SpectralSpace Y] : SpectralSpace X :=
  have : CompactSpace X := e.symm.compactSpace
  e.isOpenEmbedding.spectralSpace

namespace Topology

/-! ### The Sierpinski space -/

/-- An open subset of the Sierpinski space `Prop` which contains `False` is `Set.univ`. -/
theorem eq_univ_of_isOpen_of_false_mem {s : Set Prop} (hs : IsOpen s) (hf : False ∈ s) :
    s = Set.univ := by
  have hgen : GenerateOpen ({{True}} : Set (Set Prop)) s := hs
  induction hgen with
  | basic t ht => rw [Set.mem_singleton_iff] at ht; subst ht; simp at hf
  | univ => rfl
  | inter u v hu hv hiu hiv => rw [hiu hu hf.1, hiv hv hf.2, Set.inter_self]
  | sUnion S hS h =>
    obtain ⟨t, ht, hft⟩ := Set.mem_sUnion.mp hf
    exact Set.eq_univ_of_univ_subset ((h t ht (hS t ht) hft) ▸ Set.subset_sUnion_of_mem ht)

/-- The Sierpinski space is Kolmogorov. -/
instance t0Space_prop : T0Space Prop := by
  rw [t0Space_iff_inseparable]
  intro p q hpq
  have hiff := hpq.mem_open_iff isOpen_singleton_true
  simp only [Set.mem_singleton_iff, eq_iff_iff, iff_true] at hiff
  exact propext hiff

/-- An open subset of the Sierpinski space is closed under implication. -/
private lemma mem_of_imp_of_isOpen {s : Set Prop} (hs : IsOpen s) {p q : Prop} (h : p → q)
    (hp : p ∈ s) : q ∈ s := by
  by_cases hq : p
  · rwa [show q = p from propext ⟨fun _ => hq, h⟩]
  · rw [eq_univ_of_isOpen_of_false_mem hs (eq_false hq ▸ hp)]
    trivial

/-- Hausdorffness is inherited by a topology induced along an injective map. -/
private lemma t2Space_induced {A B : Type*} {t : TopologicalSpace B} {m : A → B}
    (hm : Function.Injective m) (ht : @T2Space B t) : @T2Space A (t.induced m) := by
  let : TopologicalSpace B := t
  let : TopologicalSpace A := t.induced m
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := ht.t2 fun h => hxy (hm h)
  exact ⟨m ⁻¹' u, m ⁻¹' v, isOpen_induced_iff.mpr ⟨u, hu, rfl⟩,
    isOpen_induced_iff.mpr ⟨v, hv, rfl⟩, hxu, hyv, huv.preimage m⟩

/-! ### Products of Sierpinski spaces -/

/-- The product of copies of the Sierpinski space `Prop` indexed by `I`, with the product
topology. -/
abbrev SierpinskiProduct (I : Type u) : Type u := I → Prop

/-- The coordinate set `{f | f i}` cut out by `i` is open. -/
theorem isOpen_setOf_apply {I : Type u} (i : I) : IsOpen {f : SierpinskiProduct I | f i} :=
  continuous_Prop.mp (continuous_apply i)

/-- The coordinate set `{f | f i}` cut out by `i` is quasi-compact. -/
theorem isCompact_setOf_apply {I : Type u} (i : I) : IsCompact {f : SierpinskiProduct I | f i} := by
  classical
  have heq : {f : SierpinskiProduct I | f i} =
      Set.univ.pi (Function.update (fun _ : I => (Set.univ : Set Prop)) i {True}) := by
    ext f
    simp [Set.mem_pi, Function.update_apply]
  rw [heq]
  refine isCompact_univ_pi fun j => ?_
  simp only [Function.update_apply]
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_univ

/-- The coordinate set cut out by `i` is the preimage of `{True}` under the `i`-th projection. -/
theorem preimage_apply_singleton_true {I : Type u} (i : I) :
    (fun f : SierpinskiProduct I => f i) ⁻¹' {True} = {f : SierpinskiProduct I | f i} := by
  ext f; simp

/-- The preimage of `{False}` under the `i`-th projection is the complement of the coordinate set
cut out by `i`. -/
theorem preimage_apply_singleton_false {I : Type u} (i : I) :
    (fun f : SierpinskiProduct I => f i) ⁻¹' {False} = {f : SierpinskiProduct I | f i}ᶜ := by
  ext f; simp

/-- The coordinate set cut out by `i` is open for the constructible topology. -/
theorem isOpen_constructibleTopology_setOf_apply {I : Type u} (i : I) :
    IsOpen[constructibleTopology (SierpinskiProduct I)] {f : SierpinskiProduct I | f i} :=
  (isCompact_setOf_apply i).isOpen_constructibleTopology_of_isOpen (isOpen_setOf_apply i)

/-- The complement of a coordinate set is open for the constructible topology. -/
theorem isOpen_constructibleTopology_compl_setOf_apply {I : Type u} (i : I) :
    IsOpen[constructibleTopology (SierpinskiProduct I)] {f : SierpinskiProduct I | f i}ᶜ :=
  IsCompact.isOpen_constructibleTopology_of_isClosed
    (by rw [compl_compl]; exact isCompact_setOf_apply i) (isOpen_setOf_apply i).isClosed_compl

/-- The product of the discrete topologies on the factors of `SierpinskiProduct I`. -/
abbrev piDiscreteTopology (I : Type u) : TopologicalSpace (SierpinskiProduct I) :=
  @Pi.topologicalSpace I (fun _ => Prop) (fun _ => ⊥)

/-- The product of the discrete topologies refines the product of the Sierpinski topologies. -/
theorem piDiscreteTopology_le (I : Type u) :
    piDiscreteTopology I ≤ (inferInstance : TopologicalSpace (SierpinskiProduct I)) := by
  unfold piDiscreteTopology Pi.topologicalSpace
  exact iInf_mono fun _ => induced_mono bot_le

/-- Every preimage of a coordinate projection is open for the product of the discrete
topologies. -/
theorem isOpen_piDiscreteTopology_preimage {I : Type u} (i : I) (s : Set Prop) :
    IsOpen[piDiscreteTopology I] ((fun f : SierpinskiProduct I => f i) ⁻¹' s) :=
  @IsOpen.preimage (SierpinskiProduct I) Prop (piDiscreteTopology I) ⊥ (fun f => f i)
    (@continuous_apply I (fun _ => Prop) (fun _ => ⊥) i) s trivial

/-- A box with finite support is closed for the product of the discrete topologies. -/
theorem isClosed_piDiscreteTopology_pi {I : Type u} (J : Finset I) (v : I → Set Prop) :
    IsClosed[piDiscreteTopology I] ((J : Set I).pi v) := by
  rw [← @isOpen_compl_iff (SierpinskiProduct I) _ (piDiscreteTopology I),
    show ((J : Set I).pi v)ᶜ =
      ⋃ i ∈ (J : Set I), (fun f : SierpinskiProduct I => f i) ⁻¹' (v i)ᶜ from by
        ext f; simp [Set.mem_pi, Set.mem_compl_iff]]
  exact @isOpen_biUnion _ _ (piDiscreteTopology I) _ _ fun i _ =>
    isOpen_piDiscreteTopology_preimage i (v i)ᶜ

/-- The product of the discrete topologies on `SierpinskiProduct I` is quasi-compact. -/
theorem compactSpace_piDiscreteTopology (I : Type u) :
    @CompactSpace (SierpinskiProduct I) (piDiscreteTopology I) :=
  @Pi.compactSpace I (fun _ => Prop) (fun _ => ⊥) fun _ => @Finite.compactSpace _ ⊥ inferInstance

/-- The product of the discrete topologies on `SierpinskiProduct I` is Hausdorff. -/
theorem t2Space_piDiscreteTopology (I : Type u) :
    @T2Space (SierpinskiProduct I) (piDiscreteTopology I) :=
  @Pi.t2Space I (fun _ => Prop) (fun _ => ⊥) fun _ =>
    @DiscreteTopology.toT2Space Prop ⊥ (@DiscreteTopology.mk Prop ⊥ rfl)

/-- A set closed for the product of the discrete topologies is quasi-compact for the product
topology. -/
theorem isCompact_of_isClosed_piDiscreteTopology {I : Type u} {A : Set (SierpinskiProduct I)}
    (hA : IsClosed[piDiscreteTopology I] A) : IsCompact A :=
  isCompact_of_le_of_isCompact (piDiscreteTopology_le I)
    (@IsClosed.isCompact _ (piDiscreteTopology I) _ (compactSpace_piDiscreteTopology I) hA)

/-! ### The constructible topology of a Sierpinski product -/

/-- A map to `Prop` whose fibres over `True` and `False` are open is continuous into the discrete
topology. -/
private lemma isOpen_preimage_of_isOpen_of_isOpen_compl {X : Type*} {t : TopologicalSpace X}
    {φ : X → Prop} (h : IsOpen[t] {x | φ x}) (hc : IsOpen[t] {x | φ x}ᶜ) (s : Set Prop) :
    IsOpen[t] (φ ⁻¹' s) := by
  rw [show φ ⁻¹' s = ⋃ p ∈ s, φ ⁻¹' {p} from by ext x; simp]
  refine @isOpen_biUnion _ _ t _ _ fun p _ => ?_
  rcases Classical.propComplete p with rfl | rfl
  · convert h using 1
    ext; simp
  · convert hc using 1
    ext; simp

private lemma constructibleTopology_le_piDiscreteTopology (I : Type u) :
    constructibleTopology (SierpinskiProduct I) ≤ piDiscreteTopology I := by
  apply le_iInf
  intro i s hs
  obtain ⟨U, -, rfl⟩ := hs
  exact isOpen_preimage_of_isOpen_of_isOpen_compl (isOpen_constructibleTopology_setOf_apply i)
    (isOpen_constructibleTopology_compl_setOf_apply i) U

private lemma piDiscreteTopology_le_constructibleTopology (I : Type u) :
    piDiscreteTopology I ≤ constructibleTopology (SierpinskiProduct I) := by
  classical
  refine le_generateFrom fun s hs => ?_
  rcases hs with ⟨hs_open, -⟩ | ⟨hs_closed, hs_compl⟩
  · exact piDiscreteTopology_le I s hs_open
  rw [@isOpen_pi_iff I (fun _ => Prop) (fun _ => ⊥)]
  intro f hf
  have hsc_cover := isOpen_pi_iff.mp hs_closed.isOpen_compl
  have hJ : ∀ g : (sᶜ : Set (SierpinskiProduct I)), ∃ (J : Finset I) (v : I → Set Prop),
      (∀ a ∈ J, IsOpen (v a) ∧ g.1 a ∈ v a) ∧ (J : Set I).pi v ⊆ sᶜ :=
    fun ⟨g, hg⟩ => hsc_cover g hg
  choose J v hv using hJ
  have hc_open : ∀ g : (sᶜ : Set (SierpinskiProduct I)), IsOpen ((J g : Set I).pi (v g)) :=
    fun g => isOpen_set_pi (Finset.finite_toSet _) fun a ha => ((hv g).1 a ha).1
  have hc_cover : sᶜ ⊆ ⋃ g : (sᶜ : Set (SierpinskiProduct I)), (J g : Set I).pi (v g) := fun g hg =>
    Set.mem_iUnion.mpr ⟨⟨g, hg⟩, Set.mem_pi.mpr fun a ha => ((hv ⟨g, hg⟩).1 a ha).2⟩
  obtain ⟨t, ht⟩ := hs_compl.elim_finite_subcover _ hc_open hc_cover
  refine ⟨t.biUnion fun g => J g, fun a => {f a}, fun a _ => ⟨trivial, Set.mem_singleton _⟩, ?_⟩
  intro h hh
  by_contra hhs
  obtain ⟨g, hgt, hh_box⟩ := Set.mem_iUnion₂.mp (ht hhs)
  have hf_not : f ∉ (J g : Set I).pi (v g) := fun hf_in => (hv g).2 hf_in hf
  rw [Set.mem_pi] at hf_not hh_box
  push Not at hf_not
  obtain ⟨a, haJ, hfa⟩ := hf_not
  have ha_mem : a ∈ ((t.biUnion fun g => J g : Finset I) : Set I) := by
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨g, hgt, Finset.mem_coe.mpr haJ⟩
  exact hfa (Set.mem_singleton_iff.mp (Set.mem_pi.mp hh a ha_mem) ▸ hh_box a haJ)

/-- The constructible topology of a product of copies of the Sierpinski space is the product of the
discrete topologies on the factors. -/
theorem constructibleTopology_sierpinskiProduct (I : Type u) :
    constructibleTopology (SierpinskiProduct I) = piDiscreteTopology I :=
  le_antisymm (constructibleTopology_le_piDiscreteTopology I)
    (piDiscreteTopology_le_constructibleTopology I)

/-- A set closed for the constructible topology of a Sierpinski product is closed for the product of
the discrete topologies. -/
private lemma isClosed_piDiscreteTopology_of_isClosed_constructibleTopology {I : Type u}
    {S : Set (SierpinskiProduct I)} (hS : IsClosed[constructibleTopology (SierpinskiProduct I)] S) :
    IsClosed[piDiscreteTopology I] S := by
  rwa [← constructibleTopology_sierpinskiProduct]

/-! ### Finite spaces are quasi-sober -/

/-- A finite topological space is quasi-sober. -/
theorem quasiSober_of_finite (X : Type u) [TopologicalSpace X] [Finite X] :
    QuasiSober X := by
  classical
  refine ⟨fun {Z} hZ hZclosed => ?_⟩
  let t : Finset (Set X) := (Set.toFinite Z).toFinset.image (fun x => closure {x})
  obtain ⟨_, ht, hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ t
    (by simp [t])
    (by
      intro x hx
      exact Set.mem_sUnion.mpr ⟨closure {x},
        Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩, subset_closure rfl⟩)
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
  exact ⟨x, Set.Subset.antisymm
    (hZclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr (by simpa using hx))) hsub⟩

/-! ### Quasi-soberness of a Sierpinski product -/

/-- If `g` holds in every coordinate where `f` does, then `g` specializes to `f`. -/
private lemma specializes_of_forall_apply {I : Type u} {f g : SierpinskiProduct I}
    (hfg : ∀ i, f i → g i) : g ⤳ f := by
  rw [specializes_iff_forall_open]
  intro V hV hfV
  rw [isOpen_pi_iff] at hV
  obtain ⟨J, s, hs, hJs⟩ := hV f hfV
  exact hJs fun j hj => mem_of_imp_of_isOpen (hs j hj).1 (hfg j) (hs j hj).2

/-- A Sierpinski product is quasi-sober. -/
instance quasiSober_sierpinskiProduct (I : Type u) : QuasiSober (SierpinskiProduct I) := by
  classical
  refine QuasiSober.mk fun {S} hS hSc => ?_
  obtain ⟨g, hgS⟩ : ∃ g : SierpinskiProduct I, ∀ i, (g i ↔ ∃ f ∈ S, f i) :=
    ⟨fun i => ∃ f ∈ S, f i, fun _ => Iff.rfl⟩
  refine ⟨g, Set.Subset.antisymm ?_ ?_⟩
  · refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hSc
    by_contra hgnot
    obtain ⟨J, s, hs, hJs⟩ := isOpen_pi_iff.mp hSc.isOpen_compl g hgnot
    have hS_union : S ⊆ ⋃ j ∈ (J : Set I), (fun f : SierpinskiProduct I => f j) ⁻¹' (s j)ᶜ := by
      intro f hf
      have hfnot : f ∉ (J : Set I).pi s := fun h => (hJs h) hf
      rw [Set.mem_pi] at hfnot
      push Not at hfnot
      obtain ⟨j, hj, hfj⟩ := hfnot
      exact Set.mem_biUnion hj hfj
    have hclosed : ∀ j ∈ (J : Set I), IsClosed ((fun f : SierpinskiProduct I => f j) ⁻¹' (s j)ᶜ) :=
      fun j hj => ((continuous_apply j).isOpen_preimage _ (hs j hj).1).isClosed_compl
    obtain ⟨j, hj, hSj⟩ :
        ∃ j ∈ (J : Set I), S ⊆ (fun f : SierpinskiProduct I => f j) ⁻¹' (s j)ᶜ := by
      obtain ⟨z, hz, hsz⟩ := isIrreducible_iff_sUnion_isClosed.mp hS
        (J.image fun j => (fun f : SierpinskiProduct I => f j) ⁻¹' (s j)ᶜ)
        (by simpa using hclosed) (by simpa [Set.sUnion_image] using hS_union)
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨j, hj, hsz⟩
    have hgj_mem : g j ∈ s j := (hs j hj).2
    by_cases hgj : g j
    · obtain ⟨f₀, hf₀S, hf₀j⟩ := (hgS j).mp hgj
      exact hSj hf₀S (show f₀ j ∈ s j from
        (propext ⟨fun _ => hgj, fun _ => hf₀j⟩ : f₀ j = g j) ▸ hgj_mem)
    · have hsj_univ : s j = Set.univ := eq_univ_of_isOpen_of_false_mem (hs j hj).1
        (by rw [show False = g j from (eq_false hgj).symm]; exact hgj_mem)
      have hempty : (fun f : SierpinskiProduct I => f j) ⁻¹' (s j)ᶜ = ∅ := by simp [hsj_univ]
      exact absurd (hempty ▸ hSj hS.nonempty.some_mem) (Set.notMem_empty _)
  · exact fun f hf =>
      (specializes_of_forall_apply fun i hfi => (hgS i).mpr ⟨f, hf, hfi⟩).mem_closure

/-! ### Constructibly closed subspaces of a Sierpinski product are spectral -/

/-- The topology induced on a subset of a Sierpinski product by the product of the discrete
topologies on the factors. -/
abbrev subtypeDiscreteTopology {I : Type u} (S : Set (SierpinskiProduct I)) :
    TopologicalSpace S :=
  (piDiscreteTopology I).induced (↑·)

/-- The induced discrete topology on a subset refines its subspace topology. -/
theorem subtypeDiscreteTopology_le {I : Type u} (S : Set (SierpinskiProduct I)) :
    subtypeDiscreteTopology S ≤ instTopologicalSpaceSubtype :=
  induced_mono (piDiscreteTopology_le I)

/-- A subset closed for the discrete product topology is quasi-compact for the induced discrete
topology. -/
theorem compactSpace_subtypeDiscreteTopology {I : Type u} {S : Set (SierpinskiProduct I)}
    (hS : IsClosed[piDiscreteTopology I] S) : @CompactSpace S (subtypeDiscreteTopology S) :=
  (@isCompact_iff_compactSpace (SierpinskiProduct I) (piDiscreteTopology I) S).mp
    (@IsClosed.isCompact _ (piDiscreteTopology I) _ (compactSpace_piDiscreteTopology I) hS)

/-- The induced discrete topology on a subset of a Sierpinski product is Hausdorff. -/
theorem t2Space_subtypeDiscreteTopology {I : Type u} (S : Set (SierpinskiProduct I)) :
    @T2Space S (subtypeDiscreteTopology S) :=
  t2Space_induced Subtype.val_injective (t2Space_piDiscreteTopology I)

/-- A quasi-compact open subset of a subspace of a Sierpinski product is quasi-compact for the
induced discrete topology. -/
private lemma isCompact_subtypeDiscreteTopology_of_isOpen {I : Type u}
    {S : Set (SierpinskiProduct I)} (hS : IsClosed[piDiscreteTopology I] S) {A : Set S}
    (hAo : IsOpen A) (hAc : IsCompact A) : @IsCompact S (subtypeDiscreteTopology S) A := by
  classical
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp hAo
  have hpt : ∀ x : A, ∃ (J : Finset I) (v : I → Set Prop), (∀ i ∈ J, IsOpen (v i)) ∧
      (x.1 : SierpinskiProduct I) ∈ (J : Set I).pi v ∧ (J : Set I).pi v ⊆ W := by
    intro x
    have hxW : (x.1 : SierpinskiProduct I) ∈ W := by
      have hx : x.1 ∈ Subtype.val ⁻¹' W := hWeq ▸ x.2
      exact hx
    obtain ⟨J, v, hv, hJv⟩ := isOpen_pi_iff.mp hWo _ hxW
    exact ⟨J, v, fun i hi => (hv i hi).1, Set.mem_pi.mpr fun i hi => (hv i hi).2, hJv⟩
  choose J v hvo hvmem hvsub using hpt
  set B : A → Set S := fun x => Subtype.val ⁻¹' ((J x : Set I).pi (v x)) with hB
  have hBo : ∀ x : A, IsOpen (B x) := fun x =>
    (isOpen_set_pi (Finset.finite_toSet _) fun i hi =>
      hvo x i (Finset.mem_coe.mp hi)).preimage continuous_subtype_val
  have hBcover : A ⊆ ⋃ x : A, B x := fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hvmem ⟨y, hy⟩⟩
  have hBsub : ∀ x : A, B x ⊆ A := fun x y hy => by rw [← hWeq]; exact hvsub x hy
  obtain ⟨t, ht⟩ := hAc.elim_finite_subcover B hBo hBcover
  rw [show A = ⋃ x ∈ (t : Set A), B x from
    Set.Subset.antisymm ht (Set.iUnion₂_subset fun x _ => hBsub x)]
  refine @Set.Finite.isCompact_biUnion S A (subtypeDiscreteTopology S) _ B
    (Finset.finite_toSet t) fun x _ => ?_
  refine @IsCompact.of_isClosed_subset S (subtypeDiscreteTopology S) Set.univ (B x)
    (@isCompact_univ S (subtypeDiscreteTopology S) (compactSpace_subtypeDiscreteTopology hS)) ?_
    (Set.subset_univ _)
  exact @IsClosed.preimage S (SierpinskiProduct I) (subtypeDiscreteTopology S)
    (piDiscreteTopology I) (↑·)
    (@continuous_induced_dom S (SierpinskiProduct I) (↑·) (piDiscreteTopology I)) _
    (isClosed_piDiscreteTopology_pi (J x) (v x))

/-- A subspace of a Sierpinski product that is closed for the constructible topology is
quasi-separated. -/
private lemma quasiSeparatedSpace_of_isClosed_constructibleTopology {I : Type u}
    {S : Set (SierpinskiProduct I)}
    (hS : IsClosed[constructibleTopology (SierpinskiProduct I)] S) : QuasiSeparatedSpace S := by
  have hS' := isClosed_piDiscreteTopology_of_isClosed_constructibleTopology hS
  refine ⟨fun U V hUo hUc hVo hVc => ?_⟩
  have hU := isCompact_subtypeDiscreteTopology_of_isOpen hS' hUo hUc
  have hV := isCompact_subtypeDiscreteTopology_of_isOpen hS' hVo hVc
  have hUcl : IsClosed[subtypeDiscreteTopology S] U :=
    @IsCompact.isClosed S (subtypeDiscreteTopology S) (t2Space_subtypeDiscreteTopology S) _ hU
  have hVcl : IsClosed[subtypeDiscreteTopology S] V :=
    @IsCompact.isClosed S (subtypeDiscreteTopology S) (t2Space_subtypeDiscreteTopology S) _ hV
  refine isCompact_of_le_of_isCompact (subtypeDiscreteTopology_le S) ?_
  exact @IsClosed.isCompact S (subtypeDiscreteTopology S) _
    (compactSpace_subtypeDiscreteTopology hS')
    (@IsClosed.inter S U V (subtypeDiscreteTopology S) hUcl hVcl)

/-- A subspace of a Sierpinski product that is closed for the constructible topology is
prespectral. -/
private lemma prespectralSpace_of_isClosed_constructibleTopology {I : Type u}
    {S : Set (SierpinskiProduct I)}
    (hS : IsClosed[constructibleTopology (SierpinskiProduct I)] S) : PrespectralSpace S := by
  classical
  have hS' := isClosed_piDiscreteTopology_of_isClosed_constructibleTopology hS
  refine PrespectralSpace.mk (isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.1) ?_)
  intro a V haV hVo
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp hVo
  have haW : (a : SierpinskiProduct I) ∈ W := by
    have h : a ∈ Subtype.val ⁻¹' W := hWeq ▸ haV
    exact h
  obtain ⟨J, v, hv, hJv⟩ := isOpen_pi_iff.mp hWo (a : SierpinskiProduct I) haW
  set Jt : Finset I := J.filter fun i => a.val i with hJt
  set B : Set (SierpinskiProduct I) := (Jt : Set I).pi fun _ => ({True} : Set Prop) with hB
  have hBmem : ∀ f : SierpinskiProduct I, f ∈ B ↔ ∀ i ∈ Jt, f i := by
    intro f
    simp [hB]
  have hBo : IsOpen B := isOpen_set_pi (Finset.finite_toSet _) fun _ _ => isOpen_singleton_true
  have hBcl : IsClosed[piDiscreteTopology I] B := isClosed_piDiscreteTopology_pi Jt _
  have haB : (a : SierpinskiProduct I) ∈ B :=
    (hBmem _).mpr fun i hi => (Finset.mem_filter.mp hi).2
  refine ⟨Subtype.val ⁻¹' B, ⟨hBo.preimage continuous_subtype_val, ?_⟩, haB, ?_⟩
  · rw [Subtype.isCompact_iff, show Subtype.val '' (Subtype.val ⁻¹' B) = B ∩ S from by
      ext x
      exact ⟨by rintro ⟨⟨y, hyS⟩, hyB, rfl⟩; exact ⟨hyB, hyS⟩,
        fun ⟨hxB, hxS⟩ => ⟨⟨x, hxS⟩, hxB, rfl⟩⟩]
    exact isCompact_of_isClosed_piDiscreteTopology
      (@IsClosed.inter _ B S (piDiscreteTopology I) hBcl hS')
  · intro x hx
    have hxB : (x : SierpinskiProduct I) ∈ B := hx
    have hxW : (x : SierpinskiProduct I) ∈ W := by
      refine hJv fun i hi => mem_of_imp_of_isOpen (hv i hi).1 (fun hai => ?_) (hv i hi).2
      exact (hBmem _).mp hxB i (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hi, hai⟩)
    have h : x ∈ Subtype.val ⁻¹' W := hxW
    rwa [hWeq] at h

/-- The generic point of the closure of a subset `Z` of a Sierpinski product still lies in any set
`S ⊇ Z` that is closed for the constructible topology. -/
private lemma mem_of_isGenericPoint_closure {I : Type u} {S Z : Set (SierpinskiProduct I)}
    (hS : IsClosed[constructibleTopology (SierpinskiProduct I)] S) (hZS : Z ⊆ S)
    {g : SierpinskiProduct I} (hg : IsGenericPoint g (closure Z)) : g ∈ S := by
  classical
  have hsub : @closure _ (piDiscreteTopology I) Z ⊆ S :=
    @closure_minimal _ (piDiscreteTopology I) Z S hZS
      (isClosed_piDiscreteTopology_of_isClosed_constructibleTopology hS)
  apply hsub
  rw [@mem_closure_iff _ (piDiscreteTopology I)]
  intro U hU hgU
  obtain ⟨J, v, hv, hJv⟩ := (@isOpen_pi_iff I (fun _ => Prop) (fun _ => ⊥) U).mp hU g hgU
  suffices h : ((J : Set I).pi v ∩ Z).Nonempty from
    ⟨h.choose, hJv h.choose_spec.1, h.choose_spec.2⟩
  have hg_mem : g ∈ closure Z := hg.mem
  have hZ_coord : ∀ f ∈ Z, ∀ i : I, f i → g i := by
    intro f hf i hfi
    have hspec : g ⤳ f := specializes_iff_mem_closure.mpr (hg.def ▸ subset_closure hf)
    exact hspec.mem_open (isOpen_setOf_apply i) hfi
  set Jt : Finset I := J.filter fun i => g i with hJt
  have hinter_open : IsOpen (⋂ i ∈ (Jt : Set I), {f : SierpinskiProduct I | f i}) :=
    Set.Finite.isOpen_biInter (Finset.finite_toSet _) fun i _ => isOpen_setOf_apply i
  have hg_inter : g ∈ ⋂ i ∈ (Jt : Set I), {f : SierpinskiProduct I | f i} := by
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact fun i hi => (Finset.mem_filter.mp hi).2
  obtain ⟨f, hf_inter, hf_Z⟩ := mem_closure_iff.mp hg_mem _ hinter_open hg_inter
  refine ⟨f, fun i hi => ?_, hf_Z⟩
  have hfg : f i = g i := by
    by_cases hgi : g i
    · have hfi : f i := by
        simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hf_inter
        exact hf_inter i (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hi, hgi⟩)
      exact propext ⟨fun _ => hgi, fun _ => hfi⟩
    · exact propext ⟨fun h => absurd (hZ_coord f hf_Z i h) hgi, fun h => absurd h hgi⟩
  rw [hfg]
  exact (hv i hi).2

/-- The closure of the generic point of `closure (Subtype.val '' Z')` inside a subspace `S` is `Z'`
itself, when `Z'` is closed in `S`. -/
private lemma closure_singleton_eq_of_isGenericPoint {I : Type u} {S : Set (SierpinskiProduct I)}
    {Z' : Set S} (hZ' : IsClosed Z') {g : SierpinskiProduct I} (hgS : g ∈ S)
    (hg : IsGenericPoint g (closure (Subtype.val '' Z'))) :
    closure {(⟨g, hgS⟩ : S)} = Z' := by
  refine Set.Subset.antisymm (fun x hx => ?_) fun x hx => ?_
  · rw [← hZ'.closure_eq, closure_subtype (s := Z'), ← hg.def]
    have hx' : (x : SierpinskiProduct I) ∈ closure (Subtype.val '' {(⟨g, hgS⟩ : S)}) :=
      closure_subtype.mp hx
    rwa [Set.image_singleton] at hx'
  · rw [closure_subtype (s := {⟨g, hgS⟩}), Set.image_singleton, hg.def]
    exact subset_closure (Set.mem_image_of_mem Subtype.val hx)

/-- A subset of a product of copies of the Sierpinski space that is closed for the constructible
topology of the product is a spectral space. -/
theorem spectralSpace_of_isClosed_withConstructibleTopology (I : Type u)
    (S : Set (SierpinskiProduct I))
    (hS : IsClosed[constructibleTopology (SierpinskiProduct I)] S) :
    SpectralSpace S := by
  have hS'' := isClosed_piDiscreteTopology_of_isClosed_constructibleTopology hS
  have : CompactSpace S := by
    rw [← isCompact_iff_compactSpace]
    exact isCompact_of_isClosed_piDiscreteTopology hS''
  have : T0Space S := Subtype.t0Space
  have : QuasiSober S := by
    refine QuasiSober.mk fun {Z'} hZ'irr hZ'cl => ?_
    have hZS : Subtype.val '' Z' ⊆ S := fun f hf => by
      obtain ⟨x, -, rfl⟩ := hf; exact x.2
    have hZirr : IsIrreducible (Subtype.val '' Z') :=
      hZ'irr.image _ continuous_subtype_val.continuousOn
    obtain ⟨g, hg⟩ := (quasiSober_sierpinskiProduct I).sober hZirr.closure isClosed_closure
    exact ⟨⟨g, mem_of_isGenericPoint_closure hS hZS hg⟩,
      closure_singleton_eq_of_isGenericPoint hZ'cl _ hg⟩
  have := quasiSeparatedSpace_of_isClosed_constructibleTopology hS
  have := prespectralSpace_of_isClosed_constructibleTopology hS
  exact SpectralSpace.mk

/-- A Sierpinski product is a spectral space. -/
instance spectralSpace_sierpinskiProduct (I : Type u) : SpectralSpace (SierpinskiProduct I) :=
  have := spectralSpace_of_isClosed_withConstructibleTopology I Set.univ
    (@isClosed_univ _ (constructibleTopology (SierpinskiProduct I)))
  (Homeomorph.Set.univ (SierpinskiProduct I)).symm.spectralSpace

/-! ### Spectral spaces embed constructibly closed into a Sierpinski product -/

/-- The tautological map from `X` into the product of copies of the Sierpinski space indexed by the
quasi-compact open subsets of `X`: the `U`-th coordinate of the image of `x` is the proposition
`x ∈ U`. -/
def memCompactOpens (X : Type u) [TopologicalSpace X] :
    X → SierpinskiProduct {U : Set X // IsOpen U ∧ IsCompact U} := fun x U => x ∈ U.1

/-- The preimage of the `U`-th coordinate set under `memCompactOpens` is `U` itself. -/
theorem preimage_memCompactOpens_setOf_apply {X : Type u} [TopologicalSpace X]
    (U : {U : Set X // IsOpen U ∧ IsCompact U}) :
    memCompactOpens X ⁻¹' {f | f U} = U.1 := rfl

/-- `memCompactOpens X` is continuous for the constructible topologies. -/
theorem continuous_constructibleTopology_memCompactOpens (X : Type u) [TopologicalSpace X] :
    Continuous[constructibleTopology X,
        constructibleTopology (SierpinskiProduct {U : Set X // IsOpen U ∧ IsCompact U})]
      (memCompactOpens X) := by
  rw [constructibleTopology_sierpinskiProduct]
  refine @continuous_pi X _ (fun _ => Prop) (constructibleTopology X) (fun _ => ⊥) _ fun U => ?_
  rw [@continuous_def X Prop (constructibleTopology X) ⊥]
  exact fun s _ => isOpen_preimage_of_isOpen_of_isOpen_compl
    (U.2.2.isOpen_constructibleTopology_of_isOpen U.2.1)
    (IsCompact.isOpen_constructibleTopology_of_isClosed
      (by rw [compl_compl]; exact U.2.2) U.2.1.isClosed_compl) s

/-- `memCompactOpens X` is a topological embedding when the quasi-compact opens of `X` form a basis
and `X` is Kolmogorov. -/
theorem isEmbedding_memCompactOpens (X : Type u) [TopologicalSpace X] [PrespectralSpace X]
    [T0Space X] : IsEmbedding (memCompactOpens X) := by
  have hbasis := PrespectralSpace.isTopologicalBasis (X := X)
  have hcont : Continuous (memCompactOpens X) :=
    continuous_pi fun U => continuous_Prop.mpr U.2.1
  have hle : TopologicalSpace.induced (memCompactOpens X) inferInstance ≤
      generateFrom {U : Set X | IsOpen U ∧ IsCompact U} := by
    refine le_generateFrom fun W hW => ?_
    obtain ⟨hWo, hWc⟩ := hW
    exact isOpen_induced_iff.mpr ⟨{f | f ⟨W, hWo, hWc⟩}, isOpen_setOf_apply _,
      preimage_memCompactOpens_setOf_apply _⟩
  have hinducing : IsInducing (memCompactOpens X) :=
    ⟨le_antisymm (continuous_iff_le_induced.mp hcont)
      (le_of_le_of_eq hle hbasis.eq_generateFrom.symm)⟩
  refine ⟨hinducing, fun x y hxy => Inseparable.eq ?_⟩
  rw [← hinducing.inseparable_iff, hxy]

/-- A spectral space `X` is homeomorphic to a subset of a product of copies of the Sierpinski space
which is closed for the constructible topology of that product. -/
theorem exists_isClosed_withConstructibleTopology_of_spectralSpace (X : Type u)
    [TopologicalSpace X] [SpectralSpace X] :
    ∃ (I : Type u) (S : Set (SierpinskiProduct I)),
      IsClosed[constructibleTopology (SierpinskiProduct I)] S ∧ Nonempty (X ≃ₜ S) := by
  refine ⟨{U : Set X // IsOpen U ∧ IsCompact U}, Set.range (memCompactOpens X), ?_,
    ⟨(isEmbedding_memCompactOpens X).toHomeomorph⟩⟩
  have hcompact : @IsCompact (SierpinskiProduct {U : Set X // IsOpen U ∧ IsCompact U})
      (constructibleTopology _) (Set.range (memCompactOpens X)) :=
    @isCompact_range X _ (constructibleTopology X) (constructibleTopology _)
      (compactSpace_constructibleTopology X) _ (continuous_constructibleTopology_memCompactOpens X)
  exact @IsCompact.isClosed _ (constructibleTopology _)
    (t2Space_constructibleTopology (SierpinskiProduct {U : Set X // IsOpen U ∧ IsCompact U})) _
    hcompact

/-- A topological space is spectral if and only if it is homeomorphic to a subset of a product of
copies of the Sierpinski space which is closed for the constructible topology of that product. -/
@[stacks 09XW]
theorem spectralSpace_iff_exists_isClosed_withConstructibleTopology (X : Type u)
    [TopologicalSpace X] :
    SpectralSpace X ↔
      ∃ (I : Type u) (S : Set (SierpinskiProduct I)),
        IsClosed[constructibleTopology (SierpinskiProduct I)] S ∧ Nonempty (X ≃ₜ S) := by
  refine ⟨fun _ => exists_isClosed_withConstructibleTopology_of_spectralSpace X, ?_⟩
  rintro ⟨I, S, hS, ⟨e⟩⟩
  have := spectralSpace_of_isClosed_withConstructibleTopology I S hS
  exact e.spectralSpace

end Topology
