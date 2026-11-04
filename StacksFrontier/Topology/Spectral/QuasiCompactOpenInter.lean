module

public import StacksFrontier.Topology.Spectral.ConstructibleTopology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Intersections of quasi-compact opens in a spectral space (Stacks 0A31)

Let `W` be a subset of a spectral space `X`. Stacks 0A31 gives five equivalent descriptions of the
subsets that arise as intersections of quasi-compact opens, here recorded as five predicates in
the `SpectralSubset` namespace:

* `IsStableInterConstructible`: `W` is an intersection of constructible sets
  and is stable under generalization;
* `IsStableCompact`: `W` is quasi-compact and stable under generalization;
* `IsGeneralizationsOfCompact`: `W = generalizationsOf E` for some quasi-compact `E`, where
  `generalizationsOf E = {x | ∃ y ∈ E, x ⤳ y}` is the set of points specializing to `E`;
* `IsInterCompactOpen`: `W` is an intersection of quasi-compact opens;
* `IsDirectedInterCompactOpen`: `W = ⋂ i, U i` for a nonempty family of quasi-compact opens that
  is downward directed under intersection.

The proof runs round the cycle `(4) ⇒ (5) ⇒ (2) ⇒ (3) ⇒ (4)` together with `(4) ⇒ (1) ⇒ (2)`.
Every step where compactness has to be produced out of nothing goes through the constructible
topology, in which a spectral space is quasi-compact Hausdorff and a quasi-compact open becomes
clopen — the "patch topology" of the source. Mathlib's `constructibleTopology` is exactly that
topology, and the facts used are `IsCompact.isClopen_constructibleTopology`,
`IsClosed.isClosed_constructibleTopology`, `IsClosed.isCompact_constructibleTopology` and
`IsClosed.isCompact_of_constructibleTopology`; "constructible" is Mathlib's
`Topology.IsConstructible`, whose generators are the *retrocompact* opens and therefore, on a
quasi-separated space, exactly the quasi-compact opens
(`QuasiSeparatedSpace.isRetrocompact_iff_isCompact`).

Under the equivalent conditions three further conclusions of 0A31 are proved:
`W` is spectral, the canonical map `W → InvLimit U` is a homeomorphism, and every open of `X`
containing `W` already contains some `U i`.

`InvLimit U` is spelled out by hand as the subspace of `∀ i, U i` of families that agree wherever
`U j ⊆ U i`, rather than as a `CategoryTheory.Limits.limit`: the index here is a bare directed
family of subsets of `X` with inclusions as transition maps, not a functor out of a category, and
the explicit description is what the homeomorphism proof manipulates.

The index type in `IsDirectedInterCompactOpen` is quantified in the same universe as `X`, which is
where the witnesses built in the proof (a subtype of `Finset (Set X)`, or `PUnit`) live.
-/

@[expose] public section

universe u

namespace SpectralSubset

variable {X : Type u} [TopologicalSpace X]

/-- The set of points specializing to (some element of) `E`; i.e., the set
of generalizations of points in `E`. Equivalently,
`generalizationsOf E = { x ∈ X | closure {x} ∩ E ≠ ∅ }`. -/
def generalizationsOf (E : Set X) : Set X := { x | ∃ y ∈ E, x ⤳ y }

/-- (1) `W` is an intersection of (spectral-)constructible subsets of `X`
and is closed under generalizations. -/
def IsStableInterConstructible (W : Set X) : Prop :=
  StableUnderGeneralization W ∧
    ∃ (S : Set (Set X)), W = ⋂₀ S ∧ ∀ s ∈ S, Topology.IsConstructible s

/-- (2) `W` is quasi-compact and closed under generalizations. -/
def IsStableCompact (W : Set X) : Prop :=
  IsCompact W ∧ StableUnderGeneralization W

/-- (3) There exists a quasi-compact subset `E ⊆ X` such that
`W = generalizationsOf E`. -/
def IsGeneralizationsOfCompact (W : Set X) : Prop :=
  ∃ E : Set X, IsCompact E ∧ W = generalizationsOf E

/-- (4) `W` is an intersection of quasi-compact open subsets of `X`. -/
def IsInterCompactOpen (W : Set X) : Prop :=
  ∃ (S : Set (Set X)), W = ⋂₀ S ∧ ∀ s ∈ S, IsOpen s ∧ IsCompact s

/-- (5) There exists a nonempty index set `I` and a family of quasi-compact
opens `U_i ⊆ X` (`i ∈ I`) such that `W = ⋂ i, U i` and the family is
"downward directed" via intersection (for all `i, j` there is `k` with
`U_k ⊆ U_i ∩ U_j`). -/
def IsDirectedInterCompactOpen (W : Set X) : Prop :=
  ∃ (I : Type u) (_ : Nonempty I) (U : I → Set X),
    (∀ i, IsOpen (U i) ∧ IsCompact (U i)) ∧
    W = ⋂ i, U i ∧
    (∀ i j, ∃ k, U k ⊆ U i ∩ U j)

/-- The categorical inverse limit (in `Top`) of the cofiltered system of
subsets `(U i)_{i ∈ I}` of `X`, with transition maps the inclusions
`U_j ↪ U_i` (whenever `U_j ⊆ U_i`). Concretely, it is the subspace of the
product `∀ i, U i` consisting of compatible families: `(f j : X) = f i`
whenever `U_j ⊆ U_i`. Carries the subspace topology from the product
topology. -/
def InvLimit {I : Type*} (U : I → Set X) : Type _ :=
  { f : (i : I) → U i // ∀ i j, U j ⊆ U i → ((f j : X)) = f i }

/-- `InvLimit U` carries the subspace topology of the product topology on `∀ i, U i`. -/
instance {I : Type*} (U : I → Set X) : TopologicalSpace (InvLimit U) :=
  inferInstanceAs (TopologicalSpace
    { f : (i : I) → U i // ∀ i j, U j ⊆ U i → ((f j : X)) = f i })

/-- The canonical map `W → InvLimit U` sending `w ∈ W` to the family
`(w)_i` (well-defined since `W ⊆ U_i` for all `i`). -/
def canonicalMap {I : Type*} (U : I → Set X) (W : Set X)
    (hW : W ⊆ ⋂ i, U i) : W → InvLimit U :=
  fun w => ⟨fun i => ⟨(w : X), Set.mem_iInter.mp (hW w.2) i⟩, fun _ _ _ => rfl⟩

/-- (4) ⇒ (5): an arbitrary intersection of quasi-compact opens is also a *directed* one, obtained
by closing the family under finite intersections. Index by the nonempty finite subsets `F ⊆ S` and
take `⋂₀ F`, which is again quasi-compact open because a spectral space is quasi-separated; the
family is downward directed by `F₁ ∪ F₂`. The empty family is handled separately, with `W = univ`
indexed by `PUnit`. -/
lemma isDirectedInterCompactOpen_of_isInterCompactOpen [SpectralSpace X] (W : Set X) :
    IsInterCompactOpen W → IsDirectedInterCompactOpen W := by
  rintro ⟨S, rfl, hS⟩
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨PUnit.{u + 1}, ⟨⟨⟩⟩, fun _ => Set.univ, fun _ => ⟨isOpen_univ, isCompact_univ⟩,
      by simp, fun _ _ => ⟨⟨⟩, by simp⟩⟩
  refine ⟨{ F : Finset (Set X) // F.Nonempty ∧ ↑F ⊆ S },
    ⟨⟨{s₀}, Finset.singleton_nonempty _, by simpa using hs₀⟩⟩,
    fun F => ⋂₀ (↑F.1 : Set (Set X)),
    fun F => ⟨F.1.finite_toSet.isOpen_sInter fun t ht => (hS t (F.2.2 ht)).1,
      QuasiSeparatedSpace.isCompact_sInter F.1.finite_toSet (fun t ht => .inl (hS t (F.2.2 ht)).1)
        fun t ht => (hS t (F.2.2 ht)).2⟩, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iInter, Set.mem_sInter]
    exact ⟨fun hx F t ht => hx t (F.2.2 ht),
      fun hx t ht => hx ⟨{t}, Finset.singleton_nonempty t, by simpa using ht⟩ t (by simp)⟩
  · rintro ⟨F₁, hF₁ne, hF₁S⟩ ⟨F₂, -, hF₂S⟩
    exact ⟨⟨F₁ ∪ F₂, hF₁ne.inl, by rw [Finset.coe_union]; exact Set.union_subset hF₁S hF₂S⟩,
      by simp [Set.sInter_union]⟩

/-- (5) ⇒ (2): a directed intersection of quasi-compact opens is closed in the constructible
topology, each quasi-compact open being constructibly clopen, hence quasi-compact; it is stable
under generalization as an intersection of opens. -/
lemma isStableCompact_of_isDirectedInterCompactOpen [SpectralSpace X] (W : Set X) :
    IsDirectedInterCompactOpen W → IsStableCompact W := by
  rintro ⟨I, -, U, hU, rfl, -⟩
  exact ⟨(@isClosed_iInter X I (constructibleTopology X) U fun i =>
      ((hU i).2.isClopen_constructibleTopology (hU i).1).1).isCompact_of_constructibleTopology,
    stableUnderGeneralization_iInter U fun i => (hU i).1.stableUnderGeneralization⟩

/-- A set stable under generalization is its own set of generalizations. -/
private lemma generalizationsOf_eq_self {W : Set X} (hW_gen : StableUnderGeneralization W) :
    generalizationsOf W = W :=
  Set.ext fun x => ⟨fun ⟨_, hy, hxy⟩ => hW_gen hxy hy, fun hx => ⟨x, hx, specializes_refl x⟩⟩

/-- (2) ⇒ (3): take `E = W`; the set of generalizations of `W` is `W` by stability. -/
lemma isGeneralizationsOfCompact_of_isStableCompact [SpectralSpace X] (W : Set X) :
    IsStableCompact W → IsGeneralizationsOfCompact W :=
  fun ⟨hW_compact, hW_gen⟩ => ⟨W, hW_compact, (generalizationsOf_eq_self hW_gen).symm⟩

/-- The set of generalizations of a quasi-compact `E` is the intersection of all quasi-compact
opens containing `E`. One inclusion is immediate from `Specializes.mem_open`. For the other, if `x`
is not a generalization of any point of `E` then `E ⊆ (closure {x})ᶜ`, and as the quasi-compact
opens form a basis some quasi-compact open lies between the two
(`PrespectralSpace.exists_isCompact_and_isOpen_between`); it contains `E` but not `x`. -/
private lemma generalizationsOf_eq_sInter [SpectralSpace X] {E : Set X} (hE : IsCompact E) :
    generalizationsOf E = ⋂₀ {U | IsOpen U ∧ IsCompact U ∧ E ⊆ U} := by
  ext x
  simp only [Set.mem_sInter, Set.mem_ofPred_eq, generalizationsOf]
  refine ⟨fun ⟨y, hy_E, hxy⟩ U ⟨hU_open, _, hEU⟩ => hxy.mem_open hU_open (hEU hy_E),
    fun hx => by_contra fun h_not => ?_⟩
  obtain ⟨U, hUc, hUo, hEU, hU⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    hE isClosed_closure.isOpen_compl
    fun y hy hy_cl => h_not ⟨y, hy, specializes_iff_mem_closure.mpr hy_cl⟩
  exact hU (hx U ⟨hUo, hUc, hEU⟩) (subset_closure rfl)

/-- (3) ⇒ (4): the set of generalizations of a quasi-compact `E` is the intersection of all
quasi-compact opens containing `E`. -/
lemma isInterCompactOpen_of_isGeneralizationsOfCompact [SpectralSpace X] (W : Set X) :
    IsGeneralizationsOfCompact W → IsInterCompactOpen W := by
  rintro ⟨E, hE_compact, rfl⟩
  exact ⟨_, generalizationsOf_eq_sInter hE_compact, fun s hs => ⟨hs.1, hs.2.1⟩⟩


/-- A subspace of a spectral space that is stable under generalization is quasi-sober: the closure
in `X` of an irreducible closed `S ⊆ W` has a generic point, which generalizes a point of `S` and
therefore lies in `W`, where it is a generic point of `S`. -/
@[sga "4 IV 9.1.11" "9.1.11 g), special case"]
lemma quasiSober_of_stableUnderGeneralization [SpectralSpace X]
    (W : Set X) (hW_gen : StableUnderGeneralization W) :
    QuasiSober W := by
  refine ⟨fun {S} hS_irr hS_closed => ?_⟩
  obtain ⟨x, hx⟩ := QuasiSober.sober
    (hS_irr.image Subtype.val continuous_subtype_val.continuousOn).closure isClosed_closure
  obtain ⟨w, hw⟩ := hS_irr.nonempty
  refine ⟨⟨x, hW_gen (hx.specializes (subset_closure ⟨w, hw, rfl⟩)) w.2⟩, Set.ext fun z => ?_⟩
  simp only [closure_subtype, Set.image_singleton]
  rw [hx.def, ← closure_subtype, hS_closed.closure_eq]

/-- A quasi-compact set stable under generalization is closed in the constructible topology: it
is the intersection of the quasi-compact opens containing it, each of which is constructibly
clopen. -/
private lemma isClosed_constructibleTopology_of_isStableCompact [SpectralSpace X] (S : Set X)
    (hS_compact : IsCompact S) (hS_gen : StableUnderGeneralization S) :
    @IsClosed X (constructibleTopology X) S := by
  rw [← generalizationsOf_eq_self hS_gen, generalizationsOf_eq_sInter hS_compact]
  exact @isClosed_sInter X (constructibleTopology X) _ (fun U ⟨hUo, hUc, _⟩ =>
    (hUc.isClopen_constructibleTopology hUo).1)

/-- The image in `X` of an open subset of a subspace `W` stable under generalization is stable
under generalization: it is the intersection of `W` with an open of `X`. -/
private lemma stableUnderGeneralization_image_val {W : Set X}
    (hW_gen : StableUnderGeneralization W) {U : Set W} (hU : IsOpen U) :
    StableUnderGeneralization (Subtype.val '' U) := by
  obtain ⟨U', hU'_open, rfl⟩ := isOpen_induced_iff.mp hU
  rw [Subtype.image_preimage_coe]
  exact fun a b hab ⟨hbW, hbU'⟩ => ⟨hW_gen hab hbW, hab.mem_open hU'_open hbU'⟩

/-- A subspace `W` of a spectral space that is stable under generalization is quasi-separated:
the images in `X` of two quasi-compact opens of `W` are quasi-compact and stable under
generalization, hence closed in the constructible topology, so their intersection is
quasi-compact. -/
lemma quasiSeparated_of_stableUnderGeneralization [SpectralSpace X]
    (W : Set X) (hW_gen : StableUnderGeneralization W) :
    QuasiSeparatedSpace W := by
  refine ⟨fun U V hUo hUc hVo hVc => ?_⟩
  rw [Subtype.isCompact_iff, Set.image_inter Subtype.val_injective]
  exact (@IsClosed.inter X _ _ (constructibleTopology X)
    (isClosed_constructibleTopology_of_isStableCompact _ (Subtype.isCompact_iff.mp hUc)
      (stableUnderGeneralization_image_val hW_gen hUo))
    (isClosed_constructibleTopology_of_isStableCompact _ (Subtype.isCompact_iff.mp hVc)
      (stableUnderGeneralization_image_val hW_gen hVo))).isCompact_of_constructibleTopology

/-- A quasi-compact subspace `W` of a spectral space that is stable under generalization is
prespectral: the inclusion is a spectral map, since for a quasi-compact open `V` of `X` the set
`W ∩ V` is closed in the constructible topology, hence quasi-compact. -/
lemma prespectral_of_stableUnderGeneralization [SpectralSpace X]
    (W : Set X) (hW_compact : IsCompact W) (hW_gen : StableUnderGeneralization W) :
    PrespectralSpace W :=
  .of_isInducing Subtype.val Topology.IsInducing.subtypeVal
    ⟨continuous_subtype_val, fun V hVo hVc => by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
      exact (@IsClosed.inter X W V (constructibleTopology X)
        (isClosed_constructibleTopology_of_isStableCompact W hW_compact hW_gen)
        (hVc.isClopen_constructibleTopology hVo).1).isCompact_of_constructibleTopology⟩

/-- The sets clopen in the constructible topology form a Boolean subalgebra of `Set X`. -/
private def clopenConstructibleSubalgebra [SpectralSpace X] : BooleanSubalgebra (Set X) where
  carrier := {s | @IsClopen X (constructibleTopology X) s}
  supClosed' := fun {a} ha {b} hb => @IsClopen.union X (constructibleTopology X) a b ha hb
  infClosed' := fun {a} ha {b} hb => @IsClopen.inter X (constructibleTopology X) a b ha hb
  compl_mem' := fun {a} ha => @IsClopen.compl X (constructibleTopology X) a ha
  bot_mem' := @isClopen_empty X (constructibleTopology X)

/-- Every constructible set is closed in the constructible topology: the generating retrocompact
opens are quasi-compact here, hence constructibly clopen, and the clopen sets form a Boolean
subalgebra. -/
lemma isClosed_constructibleTopology_of_isConstructible [SpectralSpace X] (s : Set X)
    (hs : Topology.IsConstructible s) :
    @IsClosed X (constructibleTopology X) s := by
  have h : BooleanSubalgebra.closure {U : Set X | IsOpen U ∧ IsRetrocompact U} ≤
      clopenConstructibleSubalgebra (X := X) :=
    BooleanSubalgebra.closure_le.mpr fun U hU =>
      hU.2.isCompact.isClopen_constructibleTopology hU.1
  exact (h hs).1

/-- (4) ⇒ (1): every quasi-compact open is constructible, and an intersection of opens is stable
under generalization. -/
lemma isStableInterConstructible_of_isInterCompactOpen [SpectralSpace X] (W : Set X) :
    IsInterCompactOpen W → IsStableInterConstructible W := by
  rintro ⟨S, rfl, hS⟩
  exact ⟨stableUnderGeneralization_sInter S fun s hs => (hS s hs).1.stableUnderGeneralization, S,
    rfl, fun s hs => (hS s hs).2.isConstructible (hS s hs).1⟩


/-- (1) ⇒ (2): each constructible set is closed in the constructible topology, so `W` is too, hence
quasi-compact there, hence quasi-compact in the original, coarser topology. -/
lemma isStableCompact_of_isStableInterConstructible [SpectralSpace X] (W : Set X) :
    IsStableInterConstructible W → IsStableCompact W := by
  rintro ⟨hW_gen, S, rfl, hS⟩
  refine ⟨IsClosed.isCompact_of_constructibleTopology ?_, hW_gen⟩
  exact @isClosed_sInter X (constructibleTopology X) S fun s hs =>
    isClosed_constructibleTopology_of_isConstructible s (hS s hs)

/-- **Stacks 0A31, the equivalence.** For a subset `W` of a spectral space the five conditions
(1) intersection of constructibles and stable under generalization, (2) quasi-compact and stable
under generalization, (3) the generalizations of a quasi-compact set, (4) an intersection of
quasi-compact opens, (5) a directed intersection of quasi-compact opens, are all equivalent. -/
@[stacks 0A31 "equivalence of the five characterizations"]
theorem characterizations_equiv [SpectralSpace X] (W : Set X) :
    (IsStableInterConstructible W ↔ IsStableCompact W) ∧
      (IsStableCompact W ↔ IsGeneralizationsOfCompact W) ∧
        (IsGeneralizationsOfCompact W ↔ IsInterCompactOpen W) ∧
          (IsInterCompactOpen W ↔ IsDirectedInterCompactOpen W) := by
  have h45 := isDirectedInterCompactOpen_of_isInterCompactOpen W
  have h52 := isStableCompact_of_isDirectedInterCompactOpen W
  have h23 := isGeneralizationsOfCompact_of_isStableCompact W
  have h34 := isInterCompactOpen_of_isGeneralizationsOfCompact W
  have h41 := isStableInterConstructible_of_isInterCompactOpen W
  have h12 := isStableCompact_of_isStableInterConstructible W
  exact ⟨⟨h12, fun h2 => h41 (h34 (h23 h2))⟩,
         ⟨h23, fun h3 => h52 (h45 (h34 h3))⟩,
         ⟨h34, fun h4 => h23 (h52 (h45 h4))⟩,
         ⟨h45, fun h5 => h34 (h23 (h52 h5))⟩⟩

/-- Conclusion (a): under the equivalent conditions, `W` (with the
subspace topology) is itself a spectral space. -/
@[stacks 0A31 "conclusion (a): W is spectral"]
theorem spectralSpace_of_isStableCompact [SpectralSpace X] (W : Set X) (h : IsStableCompact W) :
    SpectralSpace W := by
  -- `SpectralSpace` bundles `T0Space`, `CompactSpace`, `QuasiSober`, `QuasiSeparatedSpace` and
  -- `PrespectralSpace`; `T0Space W` is inherited from `X`, the other four are proved above.
  have : CompactSpace W := isCompact_iff_compactSpace.mp h.1
  have := quasiSober_of_stableUnderGeneralization W h.2
  have := quasiSeparated_of_stableUnderGeneralization W h.2
  have := prespectral_of_stableUnderGeneralization W h.1 h.2
  exact SpectralSpace.mk

omit [TopologicalSpace X] in
/-- All coordinates of a compatible family in `InvLimit U` are equal, by directedness. -/
lemma invLimit_coords_eq {I : Type*} [Nonempty I] (U : I → Set X)
    (hdir : ∀ i j, ∃ k, U k ⊆ U i ∩ U j)
    (f : InvLimit U) (i j : I) : ((f.1 i : X)) = (f.1 j : X) := by
  obtain ⟨k, hk⟩ := hdir i j
  exact (f.2 i k fun _ hx => (hk hx).1).symm.trans (f.2 j k fun _ hx => (hk hx).2)

/-- The inverse of `canonicalMap`: a compatible family is sent to its common coordinate. -/
noncomputable def invLimitToW {I : Type*} [Nonempty I] (U : I → Set X)
    (hdir : ∀ i j, ∃ k, U k ⊆ U i ∩ U j)
    (W : Set X) (hWeq : W = ⋂ i, U i) :
    InvLimit U → W := fun f =>
  ⟨(f.1 (Classical.arbitrary I) : X), hWeq ▸ Set.mem_iInter.2 fun i =>
    (invLimit_coords_eq U hdir f (Classical.arbitrary I) i).symm ▸ (f.1 i).2⟩

omit [TopologicalSpace X] in
/-- The canonical map is injective. -/
lemma canonicalMap_injective {I : Type*} [Nonempty I] (U : I → Set X)
    (W : Set X) (hW : W ⊆ ⋂ i, U i) :
    Function.Injective (canonicalMap U W hW) := fun _ _ h =>
  Subtype.ext (congrArg (fun f : InvLimit U => (f.1 (Classical.arbitrary I) : X)) h)

omit [TopologicalSpace X] in
/-- The canonical map is surjective: `invLimitToW` is a right inverse, by directedness. -/
lemma canonicalMap_surjective {I : Type*} [Nonempty I] (U : I → Set X)
    (hdir : ∀ i j, ∃ k, U k ⊆ U i ∩ U j)
    (W : Set X) (hW : W ⊆ ⋂ i, U i) (hWeq : W = ⋂ i, U i) :
    Function.Surjective (canonicalMap U W hW) := fun f =>
  ⟨invLimitToW U hdir W hWeq f, Subtype.ext <| funext fun i =>
    Subtype.ext <| invLimit_coords_eq U hdir f (Classical.arbitrary I) i⟩

/-- The canonical map is continuous. -/
lemma canonicalMap_continuous {I : Type*} [Nonempty I] (U : I → Set X)
    (W : Set X) (hW : W ⊆ ⋂ i, U i) :
    Continuous (canonicalMap U W hW) :=
  (continuous_pi fun _ => continuous_subtype_val.codRestrict _).subtype_mk _

/-- `invLimitToW` is continuous. -/
lemma invLimitToW_continuous {I : Type*} [Nonempty I] (U : I → Set X)
    (hdir : ∀ i j, ∃ k, U k ⊆ U i ∩ U j)
    (W : Set X) (hWeq : W = ⋂ i, U i) :
    Continuous (invLimitToW U hdir W hWeq) :=
  (continuous_pi_iff.mp continuous_subtype_val (Classical.arbitrary I)).subtype_val.subtype_mk _

/-- Conclusion (b): the canonical map `W → InvLimit U` is a homeomorphism. -/
@[stacks 0A31 "conclusion (b): W ≅ lim U_i"]
theorem exists_homeomorph_invLimit
    {I : Type*} [Nonempty I] (U : I → Set X)
    (hdir : ∀ i j, ∃ k, U k ⊆ U i ∩ U j)
    (W : Set X) (hWeq : W = ⋂ i, U i) :
    ∃ φ : W ≃ₜ InvLimit U,
      ∀ w : W, ∀ i, ((φ w).1 i : X) = (w : X) := by
  have hW : W ⊆ ⋂ i, U i := hWeq.subset
  refine ⟨{ toFun := canonicalMap U W hW
            invFun := invLimitToW U hdir W hWeq
            left_inv := fun _ => rfl
            right_inv := fun f => ?_
            continuous_toFun := canonicalMap_continuous U W hW
            continuous_invFun := invLimitToW_continuous U hdir W hWeq }, fun _ _ => rfl⟩
  exact Subtype.ext <| funext fun i =>
    Subtype.ext <| invLimit_coords_eq U hdir f (Classical.arbitrary I) i

/-- A directed family of quasi-compact opens of a spectral space meets a closed set `C` in a
nonempty intersection as soon as each member does. In the constructible topology each `U i ∩ C`
is closed, hence quasi-compact, so Mathlib's
`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed` applies; the point it produces
lies in the intersection, a statement about sets that survives the change of topology. -/
lemma nonempty_iInter_inter_of_directed [SpectralSpace X]
    {I : Type*} [Nonempty I] (U : I → Set X)
    (hUo : ∀ i, IsOpen (U i)) (hUc : ∀ i, IsCompact (U i)) (hdir : Directed (· ⊇ ·) U)
    (C : Set X) (hC : IsClosed C) (hne : ∀ i, (U i ∩ C).Nonempty) :
    (⋂ i, U i ∩ C).Nonempty := by
  have hclosed : ∀ i, @IsClosed X (constructibleTopology X) (U i ∩ C) := fun i =>
    @IsClosed.inter X (U i) C (constructibleTopology X)
      ((hUc i).isClopen_constructibleTopology (hUo i)).1 hC.isClosed_constructibleTopology
  exact @IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    X (constructibleTopology X) I _ (fun i => U i ∩ C)
    (fun i j => (hdir i j).imp fun _ ⟨hki, hkj⟩ =>
      ⟨Set.inter_subset_inter_left C hki, Set.inter_subset_inter_left C hkj⟩) hne
    (fun i => (hclosed i).isCompact_constructibleTopology) hclosed

/-- Conclusion (c): with the family `U_i` from condition (5), every open
subset `V` of `X` containing `W` contains some `U_i`. -/
@[stacks 0A31 "conclusion (c): some U_i ⊆ V"]
theorem exists_subset_of_subset_isOpen [SpectralSpace X]
    {I : Type*} [Nonempty I] (U : I → Set X)
    (hU : ∀ i, IsOpen (U i) ∧ IsCompact (U i))
    (hdir : ∀ i j, ∃ k, U k ⊆ U i ∩ U j)
    (W : Set X) (hWeq : W = ⋂ i, U i)
    (V : Set X) (hVopen : IsOpen V) (hWV : W ⊆ V) :
    ∃ i, U i ⊆ V := by
  subst hWeq
  by_contra habs
  obtain ⟨x, hx⟩ := nonempty_iInter_inter_of_directed U (fun i => (hU i).1) (fun i => (hU i).2)
    (fun i j => (hdir i j).imp fun _ hk => Set.subset_inter_iff.mp hk) Vᶜ hVopen.isClosed_compl
    fun i => Set.not_subset.mp fun h => habs ⟨i, h⟩
  have hx' := Set.mem_iInter.mp hx
  exact (hx' (Classical.arbitrary I)).2 (hWV (Set.mem_iInter.2 fun i => (hx' i).1))

end SpectralSubset
