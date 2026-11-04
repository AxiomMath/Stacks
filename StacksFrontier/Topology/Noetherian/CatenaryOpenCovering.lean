module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyClosed
public import StacksFrontier.Topology.Dimension.Catenary
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Catenary spaces are exactly those with an open covering by catenary spaces (Stacks 02I2)

A topological space `X` is *catenary* when, for any two irreducible closed subsets `T ⊆ T'`,
the strictly increasing chains of irreducible closed subsets from `T` to `T'` have bounded
length and all the *maximal* such chains — those admitting no further insertion — have one and
the same length. This file proves the two statements of tag 02I2: `X` is catenary if and only if
it admits an open covering by catenary subspaces, and, moreover, every locally closed subspace
of a catenary space is catenary.

Both rest on one piece of infrastructure, the correspondence between the irreducible closed
subsets of an open `U ⊆ X` and those irreducible closed subsets of `X` that meet `U`. The maps
are `closureInAmbient U`, taking closures of images, and `restrictToOpen U`, taking preimages;
they are mutually inverse (`closureInAmbient_restrictToOpen`,
`restrictToOpen_closureInAmbient`) because a nonempty open subset of an irreducible set is
dense in it, and strictly monotone. Consequently they match up chains from `T` to `T'` with
chains between the restrictions, preserving length (`topCodim_eq_of_open`) and maximality
in both directions. Locality of catenarity follows: an irreducible closed `T` meets some member
`U i₀` of the covering, and then so does every irreducible closed set above `T`, so the whole
question about `T ≤ T'` may be asked inside `U i₀`. The converse direction takes the covering by
the single open set `Set.univ`, using that catenarity is a topological property
(`isCatenary_of_homeomorph`). The moreover clause combines the closed case
(`isCatenary_of_isClosed`, via the closed embedding `Subtype.val`) with the open case
(`isCatenary_of_isOpen`), since a locally closed set is open in its closure.

Two remarks on the formalization. First, the index type of the covering in
`HasOpenCoveringByCatenarySpaces` is quantified over an arbitrary universe rather than over
`Type 0`; otherwise the local-to-global direction would only apply to coverings that happen to
be indexed by a small type, and would be strictly weaker than the source statement. Second, the
catenary predicate is the canonical `IrreducibleClosedsCodim.IsCatenarySpace` of
`StacksFrontier.Topology.Dimension.Catenary` (Stacks 02I1, the definition this lemma is about),
with chains modelled by `LTSeries` in the lattice `TopologicalSpace.IrreducibleCloseds X` and
codimension the supremum `IrreducibleClosedsCodim.topCodim`. Tag 02IC
(`StacksFrontier.Topology.Dimension.DimensionFunctionCatenary`) still has an independent encoding of
the same notion,
`TopologicalSpace.IsTopologicallyCatenary`, phrased over raw sets `Set X` with side conditions;
that one has not been merged here.
-/

@[expose] public section

open TopologicalSpace IrreducibleClosedsCodim

namespace CatenaryTopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- `X` has an open covering by catenary spaces: there is a family `U : ι → Set X` of open sets
covering `X`, each of which is catenary in its subspace topology. The index type `ι` ranges over
an arbitrary universe, so that every open covering of `X` — not only the ones that happen to be
indexed by a type in `Type 0` — is allowed as a witness. -/
def HasOpenCoveringByCatenarySpaces (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ (ι : Type*) (U : ι → Set X),
    (∀ i, IsOpen (U i)) ∧ (⋃ i, U i = Set.univ) ∧ ∀ i, IsCatenarySpace (U i)

/-- Map from the irreducible closed subsets of an open subset `U` to those of `X`,
sending `Z` to the closure in `X` of its underlying set. -/
@[ega "0 2.1.6", ega "III 4.4.4" "partial"]
noncomputable def closureInAmbient (U : Set X) (Z : IrreducibleCloseds U) : IrreducibleCloseds X :=
  ⟨closure (Subtype.val '' Z.carrier),
    Z.isIrreducible'.image _ continuous_subtype_val.continuousOn |>.closure, isClosed_closure⟩

/-- Restriction of an irreducible closed subset `T` of `X` to an open `U` that it meets: the
preimage of `T` in `U` is again irreducible and closed. -/
@[ega "0 2.1.6"]
noncomputable def restrictToOpen (U : Set X) (hU : IsOpen U) (T : IrreducibleCloseds X)
    (hT : (T.carrier ∩ U).Nonempty) : IrreducibleCloseds U :=
  ⟨Subtype.val ⁻¹' T.carrier,
    T.isIrreducible'.preimage (hU.isOpenEmbedding_subtypeVal) (by rwa [Subtype.range_val]),
    T.isClosed'.preimage continuous_subtype_val⟩

private lemma le_iff_carrier_subset {Y : Type*} [TopologicalSpace Y]
    {a b : IrreducibleCloseds Y} : a ≤ b ↔ a.carrier ⊆ b.carrier :=
  Iff.rfl

private lemma carrier_eq_coe {Y : Type*} [TopologicalSpace Y] (a : IrreducibleCloseds Y) :
    a.carrier = (a : Set Y) :=
  rfl

/-- The underlying set of `closureInAmbient U Z` is the closure of `Z` in `X`. -/
lemma coe_closureInAmbient (U : Set X) (Z : IrreducibleCloseds U) :
    (closureInAmbient U Z : Set X) = closure (Subtype.val '' (Z : Set U)) :=
  rfl

/-- The underlying set of `restrictToOpen U hU T hT` is the preimage of `T` in `U`. -/
lemma coe_restrictToOpen (U : Set X) (hU : IsOpen U) (T : IrreducibleCloseds X)
    (hT : (T.carrier ∩ U).Nonempty) :
    (restrictToOpen U hU T hT : Set U) = Subtype.val ⁻¹' (T : Set X) :=
  rfl

/-- The carrier of `restrictToOpen U hU T hT` is the preimage of the carrier of `T`. -/
lemma restrictToOpen_carrier (U : Set X) (hU : IsOpen U) (T : IrreducibleCloseds X)
    (hT : (T.carrier ∩ U).Nonempty) :
    (restrictToOpen U hU T hT).carrier = Subtype.val ⁻¹' T.carrier :=
  rfl

/-- The closure in `X` of an irreducible closed subset `Z` of an open `U` meets `U`: an
irreducible set is nonempty, and any point of `Z` is a point of `U` lying in the closure. -/
lemma closureInAmbient_meets_open (U : Set X) (Z : IrreducibleCloseds U) :
    ((closureInAmbient U Z).carrier ∩ U).Nonempty := by
  obtain ⟨z, hz⟩ := Z.isIrreducible'.nonempty
  exact ⟨z.val, subset_closure ⟨z, hz, rfl⟩, z.property⟩

/-- First round-trip: restricting an irreducible closed `T` of `X` to an open `U` it meets and
taking the closure again recovers `T`. Indeed the restriction has underlying set `T ∩ U`, a
nonempty open subset of the irreducible set `T`, hence dense in `T`, and `T` is closed. -/
@[ega "0 2.1.6" "density of Z ∩ U in Z", sga "3 VIB 4.2" "partial"]
lemma closureInAmbient_restrictToOpen (U : Set X) (hU : IsOpen U) (T : IrreducibleCloseds X)
    (hT : (T.carrier ∩ U).Nonempty) : closureInAmbient U (restrictToOpen U hU T hT) = T := by
  apply SetLike.ext'
  rw [coe_closureInAmbient, coe_restrictToOpen, Subtype.image_preimage_val U (T : Set X)]
  refine subset_antisymm (closure_minimal Set.inter_subset_right T.isClosed') fun x hx => ?_
  refine mem_closure_iff.2 fun V hV hxV => ?_
  obtain ⟨y, hyT, hyV, hyU⟩ := T.isIrreducible'.2 V U hV hU ⟨x, hx, hxV⟩ hT
  exact ⟨y, hyV, hyU, hyT⟩

/-- Second round-trip: taking the closure in `X` of an irreducible closed subset `Z` of `U` and
intersecting back with `U` recovers `Z`, because the closure of a subset of `U` computed in `X`
meets `U` in its closure computed in `U`, and `Z` is closed in `U`. -/
@[ega "0 2.1.6"]
lemma restrictToOpen_closureInAmbient (U : Set X) (hU : IsOpen U) (Z : IrreducibleCloseds U) :
    restrictToOpen U hU (closureInAmbient U Z) (closureInAmbient_meets_open U Z) = Z := by
  apply SetLike.ext'
  rw [coe_restrictToOpen, coe_closureInAmbient]
  ext x
  simp only [Set.mem_preimage]
  refine ⟨fun hx => ?_, fun hx => subset_closure ⟨x, hx, rfl⟩⟩
  have h := closure_subtype (s := Z.carrier) (x := x)
  rw [Z.isClosed'.closure_eq] at h
  exact h.mpr hx

/-- For `U` open, `closureInAmbient U` is strictly monotone: closure is monotone, and equality
of the two closures would give `Z₁ = Z₂` after intersecting back with `U`. -/
lemma closureInAmbient_strictMono (U : Set X) (hU : IsOpen U) :
    StrictMono (closureInAmbient U) := by
  intro Z₁ Z₂ h12
  refine lt_of_le_of_ne (closure_mono (Set.image_mono h12.le)) fun heq => h12.ne ?_
  rw [← restrictToOpen_closureInAmbient U hU Z₁, ← restrictToOpen_closureInAmbient U hU Z₂]
  congr 1

/-- If `T` meets `U`, then so does every irreducible closed `Y ≥ T`. -/
lemma meets_open_of_ge (U : Set X) (T : IrreducibleCloseds X) (hT : (T.carrier ∩ U).Nonempty)
    (Y : IrreducibleCloseds X) (hTY : T ≤ Y) : (Y.carrier ∩ U).Nonempty :=
  hT.mono (Set.inter_subset_inter_left U hTY)

/-- `restrictToOpen U hU` is strictly monotone on the irreducible closed sets meeting `U`. -/
private lemma restrictToOpen_lt_restrictToOpen (U : Set X) (hU : IsOpen U)
    {T₁ T₂ : IrreducibleCloseds X} (h : T₁ < T₂) (h₁ : (T₁.carrier ∩ U).Nonempty)
    (h₂ : (T₂.carrier ∩ U).Nonempty) : restrictToOpen U hU T₁ h₁ < restrictToOpen U hU T₂ h₂ := by
  refine lt_of_le_of_ne (le_iff_carrier_subset.2 (Set.preimage_mono (le_iff_carrier_subset.1
    h.le))) fun heq => h.ne ?_
  rw [← closureInAmbient_restrictToOpen U hU T₁ h₁, ← closureInAmbient_restrictToOpen U hU T₂ h₂]
  congr 1

/-- The restriction to an open `U` of a chain of irreducible closed subsets of `X` whose head
meets `U`, taken term by term. -/
private noncomputable def restrictLTSeries (U : Set X) (hU : IsOpen U)
    (p : LTSeries (IrreducibleCloseds X)) (hp : (p.head.carrier ∩ U).Nonempty) :
    LTSeries (IrreducibleCloseds U) :=
  ⟨p.length, fun i => restrictToOpen U hU (p i) (meets_open_of_ge U _ hp _ (p.head_le i)),
    fun i => by
      simp only [Set.mem_ofPred_eq]
      exact restrictToOpen_lt_restrictToOpen U hU (p.step i : p i.castSucc < p i.succ) _ _⟩

/-- The correspondence preserves relative codimension: chains from `T` to `T'` in `X` and
chains between their restrictions in `U` are matched up by `closureInAmbient` and
`restrictToOpen` with the same lengths, so the two suprema agree. -/
@[ega "0 14.2.3" "special case"]
lemma topCodim_eq_of_open (U : Set X) (hU : IsOpen U) (T T' : IrreducibleCloseds X)
    (hT : (T.carrier ∩ U).Nonempty) (hT' : (T'.carrier ∩ U).Nonempty) :
    topCodim (restrictToOpen U hU T hT) (restrictToOpen U hU T' hT') = topCodim T T' := by
  apply le_antisymm
  · -- (≤): Map chains in U to chains in X via closureInAmbient
    rw [topCodim_eq_iSup_head_last]
    refine iSup_le fun q => iSup_le fun hq_head => iSup_le fun hq_last => ?_
    exact length_le_topCodim T T' (q.map (closureInAmbient U) (closureInAmbient_strictMono U hU))
      (by simp [LTSeries.head_map, hq_head, closureInAmbient_restrictToOpen])
      (by simp [LTSeries.last_map, hq_last, closureInAmbient_restrictToOpen])
  · -- (≥): Map chains in X to chains in U via restrictToOpen
    rw [topCodim_eq_iSup_head_last]
    refine iSup_le fun p => iSup_le fun hp_head => iSup_le fun hp_last => ?_
    subst hp_head hp_last
    exact length_le_topCodim _ _ (restrictLTSeries U hU p hT) rfl rfl

/-- Pushing a maximal chain forward along a strictly monotone `g` keeps it maximal as soon as
every irreducible closed set inserted between consecutive images yields an insertion upstairs. -/
private lemma isMaximalChain_map {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (g : IrreducibleCloseds Y → IrreducibleCloseds Z) (hg : StrictMono g)
    {p : LTSeries (IrreducibleCloseds Y)} {a b : IrreducibleCloseds Y} (hp : IsMaximalChain p a b)
    (hins : ∀ (i : Fin p.length) (W : IrreducibleCloseds Z), g (p i.castSucc) < W →
      W < g (p i.succ) → ∃ V, p i.castSucc < V ∧ V < p i.succ) :
    IsMaximalChain (p.map g hg) (g a) (g b) := by
  rw [isMaximalChain_iff_forall_not_btwn] at hp ⊢
  refine ⟨by simp [LTSeries.head_map, hp.1], by simp [LTSeries.last_map, hp.2.1], ?_⟩
  rintro i ⟨W, hW₁, hW₂⟩
  exact hp.2.2 (i.cast (LTSeries.map_length p g hg)) (hins _ W hW₁ hW₂)

/-- Catenarity of the pair `A ≤ A'` follows from that of a pair `B ≤ B'` of equal codimension
such that every maximal chain from `A` to `A'` corresponds to one from `B` to `B'` of the same
length. -/
private lemma catenary_pair_of_codim_eq {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {A A' : IrreducibleCloseds Y} {B B' : IrreducibleCloseds Z}
    (hcod : topCodim A A' = topCodim B B')
    (hB : topCodim B B' ≠ ⊤ ∧ ∀ p, IsMaximalChain p B B' → (p.length : ℕ∞) = topCodim B B')
    (hmax : ∀ p, IsMaximalChain p A A' → ∃ q, IsMaximalChain q B B' ∧ q.length = p.length) :
    topCodim A A' ≠ ⊤ ∧ ∀ p, IsMaximalChain p A A' → (p.length : ℕ∞) = topCodim A A' := by
  refine ⟨hcod ▸ hB.1, fun p hp => ?_⟩
  obtain ⟨q, hq, hql⟩ := hmax p hp
  rw [hcod, ← hql]
  exact hB.2 q hq

/-- Pushing a chain forward by `closureInAmbient` preserves maximality: an irreducible closed
`Y` inserted between two consecutive terms would meet `U`, since the smaller term does, and its
restriction to `U` would then be inserted between the corresponding terms of the original
chain. -/
lemma map_closureInAmbient_maximal (U : Set X) (hU : IsOpen U) (T₀ T₀' : IrreducibleCloseds U)
    (q : LTSeries (IrreducibleCloseds U)) (hq : IsMaximalChain q T₀ T₀') :
    IsMaximalChain (q.map (closureInAmbient U) (closureInAmbient_strictMono U hU))
      (closureInAmbient U T₀) (closureInAmbient U T₀') := by
  refine isMaximalChain_map _ _ hq fun i Y hY₁ hY₂ => ?_
  -- Y meets U since closureInAmbient(q(i)) ≤ Y and closureInAmbient(q(i)) meets U
  have hY : (Y.carrier ∩ U).Nonempty :=
    meets_open_of_ge U _ (closureInAmbient_meets_open U _) Y hY₁.le
  -- restrictToOpen Y is strictly between q(i) and q(i+1), contradicting maximality of q
  refine ⟨restrictToOpen U hU Y hY, ?_, ?_⟩
  · rw [← restrictToOpen_closureInAmbient U hU (q i.castSucc)]
    exact restrictToOpen_lt_restrictToOpen U hU hY₁ _ _
  · rw [← restrictToOpen_closureInAmbient U hU (q i.succ)]
    exact restrictToOpen_lt_restrictToOpen U hU hY₂ _ _

/-- Restricting a maximal chain of `X` from `T` to `T'` to an open `U` meeting `T` yields a
maximal chain of `U` of the same length. Every term contains `T`, hence meets `U`, so the
restriction is defined term by term; maximality is inherited because an insertion in `U` would
push forward to an insertion in `X`. -/
lemma map_restrictToOpen_maximal (U : Set X) (hU : IsOpen U) (T T' : IrreducibleCloseds X)
    (hle : T ≤ T') (hT : (T.carrier ∩ U).Nonempty) (p : LTSeries (IrreducibleCloseds X))
    (hp : IsMaximalChain p T T') :
    ∃ q : LTSeries (IrreducibleCloseds U),
      IsMaximalChain q (restrictToOpen U hU T hT)
          (restrictToOpen U hU T' (meets_open_of_ge U T hT T' hle)) ∧
        q.length = p.length := by
  rw [isMaximalChain_iff_forall_not_btwn] at hp
  obtain ⟨rfl, rfl, hp⟩ := hp
  -- Each p(i) satisfies T ≤ p(i), so p(i) meets U: restrict the chain term by term
  refine ⟨restrictLTSeries U hU p hT, ?_, rfl⟩
  rw [isMaximalChain_iff_forall_not_btwn]
  -- head and last are the restrictions of T and T'; it remains to check maximality
  refine ⟨rfl, rfl, ?_⟩
  rintro i ⟨Y₀, hY₀_gt, hY₀_lt⟩
  have h (j) := closureInAmbient_restrictToOpen U hU (p j) (meets_open_of_ge U _ hT _ (p.head_le j))
  exact hp i ⟨closureInAmbient U Y₀, (h _).symm.trans_lt (closureInAmbient_strictMono U hU hY₀_gt),
    (closureInAmbient_strictMono U hU hY₀_lt).trans_eq (h _)⟩

/-- Catenarity pulls back along an order embedding `g` of irreducible closed subsets whose image
contains every irreducible closed set below a point of the image. -/
private lemma isCatenary_of_le_iff {Y : Type*} [TopologicalSpace Y]
    (g : IrreducibleCloseds Y → IrreducibleCloseds X) (hg : ∀ a b, g a ≤ g b ↔ a ≤ b)
    (hdown : ∀ b Z, Z ≤ g b → ∃ W, g W = Z) (hX : IsCatenarySpace X) : IsCatenarySpace Y := by
  have hmono : StrictMono g := strictMono_of_le_iff_le fun a b => (hg a b).symm
  have hlt : ∀ a b, g a < g b → a < b := fun a b h =>
    lt_of_le_of_ne ((hg a b).1 h.le) fun e => h.ne (by rw [e])
  intro S S' hSS'
  refine catenary_pair_of_codim_eq (topCodim_eq_of_le_iff g hg S S' (hdown S')).symm
    (hX (g S) (g S') ((hg S S').2 hSS')) fun p hp => ⟨p.map g hmono, ?_, rfl⟩
  refine isMaximalChain_map g hmono hp fun i Z hZ₁ hZ₂ => ?_
  obtain ⟨W, rfl⟩ := hdown _ Z hZ₂.le
  exact ⟨W, hlt _ _ hZ₁, hlt _ _ hZ₂⟩

/-- Catenarity is a topological property: a homeomorphism `e : X ≃ₜ Y` induces, by taking
images, an order isomorphism between the irreducible closed subsets of `X` and of `Y`, and hence
preserves chains, their lengths, maximality and `topCodim`. -/
lemma isCatenary_of_homeomorph {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y)
    (hX : IsCatenarySpace X) : IsCatenarySpace Y := by
  let g : IrreducibleCloseds Y → IrreducibleCloseds X := fun S =>
    ⟨e.symm '' S.carrier, S.isIrreducible'.image e.symm e.symm.continuous.continuousOn,
      e.symm.isClosedMap _ S.isClosed'⟩
  let f : IrreducibleCloseds X → IrreducibleCloseds Y := fun T =>
    ⟨e '' T.carrier, T.isIrreducible'.image e e.continuous.continuousOn,
      e.isClosedMap _ T.isClosed'⟩
  have hfg : ∀ S : IrreducibleCloseds Y, f (g S) = S := by
    intro S
    apply SetLike.ext'
    simp only [f, g, IrreducibleCloseds.coe_mk, carrier_eq_coe]
    rw [Set.image_image]
    simp [Homeomorph.apply_symm_apply]
  have hgf : ∀ T : IrreducibleCloseds X, g (f T) = T := by
    intro T
    apply SetLike.ext'
    simp only [f, g, IrreducibleCloseds.coe_mk, carrier_eq_coe]
    rw [Set.image_image]
    simp [Homeomorph.symm_apply_apply]
  -- `g` is an order embedding with `f` as inverse, so it identifies the two codimensions.
  refine isCatenary_of_le_iff g (fun a b => ⟨fun hab => ?_, fun hab => Set.image_mono hab⟩)
    (fun _ Z _ => ⟨f Z, hgf Z⟩) hX
  have h : f (g a) ≤ f (g b) := Set.image_mono hab
  rwa [hfg, hfg] at h

/-- Catenarity transfers from `X` to the subspace `Set.univ`, along the canonical homeomorphism
`X ≃ₜ ↥(Set.univ : Set X)`. -/
lemma isCatenary_univ_of_isCatenary (hX : IsCatenarySpace X) :
    IsCatenarySpace (Set.univ : Set X) :=
  isCatenary_of_homeomorph (Homeomorph.Set.univ X).symm hX

/-- A catenary space has an open covering by catenary spaces: the one-member covering by
`Set.univ`. -/
lemma hasOpenCoveringByCatenarySpaces_of_isCatenary (hX : IsCatenarySpace X) :
    HasOpenCoveringByCatenarySpaces X :=
  ⟨PUnit, fun _ => Set.univ, fun _ => isOpen_univ, Set.iUnion_const Set.univ, fun _ =>
    isCatenary_univ_of_isCatenary hX⟩

/-- Catenarity is local: a space covered by open catenary subspaces is catenary. Given
`T ≤ T'`, pick a member `U i₀` of the covering meeting `T`; then it meets every irreducible
closed set above `T`, so chains from `T` to `T'` correspond to chains from `T ∩ U i₀` to
`T' ∩ U i₀`, with the same lengths and the same maximal ones. -/
lemma isCatenary_of_hasOpenCoveringByCatenarySpaces (h : HasOpenCoveringByCatenarySpaces X) :
    IsCatenarySpace X := by
  obtain ⟨ι, U, hU_open, hU_cover, hU_cat⟩ := h
  intro T T' hTT'
  obtain ⟨x, hxT⟩ := T.isIrreducible'.nonempty
  obtain ⟨i₀, hx_Ui⟩ := Set.iUnion_eq_univ_iff.mp hU_cover x
  have hT_meets : (T.carrier ∩ U i₀).Nonempty := ⟨x, hxT, hx_Ui⟩
  have hT'_meets : (T'.carrier ∩ U i₀).Nonempty := meets_open_of_ge (U i₀) T hT_meets T' hTT'
  set T₀ := restrictToOpen (U i₀) (hU_open i₀) T hT_meets
  set T₀' := restrictToOpen (U i₀) (hU_open i₀) T' hT'_meets
  exact catenary_pair_of_codim_eq
    (topCodim_eq_of_open (U i₀) (hU_open i₀) T T' hT_meets hT'_meets).symm
    (hU_cat i₀ T₀ T₀'
      (le_iff_carrier_subset.2 (Set.preimage_mono (le_iff_carrier_subset.1 hTT'))))
    fun p hp => map_restrictToOpen_maximal (U i₀) (hU_open i₀) T T' hTT' hT_meets p hp

/-- **Stacks 02I2.** A topological space is catenary if and only if it has an open covering by
catenary spaces. -/
@[stacks 02I2]
theorem isCatenary_iff_hasOpenCoveringByCatenarySpaces (X : Type*) [TopologicalSpace X] :
    IsCatenarySpace X ↔ HasOpenCoveringByCatenarySpaces X :=
  ⟨hasOpenCoveringByCatenarySpaces_of_isCatenary, isCatenary_of_hasOpenCoveringByCatenarySpaces⟩

/-- Open subspaces of catenary spaces are catenary: transport `T₀ ≤ T₀'` to
`closureInAmbient U T₀ ≤ closureInAmbient U T₀'` in `X`, apply catenarity there, and transport
the bound on chain lengths and the equality of maximal chain lengths back along the
correspondence. -/
lemma isCatenary_of_isOpen (hX : IsCatenarySpace X) (U : Set X) (hU : IsOpen U) :
    IsCatenarySpace U := by
  intro T₀ T₀' hT₀T₀'
  have hcod := topCodim_eq_of_open U hU (closureInAmbient U T₀) (closureInAmbient U T₀')
    (closureInAmbient_meets_open U T₀) (closureInAmbient_meets_open U T₀')
  rw [restrictToOpen_closureInAmbient, restrictToOpen_closureInAmbient] at hcod
  exact catenary_pair_of_codim_eq hcod
    (hX _ _ (closure_mono (Set.image_mono hT₀T₀')))
    fun p hp => ⟨_, map_closureInAmbient_maximal U hU T₀ T₀' p hp, rfl⟩

/-- Closed subspaces of catenary spaces are catenary. For `F` closed in `X`, taking images
under the closed embedding `Subtype.val` identifies the irreducible closed subsets of `F` with
those irreducible closed subsets of `X` contained in `F`, an order embedding preserving chain
lengths. Maximality transfers because an irreducible closed `Y` of `X` inserted between two
consecutive terms of the image chain is contained in the larger one, hence in `F`, so it is the
image of an irreducible closed subset of `F`. -/
lemma isCatenary_of_isClosed (hX : IsCatenarySpace X) (F : Set X) (hF : IsClosed F) :
    IsCatenarySpace F := by
  let g : IrreducibleCloseds F → IrreducibleCloseds X := fun T_F =>
    ⟨Subtype.val '' T_F.carrier, T_F.isIrreducible'.image _ continuous_subtype_val.continuousOn,
      hF.isClosedEmbedding_subtypeVal.isClosedMap _ T_F.isClosed'⟩
  -- `g` is an order embedding onto the irreducible closeds of `X` contained in `F`, so it
  -- identifies the two codimensions.
  refine isCatenary_of_le_iff g (fun a b => Set.image_subset_image_iff Subtype.val_injective)
    (fun b Z hZ => ?_) hX
  have hZF : Z.carrier ⊆ F := fun x hx => by
    obtain ⟨t, -, rfl⟩ := hZ hx
    exact t.property
  have hirr : IsIrreducible (Subtype.val ⁻¹' Z.carrier : Set F) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := Z.isIrreducible'.nonempty
      exact ⟨⟨y, hZF hy⟩, hy⟩
    rintro U V hU hV ⟨u, hu, huU⟩ ⟨v, hv, hvV⟩
    obtain ⟨W₁, hW₁, rfl⟩ := isOpen_induced_iff.1 hU
    obtain ⟨W₂, hW₂, rfl⟩ := isOpen_induced_iff.1 hV
    obtain ⟨z, hzZ, hz₁, hz₂⟩ := Z.isIrreducible'.2 W₁ W₂ hW₁ hW₂ ⟨u.1, hu, huU⟩ ⟨v.1, hv, hvV⟩
    exact ⟨⟨z, hZF hzZ⟩, hzZ, hz₁, hz₂⟩
  exact ⟨⟨Subtype.val ⁻¹' Z.carrier, hirr, Z.isClosed'.preimage continuous_subtype_val⟩,
    SetLike.ext' (Set.image_preimage_eq_of_subset (by rwa [Subtype.range_val]))⟩

/-- The canonical homeomorphism between `Z`, as a subspace of `X`, and the preimage of `Z` in
the subspace `closure Z`. Both carry the topology induced from `X`. -/
noncomputable def subtypeClosureHomeomorph (Z : Set X) :
    ↥Z ≃ₜ ↥((Subtype.val : ↥(closure Z) → X) ⁻¹' Z) where
  toFun := fun ⟨x, hx⟩ => ⟨⟨x, subset_closure hx⟩, hx⟩
  invFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  continuous_toFun := (continuous_inclusion subset_closure).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- **Stacks 02I2, moreover clause.** Every locally closed subspace of a catenary space is
catenary: a locally closed `Z` is open in `closure Z`, which is a closed — hence catenary —
subspace of `X`, and catenarity passes to open subspaces. -/
@[stacks 02I2 "moreover: locally closed subspace is catenary"]
theorem isCatenary_of_isLocallyClosed (X : Type*) [TopologicalSpace X] (hX : IsCatenarySpace X)
    (Z : Set X) (hZ : IsLocallyClosed Z) : IsCatenarySpace Z :=
  -- ↥Z ≃ₜ ↥(val ⁻¹' Z : Set ↥(closure Z)), so transfer catenarity
  isCatenary_of_homeomorph (subtypeClosureHomeomorph Z).symm <|
    -- Z is locally closed → Z is open in closure Z, and an open subspace of a catenary space is
    -- catenary; closure Z is closed in X, hence catenary
    isCatenary_of_isOpen (isCatenary_of_isClosed hX _ isClosed_closure) _
      hZ.isOpen_preimage_val_closure

end CatenaryTopologicalSpace
