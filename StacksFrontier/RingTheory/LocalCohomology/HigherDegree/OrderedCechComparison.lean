module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.OrderedAlternatingComparison
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CechTupleSections
public import StacksFrontier.RingTheory.Cech.Shrink
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Kernel

/-!
# The Čech complex of the standard covering is the algebraic Čech complex, shifted

Let `A` be a commutative ring, let `f : Fin r → A` be a finite family and let `M` be an
`A`-module. The complement `U = Spec A \ V(f₁, …, f_r)` is covered by the standard opens
`D(f_i)`, and the ordered Čech complex of that covering with coefficients in the sheaf `M̃`
associated to `M` has, in degree `p`, one factor for each strictly increasing tuple
`i₀ < ⋯ < i_p`, namely `Γ(D(f_{i₀} ⋯ f_{i_p}), M̃) = M_{f_{i₀} ⋯ f_{i_p}}`.

The extended alternating Čech complex `C^•(f₁, …, f_r; M)` has, in degree `p + 1`, exactly the
same factors: its index type is the `(p+1)`-element subsets of `Fin r`, and a strictly increasing
tuple of length `p + 1` is the same thing as a `(p+1)`-element subset. The resulting degreewise
identification commutes with the two differentials, giving an isomorphism of cochain complexes

`Č^•(𝒰, M̃) ≅ C^{•+1}(f₁, …, f_r; M)`,

so that in every degree `p ≥ 1` the Čech cohomology of the standard covering is the degree-`p+1`
cohomology of the extended alternating Čech complex. In degree zero the extended Čech complex has
the extra term `M`, which the Čech complex of the covering does not see.

## Main definitions

* `Stacks.LocalCohomology.cechModEquivOfEq` — the identification of two Čech localizations at
  equal sets of indices.
* `Stacks.LocalCohomology.ordIndexEquiv` — strictly increasing tuples of indices are the sets of
  indices of the same size.
* `Stacks.LocalCohomology.orderedCechStandard` — the ordered Čech complex of the standard
  covering of `U = Spec A \ V(f₁, …, f_r)` with coefficients in `M̃`.
* `Stacks.LocalCohomology.ordCochainEquivCechTerm` — the degreewise comparison
  `Č^p(𝒰, M̃) ≅ C^{p+1}(f₁, …, f_r; M)`.
* `Stacks.LocalCohomology.orderedCechHomologyIsoCechComplexHomology` — the comparison on
  cohomology in degrees above zero.

## Main results

* `Stacks.LocalCohomology.cechComponent_cechD` — the component of the differential of the
  extended alternating Čech complex at a set `T` of indices: the alternating sum, over the
  elements `k` of `T`, of the transition maps out of the component at `T \ {k}`.
* `Stacks.LocalCohomology.cechSign_ordIndex` — the Čech sign of the `j`-th entry of a strictly
  increasing tuple is `(-1)^j`.
* `Stacks.LocalCohomology.ordCochainToCechTerm_ordD` — the degreewise comparison commutes with
  the differentials.

## References

* [Stacks Project, Tag 01FI](https://stacks.math.columbia.edu/tag/01FI)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe v u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (M : ModuleCat.{max u v} A)

/-! ### Transport along an equality of index sets -/

/-- The transition map along the identity inclusion is the identity. -/
theorem cechι_le_refl_apply {s : Finset (Fin r)} (x : Cech.cechMod f (M : Type _) s) :
    Cech.cechι f (M : Type _) (le_refl s) x = x := by
  rw [Cech.cechι_rfl]
  rfl

/-- The identification of two Čech localizations at equal sets of indices, by the transition
maps `Cech.cechι` in both directions. -/
def cechModEquivOfEq {s t : Finset (Fin r)} (h : s = t) :
    Cech.cechMod f (M : Type _) s ≃ₗ[A] Cech.cechMod f (M : Type _) t :=
  LinearEquiv.ofLinearMap (Cech.cechι f (M : Type _) h.subset) (Cech.cechι f (M : Type _) h.ge)
    (by rw [Cech.cechι_comp, Cech.cechι_rfl]) (by rw [Cech.cechι_comp, Cech.cechι_rfl])

/-- The identification along the reflexive equality `s = s` is the identity. -/
@[simp] theorem cechModEquivOfEq_rfl {s : Finset (Fin r)}
    (x : Cech.cechMod f (M : Type _) s) : cechModEquivOfEq f M (rfl : s = s) x = x :=
  cechι_le_refl_apply f M x

/-- A transition map absorbs a transport along an equality of index sets. -/
theorem cechι_cechModEquivOfEq {s t w : Finset (Fin r)} (h : s = t) (h' : t ⊆ w)
    (x : Cech.cechMod f (M : Type _) s) :
    Cech.cechι f (M : Type _) h' (cechModEquivOfEq f M h x) =
      Cech.cechι f (M : Type _) (h.subset.trans h') x :=
  Cech.cechι_cechι f (M : Type _) h.subset h' x

/-! ### The differential of the extended alternating Čech complex, in components -/

/-- Erasing an element from a `(p+1)`-element set of indices leaves a `p`-element set. -/
theorem card_erase_of_card_succ {p : ℕ} (T : {t : Finset (Fin r) // t.card = p + 1})
    {k : Fin r} (hk : k ∈ T.1) : (T.1.erase k).card = p := by
  rw [Finset.card_erase_of_mem hk, T.2, Nat.add_sub_cancel]

/-- The component at a `(p+1)`-element set `T` of the differential of `x` in the extended
alternating Čech complex is the sum, over the elements `k` of `T`, of the transition map applied
to the component of `x` at `T \ {k}`, with the Čech sign of `k` in `T`. -/
theorem cechComponent_cechD (p : ℕ) (x : Cech.cechTerm f (M : Type _) p)
    (T : {t : Finset (Fin r) // t.card = p + 1}) :
    cechComponent f M (p + 1) T (Cech.cechD f (M : Type _) p x) =
      ∑ k ∈ T.1.attach, Cech.cechSign T.1 k.1 •
        Cech.cechι f (M : Type _) (Finset.erase_subset k.1 T.1)
          (cechComponent f M p ⟨T.1.erase k.1, card_erase_of_card_succ T k.2⟩ x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, zsmul_zero, Finset.sum_const_zero]
  | of s y =>
      rw [← DirectSum.lof_eq_of A, Cech.cechD_lof, map_sum]
      simp only [map_zsmul]
      by_cases hsub : s.1 ⊆ T.1
      · have hne : s.1 ≠ T.1 := fun h => by
          have := s.2; rw [h, T.2] at this; omega
        obtain ⟨k₀, hk₀T, hk₀s⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hsub hne)
        have hins : insert k₀ s.1 = T.1 :=
          Finset.eq_of_subset_of_card_le (Finset.insert_subset hk₀T hsub)
            (by rw [Finset.card_insert_of_notMem hk₀s, s.2, T.2])
        have hers : T.1.erase k₀ = s.1 := by
          rw [← hins, Finset.erase_insert hk₀s]
        rw [Finset.sum_eq_single_of_mem (⟨k₀, by simpa using hk₀s⟩ :
            {i // i ∈ s.1ᶜ}) (Finset.mem_attach _ _) ?_,
          Finset.sum_eq_single_of_mem (⟨k₀, hk₀T⟩ : {i // i ∈ T.1})
            (Finset.mem_attach _ _) ?_]
        · have hsign : Cech.cechSign s.1 k₀ = Cech.cechSign T.1 k₀ := by
            rw [← hers]; exact Cech.cechSign_erase T.1 k₀
          rw [cechComponent_lof_of_eq f M _ _ hins, cechComponent_lof_of_eq f M _ _ hers.symm,
            Cech.cechι_cechι, Cech.cechι_cechι, hsign]
        · intro b _ hb
          have hbne : s.1 ≠ T.1.erase b.1 := by
            intro hbs
            refine hb (Subtype.ext ?_)
            have hk₀ : k₀ ∉ T.1.erase b.1 := hbs ▸ hk₀s
            by_contra hne2
            exact hk₀ (Finset.mem_erase.2 ⟨fun h => hne2 h.symm, hk₀T⟩)
          rw [cechComponent_lof_of_ne f M _ _ hbne, map_zero, zsmul_zero]
        · intro b _ hb
          have hb' : b.1 ∉ s.1 := Finset.mem_compl.1 b.2
          have hbne : insert b.1 s.1 ≠ T.1 := by
            intro hbT
            refine hb (Subtype.ext ?_)
            have hmem : k₀ ∈ insert b.1 s.1 := hbT ▸ hk₀T
            rcases Finset.mem_insert.1 hmem with h | h
            · exact h.symm
            · exact absurd h hk₀s
          rw [cechComponent_lof_of_ne f M _ _ hbne, zsmul_zero]
      · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
        · intro k _
          have hbne : s.1 ≠ T.1.erase k.1 := fun hs =>
            hsub (hs ▸ Finset.erase_subset k.1 T.1)
          rw [cechComponent_lof_of_ne f M _ _ hbne, map_zero, zsmul_zero]
        · intro i _
          have hbne : insert i.1 s.1 ≠ T.1 := fun hi =>
            hsub (hi ▸ Finset.subset_insert i.1 s.1)
          rw [cechComponent_lof_of_ne f M _ _ hbne, zsmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, zsmul_add, Finset.sum_add_distrib]

/-! ### Strictly increasing tuples and sets of indices -/

/-- The entries of a strictly increasing tuple of indices, as indices of `Fin r`, are strictly
increasing. -/
private theorem strictMono_down_ordIndex {p : ℕ}
    (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    StrictMono (fun k => (σ.1 k).down) := fun a b hab => by
  simpa using σ.2 hab

/-- The set of indices of a strictly increasing tuple has the expected cardinality. -/
theorem card_cechTupleIndices_ordIndex {p : ℕ}
    (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    (cechTupleIndices ULift.down σ.1).card = p + 1 := by
  rw [cechTupleIndices, Finset.card_image_of_injective _ (strictMono_down_ordIndex σ).injective,
    Finset.card_univ, Fintype.card_fin]

/-- Strictly increasing tuples of indices are the sets of indices of the same size: a tuple goes
to the set of its entries, a set to the increasing enumeration of its elements. -/
def ordIndexEquiv (p : ℕ) :
    CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p ≃ {t : Finset (Fin r) // t.card = p + 1} where
  toFun σ := ⟨cechTupleIndices ULift.down σ.1, card_cechTupleIndices_ordIndex σ⟩
  invFun t := ⟨fun k => ULift.up (t.1.orderEmbOfFin t.2 k), fun a b hab => by
    simpa using (t.1.orderEmbOfFin t.2).strictMono hab⟩
  left_inv σ := Subtype.ext <| funext fun k => ULift.ext <|
    congrFun (Finset.orderEmbOfFin_unique (s := cechTupleIndices ULift.down σ.1)
      (card_cechTupleIndices_ordIndex σ) (f := fun k => (σ.1 k).down)
      (fun x => (mem_cechTupleIndices ULift.down σ.1 _).2 ⟨x, rfl⟩)
      (fun a b hab => by simpa using σ.2 hab)).symm k
  right_inv t := by
    apply Subtype.ext
    apply Finset.coe_injective
    change ((Finset.image (fun k => t.1.orderEmbOfFin t.2 k) Finset.univ : Finset (Fin r)) :
      Set (Fin r)) = (t.1 : Set (Fin r))
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact Finset.range_orderEmbOfFin t.1 t.2

/-- Omitting the `j`-th entry of a strictly increasing tuple erases the `j`-th smallest index
from its set of indices. -/
theorem cechTupleIndices_omit {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) (p + 1))
    (j : Fin (p + 2)) :
    cechTupleIndices ULift.down (σ.1 ∘ j.succAbove) =
      (cechTupleIndices ULift.down σ.1).erase (σ.1 j).down := by
  have hinj := (strictMono_down_ordIndex σ).injective
  ext a
  simp only [cechTupleIndices, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase,
    Function.comp_apply]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne j k (hinj h), ⟨j.succAbove k, rfl⟩⟩
  · rintro ⟨hne, k, rfl⟩
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (x := k) (y := j) fun h => hne (by rw [h])
    exact ⟨z, by rw [hz]⟩

/-- The Čech sign of the `j`-th entry of a strictly increasing tuple in its set of indices is
`(-1)^j`. -/
theorem cechSign_ordIndex {p : ℕ} (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p)
    (j : Fin (p + 1)) :
    Cech.cechSign (cechTupleIndices ULift.down σ.1) (σ.1 j).down = (-1 : ℤ) ^ (j : ℕ) := by
  have hmono := strictMono_down_ordIndex σ
  have hfilter : (cechTupleIndices ULift.down σ.1).filter (· < (σ.1 j).down) =
      Finset.image (fun k => (σ.1 k).down) (Finset.univ.filter (fun i => i < j)) := by
    ext a
    simp only [cechTupleIndices, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, rfl⟩, hlt⟩
      exact ⟨k, hmono.lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, hmono hk⟩
  rw [Cech.cechSign, hfilter, Finset.card_image_of_injective _ hmono.injective,
    show (Finset.univ.filter (fun i : Fin (p + 1) => i < j)) = Finset.Iio j from by ext i; simp,
    Fin.card_Iio]


/-! ### Moving a component along an equality of index sets -/

/-- Two components at index sets that are equal, followed by transition maps into a common set,
agree. -/
theorem cechι_cechComponent_congr (q : ℕ)
    {t t' : {t : Finset (Fin r) // t.card = q}} (h : t.1 = t'.1)
    {w : Finset (Fin r)} (hw : t.1 ⊆ w) (hw' : t'.1 ⊆ w)
    (x : Cech.cechTerm f (M : Type _) q) :
    Cech.cechι f (M : Type _) hw (cechComponent f M q t x) =
      Cech.cechι f (M : Type _) hw' (cechComponent f M q t' x) := by
  obtain rfl : t = t' := Subtype.ext h
  rfl

/-- The set of indices of a face of a strictly increasing tuple is contained in the set of
indices of the tuple. -/
theorem ordIndexEquiv_omit_subset {p : ℕ}
    (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) (p + 1)) (j : Fin (p + 2)) :
    (ordIndexEquiv p ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩).1 ⊆
      (ordIndexEquiv (p + 1) σ).1 :=
  cechTupleIndices_comp_subset ULift.down σ.1 j.succAbove

/-- The component of the differential of the extended alternating Čech complex at the set of
indices of a strictly increasing tuple `σ` is the alternating sum, over the positions `j`, of the
transition maps applied to the components at the faces of `σ`. -/
theorem cechComponent_cechD_ordIndexEquiv (p : ℕ) (x : Cech.cechTerm f (M : Type _) (p + 1))
    (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) (p + 1)) :
    cechComponent f M (p + 2) (ordIndexEquiv (p + 1) σ) (Cech.cechD f (M : Type _) (p + 1) x) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Cech.cechι f (M : Type _) (ordIndexEquiv_omit_subset σ j)
          (cechComponent f M (p + 1) (ordIndexEquiv p ⟨σ.1 ∘ j.succAbove,
            CechCochains.strictMono_omit σ.2 j⟩) x) := by
  have hmem : ∀ j : Fin (p + 2), (σ.1 j).down ∈ (ordIndexEquiv (p + 1) σ).1 := fun j =>
    (mem_cechTupleIndices ULift.down σ.1 _).2 ⟨j, rfl⟩
  refine (cechComponent_cechD f M (p + 1) x (ordIndexEquiv (p + 1) σ)).trans
    (Finset.sum_bij (fun (j : Fin (p + 2)) _ => (⟨(σ.1 j).down, hmem j⟩ :
      {a // a ∈ (ordIndexEquiv (p + 1) σ).1})) (fun j _ => Finset.mem_attach _ _)
      (fun j₁ _ j₂ _ h => ?_) (fun b _ => ?_) (fun j _ => ?_)).symm
  · exact (strictMono_down_ordIndex σ).injective (congrArg Subtype.val h)
  · obtain ⟨j, hj⟩ := (mem_cechTupleIndices ULift.down σ.1 b.1).1 b.2
    exact ⟨j, Finset.mem_univ _, Subtype.ext hj⟩
  · have key := cechι_cechComponent_congr f M (p + 1)
      (t := ordIndexEquiv p ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩)
      (t' := ⟨(ordIndexEquiv (p + 1) σ).1.erase (σ.1 j).down,
        card_erase_of_card_succ (ordIndexEquiv (p + 1) σ) (hmem j)⟩)
      (cechTupleIndices_omit σ j) (ordIndexEquiv_omit_subset σ j)
      (Finset.erase_subset _ _) x
    exact congrArg₂ (fun (z : ℤ) (y : Cech.cechMod f (M : Type _) (ordIndexEquiv (p + 1) σ).1) =>
      z • y) (cechSign_ordIndex σ j).symm key

/-! ### The ordered Čech complex of the standard covering -/

/-- The ordered Čech complex of the standard covering of `U = Spec A \ V(f₁, …, f_r)` by the
basic opens `D(f_i)`, with coefficients in the sheaf associated to `M`. -/
abbrev orderedCechStandard : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  Stacks.Cech.orderedCechComplex (cechStandardOpen f) (associatedAbPresheaf M)

/-- The degreewise comparison as a map: an ordered Čech cochain of the standard covering is
sent to the sum of its values, each placed in the summand of `C^{p+1}(f₁, …, f_r; M)` indexed by
the set of indices of the corresponding strictly increasing tuple. -/
def ordCochainToCechTerm (p : ℕ) (s : (orderedCechStandard f M).X p) :
    Cech.cechTerm f (M : Type _) (p + 1) :=
  ∑ σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p,
    DirectSum.lof A {t : Finset (Fin r) // t.card = p + 1}
        (fun t => Cech.cechMod f (M : Type _) t.1) (ordIndexEquiv p σ)
      (cechStandardTupleSectionsEquiv f M σ.1 (s σ))

/-- The component of the comparison at the set of indices of a tuple is the value of the cochain
at that tuple. -/
theorem cechComponent_ordCochainToCechTerm (p : ℕ) (s : (orderedCechStandard f M).X p)
    (σ₀ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) p) :
    cechComponent f M (p + 1) (ordIndexEquiv p σ₀) (ordCochainToCechTerm f M p s) =
      cechStandardTupleSectionsEquiv f M σ₀.1 (s σ₀) :=
  (map_sum (cechComponent f M (p + 1) (ordIndexEquiv p σ₀)) _ Finset.univ).trans
    ((Finset.sum_eq_single_of_mem σ₀ (Finset.mem_univ _) (fun _ _ hτ =>
      cechComponent_lof_of_ne f M _ _
        (fun h => hτ ((ordIndexEquiv p).injective (Subtype.ext h))) _)).trans
      ((cechComponent_lof_of_eq f M _ _ rfl _).trans (cechι_le_refl_apply f M _)))

/-- The degreewise comparison `Č^p(𝒰, M̃) ≅ C^{p+1}(f₁, …, f_r; M)`: the ordered Čech
cochains of the standard covering in degree `p` are the degree-`p+1` term of the extended
alternating Čech complex. -/
def ordCochainEquivCechTerm (p : ℕ) :
    ((orderedCechStandard f M).X p) ≃+ Cech.cechTerm f (M : Type _) (p + 1) :=
  AddEquiv.mk'
    { toFun := ordCochainToCechTerm f M p
      invFun := fun x σ => (cechStandardTupleSectionsEquiv f M σ.1).symm
        (cechComponent f M (p + 1) (ordIndexEquiv p σ) x)
      left_inv := fun s => by
        funext σ
        exact (congrArg (cechStandardTupleSectionsEquiv f M σ.1).symm
            (cechComponent_ordCochainToCechTerm f M p s σ)).trans
          ((cechStandardTupleSectionsEquiv f M σ.1).symm_apply_apply (s σ))
      right_inv := fun x => by
        refine DirectSum.ext fun t => ?_
        obtain ⟨σ, rfl⟩ : ∃ σ, ordIndexEquiv p σ = t :=
          ⟨(ordIndexEquiv p).symm t, (ordIndexEquiv p).apply_symm_apply t⟩
        exact (cechComponent_ordCochainToCechTerm f M p _ σ).trans
          ((cechStandardTupleSectionsEquiv f M σ.1).apply_symm_apply _) }
    (fun s t => by
      refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) Finset.sum_add_distrib
      exact (congrArg (DirectSum.lof A {t : Finset (Fin r) // t.card = p + 1}
          (fun t => Cech.cechMod f (M : Type _) t.1) (ordIndexEquiv p σ))
        (map_add (cechStandardTupleSectionsEquiv f M σ.1) (s σ) (t σ))).trans
        (map_add _ _ _))

/-! ### The comparison is compatible with the differentials -/

/-- The ordered Čech differential of the standard covering, under the comparison of the sections
with the Čech localizations, is the alternating sum of the transition maps. -/
theorem cechStandardTupleSectionsEquiv_ordD (p : ℕ) (s : (orderedCechStandard f M).X p)
    (σ : CechCochains.OrdIndex (I := ULift.{u} (Fin r)) (p + 1)) :
    cechStandardTupleSectionsEquiv f M σ.1
        (CechCochains.ordD (cechStandardOpen f) (associatedAbPresheaf M) p s σ) =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        Cech.cechι f (M : Type _) (cechTupleIndices_comp_subset ULift.down σ.1 j.succAbove)
          (cechStandardTupleSectionsEquiv f M (σ.1 ∘ j.succAbove)
            (s ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩)) := by
  have hd : CechCochains.ordD (cechStandardOpen f) (associatedAbPresheaf M) p s σ =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        CechCochains.restr (associatedAbPresheaf M)
          (CechCochains.inter_le_omit (cechStandardOpen f) σ.1 j)
          (s ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩) := rfl
  refine (congrArg (cechStandardTupleSectionsEquiv f M σ.1) hd).trans ?_
  refine (map_sum (cechStandardTupleSectionsEquiv f M σ.1) _ Finset.univ).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (map_zsmul (cechStandardTupleSectionsEquiv f M σ.1) _ _).trans ?_
  exact congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) • z)
    (cechTupleSectionsEquiv_restrict f ULift.down M (cechStandardOpen_eq_basicOpen f)
      (cechTupleIndices_comp_subset ULift.down σ.1 j.succAbove) _)

/-- The degreewise comparison `Stacks.LocalCohomology.ordCochainToCechTerm` commutes with the
Čech differential of the covering and the differential of the extended alternating Čech
complex. -/
theorem ordCochainToCechTerm_ordD (p : ℕ) (s : (orderedCechStandard f M).X p) :
    ordCochainToCechTerm f M (p + 1)
        (CechCochains.ordD (cechStandardOpen f) (associatedAbPresheaf M) p s) =
      Cech.cechD f (M : Type _) (p + 1) (ordCochainToCechTerm f M p s) := by
  refine DirectSum.ext fun T => ?_
  obtain ⟨σ, rfl⟩ := (ordIndexEquiv (p + 1)).surjective T
  refine ((cechComponent_ordCochainToCechTerm f M (p + 1) _ σ).trans
    ((cechStandardTupleSectionsEquiv_ordD f M p s σ).trans ?_)).trans
      (cechComponent_cechD_ordIndexEquiv f M p (ordCochainToCechTerm f M p s) σ).symm
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (fun z => ((-1 : ℤ) ^ (j : ℕ)) •
      Cech.cechι f (M : Type _) (ordIndexEquiv_omit_subset σ j) z)
    (cechComponent_ordCochainToCechTerm f M p s
      ⟨σ.1 ∘ j.succAbove, CechCochains.strictMono_omit σ.2 j⟩).symm


/-! ### The comparison on cohomology -/

/-- The degreewise comparison, as an isomorphism of the terms of the two complexes: the
degree-`p` term of the ordered Čech complex of the standard covering and the degree-`p+1` term
of the extended alternating Čech complex, the latter read as an abelian group. -/
def ordCechXIso (p : ℕ) :
    (orderedCechStandard f M).X p ≅
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).obj
        ((_root_.Cech.cechComplex f (M : Type _)).X (p + 1)) :=
  (ordCochainEquivCechTerm f M p).toAddCommGrpIso

/-- The degreewise comparison `Stacks.LocalCohomology.ordCechXIso` commutes with the
differentials, as a square of morphisms of abelian groups. -/
theorem ordCechXIso_comm (p : ℕ) :
    (ordCechXIso f M p).hom ≫
        (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).map
          ((_root_.Cech.cechComplex f (M : Type _)).d (p + 1) (p + 2)) =
      (orderedCechStandard f M).d p (p + 1) ≫ (ordCechXIso f M (p + 1)).hom := by
  rw [_root_.Cech.cechComplex_d f (M : Type _) (p + 1),
    Stacks.Cech.orderedCechComplex_d (cechStandardOpen f) (associatedAbPresheaf M) p]
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => (ordCochainToCechTerm_ordD f M p s).symm)

/-- The three-term truncation of the ordered Čech complex of the standard covering around degree
`q + 1` is the three-term truncation of the extended alternating Čech complex around degree
`q + 2`. -/
def ordCechShortComplexIso (q : ℕ) :
    (orderedCechStandard f M).sc' q (q + 1) (q + 2) ≅
      ((_root_.Cech.cechComplex f (M : Type _)).sc' (q + 1) (q + 2) (q + 3)).map
        (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}) :=
  ShortComplex.isoMk (ordCechXIso f M q) (ordCechXIso f M (q + 1)) (ordCechXIso f M (q + 2))
    (ordCechXIso_comm f M q) (ordCechXIso_comm f M (q + 1))

/-- In every degree `q + 1 ≥ 1` the degree-`q+1` cohomology of the ordered Čech complex of the
covering of `U = Spec A \ V(f₁, …, f_r)` by the standard opens is the degree-`q+2` cohomology of
`C^•(f₁, …, f_r; M)`, read as an abelian group. -/
def orderedCechHomologyIsoCechComplexHomology (q : ℕ) :
    (orderedCechStandard f M).homology (q + 1) ≅
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).obj
        ((_root_.Cech.cechComplex f (M : Type _)).homology (q + 2)) :=
  (orderedCechStandard f M).homologyIsoSc' q (q + 1) (q + 2) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (ordCechShortComplexIso f M q) ≪≫
    ShortComplex.mapHomologyIso _ _ ≪≫
    (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}).mapIso
      (((_root_.Cech.cechComplex f (M : Type _)).homologyIsoSc' (q + 1) (q + 2) (q + 3)
        (by simp) (by simp)).symm)

end Stacks.LocalCohomology

end
