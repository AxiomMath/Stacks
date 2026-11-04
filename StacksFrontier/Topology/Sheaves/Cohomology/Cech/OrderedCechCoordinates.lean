module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingCochainGroups
public import StacksFrontier.RingTheory.Cech.Reindex
public import StacksFrontier.RingTheory.Cech.OrderedIndexing

/-!
# Ordered Čech cochains read in an algebraic Čech complex

Let `U : I → Opens X` be a family of opens indexed by a finite linearly ordered set `I ≃o Fin r`
and `ℱ` an abelian presheaf on `X`. Suppose that the sections of `ℱ` over every finite
intersection `U_{i₀} ∩ ⋯ ∩ U_{i_p}` are identified, injectively and compatibly with restriction,
with a subgroup `Pos_S` of a localization `M_{f_S}` of a module `M` over a ring `A`, where
`S = {i₀, …, i_p}` and `f_S = ∏_{k ∈ S} f_k` for a family `f : Fin r → A`. Then the ordered Čech
complex of `ℱ` is identified with the subcomplex of the extended Čech complex `C^•(f; M)` of
`Cech.cechComplex` whose components lie in the `Pos_S`, shifted by one. So exactness of that
subcomplex in a degree `q + 2` gives exactness of the ordered Čech complex in degree `q + 1`.

This is how a Čech computation on a scheme covered by standard opens is reduced to commutative
algebra.

## Main definitions

* `CechCochains.Coordinates.supp`: the set of values of an index tuple, read in `Fin r`.
* `CechCochains.Coordinates.tup`: the increasing tuple enumerating a set of indices.
* `CechCochains.Coordinates.toCechTerm`: the comparison map from the ordered Čech cochains of `ℱ`
  to the terms of `C^•(f; M)`.

## Main results

* `CechCochains.Coordinates.toCechTerm_ordD`: the comparison is a map of complexes.
* `CechCochains.Coordinates.exists_ordD_eq_of_exists_cechD_eq`: **exactness of the subcomplex
  cut out by the `Pos_S` gives exactness of the ordered Čech complex.**

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace CechCochains.Coordinates

open ExtendedAlternatingCech (Idx)

variable {X : TopCat} {I : Type*} [LinearOrder I] {r : ℕ} (e : I ≃o Fin r)

/-! ### Index tuples and index sets -/

/-- The set of values of an index tuple, read in `Fin r`. -/
def supp {p : ℕ} (i : Fin p → I) : Finset (Fin r) := Finset.univ.image (e ∘ i)

/-- A strictly increasing tuple of length `p + 1` takes `p + 1` distinct values. -/
theorem card_supp {p : ℕ} {i : Fin (p + 1) → I} (hi : StrictMono i) :
    (supp e i).card = p + 1 := by
  rw [supp, Finset.card_image_of_injective _ (e.injective.comp hi.injective), Finset.card_univ,
    Fintype.card_fin]

/-- The increasing tuple enumerating a set of `p + 1` indices. -/
def tup {p : ℕ} (s : Idx r (p + 1)) : OrdIndex (I := I) p :=
  ⟨e.symm ∘ s.1.orderEmbOfFin s.2, e.symm.strictMono.comp (s.1.orderEmbOfFin s.2).strictMono⟩

/-- The set of values of the enumeration of a set of indices is that set. -/
theorem supp_tup {p : ℕ} (s : Idx r (p + 1)) : supp e (tup e s).1 = s.1 := by
  apply Finset.coe_injective
  rw [supp, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  change Set.range (e ∘ e.symm ∘ s.1.orderEmbOfFin s.2) = _
  rw [← Function.comp_assoc, show (e : I → Fin r) ∘ e.symm = id from funext e.apply_symm_apply,
    Function.id_comp, Finset.range_orderEmbOfFin]

/-- An increasing tuple is the enumeration of its set of values. -/
theorem tup_supp {p : ℕ} (i : OrdIndex (I := I) p) :
    tup e ⟨supp e i.1, card_supp e i.2⟩ = i := by
  refine Subtype.ext (funext fun k => ?_)
  have h := Finset.orderEmbOfFin_unique (card_supp e i.2)
    (f := e ∘ i.1) (fun y => Finset.mem_image.2 ⟨y, Finset.mem_univ y, rfl⟩)
    (e.strictMono.comp i.2)
  change e.symm ((supp e i.1).orderEmbOfFin (card_supp e i.2) k) = i.1 k
  rw [← h]
  exact e.symm_apply_apply _

/-- Omitting a position of a tuple shrinks its set of values. -/
theorem supp_omit_subset {p : ℕ} (i : Fin (p + 1) → I) (j : Fin (p + 1)) :
    supp e (i ∘ j.succAbove) ⊆ supp e i := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_image.2 ⟨j.succAbove k, Finset.mem_univ _, rfl⟩

/-- **Deleting the `j`-th smallest index of a set and re-enumerating omits the `j`-th position
of the enumeration.** -/
theorem tup_erase {p : ℕ} (t : Idx r (p + 2)) (j : Fin (p + 2)) :
    tup e (Idx.erase t ⟨t.1.orderEmbOfFin t.2 j, t.1.orderEmbOfFin_mem t.2 j⟩) =
      ⟨(tup e t).1 ∘ j.succAbove, strictMono_omit (tup e t).2 j⟩ := by
  refine Subtype.ext (funext fun k => ?_)
  exact congrArg e.symm (congrFun (Cech.orderEmbOfFin_erase t.1 t.2 j _) k)

/-! ### The comparison map -/

variable (U : I → Opens X) (ℱ : TopCat.Presheaf Ab X)
  {A : Type*} [CommRing A] (f : Fin r → A) (M : Type*) [AddCommGroup M] [Module A M]
  (Ψ : ∀ (p : ℕ) (i : OrdIndex (I := I) p),
    (ℱ.obj (op (inter U i.1)) : Type _) →+ Cech.cechMod f M (supp e i.1))

/-- **The comparison map** from the degree-`p` ordered Čech cochains of `ℱ` to the degree-`p + 1`
term of `C^•(f; M)`: the component at a set `S` of `p + 1` indices is the coordinate of the value
of the cochain at the enumeration of `S`. -/
def toCechTerm (p : ℕ) : OrdCochain U ℱ p →+ Cech.cechTerm f M (p + 1) where
  toFun c := DFinsupp.equivFunOnFintype.symm fun s =>
    Cech.cechι f M (supp_tup e s).le (Ψ p (tup e s) (c (tup e s)))
  map_zero' := by
    ext s
    change Cech.cechι f M (supp_tup e s).le (Ψ p _ 0) = 0
    rw [map_zero, map_zero]
  map_add' c c' := by
    ext s
    change Cech.cechι f M (supp_tup e s).le (Ψ p _ (c _ + c' _)) =
      Cech.cechι f M (supp_tup e s).le (Ψ p _ (c _)) +
        Cech.cechι f M (supp_tup e s).le (Ψ p _ (c' _))
    rw [map_add, map_add]

/-- The component of `toCechTerm` at a set `s` of indices is the coordinate of the value of the
cochain at the enumeration of `s`, pushed to the localization at `s`. -/
theorem toCechTerm_apply (p : ℕ) (c : OrdCochain U ℱ p) (s : Idx r (p + 1)) :
    toCechTerm e U ℱ f M Ψ p c s =
      Cech.cechι f M (supp_tup e s).le (Ψ p (tup e s) (c (tup e s))) :=
  rfl

/-- The localized coordinate of a cochain at a tuple, pushed to a set containing its values,
depends on the tuple only through its value. -/
theorem cechι_Ψ_congr {p : ℕ} (c : OrdCochain U ℱ p) {i i' : OrdIndex (I := I) p} (h : i = i')
    {T : Finset (Fin r)} (hT : supp e i.1 ⊆ T) (hT' : supp e i'.1 ⊆ T) :
    Cech.cechι f M hT (Ψ p i (c i)) = Cech.cechι f M hT' (Ψ p i' (c i')) := by
  subst h; rfl

variable {e U ℱ f M Ψ}

/-- **The comparison map is a map of complexes**, when the coordinates are compatible with
restriction: the alternating sum over the omitted positions of a tuple is the signed sum over
the elements of its set of values. -/
theorem toCechTerm_ordD
    (hnat : ∀ (p : ℕ) (i : OrdIndex (I := I) (p + 1)) (j : Fin (p + 2))
      (x : (ℱ.obj (op (inter U (i.1 ∘ j.succAbove))) : Type _)),
      Ψ (p + 1) i (restr ℱ (inter_le_omit U i.1 j) x) =
        Cech.cechι f M (supp_omit_subset e i.1 j)
          (Ψ p ⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ x))
    (p : ℕ) (c : OrdCochain U ℱ p) :
    toCechTerm e U ℱ f M Ψ (p + 1) (ordD U ℱ p c) =
      Cech.cechD f M (p + 1) (toCechTerm e U ℱ f M Ψ p c) := by
  ext t
  rw [Cech.cechD_component, toCechTerm_apply]
  change Cech.cechι f M (supp_tup e t).le (Ψ (p + 1) (tup e t)
    (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      restr ℱ (inter_le_omit U (tup e t).1 j)
        (c ⟨(tup e t).1 ∘ j.succAbove, strictMono_omit (tup e t).2 j⟩))) = _
  rw [map_sum, map_sum]
  -- reindex the sum over the elements of `t` by their positions
  have hbij : ∀ k : Fin (p + 2), t.1.orderEmbOfFin t.2 k ∈ t.1 :=
    fun k => t.1.orderEmbOfFin_mem t.2 k
  rw [← Equiv.sum_comp (t.1.orderIsoOfFin t.2).toEquiv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, hnat, Cech.cechι_cechι]
  have hk : ((t.1.orderIsoOfFin t.2).toEquiv j : t.1) =
      ⟨t.1.orderEmbOfFin t.2 j, hbij j⟩ := rfl
  rw [hk, Cech.cechSign_orderEmbOfFin, toCechTerm_apply, Cech.cechι_cechι]
  congr 1
  exact cechι_Ψ_congr e U ℱ f M Ψ c (tup_erase e t j).symm _ _

/-- The component of `toCechTerm` at the set of values of a tuple is the coordinate of the value of
the cochain at that tuple. -/
private theorem toCechTerm_apply_supp (p : ℕ) (c : OrdCochain U ℱ p) (i : OrdIndex (I := I) p) :
    toCechTerm e U ℱ f M Ψ p c ⟨supp e i.1, card_supp e i.2⟩ = Ψ p i (c i) := by
  rw [toCechTerm_apply, cechι_Ψ_congr e U ℱ f M Ψ c (tup_supp e i) _ subset_rfl, Cech.cechι_rfl]
  rfl

/-- The comparison map is injective when the coordinates are. -/
theorem toCechTerm_injective
    (hinj : ∀ (p : ℕ) (i : OrdIndex (I := I) p), Function.Injective (Ψ p i))
    (p : ℕ) : Function.Injective (toCechTerm e U ℱ f M Ψ p) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  have h := DFunLike.congr_fun hc ⟨supp e i.1, card_supp e i.2⟩
  rw [toCechTerm_apply_supp, DFinsupp.zero_apply] at h
  exact (map_eq_zero_iff _ (hinj p i)).1 h

/-- A component of a cochain of `C^•(f; M)`, pushed along an equality of index sets. -/
theorem cechι_apply_congr {p : ℕ} (w : Cech.cechTerm f M p) {s s' : Idx r p} (h : s' = s)
    (hss : s'.1 ⊆ s.1) : Cech.cechι f M hss (w s') = w s := by
  subst h
  rw [Cech.cechι_rfl]
  rfl

/-- **Exactness of the subcomplex of `C^•(f; M)` cut out by the `Pos_S` gives exactness of the
ordered Čech complex**, as soon as the coordinates of the sections of `ℱ` are injective, compatible
with restriction, and have image exactly `Pos_S`. Degree `q + 1` of the ordered complex is degree
`q + 2` of `C^•(f; M)`. -/
theorem exists_ordD_eq_of_exists_cechD_eq
    (Pos : ∀ s : Finset (Fin r), AddSubgroup (Cech.cechMod f M s))
    (hnat : ∀ (p : ℕ) (i : OrdIndex (I := I) (p + 1)) (j : Fin (p + 2))
      (x : (ℱ.obj (op (inter U (i.1 ∘ j.succAbove))) : Type _)),
      Ψ (p + 1) i (restr ℱ (inter_le_omit U i.1 j) x) =
        Cech.cechι f M (supp_omit_subset e i.1 j)
          (Ψ p ⟨i.1 ∘ j.succAbove, strictMono_omit i.2 j⟩ x))
    (hinj : ∀ (p : ℕ) (i : OrdIndex (I := I) p), Function.Injective (Ψ p i))
    (hpos : ∀ (p : ℕ) (i : OrdIndex (I := I) p) x, Ψ p i x ∈ Pos (supp e i.1))
    (hsurj : ∀ (p : ℕ) (i : OrdIndex (I := I) p) z, z ∈ Pos (supp e i.1) → ∃ x, Ψ p i x = z)
    (hι : ∀ {s t : Finset (Fin r)} (h : s ⊆ t) z, z ∈ Pos s → Cech.cechι f M h z ∈ Pos t)
    (q : ℕ)
    (hex : ∀ z : Cech.cechTerm f M (q + 2), (∀ s, z s ∈ Pos s.1) →
      Cech.cechD f M (q + 2) z = 0 →
        ∃ w : Cech.cechTerm f M (q + 1), (∀ s, w s ∈ Pos s.1) ∧ Cech.cechD f M (q + 1) w = z)
    (c : OrdCochain U ℱ (q + 1)) (hc : ordD U ℱ (q + 1) c = 0) :
    ∃ b, ordD U ℱ q b = c := by
  have hz : Cech.cechD f M (q + 1 + 1) (toCechTerm e U ℱ f M Ψ (q + 1) c) = 0 := by
    rw [← toCechTerm_ordD hnat (q + 1) c, hc, map_zero]
  have hzpos : ∀ s, toCechTerm e U ℱ f M Ψ (q + 1) c s ∈ Pos s.1 := fun s => by
    rw [toCechTerm_apply]
    exact hι _ _ (hpos _ _ _)
  obtain ⟨w, hw, hdw⟩ := hex _ hzpos hz
  obtain ⟨b, hb⟩ : ∃ b : OrdCochain U ℱ q,
      ∀ i, Ψ q i (b i) = w ⟨supp e i.1, card_supp e i.2⟩ := by
    choose b hb using fun i : OrdIndex (I := I) q =>
      hsurj q i _ (hw ⟨supp e i.1, card_supp e i.2⟩)
    exact ⟨b, hb⟩
  have hbw : toCechTerm e U ℱ f M Ψ q b = w := by
    ext s
    rw [toCechTerm_apply, hb]
    exact cechι_apply_congr (s' := ⟨supp e (tup e s).1, card_supp e (tup e s).2⟩) w
      (Subtype.ext (supp_tup e s)) (supp_tup e s).le
  refine ⟨b, toCechTerm_injective hinj (q + 1) ?_⟩
  rw [toCechTerm_ordD hnat, hbw, hdw]

end CechCochains.Coordinates

end
