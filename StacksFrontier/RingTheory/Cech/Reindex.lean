module

public import StacksFrontier.RingTheory.Cech.Extended

/-!
# Restricting the Čech complex to a subfamily of the generators

Let `R` be a commutative ring, `M` an `R`-module, `g : Fin s → R` a family of elements and
`e : Fin r ↪o Fin s` an order embedding with `g ∘ e = f`. Then `f` is a subfamily of `g`, and for
every `S ⊆ Fin r` the two localizing submonoids agree,
`Cech.cechSub g (S.map e) = Cech.cechSub f S`, because the two products have the same factors.
Reading off the components of `C^•(g; M)` indexed by sets of the form `S.map e` therefore gives a
map of complexes `C^•(g; M) ⟶ C^•(f; M)`.

This is the comparison that makes a construction on `C^•(f; M)` independent of the chosen
generating family: two families `f` and `g` of generators of the same ideal are both subfamilies
of `Fin.append f g`, so a construction natural for subfamily restriction takes the same value on
both.

Degreewise the map is a projection onto a subfamily of summands, so the only thing to check is
that it commutes with the differential, and for that one needs the component formula for the
Čech differential: the `T`-component of `d x` is the alternating sum, over the elements `k` of
`T`, of the localization maps applied to the components `x_{T ∖ k}`.

## Main definitions

* `Cech.idxErase` — the index set `T` with one of its elements removed.
* `Cech.reindexIdx` — the index map `S ↦ S.map e` on `p`-element subsets.
* `Cech.reindexLoc` — the identification `M_{∏_{S.map e} g} ≃ₗ M_{∏_S f}` of the corresponding
  localizations.
* `Cech.cechTermRestrict` — the degreewise restriction map.
* `Cech.cechRestrict` — the restriction map of complexes `C^•(g; M) ⟶ C^•(f; M)`.

## Main results

* `Cech.cechD_component` — the component formula for the Čech differential.
* `Cech.cechTermRestrict_comm` — the restriction maps commute with the differentials.
* `Cech.cechTermRestrict_lof_zero` — in degree zero the restriction map is the identity of `M`,
  under the identification of both degree-zero terms with `M`.

## Implementation notes

`Cech.idxErase` duplicates `ExtendedAlternatingCech.Idx.erase` and exists only because the
latter is a semireducible definition. The component formula composes the localization map
`Cech.cechι f M (Finset.erase_subset k T)`, whose source is `cechMod f M (T.erase k)`, with the
projection onto the component indexed by the erased index set, whose target is
`cechMod f M ↑(erased index)`; those two agree only after the erasure is unfolded. `rw` and
`simp` check type-correctness at `implicit` transparency, at which a semireducible definition
does not unfold, so every rewrite inside such a composite was rejected with *the target
expression is not type-correct*. Making the erasure an `abbrev` — reducible — makes the two
spellings agree at that transparency and the rewrites go through.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public section

open CategoryTheory
open ExtendedAlternatingCech (Idx)

namespace Cech

universe u v

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : Type v) [AddCommGroup M]
  [Module R M]

/-! ### The component formula for the differential -/

variable {f M}

/-- The index set `T` with the element `k` removed, as an index of the Čech term one degree
down. Reducible on purpose: see the implementation notes. -/
abbrev idxErase {p : ℕ} (T : Idx r (p + 1)) (k : T.1) : Idx r p :=
  ⟨T.1.erase k.1, by
    have h := T.2
    rw [Finset.card_erase_of_mem k.2]
    omega⟩

/-- The component of a summand `lof i b` at another index `j ≠ i` vanishes. -/
private theorem component_lof_of_ne {ι : Type*} [DecidableEq ι] {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] {i j : ι} (h : i ≠ j) (b : N i) :
    DirectSum.component R ι N j (DirectSum.lof R ι N i b) = 0 := by
  rw [DirectSum.component.of, dite_eq_right h]

/-- The localization map applied to a component depends on the index set only through its value,
not through the proof that the value has the right cardinality. -/
theorem cechι_component_congr {p : ℕ} {W : Finset (Fin r)} {V V' : Idx r p} (h : V = V')
    (z : cechTerm f M p) (hsub : V.1 ⊆ W) (hsub' : V'.1 ⊆ W) :
    cechι f M hsub (DirectSum.component R (Idx r p) (fun t => cechMod f M t.1) V z) =
      cechι f M hsub' (DirectSum.component R (Idx r p) (fun t => cechMod f M t.1) V' z) := by
  subst h
  rfl

variable (f M)

/-- The single summand of `Cech.cechD` landing in the component indexed by `T = insert k S`,
rewritten as the summand of the component formula belonging to the element `k` of `T`. -/
theorem cechD_summand (p : ℕ) (S : Idx r p) (k : ↥(S.1ᶜ)) (T : Idx r (p + 1))
    (hT : (⟨insert k.1 S.1, by
      rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp k.2), S.2]⟩ : Idx r (p + 1)) = T)
    (x : cechMod f M S.1) :
    cechSign S.1 k.1 •
      DirectSum.component R (Idx r (p + 1)) (fun t => cechMod f M t.1) T
        (DirectSum.lof R (Idx r (p + 1)) (fun t => cechMod f M t.1)
          ⟨insert k.1 S.1, by
            rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp k.2), S.2]⟩
          (cechι f M (Finset.subset_insert _ _) x)) =
    cechSign T.1 k.1 • cechι f M (Finset.erase_subset k.1 T.1)
      (DirectSum.component R (Idx r p) (fun t => cechMod f M t.1)
        (idxErase T ⟨k.1, by rw [← hT]; exact Finset.mem_insert_self _ _⟩)
        (DirectSum.lof R (Idx r p) (fun t => cechMod f M t.1) S x)) := by
  subst T
  have hS : idxErase (⟨insert k.1 S.1, by
      rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp k.2), S.2]⟩ : Idx r (p + 1))
      ⟨k.1, Finset.mem_insert_self _ _⟩ = S :=
    Subtype.ext (Finset.erase_insert (Finset.mem_compl.mp k.2))
  rw [DirectSum.component.lof_self, cechSign_insert,
    cechι_component_congr hS (DirectSum.lof R (Idx r p) (fun t => cechMod f M t.1) S x)
      (Finset.erase_subset k.1 (insert k.1 S.1)) (Finset.subset_insert k.1 S.1),
    DirectSum.component.lof_self]

/-- **The component formula for the Čech differential.** The component of `d^p x` at a
`(p+1)`-element index set `T` is the alternating sum, over the elements `k` of `T`, of the
localization maps applied to the components of `x` at `T ∖ k`. -/
theorem cechD_component (p : ℕ) (x : cechTerm f M p) (T : Idx r (p + 1)) :
    (cechD f M p x) T = ∑ k : T.1,
      cechSign T.1 k • cechι f M (Finset.erase_subset k.1 T.1) (x (idxErase T k)) := by
  simp only [DirectSum.apply_eq_component (R := R)]
  induction x using DirectSum.induction_on with
  | zero => simp [zsmul_zero]
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_add]
    exact (zsmul_add _ _ _).symm
  | of S y =>
    rw [← DirectSum.lof_eq_of R, cechD_lof, map_sum]
    simp only [map_zsmul]
    apply Finset.sum_bij_ne_zero (fun k _ hn => (⟨k.1, by
      by_contra hmem
      have hne : (⟨insert k.1 S.1, by
          rw [Finset.card_insert_of_notMem (Finset.mem_compl.mp k.2), S.2]⟩ :
          Idx r (p + 1)) ≠ T := fun he => hmem (he ▸ Finset.mem_insert_self _ _)
      exact hn (by rw [component_lof_of_ne hne, zsmul_zero])⟩ : T.1))
    · exact fun _ _ _ => Finset.mem_univ _
    · intro a _ _ b _ _ hab
      exact Subtype.ext (congrArg (fun z : T.1 => z.1) hab)
    · intro k _ hn
      obtain rfl : S = idxErase T k := by
        by_contra hne
        exact hn (by rw [component_lof_of_ne hne, map_zero, zsmul_zero])
      let j : ↥((idxErase T k).1ᶜ) := ⟨k.1, Finset.mem_compl.mpr (Finset.notMem_erase _ _)⟩
      refine ⟨j, by simp, ?_, rfl⟩
      rw [cechD_summand f M p _ j T (Subtype.ext (Finset.insert_erase k.2)) y]
      exact hn
    · intro k _ hn
      refine cechD_summand f M p S k T ?_ y
      by_contra hne
      exact hn (by rw [component_lof_of_ne hne, zsmul_zero])

/-! ### Restriction to a subfamily -/

/-- Localizing a module at two submonoids that happen to be equal gives the same module. -/
def localizedCongr {S T : Submonoid R} (h : S = T) :
    LocalizedModule S M ≃ₗ[R] LocalizedModule T M := by
  subst h
  exact LinearEquiv.refl R _

/-- `Cech.localizedCongr` keeps the numerator and the denominator of a fraction. -/
theorem localizedCongr_mk {S T : Submonoid R} (h : S = T) (m : M) (t : S) :
    localizedCongr M h (LocalizedModule.mk m t) =
      LocalizedModule.mk m (⟨t.1, show (t : R) ∈ T from h ▸ t.2⟩ : T) := by
  subst h
  rfl

/-- `Cech.localizedCongr` fixes a fraction with denominator one. -/
theorem localizedCongr_mk_one {S T : Submonoid R} (h : S = T) (m : M) :
    localizedCongr M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  subst h
  rfl

variable {s : ℕ} (g : Fin s → R) (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i)

/-- A `p`-element index set for `f`, viewed as a `p`-element index set for the larger family
`g`. -/
abbrev reindexIdx {p : ℕ} (S : Idx r p) : Idx s p :=
  ⟨S.1.map e.toEmbedding, by simp [S.2]⟩

include he in
/-- The two localizing submonoids agree: the products `∏_{i ∈ S.map e} g i` and `∏_{i ∈ S} f i`
have the same factors. -/
theorem cechSub_reindex (S : Finset (Fin r)) :
    cechSub g (S.map e.toEmbedding) = cechSub f S := by
  simp [cechSub, Finset.prod_map, he]

/-- The identification of the localization of `M` indexed by `S.map e` for the family `g` with
the one indexed by `S` for the subfamily `f`. -/
def reindexLoc (S : Finset (Fin r)) :
    cechMod g M (S.map e.toEmbedding) ≃ₗ[R] cechMod f M S :=
  localizedCongr M (cechSub_reindex f g e he S)

/-- The transition maps fix a fraction with denominator one. -/
@[simp]
theorem cechι_mk_one {S T : Finset (Fin r)} (h : S ⊆ T) (m : M) :
    cechι f M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  rw [← LocalizedModule.mkLinearMap_apply (cechSub f S) M m, cechι_mk,
    LocalizedModule.mkLinearMap_apply]

/-- `Cech.reindexLoc` fixes a fraction with denominator one. -/
@[simp]
theorem reindexLoc_mk_one (S : Finset (Fin r)) (m : M) :
    reindexLoc f M g e he S (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  localizedCongr_mk_one M _ m

/-- `Cech.reindexLoc` keeps the numerator and the denominator of a fraction. -/
theorem reindexLoc_mk (S : Finset (Fin r)) (m : M) (t : cechSub g (S.map e.toEmbedding)) :
    reindexLoc f M g e he S (LocalizedModule.mk m t) =
      LocalizedModule.mk m (⟨(t : R), show (t : R) ∈ cechSub f S from
        cechSub_reindex f g e he S ▸ t.2⟩ : cechSub f S) :=
  localizedCongr_mk M (cechSub_reindex f g e he S) m t

/-- The identification is compatible with the transition maps of the two Čech complexes. -/
theorem reindexLoc_naturality {S T : Finset (Fin r)} (h : S ⊆ T)
    (x : cechMod g M (S.map e.toEmbedding)) :
    reindexLoc f M g e he T (cechι g M (Finset.map_subset_map.mpr h) x) =
      cechι f M h (reindexLoc f M g e he S x) := by
  have hu := isUnit_algebraMap f M h (LocalizedModule.mkLinearMap (cechSub f T) M)
  rw [← cechSub_reindex f g e he S] at hu
  have hh : (reindexLoc f M g e he T).toLinearMap.comp
      (cechι g M (Finset.map_subset_map.mpr h)) =
      (cechι f M h).comp (reindexLoc f M g e he S).toLinearMap := by
    refine IsLocalizedModule.ext (cechSub g (S.map e.toEmbedding))
      (LocalizedModule.mkLinearMap _ M) hu (LinearMap.ext fun m => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LocalizedModule.mkLinearMap_apply, reindexLoc_mk_one, cechι_mk_one]
  exact LinearMap.congr_fun hh x

/-- **The degreewise restriction map** `C^p(g; M) → C^p(f; M)`: the component at `S` is the
component of the source at `S.map e`. -/
def cechTermRestrict (p : ℕ) : cechTerm g M p →ₗ[R] cechTerm f M p :=
  (DirectSum.linearEquivFunOnFintype R _ _).symm.toLinearMap.comp
    (LinearMap.pi fun S => (reindexLoc f M g e he S.1).toLinearMap.comp
      (DirectSum.component R _ _ (reindexIdx e S)))

/-- The component of the restriction map at `S` is the component of the source at `S.map e`. -/
@[simp]
theorem cechTermRestrict_apply (p : ℕ) (x : cechTerm g M p) (S : Idx r p) :
    cechTermRestrict f M g e he p x S = reindexLoc f M g e he S.1 (x (reindexIdx e S)) :=
  rfl

/-- Erasing an element and reindexing commute. -/
theorem reindexIdx_erase {p : ℕ} (T : Idx r (p + 1)) (k : T.1) :
    idxErase (reindexIdx e T) ⟨e k.1, Finset.mem_map.mpr ⟨k.1, k.2, rfl⟩⟩ =
      reindexIdx e (idxErase T k) :=
  Subtype.ext (Finset.map_erase e.toEmbedding T.1 k.1).symm

/-- The Čech sign is unchanged by an order-preserving reindexing of the index set. -/
theorem cechSign_map (T : Finset (Fin r)) (k : Fin r) :
    cechSign (T.map e.toEmbedding) (e k) = cechSign T k := by
  simp [cechSign, Finset.filter_map]

include he in
/-- The identification of localizations is compatible with erasing an index. -/
theorem reindexLoc_erase {p : ℕ} (T : Idx r (p + 1)) (k : T.1) (x : cechTerm g M p) :
    reindexLoc f M g e he T.1
      (cechι g M (Finset.erase_subset (e k.1) (T.1.map e.toEmbedding))
        (x (idxErase (reindexIdx e T) ⟨e k.1, Finset.mem_map.mpr ⟨k.1, k.2, rfl⟩⟩))) =
      cechι f M (Finset.erase_subset k.1 T.1)
        (reindexLoc f M g e he (T.1.erase k.1) (x (reindexIdx e (idxErase T k)))) := by
  rw [← reindexLoc_naturality f M g e he (Finset.erase_subset k.1 T.1)]
  congr 1
  exact cechι_component_congr (reindexIdx_erase e T k) x
    (Finset.erase_subset (e k.1) (T.1.map e.toEmbedding))
    (Finset.map_subset_map.mpr (Finset.erase_subset k.1 T.1))

include he in
/-- **The restriction maps commute with the Čech differentials.** -/
theorem cechTermRestrict_comm (p : ℕ) (x : cechTerm g M p) :
    cechTermRestrict f M g e he (p + 1) (cechD g M p x) =
      cechD f M p (cechTermRestrict f M g e he p x) := by
  refine DirectSum.ext_component R fun T => ?_
  change (cechTermRestrict f M g e he (p + 1) (cechD g M p x)) T =
    (cechD f M p (cechTermRestrict f M g e he p x)) T
  rw [cechTermRestrict_apply, cechD_component, map_sum, cechD_component]
  simp only [map_zsmul, cechTermRestrict_apply]
  symm
  refine Finset.sum_bij
    (fun k _ => (⟨e k.1, Finset.mem_map.mpr ⟨k.1, k.2, rfl⟩⟩ : (reindexIdx e T).1))
    (by intros; simp) (fun a _ b _ hab => Subtype.ext (e.injective
      (congrArg Subtype.val hab))) (fun b _ => ?_) (fun k _ => ?_)
  · obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp b.2
    exact ⟨⟨a, ha⟩, by simp, Subtype.ext hab⟩
  · rw [show cechSign (reindexIdx e T).1 (e k.1) = cechSign T.1 k.1 from
      cechSign_map e T.1 k.1]
    exact congrArg (fun y => cechSign T.1 k.1 • y) (reindexLoc_erase f M g e he T k x).symm

include he in
/-- **The restriction map of complexes** `C^•(g; M) ⟶ C^•(f; M)`. -/
def cechRestrict : cechComplex g M ⟶ cechComplex f M where
  f p := ModuleCat.ofHom (cechTermRestrict f M g e he p)
  comm' p q hpq := by
    change p + 1 = q at hpq
    subst q
    ext x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, cechComplex, CochainComplex.of_d]
    exact (cechTermRestrict_comm f M g e he p x).symm

include he in
/-- In degree zero the restriction map is the identity: both degree-zero terms are the single
summand indexed by the empty set, which is `M` itself. -/
theorem cechTermRestrict_lof_zero (m : M) :
    cechTermRestrict f M g e he 0
        (DirectSum.lof R (Idx s 0) (fun S => cechMod g M S.1) default
          (LocalizedModule.mkLinearMap (cechSub g (∅ : Finset (Fin s))) M m)) =
      DirectSum.lof R (Idx r 0) (fun S => cechMod f M S.1) default
        (LocalizedModule.mkLinearMap (cechSub f (∅ : Finset (Fin r))) M m) := by
  refine DirectSum.ext_component R fun S => ?_
  obtain rfl : S = default := Subsingleton.elim _ _
  rw [DirectSum.component.lof_self, ← DirectSum.apply_eq_component, cechTermRestrict_apply]
  have h1 : ((DirectSum.lof R (Idx s 0) (fun S => cechMod g M S.1) default)
        (LocalizedModule.mkLinearMap (cechSub g (∅ : Finset (Fin s))) M m))
      (reindexIdx e (default : Idx r 0)) = LocalizedModule.mk m 1 := by
    rw [DirectSum.apply_eq_component (R := R)]
    exact (DirectSum.component.lof_self R (default : Idx s 0) _).trans
      (LocalizedModule.mkLinearMap_apply _ _ m)
  rw [h1, reindexLoc_mk_one, LocalizedModule.mkLinearMap_apply]

end Cech

end
