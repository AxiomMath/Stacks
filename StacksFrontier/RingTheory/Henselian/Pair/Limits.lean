module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Henselian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Henselian.Pair.Operations

@[expose] public section

/-!
# Limits and colimits of henselian pairs

The henselian condition on a pair is stable under the elementary limit constructions. A filtered
colimit of henselian pairs is henselian along the colimit of the ideals; a product of pairs is
henselian exactly when each factor is; and a limit of a system of henselian pairs is henselian
along the limit ideal. Because a filtered colimit of henselian ideals is henselian, every ring
has a largest henselian ideal.

Stability fails for non-filtered colimits: Moret-Bailly's example
`padicInt_tensorProduct_not_henselian` exhibits a coproduct of two copies of the henselian pair
`(ℤ_[p], (p))` which is not henselian.

## Main results

* `henselianPair_colimit`: a filtered colimit of henselian pairs is henselian.
* `padicInt_tensorProduct_not_henselian`: `ℤ_[p] ⊗[ℤ] ℤ_[p]` is not henselian at `p` for odd
  primes `p`, so the filtered hypothesis cannot be dropped.
* `henselianPair_pi_iff`: a product of pairs is henselian if and only if every factor is.
* `henselianPair_limit`: a limit of henselian pairs is henselian along the limit ideal.
* `exists_greatest_henselianPair`: every commutative ring has a largest henselian ideal.

## Implementation notes

Diagrams of rings are functors to `CommRingCat`, and the colimit and limit ideals are the
supremum of the images and the infimum of the preimages respectively. The largest henselian ideal
is characterized by its universal property in the ideal lattice rather than constructed
explicitly.

## References

* [Stacks: Tag 09XD](https://stacks.math.columbia.edu/tag/09XD)
-/

open CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

universe u v

section

private lemma monic_lift_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (p : Polynomial (R ⧸ I)) (hp : p.Monic) :
    ∃ q : Polynomial R, q.Monic ∧ q.map (Ideal.Quotient.mk I) = p := by
  have hl : p ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
    Polynomial.mem_lifts_of_surjective (Ideal.Quotient.mk_surjective) p
  obtain ⟨q, hq, -, hmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hl hp
  exact ⟨q, hmonic, hq⟩

/-- Every commutative ring `R` forms a henselian pair with the zero ideal `⊥`. -/
lemma henselianPair_bot (R : Type*) [CommRing R] :
    HenselianPair R (⊥ : Ideal R) := by
  classical
  let e := RingEquiv.quotientBot R
  have he : e.toRingHom.comp (Ideal.Quotient.mk (⊥ : Ideal R)) = RingHom.id R := by
    ext x
    exact RingEquiv.quotientBot_mk x
  constructor
  · exact bot_le
  · intro f hf g₀ h₀ hg₀ hh₀ hfac _
    refine ⟨g₀.map e.toRingHom, h₀.map e.toRingHom,
      hg₀.map _, hh₀.map _, ?_, ?_, ?_⟩
    · simpa only [Polynomial.map_map, he, Polynomial.map_id, Polynomial.map_mul] using
        congrArg (Polynomial.map e.toRingHom) hfac
    all_goals
      apply Polynomial.map_injective e.toRingHom e.injective
      simp only [Polynomial.map_map, ← RingHom.comp_assoc, he, RingHom.id_comp]

/-- The coconical maps of a cocone are compatible with the maps of the diagram, elementwise. -/
private lemma cocone_app_map_apply {J : Type v} [SmallCategory J] {F : J ⥤ CommRingCat.{max u v}}
    (c : Cocone F) {j k : J} (f : j ⟶ k) (x : F.obj j) :
    c.ι.app k (F.map f x) = c.ι.app j x := by
  simp

variable {J : Type v} [SmallCategory J] [IsFiltered J] [Nonempty J]
    (F : J ⥤ CommRingCat.{max u v}) (I : ∀ j, Ideal (F.obj j))
    (hI : ∀ ⦃j k⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    (c : Cocone F) (hc : IsColimit c)

include hI in
omit [Nonempty J] in
private lemma idealMap_directed :
    Directed (· ≤ ·) (fun j ↦ (Ideal.map (c.ι.app j).hom (I j) : Ideal c.pt)) := by
  intro j k
  have hle : ∀ {i} (f : i ⟶ IsFiltered.max j k), Ideal.map (c.ι.app i).hom (I i) ≤
      Ideal.map (c.ι.app (IsFiltered.max j k)).hom (I (IsFiltered.max j k)) := fun {i} f ↦ by
    rw [← c.w f, CommRingCat.hom_comp, ← Ideal.map_map]
    exact Ideal.map_mono (hI _)
  exact ⟨_, hle (IsFiltered.leftToMax j k), hle (IsFiltered.rightToMax j k)⟩

include hc in
private lemma exists_rep (x : c.pt) :
    ∃ (j : J) (y : F.obj j), c.ι.app j y = x := by
  let S : Subring c.pt :=
    { carrier := {x | ∃ (j : J) (y : F.obj j), c.ι.app j y = x}
      zero_mem' := ⟨Classical.choice inferInstance, 0, map_zero _⟩
      one_mem' := ⟨Classical.choice inferInstance, 1, map_one _⟩
      add_mem' := by
        rintro a b ⟨j, a', rfl⟩ ⟨k, b', rfl⟩
        refine ⟨IsFiltered.max j k,
          F.map (IsFiltered.leftToMax j k) a' + F.map (IsFiltered.rightToMax j k) b', ?_⟩
        rw [map_add]
        simp
      neg_mem' := by
        rintro a ⟨j, a', rfl⟩
        exact ⟨j, -a', map_neg _ _⟩
      mul_mem' := by
        rintro a b ⟨j, a', rfl⟩ ⟨k, b', rfl⟩
        refine ⟨IsFiltered.max j k,
          F.map (IsFiltered.leftToMax j k) a' * F.map (IsFiltered.rightToMax j k) b', ?_⟩
        rw [map_mul]
        simp }
  let t : Cocone F :=
    { pt := CommRingCat.of S
      ι :=
        { app := fun j ↦ CommRingCat.ofHom
            { toFun := fun y ↦ ⟨c.ι.app j y, ⟨j, y, rfl⟩⟩
              map_one' := Subtype.ext (map_one _)
              map_mul' := fun _ _ ↦ Subtype.ext (map_mul _ _ _)
              map_zero' := Subtype.ext (map_zero _)
              map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _) }
          naturality := by
            intro j k f
            ext y
            exact Subtype.ext (ConcreteCategory.congr_hom (c.w f) y) } }
  let d : c.pt ⟶ CommRingCat.of S := IsColimit.desc hc t
  let inc : CommRingCat.of S ⟶ c.pt := CommRingCat.ofHom S.subtype
  have hd : d ≫ inc = 𝟙 c.pt := by
    apply IsColimit.hom_ext hc
    intro j
    rw [← Category.assoc, IsColimit.fac hc t j]
    rfl
  obtain ⟨j, y, hy⟩ := (d x).property
  exact ⟨j, y, hy.trans (by simpa [d, inc] using ConcreteCategory.congr_hom hd x)⟩

include hI hc in
private lemma mem_mappedIdeal_descends {j : J} {x : c.pt}
    (hx : x ∈ Ideal.map (c.ι.app j).hom (I j)) :
    ∃ (k : J) (_f : j ⟶ k) (y : F.obj k), y ∈ I k ∧ c.ι.app k y = x := by
  change x ∈ Ideal.span ((c.ι.app j) '' (I j)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨j, 𝟙 j, y, hy, by simp⟩
  | zero =>
      exact ⟨j, 𝟙 j, 0, (I j).zero_mem, by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨jx, fx, x', hx', hxe⟩ := hx
      obtain ⟨jy, fy, y', hy', hye⟩ := hy
      let k := IsFiltered.max jx jy
      let gx := IsFiltered.leftToMax jx jy
      let gy := IsFiltered.rightToMax jx jy
      refine ⟨k, fx ≫ gx, F.map gx x' + F.map gy y',
        (I k).add_mem (hI gx (Ideal.mem_map_of_mem _ hx'))
          (hI gy (Ideal.mem_map_of_mem _ hy')), ?_⟩
      rw [map_add]
      rw [cocone_app_map_apply, cocone_app_map_apply, hxe, hye]
  | smul a x _ hx =>
      obtain ⟨jx, fx, x', hx', hxe⟩ := hx
      obtain ⟨ja, a', ha'⟩ := exists_rep F c hc a
      let k := IsFiltered.max jx ja
      let g := IsFiltered.leftToMax jx ja
      let ga := IsFiltered.rightToMax jx ja
      let a'' := F.map ga a'
      refine ⟨k, fx ≫ g, a'' * F.map g x',
        (I k).mul_mem_left _ (hI g (Ideal.mem_map_of_mem _ hx')), ?_⟩
      rw [smul_eq_mul, map_mul]
      rw [cocone_app_map_apply, cocone_app_map_apply, ha', hxe]

include hI hc in
private lemma mem_colimitIdeal_iff (x : c.pt) :
    x ∈ (⨆ j, (Ideal.map (c.ι.app j).hom (I j) : Ideal c.pt)) ↔
      ∃ (j : J) (y : F.obj j), y ∈ I j ∧ c.ι.app j y = x := by
  rw [Submodule.mem_iSup_of_directed _ (idealMap_directed F I hI c)]
  constructor
  · rintro ⟨j, hx⟩
    obtain ⟨k, -, y, hy, hxy⟩ := mem_mappedIdeal_descends F I hI c hc hx
    exact ⟨k, y, hy, hxy⟩
  · rintro ⟨j, y, hy, rfl⟩
    exact ⟨j, Ideal.mem_map_of_mem (c.ι.app j).hom hy⟩

include hc in
private lemma exists_rep_finset {α : Type*} (s : Finset α) (x : α → c.pt) :
    ∃ (j : J) (y : α → F.obj j), ∀ i ∈ s, c.ι.app j (y i) = x i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨Classical.choice inferInstance, fun _ ↦ 0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨j, y, hy⟩ := ih
      obtain ⟨k, z, hz⟩ := exists_rep F c hc (x a)
      let l := IsFiltered.max j k
      let f := IsFiltered.leftToMax j k
      let g := IsFiltered.rightToMax j k
      refine ⟨l, fun i ↦ if i = a then F.map g z else F.map f (y i), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | his
      · simp only [ite_true]
        exact (cocone_app_map_apply c g z).trans hz
      · have hia : i ≠ a := by intro h; exact ha (h ▸ his)
        simp only [hia, ite_false]
        exact (cocone_app_map_apply c f (y i)).trans (hy i his)

include hc in
private lemma exists_rep_polynomials (p : Fin 5 → Polynomial c.pt) :
    ∃ (j : J) (q : Fin 5 → Polynomial (F.obj j)),
      ∀ i, (q i).map (c.ι.app j).hom = p i := by
  classical
  -- Represent every coefficient at once, indexed by both the polynomial and the degree.
  let t : Finset (Fin 5 × ℕ) :=
    Finset.univ.biUnion (fun i : Fin 5 ↦ (p i).support.image (i, ·))
  obtain ⟨j, z, hz⟩ := exists_rep_finset F c hc t (fun a ↦ (p a.1).coeff a.2)
  refine ⟨j, fun i ↦ ∑ n ∈ (p i).support, monomial n (z (i, n)), ?_⟩
  intro i
  rw [Polynomial.map_sum]
  simp only [map_monomial]
  conv_rhs => rw [← (p i).sum_monomial_eq]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hz (i, n) (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩)]

include hI hc in
private lemma eventually_mem_ideal [PreservesColimitsOfShape J (forget CommRingCat.{max u v})]
    {j : J} (x : F.obj j)
    (hx : c.ι.app j x ∈
      (⨆ k, (Ideal.map (c.ι.app k).hom (I k) : Ideal c.pt))) :
    ∃ (k : J) (f : j ⟶ k), F.map f x ∈ I k := by
  obtain ⟨l, y, hy, heq⟩ :=
    (mem_colimitIdeal_iff F I hI c hc _).mp hx
  obtain ⟨k, f, g, hfg⟩ := (hc.eq_iff F).mp heq.symm
  refine ⟨k, f, ?_⟩
  rw [hfg]
  exact hI g (Ideal.mem_map_of_mem _ hy)

include hI hc in
private lemma eventually_mem_ideal_finset
    [PreservesColimitsOfShape J (forget CommRingCat.{max u v})]
    {α : Type*} {j : J} (s : Finset α) (x : α → F.obj j)
    (hx : ∀ a ∈ s, c.ι.app j (x a) ∈
      (⨆ k, (Ideal.map (c.ι.app k).hom (I k) : Ideal c.pt))) :
    ∃ (k : J) (f : j ⟶ k), ∀ a ∈ s, F.map f (x a) ∈ I k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨j, 𝟙 j, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨k, f, hf⟩ := ih (by
        intro b hb
        exact hx b (Finset.mem_insert_of_mem hb))
      obtain ⟨l, g, hg⟩ := eventually_mem_ideal F I hI c hc (x a)
        (hx a (Finset.mem_insert_self _ _))
      let m := IsFiltered.max k l
      let α := f ≫ IsFiltered.leftToMax k l
      let β := g ≫ IsFiltered.rightToMax k l
      let t := IsFiltered.coeq α β
      let γ : m ⟶ t := IsFiltered.coeqHom α β
      let fk : k ⟶ t := IsFiltered.leftToMax k l ≫ γ
      let gl : l ⟶ t := IsFiltered.rightToMax k l ≫ γ
      refine ⟨t, f ≫ fk, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hbs
      · have heq : f ≫ fk = g ≫ gl := by
          simpa only [fk, gl, α, β, Category.assoc] using
            (IsFiltered.coeq_condition α β)
        rw [heq, Functor.map_comp_apply]
        exact hI gl (Ideal.mem_map_of_mem _ hg)
      · rw [Functor.map_comp_apply]
        exact hI fk (Ideal.mem_map_of_mem _ (hf b hbs))

include hI hc in
private lemma eventually_polynomials_mod_ideal
    [PreservesColimitsOfShape J (forget CommRingCat.{max u v})]
    {j : J} (d : Fin 2 → Polynomial (F.obj j))
    (hd : ∀ i n, c.ι.app j ((d i).coeff n) ∈
      (⨆ k, (Ideal.map (c.ι.app k).hom (I k) : Ideal c.pt))) :
    ∃ (k : J) (f : j ⟶ k),
      ∀ i, (d i).map ((Ideal.Quotient.mk (I k)).comp (F.map f).hom) = 0 := by
  classical
  let s : Finset (Fin 2 × ℕ) :=
    Finset.univ.biUnion (fun i : Fin 2 ↦ (d i).support.image (i, ·))
  obtain ⟨k, f, hf⟩ := eventually_mem_ideal_finset F I hI c hc s
    (fun a ↦ (d a.1).coeff a.2) (by
      intro a ha
      exact hd a.1 a.2)
  refine ⟨k, f, ?_⟩
  intro i
  ext n
  by_cases hn : n ∈ (d i).support
  · have hmem : F.map f ((d i).coeff n) ∈ I k :=
      hf (i, n) (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩)
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] using hmem
  · have hz : (d i).coeff n = 0 := by
      simpa only [mem_support_iff, not_ne_iff] using hn
    simp [Polynomial.coeff_map, hz]

/-- A filtered colimit of Henselian pairs is a Henselian pair. -/
@[stacks 0FWT]
theorem henselianPair_colimit
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{max u v}) (I : ∀ j, Ideal (F.obj j))
    (hI : ∀ ⦃j k⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    (c : Cocone F) (hc : IsColimit c)
    (hH : ∀ j, HenselianPair (F.obj j) (I j)) :
    HenselianPair c.pt (⨆ j, Ideal.map (c.ι.app j).hom (I j)) := by
  classical
  let : PreservesColimitsOfShape J (forget CommRingCat.{max u v}) := by
    constructor
    intro F'
    exact preservesColimit_of_preserves_colimit_cocone
      (CommRingCat.FilteredColimits.colimitCoconeIsColimit.{v, u} F')
      (Types.TypeMax.colimitCoconeIsColimit (F' ⋙ forget CommRingCat))
  by_cases hne : Nonempty J
  · let : Nonempty J := hne
    let K : Ideal c.pt := ⨆ j, Ideal.map (c.ι.app j).hom (I j)
    constructor
    · intro x hx
      rw [Ideal.mem_jacobson_bot]
      intro y
      obtain ⟨j, xj, hxj, hxeq⟩ := (mem_colimitIdeal_iff F I hI c hc x).mp hx
      obtain ⟨k, yk, hyeq⟩ := exists_rep F c hc y
      let l := IsFiltered.max j k
      let f := IsFiltered.leftToMax j k
      let g := IsFiltered.rightToMax j k
      let xl : F.obj l := F.map f xj
      let yl : F.obj l := F.map g yk
      have hxl : xl ∈ (⊥ : Ideal (F.obj l)).jacobson :=
        (hH l).1 (hI f (Ideal.mem_map_of_mem _ hxj))
      have hu : IsUnit (xl * yl + 1) := Ideal.mem_jacobson_bot.mp hxl yl
      have hxu : c.ι.app l xl = x := (cocone_app_map_apply c f xj).trans hxeq
      have hyu : c.ι.app l yl = y := (cocone_app_map_apply c g yk).trans hyeq
      simpa only [map_add, map_mul, map_one, hxu, hyu] using hu.map (c.ι.app l).hom
    · intro p hp g₀ h₀ hg₀ hh₀ hfac hcop
      obtain ⟨G, hGmonic, hGred⟩ := monic_lift_quotient K g₀ hg₀
      obtain ⟨H, hHmonic, hHred⟩ := monic_lift_quotient K h₀ hh₀
      obtain ⟨u₀, v₀, huv⟩ := hcop
      obtain ⟨U, hUred⟩ := Polynomial.map_surjective
        (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective u₀
      obtain ⟨V, hVred⟩ := Polynomial.map_surjective
        (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective v₀
      let P : Fin 5 → Polynomial c.pt := ![p, G, H, U, V]
      obtain ⟨j, Q, hQ⟩ := exists_rep_polynomials F c hc P
      have hQf : (Q 0).map (c.ι.app j).hom = p := by simpa [P] using hQ 0
      have hQg : (Q 1).map (c.ι.app j).hom = G := by simpa [P] using hQ 1
      have hQh : (Q 2).map (c.ι.app j).hom = H := by simpa [P] using hQ 2
      have hQu : (Q 3).map (c.ι.app j).hom = U := by simpa [P] using hQ 3
      have hQv : (Q 4).map (c.ι.app j).hom = V := by simpa [P] using hQ 4
      obtain ⟨qf, hqf, -, hqfm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
        ((Polynomial.mem_lifts _).mpr ⟨Q 0, hQf⟩) hp
      obtain ⟨qg, hqg, -, hqgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
        ((Polynomial.mem_lifts _).mpr ⟨Q 1, hQg⟩) hGmonic
      obtain ⟨qh, hqh, -, hqhm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
        ((Polynomial.mem_lifts _).mpr ⟨Q 2, hQh⟩) hHmonic
      let D : Fin 2 → Polynomial (F.obj j) :=
        ![qf - qg * qh, 1 - qg * Q 3 - qh * Q 4]
      have hD0 : (D 0).map ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) = 0 := by
        show (qf - qg * qh).map ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) = 0
        rw [Polynomial.map_sub, Polynomial.map_mul]
        apply sub_eq_zero.mpr
        calc
          qf.map ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) =
              p.map (Ideal.Quotient.mk K) := by rw [← Polynomial.map_map, hqf]
          _ = g₀ * h₀ := hfac
          _ = qg.map ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) *
              qh.map ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) := by
                rw [← Polynomial.map_map, hqg, hGred,
                  ← Polynomial.map_map, hqh, hHred]
      have hD1 : (D 1).map ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) = 0 := by
        show (1 - qg * Q 3 - qh * Q 4).map
          ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) = 0
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one]
        rw [← Polynomial.map_map, hqg, hGred,
          ← Polynomial.map_map, hQu, hUred,
          ← Polynomial.map_map, hqh, hHred,
          ← Polynomial.map_map, hQv, hVred]
        rw [sub_sub, show g₀ * u₀ + h₀ * v₀ = 1 by simpa [mul_comm] using huv]
        simp
      have hD : ∀ i n, c.ι.app j ((D i).coeff n) ∈ K := by
        intro i n
        have hzero : ((Ideal.Quotient.mk K).comp (c.ι.app j).hom)
            ((D i).coeff n) = 0 := by
          have h := congrArg (fun r : Polynomial (c.pt ⧸ K) ↦ r.coeff n)
            (by fin_cases i <;> assumption :
              (D i).map ((Ideal.Quotient.mk K).comp (c.ι.app j).hom) = 0)
          simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using h
        exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero
      obtain ⟨k, f, hDk⟩ := eventually_polynomials_mod_ideal F I hI c hc D hD
      let qfk : Polynomial (F.obj k) := qf.map (F.map f).hom
      let qgk : Polynomial (F.obj k) := qg.map (F.map f).hom
      let qhk : Polynomial (F.obj k) := qh.map (F.map f).hom
      let quk : Polynomial (F.obj k) := (Q 3).map (F.map f).hom
      let qvk : Polynomial (F.obj k) := (Q 4).map (F.map f).hom
      have hfac_k : qfk.map (Ideal.Quotient.mk (I k)) =
          qgk.map (Ideal.Quotient.mk (I k)) * qhk.map (Ideal.Quotient.mk (I k)) := by
        have h := hDk 0
        simp only [D, Matrix.cons_val_zero, Polynomial.map_sub, Polynomial.map_mul] at h
        have h' : qfk.map (Ideal.Quotient.mk (I k)) -
            qgk.map (Ideal.Quotient.mk (I k)) *
              qhk.map (Ideal.Quotient.mk (I k)) = 0 := by
          simpa only [← Polynomial.map_map, qfk, qgk, qhk] using h
        exact sub_eq_zero.mp h'
      have hcop_k : IsCoprime (qgk.map (Ideal.Quotient.mk (I k)))
          (qhk.map (Ideal.Quotient.mk (I k))) := by
        refine ⟨quk.map (Ideal.Quotient.mk (I k)),
          qvk.map (Ideal.Quotient.mk (I k)), ?_⟩
        have h := hDk 1
        change (1 - qg * Q 3 - qh * Q 4).map
          ((Ideal.Quotient.mk (I k)).comp (F.map f).hom) = 0 at h
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_one] at h
        rw [sub_sub] at h
        have heq := sub_eq_zero.mp h
        simpa only [← Polynomial.map_map, qgk, qhk, quk, qvk, mul_comm] using heq.symm
      obtain ⟨gk, hk, hgkm, hhkm, hfacgk, hgk, hhk⟩ :=
        (hH k).2 qfk (hqfm.map _) _ _
          ((hqgm.map (F.map f).hom).map (Ideal.Quotient.mk (I k)))
          ((hqhm.map (F.map f).hom).map (Ideal.Quotient.mk (I k))) hfac_k hcop_k
      have hcone : (c.ι.app k).hom.comp (F.map f).hom = (c.ι.app j).hom := by
        ext x
        exact cocone_app_map_apply c f x
      have hrep (r : Polynomial (F.obj j)) :
          (r.map (F.map f).hom).map (c.ι.app k).hom = r.map (c.ι.app j).hom := by
        rw [Polynomial.map_map, hcone]
      have hIK : Ideal.map (c.ι.app k).hom (I k) ≤ K := le_iSup_of_le k le_rfl
      have hIK' : I k ≤ Ideal.comap (c.ι.app k).hom K :=
        Ideal.map_le_iff_le_comap.mp hIK
      let φ : (F.obj k ⧸ I k) →+* (c.pt ⧸ K) :=
        Ideal.quotientMap K (c.ι.app k).hom hIK'
      have hφ : φ.comp (Ideal.Quotient.mk (I k)) =
          (Ideal.Quotient.mk K).comp (c.ι.app k).hom := by
        ext x
        simp only [RingHom.comp_apply, φ, Ideal.quotientMap_mk]
      have hlift (r s : Polynomial (F.obj k))
          (h : r.map (Ideal.Quotient.mk (I k)) = s.map (Ideal.Quotient.mk (I k))) :
          (r.map (c.ι.app k).hom).map (Ideal.Quotient.mk K) =
            (s.map (c.ι.app k).hom).map (Ideal.Quotient.mk K) := by
        simpa only [Polynomial.map_map, hφ] using congrArg (Polynomial.map φ) h
      refine ⟨gk.map (c.ι.app k).hom, hk.map (c.ι.app k).hom,
        hgkm.map _, hhkm.map _, ?_, ?_, ?_⟩
      · have h := congrArg (Polynomial.map (c.ι.app k).hom) hfacgk
        rw [Polynomial.map_mul] at h
        exact ((hrep qf).trans hqf).symm.trans h
      · rw [hlift _ _ hgk, hrep qg, hqg, hGred]
      · rw [hlift _ _ hhk, hrep qh, hqh, hHred]
  · have : IsEmpty J := ⟨fun j ↦ hne ⟨j⟩⟩
    simpa using henselianPair_bot c.pt

end

section

private lemma not_isLocalRing_of_idempotent {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    ¬ IsLocalRing R := by
  intro hR
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact h1 ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he)
  · have h' := (IsIdempotentElem.iff_eq_one_of_isUnit h).mp he.one_sub
    exact h0 (by linear_combination -h')

private lemma not_connectedSpace_of_idempotent {R : Type*} [CommRing R]
    {e : R} (he : IsIdempotentElem e) (h0 : e ≠ 0) (h1 : e ≠ 1) :
    ¬ ConnectedSpace (PrimeSpectrum R) := by
  intro hR
  have hcl : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨e, he, rfl⟩
  rcases isClopen_iff.mp hcl with h | h
  · apply h0
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero
    ext x
    simp [h]
  · apply h1
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .one
    ext x
    simp [h]

private lemma not_isSquare_one_add_prime {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    ¬ IsSquare ((1 + (p : ℤ)) : ℚ) := by
  rw [← Int.cast_one, ← Int.cast_add, Rat.isSquare_intCast_iff]
  have heq : (1 + (p : ℤ)) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [heq, Int.isSquare_natCast_iff]
  rintro ⟨k, hk⟩
  have hk2 : 2 ≤ k := by nlinarith [hp.two_le]
  have hmul : (k - 1) * (k + 1) = p := by
    have : k - 1 + 1 = k := Nat.sub_add_cancel (by omega)
    nlinarith
  have hd : k - 1 ∣ p := ⟨k + 1, hmul.symm⟩
  rcases hp.eq_one_or_self_of_dvd _ hd with h | h
  · apply h3
    have : k = 2 := by omega
    subst k
    norm_num at hmul
    omega
  · nlinarith [hp.two_le]

private lemma exists_sq_eq_of_henselian {R : Type*} [CommRing R] (I : Ideal R)
    [HenselianRing R I] {t : R} (ht : 1 - t ∈ I) (h2 : IsUnit (2 : R)) :
    ∃ u : R, u ^ 2 = t := by
  let f : Polynomial R := Polynomial.X ^ 2 - Polynomial.C t
  obtain ⟨u, hu, -⟩ := HenselianRing.is_henselian f
    (Polynomial.monic_X_pow_sub_C t (by decide)) 1 (by simpa [f] using ht)
    (by convert h2.map (Ideal.Quotient.mk I) using 1; norm_num [f])
  exact ⟨u, by simpa [f, Polynomial.IsRoot, sub_eq_zero] using hu⟩

private lemma padicInt_exists_quadratic_data (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    ∃ t u v w : ℤ_[p],
      t = algebraMap ℤ ℤ_[p] (if p = 3 then 7 else 1 + (p : ℤ)) ∧
      ¬ IsSquare ((if p = 3 then (7 : ℤ) else 1 + (p : ℤ)) : ℚ) ∧
      u ^ 2 = t ∧ 2 * v = 1 ∧ t * w = 1 := by
  have hprime : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp
  let m := IsLocalRing.maximalIdeal ℤ_[p]
  let t : ℤ_[p] := algebraMap ℤ ℤ_[p] (if p = 3 then 7 else 1 + (p : ℤ))
  have ht : PadicInt.toZMod t = 1 := by
    dsimp [t]
    split_ifs with h
    · subst p; norm_num only [map_ofNat]; rfl
    · simp
  have ht' : 1 - t ∈ m := by
    show 1 - t ∈ IsLocalRing.maximalIdeal ℤ_[p]
    rw [← PadicInt.ker_toZMod]
    show PadicInt.toZMod (1 - t) = 0
    simp [ht]
  have h2 : IsUnit (2 : ℤ_[p]) := by
    apply isUnit_of_map_unit PadicInt.toZMod
    rw [map_ofNat, isUnit_iff_ne_zero]
    exact (ZMod.natCast_eq_zero_iff 2 p).not.mpr (by
      intro h
      rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
      · exact hprime.ne_one h
      · exact hp2 h)
  have htunit : IsUnit t := isUnit_of_map_unit PadicInt.toZMod t (by rw [ht]; exact isUnit_one)
  obtain ⟨u, hu⟩ := exists_sq_eq_of_henselian m ht' h2
  obtain ⟨v, hv⟩ := h2.exists_right_inv
  obtain ⟨w, hw⟩ := htunit.exists_right_inv
  refine ⟨t, u, v, w, rfl, ?_, hu, hv, hw⟩
  split_ifs with h
  · norm_num
  · exact not_isSquare_one_add_prime hprime h

private lemma isIdempotentElem_half_one_sub_of_sq_eq_one {R : Type*} [CommRing R]
    {v y : R} (hv : 2 * v = 1) (hy : y ^ 2 = 1) :
    IsIdempotentElem (v * (1 - y)) := by
  show (v * (1 - y)) * (v * (1 - y)) = v * (1 - y)
  linear_combination (v * (1 - y)) * hv +
    v ^ 2 * hy

private lemma exists_linearMap_one_apply_of_not_isSquare {K : Type*} [Field K]
    [CharZero K] {n : ℚ} {x : K} (hn : ¬ IsSquare n) (hx : x ^ 2 = (n : K)) :
    ∃ f : K →ₗ[ℚ] K, f 1 = 1 ∧ f x = 0 := by
  have hmem : (1 : K) ∉ Submodule.span ℚ {x} := by
    rintro h
    obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp h
    have hqx : (q : K) * x = 1 := by simpa [Algebra.smul_def] using hq
    have hq0 : (q : K) ≠ 0 := by intro h; simp [h] at hqx
    have hxq : x = (q : K)⁻¹ := by
      apply (mul_left_cancel₀ hq0)
      rw [hqx, mul_inv_cancel₀ hq0]
    apply hn
    refine ⟨q⁻¹, ?_⟩
    apply Rat.cast_injective (α := K)
    push_cast
    rw [← hx, hxq, pow_two]
  obtain ⟨f, hf, h1⟩ := LinearMap.exists_extend_of_notMem
    (0 : (Submodule.span ℚ {x}) →ₗ[ℚ] K) hmem (1 : K)
  refine ⟨f, h1, ?_⟩
  have := DFunLike.congr_fun hf ⟨x, Submodule.subset_span (Set.mem_singleton x)⟩
  simpa using this

private lemma tensor_quadratic_idempotent {R : Type*} [CommRing R] (n : ℤ)
    {u v w : R} (hu : u ^ 2 = (n : R)) (hv : 2 * v = 1) (hw : (n : R) * w = 1) :
    IsIdempotentElem ((v ⊗ₜ[ℤ] (1 : R)) *
      ((1 : R) ⊗ₜ[ℤ] (1 : R) - (w * u) ⊗ₜ[ℤ] u)) := by
  have hv' : (2 : R ⊗[ℤ] R) * (v ⊗ₜ[ℤ] (1 : R)) = 1 := by
    have h := congrArg (Algebra.TensorProduct.includeLeft : R →ₐ[ℤ] R ⊗[ℤ] R) hv
    rw [map_mul, map_ofNat, map_one] at h
    exact h
  have hy : ((w * u) ⊗ₜ[ℤ] u : R ⊗[ℤ] R) ^ 2 = 1 := by
    rw [Algebra.TensorProduct.tmul_pow, mul_pow, hu]
    have hn : (n : R) = n • (1 : R) := by simp
    rw [hn, ← TensorProduct.smul_tmul, zsmul_eq_mul]
    have hcalc : (n : R) * (w ^ 2 * (n • (1 : R))) = 1 := by
      simp only [zsmul_eq_mul, mul_one]
      linear_combination ((n : R) * w + 1) * hw
    rw [hcalc, ← Algebra.TensorProduct.one_def]
  simpa only [← Algebra.TensorProduct.one_def] using
    isIdempotentElem_half_one_sub_of_sq_eq_one hv' hy

private lemma tensor_quadratic_idempotent_ne {R K : Type*} [CommRing R] [Field K]
    [CharZero K] (ι : R →+* K) (n : ℤ) (hn : ¬ IsSquare (n : ℚ))
    {u v : R} (hu : u ^ 2 = (n : R)) (hv : 2 * v = 1) (w : R) :
    let e : R ⊗[ℤ] R := (v ⊗ₜ[ℤ] (1 : R)) *
      ((1 : R) ⊗ₜ[ℤ] (1 : R) - (w * u) ⊗ₜ[ℤ] u)
    e ≠ 0 ∧ e ≠ 1 := by
  have hu' : (ι u) ^ 2 = ((n : ℚ) : K) := by
    simpa using congrArg ι hu
  obtain ⟨f, hf1, hfu⟩ := exists_linearMap_one_apply_of_not_isSquare hn hu'
  let a : R →ₗ[ℤ] K := ι.toIntAlgHom.toLinearMap
  let b : R →ₗ[ℤ] K := (f.restrictScalars ℤ).comp a
  let L : R ⊗[ℤ] R →ₗ[ℤ] K :=
    TensorProduct.lift (((LinearMap.mul ℤ K).compl₂ b).comp a)
  have hL (x y : R) : L (x ⊗ₜ[ℤ] y) = ι x * f (ι y) := rfl
  have he : L ((v ⊗ₜ[ℤ] (1 : R)) *
      ((1 : R) ⊗ₜ[ℤ] (1 : R) - (w * u) ⊗ₜ[ℤ] u)) = ι v := by
    simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, map_sub, hL, map_one, hf1, hfu, mul_zero, sub_zero]
  have hL1 : L 1 = 1 := by rw [Algebra.TensorProduct.one_def, hL, map_one, hf1, mul_one]
  have hv' : (2 : K) * ι v = 1 := by simpa only [map_mul, map_ofNat, map_one] using congrArg ι hv
  constructor
  · intro h
    have h0 : ι v = 0 := by simpa only [he, map_zero] using congrArg L h
    rw [h0, mul_zero] at hv'
    exact zero_ne_one hv'
  · intro h
    have h1 : ι v = 1 := by simpa only [he, hL1] using congrArg L h
    rw [h1, mul_one] at hv'
    norm_num at hv'

private lemma ringHom_eq_of_ker_eq_span {R S : Type*} [CommRing R] [CommRing S]
    (p : ℕ) (f : R →+* ZMod p) (hf : RingHom.ker f = Ideal.span {(p : R)})
    (g : R →+* S) (hp : (p : S) = 0) (h : ZMod p →+* S) (x : R) :
    g x = h (f x) := by
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (f x)
  have hm : x - (n : R) ∈ RingHom.ker f := by
    show f (x - (n : R)) = 0
    simp [hn]
  rw [hf, Ideal.mem_span_singleton] at hm
  obtain ⟨y, hy⟩ := hm
  have hg := congrArg g hy
  simp only [map_sub, map_mul, map_natCast, map_intCast, hp, zero_mul] at hg
  rw [← hn, map_intCast]
  exact sub_eq_zero.mp hg

private lemma tensor_quotient_equiv_zmod {R : Type*} [CommRing R]
    (p : ℕ) (f : R →+* ZMod p) (hf : RingHom.ker f = Ideal.span {(p : R)}) :
    Nonempty (((R ⊗[ℤ] R) ⧸ Ideal.span {(p : R ⊗[ℤ] R)}) ≃+* ZMod p) := by
  let A := R ⊗[ℤ] R
  let I : Ideal A := Ideal.span {(p : A)}
  let q := Ideal.Quotient.mk I
  let F : A →+* ZMod p := (Algebra.TensorProduct.lift f.toIntAlgHom f.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom
  have hF : I ≤ RingHom.ker F := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show F (p : A) = 0
    exact (map_natCast F p).trans (ZMod.natCast_self p)
  let G : A ⧸ I →+* ZMod p := Ideal.Quotient.lift I F hF
  have hp : (p : A ⧸ I) = 0 := by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let : CharP (A ⧸ I) (ringChar (A ⧸ I)) := ringChar.charP _
  let H : ZMod p →+* A ⧸ I := ZMod.castHom (ringChar.dvd (R := A ⧸ I) hp) _
  have hleft (x : R) : q (x ⊗ₜ[ℤ] (1 : R)) = H (f x) :=
    ringHom_eq_of_ker_eq_span (S := A ⧸ I) p f hf
      (q.comp (Algebra.TensorProduct.includeLeft : R →ₐ[ℤ] A).toRingHom) hp H x
  have hright (x : R) : q ((1 : R) ⊗ₜ[ℤ] x) = H (f x) :=
    ringHom_eq_of_ker_eq_span (S := A ⧸ I) p f hf
      (q.comp (Algebra.TensorProduct.includeRight : R →ₐ[ℤ] A).toRingHom) hp H x
  have hFG (x : A) : G (q x) = F x := rfl
  have hGH : Function.LeftInverse H G := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hFG]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have hxy : (x ⊗ₜ[ℤ] y : A) =
          (x ⊗ₜ[ℤ] (1 : R)) * ((1 : R) ⊗ₜ[ℤ] y) := by
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      show H (f x * f y) = q (x ⊗ₜ[ℤ] y)
      rw [map_mul, hxy, map_mul, hleft, hright]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hHG : Function.RightInverse H G := by
    intro x
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    simp only [map_intCast]
  exact ⟨RingEquiv.ofBijective G ⟨hGH.injective, hHG.surjective⟩⟩

/-- For an odd prime `p`, the coproduct over `ℤ` of two copies of the Henselian pair
`(ℤ_[p], (p))` is not Henselian. Its residue ring is `ZMod p`, and an explicit nontrivial
idempotent, built from a square root of an integer which is not a rational square, witnesses that
its spectrum is disconnected. -/
@[stacks 0FWU]
theorem padicInt_tensorProduct_not_henselian (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    let R := ℤ_[p]
    let A := R ⊗[ℤ] R
    let I : Ideal A := Ideal.span {algebraMap ℤ A (p : ℤ)}
    HenselianRing R (Ideal.span {(p : R)}) ∧
      Ideal.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℤ] A).toRingHom
        (Ideal.span {(p : R)}) = I ∧
      Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[ℤ] A).toRingHom
        (Ideal.span {(p : R)}) = I ∧
      Nonempty ((A ⧸ I) ≃+* ZMod p) ∧
      (HenselianRing A I → IsLocalRing A) ∧
      ¬ IsLocalRing A ∧
      ¬ HenselianRing A I ∧
      ¬ ConnectedSpace (PrimeSpectrum A) ∧
      ∃ t u v w : R,
        t = algebraMap ℤ R (if p = 3 then 7 else 1 + (p : ℤ)) ∧
        ¬ IsSquare ((if p = 3 then (7 : ℤ) else 1 + (p : ℤ)) : ℚ) ∧
        u ^ 2 = t ∧ 2 * v = 1 ∧ t * w = 1 ∧
        let e : A := (v ⊗ₜ[ℤ] (1 : R)) *
          ((1 : R) ⊗ₜ[ℤ] (1 : R) - (w * u) ⊗ₜ[ℤ] u)
        IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  dsimp only
  let R := ℤ_[p]
  let A := R ⊗[ℤ] R
  let I : Ideal A := Ideal.span {algebraMap ℤ A (p : ℤ)}
  obtain ⟨t, u, v, w, ht, hn, hu, hv, hw⟩ := padicInt_exists_quadratic_data p hp
  let n : ℤ := if p = 3 then 7 else 1 + (p : ℤ)
  have hu' : u ^ 2 = (n : R) := hu.trans ht
  have hw' : (n : R) * w = 1 := (congrArg (· * w) ht.symm).trans hw
  have hn' : ¬ IsSquare (n : ℚ) := by simpa [n] using hn
  let e : A := (v ⊗ₜ[ℤ] (1 : R)) *
    ((1 : R) ⊗ₜ[ℤ] (1 : R) - (w * u) ⊗ₜ[ℤ] u)
  have he : IsIdempotentElem e := tensor_quadratic_idempotent n hu' hv hw'
  obtain ⟨he0, he1⟩ := tensor_quadratic_idempotent_ne
    (algebraMap ℤ_[p] ℚ_[p]) n hn' hu' hv w
  have hnotlocal : ¬ IsLocalRing A := not_isLocalRing_of_idempotent he he0 he1
  have hI : I = Ideal.span {(p : A)} :=
    congrArg (fun a : A => Ideal.span {a}) (map_natCast (algebraMap ℤ A) p)
  have hres : Nonempty ((A ⧸ I) ≃+* ZMod p) := by
    rw [hI]
    exact tensor_quotient_equiv_zmod p PadicInt.toZMod
      (PadicInt.ker_toZMod.trans PadicInt.maximalIdeal_eq_span_p)
  have hlocal : HenselianRing A I → IsLocalRing A := by
    intro hH
    obtain ⟨E⟩ := hres
    have : IsLocalRing (A ⧸ I) := E.symm.isLocalRing
    have : IsLocalHom (Ideal.Quotient.mk I) :=
      isLocalHom_of_le_jacobson_bot I hH.jac
    exact RingHom.domain_isLocalRing (Ideal.Quotient.mk I)
  refine ⟨?_, ?_, ?_, hres, hlocal, hnotlocal, fun h => hnotlocal (hlocal h),
    not_connectedSpace_of_idempotent he he0 he1, t, u, v, w, ht, hn, hu, hv, hw, he, he0, he1⟩
  · rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact hI.symm
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact hI.symm

end

section

private noncomputable def quotientPiHom {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] (I : ∀ j, Ideal (A j)) :
    (((j : J) → A j) ⧸ (Ideal.pi I)) →+* ((j : J) → (A j ⧸ I j)) :=
  Ideal.Quotient.lift (Ideal.pi I)
    (RingHom.pi fun j ↦ (Ideal.Quotient.mk (I j)).comp (Pi.evalRingHom A j)) fun x hx ↦ by
      ext j
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)

private theorem quotientPiHom_mk {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] (I : ∀ j, Ideal (A j)) (x : ∀ j, A j) :
    quotientPiHom A I (Ideal.Quotient.mk (Ideal.pi I) x) =
      fun j ↦ Ideal.Quotient.mk (I j) (x j) := by
  rfl

private theorem quotientPiHom_bijective {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] (I : ∀ j, Ideal (A j)) :
    Function.Bijective (quotientPiHom A I) := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn' with | _ x =>
      induction y using Quotient.inductionOn' with | _ y =>
        apply Ideal.Quotient.eq.mpr
        intro j
        have := congrFun hxy j
        change Ideal.Quotient.mk (I j) (x j) = Ideal.Quotient.mk (I j) (y j) at this
        exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (x j) (y j)).mp this
  · intro y
    choose x hx using fun j ↦ Ideal.Quotient.mk_surjective (y j)
    refine ⟨Ideal.Quotient.mk (Ideal.pi I) x, ?_⟩
    ext j
    simpa only [quotientPiHom_mk] using hx j

private noncomputable def assembleMonic {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] (p : ∀ j, Polynomial (A j)) (n : ℕ) :
    Polynomial ((j : J) → A j) :=
  Polynomial.X ^ n + ∑ k : Fin n,
    Polynomial.C (fun j ↦ (p j).coeff k) * Polynomial.X ^ (k : ℕ)

private theorem assembleMonic_monic {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] (p : ∀ j, Polynomial (A j)) (n : ℕ) :
    (assembleMonic A p n).Monic := by
  apply Polynomial.monic_X_pow_add
  simpa only using Polynomial.degree_sum_fin_lt
    (fun k : Fin n ↦ fun j ↦ (p j).coeff k)

private theorem assembleMonic_map {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] (p : ∀ j, Polynomial (A j)) (n : ℕ)
    (hp : ∀ j, (p j).Monic) (hn : ∀ j, Nontrivial (A j) → (p j).natDegree = n) (j : J) :
    (assembleMonic A p n).map (Pi.evalRingHom A j) = p j := by
  cases subsingleton_or_nontrivial (A j) with
  | inl hs => exact Subsingleton.elim _ _
  | inr hj =>
  let := hj
  rw [assembleMonic, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_C, Pi.evalRingHom_apply]
  simp_rw [Polynomial.map_pow, Polynomial.map_X]
  rw [← hn j hj]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ ↦ Polynomial.C ((p j).coeff k) * Polynomial.X ^ k)]
  exact (hp j).as_sum.symm

private theorem polynomial_eq_of_eval_maps_eq {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] {p q : Polynomial ((j : J) → A j)}
    (h : ∀ j, p.map (Pi.evalRingHom A j) = q.map (Pi.evalRingHom A j)) : p = q := by
  ext n j
  simpa only [Polynomial.coeff_map, Pi.evalRingHom_apply] using
    congrArg (fun r ↦ r.coeff n) (h j)

/-- A product of pairs is henselian if and only if each component pair is henselian. -/
@[stacks 0ATD]
theorem henselianPair_pi_iff {J : Type u} (A : J → Type v) [∀ j, CommRing (A j)]
    (I : ∀ j, Ideal (A j)) :
    HenselianPair ((j : J) → A j) (Ideal.pi I) ↔
      ∀ j, HenselianPair (A j) (I j) := by
  constructor
  · intro h j
    let : Algebra ((k : J) → A k) (A j) := (Pi.evalRingHom A j).toAlgebra
    let : Algebra.IsIntegral ((k : J) → A k) (A j) :=
      ⟨(Pi.evalRingHom A j).isIntegral_of_surjective (Function.surjective_eval j)⟩
    have h' := henselianPair_map_of_isIntegral
      (A := (k : J) → A k) (B := A j) (Ideal.pi I) h
    change HenselianPair (A j) ((Ideal.pi I).map (Pi.evalRingHom A j)) at h'
    simpa only [Ideal.map_evalRingHom_pi] using h'
  · intro h
    rw [HenselianPair]
    constructor
    · intro x hx
      rw [Ideal.mem_jacobson_bot]
      intro y
      rw [Pi.isUnit_iff]
      intro j
      exact (Ideal.mem_jacobson_bot.mp ((h j).1 (hx j))) (y j)
    · intro f hf g₀ h₀ hg₀ hh₀ hfac hcop
      let qpi := quotientPiHom A I
      have hqpi : Function.Bijective qpi := quotientPiHom_bijective A I
      let e : (((j : J) → A j) ⧸ (Ideal.pi I)) ≃+* ((j : J) → (A j ⧸ I j)) :=
        RingEquiv.ofBijective qpi hqpi
      let φ (j : J) : (((j : J) → A j) ⧸ (Ideal.pi I)) →+* (A j ⧸ I j) :=
        (Pi.evalRingHom (fun j ↦ A j ⧸ I j) j).comp e.toRingHom
      have hφmk (j : J) (x : ∀ j, A j) :
          φ j (Ideal.Quotient.mk (Ideal.pi I) x) = Ideal.Quotient.mk (I j) (x j) := by
        rfl
      have hf_j (j : J) : (f.map (Pi.evalRingHom A j)).Monic := hf.map _
      have hg₀_j (j : J) : (g₀.map (φ j)).Monic := hg₀.map _
      have hh₀_j (j : J) : (h₀.map (φ j)).Monic := hh₀.map _
      have hfac_j (j : J) :
          (f.map (Pi.evalRingHom A j)).map (Ideal.Quotient.mk (I j)) =
            g₀.map (φ j) * h₀.map (φ j) := by
        calc
          _ = f.map ((Ideal.Quotient.mk (I j)).comp (Pi.evalRingHom A j)) := by
            rw [Polynomial.map_map]
          _ = f.map ((φ j).comp (Ideal.Quotient.mk (Ideal.pi I))) := by
            congr 1
          _ = (g₀ * h₀).map (φ j) := by rw [← Polynomial.map_map, hfac]
          _ = _ := by rw [Polynomial.map_mul]
      have hcop_j (j : J) : IsCoprime (g₀.map (φ j)) (h₀.map (φ j)) :=
        hcop.map (Polynomial.mapRingHom (φ j))
      choose g h' hg hh hfhg hgred hhred using fun j ↦
        (h j).2 (f.map (Pi.evalRingHom A j)) (hf_j j)
          (g₀.map (φ j)) (h₀.map (φ j)) (hg₀_j j) (hh₀_j j)
          (hfac_j j) (hcop_j j)
      have hdeg (j : J) [Nontrivial (A j)] (u : Polynomial (A j))
          (w : Polynomial (((j : J) → A j) ⧸ Ideal.pi I)) (hu : u.Monic) (hw : w.Monic)
          (hred : u.map (Ideal.Quotient.mk (I j)) = w.map (φ j)) : u.natDegree = w.natDegree := by
        have hIne : I j ≠ ⊤ := by
          intro htop
          have hjac : (⊥ : Ideal (A j)).jacobson = ⊤ := by
            apply top_unique
            simpa only [htop] using (h j).1
          have : (⊥ : Ideal (A j)) = ⊤ := Ideal.jacobson_eq_top_iff.mp hjac
          exact bot_ne_top this
        let : Nontrivial (A j ⧸ I j) := Ideal.Quotient.nontrivial_iff.mpr hIne
        calc
          u.natDegree = (u.map (Ideal.Quotient.mk (I j))).natDegree :=
            (hu.natDegree_map _).symm
          _ = (w.map (φ j)).natDegree := congrArg Polynomial.natDegree hred
          _ = w.natDegree := hw.natDegree_map _
      have hgn (j : J) [Nontrivial (A j)] : (g j).natDegree = g₀.natDegree :=
        hdeg j _ _ (hg j) hg₀ (hgred j)
      have hhn (j : J) [Nontrivial (A j)] : (h' j).natDegree = h₀.natDegree :=
        hdeg j _ _ (hh j) hh₀ (hhred j)
      let G := assembleMonic A g g₀.natDegree
      let H := assembleMonic A h' h₀.natDegree
      have hGmap (j : J) : G.map (Pi.evalRingHom A j) = g j :=
        assembleMonic_map A g _ hg hgn j
      have hHmap (j : J) : H.map (Pi.evalRingHom A j) = h' j :=
        assembleMonic_map A h' _ hh hhn j
      refine ⟨G, H, assembleMonic_monic A g _, assembleMonic_monic A h' _, ?_, ?_, ?_⟩
      · apply polynomial_eq_of_eval_maps_eq A
        intro j
        rw [Polynomial.map_mul, hGmap, hHmap, hfhg]
      all_goals
        apply Polynomial.map_injective qpi hqpi.1
        apply polynomial_eq_of_eval_maps_eq (fun j ↦ A j ⧸ I j)
        intro j
        have hcomp :
            ((Pi.evalRingHom (fun j ↦ A j ⧸ I j) j).comp qpi).comp
                (Ideal.Quotient.mk (Ideal.pi I)) =
              (Ideal.Quotient.mk (I j)).comp (Pi.evalRingHom A j) := by
          ext x
          exact hφmk j x
        rw [Polynomial.map_map, Polynomial.map_map, hcomp, ← Polynomial.map_map]
      · rw [hGmap, hgred]
        show g₀.map ((Pi.evalRingHom (fun j ↦ A j ⧸ I j) j).comp qpi) = _
        rw [Polynomial.map_map]
      · rw [hHmap, hhred]
        show h₀.map ((Pi.evalRingHom (fun j ↦ A j ⧸ I j) j).comp qpi) = _
        rw [Polynomial.map_map]

end

section

private lemma exists_of_compatible
    {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{u})
    (c : Cone F) (hc : IsLimit c) (x : ∀ j, F.obj j)
    (hx : ∀ ⦃j k⦄ (f : j ⟶ k), (F.map f).hom (x j) = x k) :
    ∃ y : c.pt, ∀ j, (c.π.app j).hom y = x j := by
  let d : Cone F :=
    { pt := CommRingCat.of (Polynomial c.pt)
      π :=
        { app := fun j ↦ CommRingCat.ofHom
              (Polynomial.eval₂RingHom (c.π.app j).hom (x j))
          naturality := by
            intro j k f
            show 𝟙 _ ≫ CommRingCat.ofHom
                (Polynomial.eval₂RingHom (c.π.app k).hom (x k)) =
              CommRingCat.ofHom (Polynomial.eval₂RingHom (c.π.app j).hom (x j)) ≫ F.map f
            rw [Category.id_comp]
            apply CommRingCat.hom_ext
            apply Polynomial.ringHom_ext
            · intro a
              simp only [Functor.const_obj_obj, ConcreteCategory.hom_ofHom, coe_eval₂RingHom,
                eval₂_C, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
              exact (ConcreteCategory.congr_hom (c.w f) a).symm
            · simp only [Functor.const_obj_obj, ConcreteCategory.hom_ofHom, coe_eval₂RingHom,
                eval₂_X, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
              exact (hx f).symm } }
  exact ⟨(hc.lift d).hom Polynomial.X, fun j ↦ by
    calc
      (c.π.app j).hom ((hc.lift d).hom Polynomial.X) =
          (d.π.app j).hom Polynomial.X :=
        ConcreteCategory.congr_hom (hc.fac d j) Polynomial.X
      _ = x j := by simp [d]⟩

private lemma eq_of_apply_eq
    {J : Type v} [SmallCategory J] {F : J ⥤ CommRingCat.{u}}
    {c : Cone F} (hc : IsLimit c) {x y : c.pt}
    (h : ∀ j, (c.π.app j).hom x = (c.π.app j).hom y) : x = y := by
  let f : CommRingCat.of (Polynomial c.pt) ⟶ c.pt := CommRingCat.ofHom
    (Polynomial.evalRingHom x)
  let g : CommRingCat.of (Polynomial c.pt) ⟶ c.pt := CommRingCat.ofHom
    (Polynomial.evalRingHom y)
  have hfg : f = g := hc.hom_ext fun j ↦ by
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      simp [f, g]
    · simpa [CommRingCat.comp_apply, f, g] using h j
  simpa [f, g] using ConcreteCategory.congr_hom hfg Polynomial.X

/-- A limit of henselian pairs is a henselian pair. -/
@[stacks 0EM6]
theorem henselianPair_limit
    {J : Type v} [SmallCategory J]
    (F : J ⥤ CommRingCat.{u}) (I : ∀ j, Ideal (F.obj j))
    (hI : ∀ ⦃j k⦄ (f : j ⟶ k), Ideal.map (F.map f).hom (I j) ≤ I k)
    (c : Cone F) (hc : IsLimit c)
    (h : ∀ j, HenselianPair (F.obj j) (I j)) :
    HenselianPair c.pt
      (⨅ j, Ideal.comap (c.π.app j).hom (I j)) := by
  apply ((henselianPair_tfae.{u, u} c.pt
    (⨅ j, Ideal.comap (c.π.app j).hom (I j))).out 5 1).mp
  constructor
  · unfold IsContainedInJacobson
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    have hxj : ∀ j : J, (c.π.app j).hom x ∈ I j := fun j ↦ Ideal.mem_iInf.mp hx j
    have hu : ∀ j : J, IsUnit ((c.π.app j).hom (x * y + (1 : c.pt))) := by
      intro j
      rw [map_add, map_mul, map_one]
      exact Ideal.mem_jacobson_bot.mp ((h j).1 (hxj j)) ((c.π.app j).hom y)
    choose z hz using fun j ↦ isUnit_iff_exists_inv.mp (hu j)
    have hzcompat : ∀ ⦃j k⦄ (f : j ⟶ k), (F.map f).hom (z j) = z k := by
      intro j k f
      apply (hu k).mul_right_cancel
      have hq : (F.map f).hom ((c.π.app j).hom (x * y + (1 : c.pt))) =
          (c.π.app k).hom (x * y + (1 : c.pt)) := by
        simpa only [CommRingCat.comp_apply] using
          ConcreteCategory.congr_hom (c.w f) (x * y + (1 : c.pt))
      calc
        (F.map f).hom (z j) * (c.π.app k).hom (x * y + (1 : c.pt)) =
            (F.map f).hom (z j) *
              (F.map f).hom ((c.π.app j).hom (x * y + (1 : c.pt))) :=
          congrArg ((F.map f).hom (z j) * ·) hq.symm
        _ = (F.map f).hom (z j * (c.π.app j).hom (x * y + (1 : c.pt))) := by rw [map_mul]
        _ = 1 := by rw [mul_comm, hz j, map_one]
        _ = z k * (c.π.app k).hom (x * y + (1 : c.pt)) := by rw [mul_comm, hz k]
    obtain ⟨z, hz'⟩ := exists_of_compatible F c hc z hzcompat
    apply isUnit_iff_exists_inv.mpr
    refine ⟨z, eq_of_apply_eq hc fun j ↦ ?_⟩
    simpa [map_add, map_mul, map_one, hz'] using hz j
  · intro f hf n hn a hfa
    have hj : ∀ j, HenselianPair (F.obj j) (I j) := h
    have hcrit := fun j ↦
      ((henselianPair_tfae.{u, u} (F.obj j) (I j)).out 1 5).mp (hj j)
    let fj : ∀ j, Polynomial (F.obj j) := fun j ↦ f.map (c.π.app j).hom
    let aj : ∀ j, Fin (n + 1) → I j := fun j i ↦
      ⟨(c.π.app j).hom (a i : c.pt), (Ideal.mem_iInf.mp (a i).property j : _)⟩
    have hfj : ∀ j, fj j = Polynomial.X ^ n * (Polynomial.X - 1) +
        ∑ i : Fin (n + 1), Polynomial.C (aj j i : F.obj j) * Polynomial.X ^ (i : ℕ) := by
      intro j
      simp only [fj, hfa, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_sum,
        Polynomial.map_C]
      simp [aj]
    have hmonic : ∀ j, (fj j).Monic := fun j ↦ hf.map _
    choose α hα hαuniq using fun j ↦
      (hcrit j).2 (fj j) (hmonic j) n hn (aj j) (hfj j)
    have hαmem : ∀ j, α j - 1 ∈ I j := fun j ↦ (hα j).1
    have hαroot : ∀ j, (fj j).IsRoot (α j) := fun j ↦ (hα j).2
    have hαcompat : ∀ ⦃j k⦄ (g : j ⟶ k), (F.map g).hom (α j) = α k := by
      intro j k g
      apply hαuniq k
      constructor
      · rw [← (F.map g).hom.map_one, ← map_sub]
        exact hI g (Ideal.mem_map_of_mem _ (hαmem j))
      · have hm : (fj j).map (F.map g).hom = fj k := by
          apply Polynomial.ext
          intro m
          simp only [fj, Polynomial.coeff_map]
          exact ConcreteCategory.congr_hom (c.w g) (f.coeff m)
        rw [← hm]
        exact (hαroot j).map
    obtain ⟨α, hα⟩ := exists_of_compatible F c hc α hαcompat
    refine ⟨α, ⟨?_, ?_⟩, ?_⟩
    · apply Ideal.mem_iInf.mpr
      intro j
      show (c.π.app j).hom (α - (1 : c.pt)) ∈ I j
      simpa [hα j] using hαmem j
    · rw [Polynomial.IsRoot]
      apply eq_of_apply_eq hc
      intro j
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
      simpa [fj, hα j] using hαroot j
    · intro β hβ
      rcases hβ with ⟨hβmem, hβroot⟩
      apply eq_of_apply_eq hc
      intro j
      rw [hα j]
      apply hαuniq j
      constructor
      · simpa using (Ideal.mem_iInf.mp hβmem j : _)
      · simpa [fj] using
          (Polynomial.IsRoot.map (f := (c.π.app j).hom) hβroot)

end

section

private abbrev HenselianIdeal (A : Type u) [CommRing A] :=
  {I : Ideal A // HenselianPair A I}

/-- Every commutative ring has a largest ideal with respect to which it forms a henselian pair. -/
@[stacks 0G1S]
theorem exists_greatest_henselianPair (A : Type u) [CommRing A] :
    ∃ I : Ideal A, HenselianPair A I ∧
      ∀ J : Ideal A, HenselianPair A J → J ≤ I := by
  let : SemilatticeSup (HenselianIdeal A) := {
    sup := fun I J => ⟨I.1 ⊔ J.1, henselianPair_sup I.2 J.2⟩
    le_sup_left := fun I J => (le_sup_left : I.1 ≤ I.1 ⊔ J.1)
    le_sup_right := fun I J => (le_sup_right : J.1 ≤ I.1 ⊔ J.1)
    sup_le := fun I J K hI hJ => (sup_le hI hJ : I.1 ⊔ J.1 ≤ K.1) }
  let : Nonempty (HenselianIdeal A) := ⟨⟨⊥, henselianPair_bot A⟩⟩
  let : IsConnected (HenselianIdeal A) := IsFiltered.isConnected _
  let F : HenselianIdeal A ⥤ CommRingCat.{u} :=
    (Functor.const (HenselianIdeal A)).obj (CommRingCat.of A)
  have hc : IsColimit (constCocone (HenselianIdeal A) (CommRingCat.of A)) :=
    isColimitConstCocone (HenselianIdeal A) (CommRingCat.of A)
  have hcompat : ∀ ⦃j k : HenselianIdeal A⦄ (f : j ⟶ k),
      Ideal.map (F.map f).hom j.1 ≤ k.1 := by
    intro j k f
    simpa [F] using (leOfHom f)
  have hsup : HenselianPair A (⨆ j : HenselianIdeal A, j.1) := by
    have hcol :=
      henselianPair_colimit.{0, u} F (fun j => j.1) hcompat
        (constCocone (HenselianIdeal A) (CommRingCat.of A)) hc (fun j => j.2)
    change HenselianPair A
      (⨆ j : HenselianIdeal A, Ideal.map (RingHom.id A) j.1) at hcol
    simpa only [Ideal.map_id] using hcol
  exact ⟨⨆ j : HenselianIdeal A, j.1, hsup,
    fun J hJ ↦ le_iSup (fun j : HenselianIdeal A => j.1) ⟨J, hJ⟩⟩

end

end
