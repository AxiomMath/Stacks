module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseRestrictionCode
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSpanGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSpanSubcomplex

/-!
# Small quasi-isomorphic subcomplexes of complexes of sheaves of modules

Let `(C, J)` be a site with a dense family of objects `c : ι → C`, and `R` a sheaf of rings on
it, such that the family, the arrows between its members and the rings of sections of `R` over
them are bounded by an infinite cardinal `ν`. This file proves a Löwenheim–Skolem statement for
complexes of sheaves of `R`-modules, the version of Stacks 0GYY for a non-chaotic topology:
**a complex `K` of sheaves of `R`-modules whose homology sheaves have at most `ν` sections over
each member of the family contains a subcomplex with at most `2 ^ ν` sections over each member
of the family, whose inclusion is a quasi-isomorphism**
(`Stacks.SheafOfModules.exists_quasiIso_subcomplex_of_dense`). On a site which is essentially
small relative to a universe `z`, with `z`-small rings of sections, this says that a complex
whose homology sheaves have `z`-small sections contains a subcomplex with `z`-small sections
whose inclusion is a quasi-isomorphism
(`Stacks.SheafOfModules.exists_small_quasiIso_subcomplex_of_small_homology`).

## The argument

The subcomplex is the locally spanned subcomplex of the enlargement of a set of generators
(`Stacks.SheafOfModules.DenseSpan.subcomplex`, `Stacks.SheafOfModules.DenseSpan.enlargement`),
whose inclusion is a quasi-isomorphism under two conditions
(`Stacks.SheafOfModules.DenseSpan.quasiIso_incl`). The enlargement supplies the second (the
boundaries in the span have primitives in the subcomplex). For the first, the starting
generators are **cycle lifts of the homology sections**
(`Stacks.SheafOfModules.HomologyLifts.cycleLifts`): for every section `h` of every homology sheaf
`H^n(K)` over a member of the family, a covering on which `h` lifts to cycles is chosen, and a
cycle lift over every member of that covering whose source is in the family. A cycle `z` of `K`
over a member of the family has a class `h`; on the chosen covering, `z` differs from the chosen
lift by a cycle whose class vanishes, which is locally a boundary
(`Stacks.SheafOfModules.exists_covering_boundary_of_homologyπ_eq_zero`).

## Main results

* `Stacks.SheafOfModules.exists_quasiIso_subcomplex_of_dense`: the cardinal form, over a dense
  family.
* `Stacks.SheafOfModules.exists_small_quasiIso_subcomplex_of_small_homology`: the universe form,
  over an essentially small site.
* `Stacks.SheafOfModules.exists_small_quasiIso_subcomplex_of_small_homology_bounded`: the
  subcomplex also keeps the strict and the cohomological bounds of the complex.

## References

* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal
open Stacks.SheafOfModules.DenseSpan

universe z w t v u u'

namespace Stacks.SheafOfModules

/-! ### Restrictions of sections -/

section Restriction

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A cycle whose class in the homology sheaf vanishes is locally a boundary.** -/
theorem exists_covering_boundary_of_homologyπ_eq_zero
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (_root_.SheafOfModules.{w} R) c) (i j : ι) (hij : c.prev j = i)
    {V : C} (x : (K.cycles j).val.obj (op V)) (hx : (K.homologyπ j).val.app (op V) x = 0) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ ⦃W : C⦄ (p : W ⟶ V), T p →
      ∃ y : (K.X i).val.obj (op W),
        (K.d i j).val.app (op W) y = (K.X j).val.map p.op ((K.iCycles j).val.app (op V) x) := by
  obtain ⟨T, hT, hl⟩ := _root_.SheafOfModules.exists_mem_sieve_of_exact
    (ShortComplex.exact_of_g_is_cokernel
      (ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (K.toCycles_comp_homologyπ i j))
      (K.homologyIsCokernel i j hij)) V x hx
  refine ⟨T, hT, fun W p hp => ?_⟩
  obtain ⟨y, hy⟩ := hl p hp
  refine ⟨y, ?_⟩
  have h₁ : (K.d i j).val.app (op W) y =
      (K.iCycles j).val.app (op W) ((K.toCycles i j).val.app (op W) y) := by
    show (K.d i j).val.app (op W) y = (K.toCycles i j ≫ K.iCycles j).val.app (op W) y
    rw [K.toCycles_i]
  rw [h₁]
  exact (congrArg ((K.iCycles j).val.app (op W)) hy).trans
    (PresheafOfModules.naturality_apply (K.iCycles j).val p.op x)

/-- **A subcomplex of a strictly bounded complex is strictly bounded**, with the same bounds. -/
theorem isStrictlyGE_of_mono {K' K : CochainComplex (_root_.SheafOfModules.{w} R) ℤ}
    (i : K' ⟶ K) [Mono i] (a : ℤ) [K.IsStrictlyGE a] : K'.IsStrictlyGE a :=
  (K'.isStrictlyGE_iff a).2 fun n hn => (K.isZero_of_isStrictlyGE a n hn).of_mono (i.f n)

/-- The upper half of `Stacks.SheafOfModules.isStrictlyGE_of_mono`. -/
theorem isStrictlyLE_of_mono {K' K : CochainComplex (_root_.SheafOfModules.{w} R) ℤ}
    (i : K' ⟶ K) [Mono i] (b : ℤ) [K.IsStrictlyLE b] : K'.IsStrictlyLE b :=
  (K'.isStrictlyLE_iff b).2 fun n hn => (K.isZero_of_isStrictlyLE b n hn).of_mono (i.f n)

end Restriction

/-! ### Cycle lifts of the homology sections -/

namespace HomologyLifts

variable {C : Type u'} [Category.{t} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {ι : Type t} (c : ι → C) (K : CochainComplex (_root_.SheafOfModules.{t} R) ℤ)

/-- The chosen covering on which a section of a homology sheaf lifts to cycles. -/
def cycleLiftCover (n : ℤ) (i : ι) (h : (K.homology n).val.obj (op (c i))) : Sieve (c i) :=
  Classical.choose (_root_.SheafOfModules.exists_mem_sieve_of_epi (K.homologyπ n) (c i) h)

/-- The chosen covering of `cycleLiftCover` is a covering sieve. -/
theorem cycleLiftCover_mem (n : ℤ) (i : ι) (h : (K.homology n).val.obj (op (c i))) :
    cycleLiftCover c K n i h ∈ J (c i) :=
  (Classical.choose_spec
    (_root_.SheafOfModules.exists_mem_sieve_of_epi (K.homologyπ n) (c i) h)).1

/-- The chosen cycle lift of a section of a homology sheaf over a member of its covering. -/
def cycleLift (n : ℤ) (i : ι) (h : (K.homology n).val.obj (op (c i))) (i' : ι) (a : c i' ⟶ c i)
    (ha : cycleLiftCover c K n i h a) : (K.cycles n).val.obj (op (c i')) :=
  Classical.choose ((Classical.choose_spec
    (_root_.SheafOfModules.exists_mem_sieve_of_epi (K.homologyπ n) (c i) h)).2 a ha)

/-- The chosen cycle lift `cycleLift` maps to the restriction of the homology section it lifts. -/
theorem homologyπ_cycleLift (n : ℤ) (i : ι) (h : (K.homology n).val.obj (op (c i))) (i' : ι)
    (a : c i' ⟶ c i) (ha : cycleLiftCover c K n i h a) :
    (K.homologyπ n).val.app (op (c i')) (cycleLift c K n i h i' a ha) =
      (K.homology n).val.map a.op h :=
  Classical.choose_spec ((Classical.choose_spec
    (_root_.SheafOfModules.exists_mem_sieve_of_epi (K.homologyπ n) (c i) h)).2 a ha)

/-- The indices of the cycle lifts. -/
abbrev CycleLiftIndex : Type t :=
  Σ (n : ℤ) (i : ι) (h : (K.homology n).val.obj (op (c i))) (i' : ι),
    {a : c i' ⟶ c i // cycleLiftCover c K n i h a}

/-- **The cycle lifts of the homology sections**, as generators. -/
def cycleLifts : Gens c K :=
  Set.range fun x : CycleLiftIndex c K => (⟨x.1, x.2.2.2.1, (K.iCycles x.1).val.app _
    (cycleLift c K x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2)⟩ : GenType c K)

/-- The cycle lifts are bounded by `ν` when the family, its arrows and the sections of the
homology sheaves over it are. -/
theorem mk_cycleLifts_le {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hι : #ι ≤ ν)
    (hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν)
    (hH : ∀ (n : ℤ) (i : ι), #((K.homology n).val.obj (op (c i))) ≤ ν) : #(cycleLifts c K) ≤ ν :=
  Cardinal.mk_range_le.trans (mk_sigma_int_le hν fun n => mk_sigma_le_of_le hν hι fun i =>
    mk_sigma_le_of_le hν (hH n i) fun _ => mk_sigma_le_of_le hν hι fun i' =>
      (Cardinal.mk_subtype_le _).trans (hHom i' i))

variable [(inducedFunctor c).IsCoverDense J]

/-- **Every cycle over a member of the family is locally homologous to a cycle of the locally
spanned subcomplex**, as soon as the generators contain the cycle lifts of the homology
sections. This is the first condition of `Stacks.SheafOfModules.DenseSpan.quasiIso_incl`. -/
theorem exists_mem_closure_of_cycleLifts_subset (G : Gens c K) (hG : cycleLifts c K ⊆ G) (j n k : ℤ)
    (hj : j + 1 = n) (hk : n + 1 = k) (i : ι) (z : (K.X n).val.obj (op (c i)))
    (hz : (K.d n k).val.app (op (c i)) z = 0) :
    ∃ S : Sieve (c i), S ∈ J (c i) ∧ ∀ ⦃W : C⦄ (b : W ⟶ c i), S b →
      ∃ p : (K.X n).val.obj (op W), p ∈ (closure G n).obj (op W) ∧
        (K.d n k).val.app (op W) p = 0 ∧
        ∃ y : (K.X j).val.obj (op W),
          (K.X n).val.map b.op z = p + (K.d j n).val.app (op W) y := by
  obtain ⟨ξ, hξ⟩ := _root_.SheafOfModules.exists_iCycles_section K n k hk (op (c i)) z hz
  let h := (K.homologyπ n).val.app (op (c i)) ξ
  refine exists_mem_sieve_of_dense (c := c) (cycleLiftCover c K n i h)
    (cycleLiftCover_mem c K n i h)
    fun i' a ha => ?_
  let c' := cycleLift c K n i h i' a ha
  have hc' : (⟨n, i', (K.iCycles n).val.app _ c'⟩ : GenType c K) ∈ G :=
    hG ⟨⟨n, i, h, i', a, ha⟩, rfl⟩
  have hπ : (K.homologyπ n).val.app _ ((K.cycles n).val.restrictₛₗ a.op ξ - c') = 0 := by
    rw [map_sub, show (K.homologyπ n).val.app _ ((K.cycles n).val.restrictₛₗ a.op ξ)
      = (K.homology n).val.restrictₛₗ a.op ((K.homologyπ n).val.app _ ξ) from
        PresheafOfModules.naturality_apply (K.homologyπ n).val a.op ξ, homologyπ_cycleLift]
    exact sub_self _
  obtain ⟨S, hS, hl⟩ := exists_covering_boundary_of_homologyπ_eq_zero K j n
    (by simp; omega) _ hπ
  refine ⟨S, hS, fun W b hb => ?_⟩
  obtain ⟨y, hy⟩ := hl b hb
  have hd : (K.d n k).val.app (op W) ((K.X n).val.restrictₛₗ b.op ((K.iCycles n).val.app _ c'))
      = 0 := by
    refine (PresheafOfModules.naturality_apply (K.d n k).val b.op _).trans ?_
    show (K.X k).val.restrictₛₗ b.op ((K.iCycles n ≫ K.d n k).val.app _ c') = 0
    rw [K.iCycles_d]
    exact map_zero _
  refine ⟨(K.X n).val.restrictₛₗ b.op ((K.iCycles n).val.app _ c'),
    (closure G n).map b.op (mem_closure_of_mem G hc'), hd, y, ?_⟩
  have key : (K.X n).val.restrictₛₗ (b ≫ a).op z =
      (K.X n).val.restrictₛₗ b.op ((K.iCycles n).val.app _ c') +
        (K.d j n).val.app (op W) y := by
    rw [hy]
    show _ = _ + (K.X n).val.restrictₛₗ b.op
      ((K.iCycles n).val.app _ ((K.cycles n).val.restrictₛₗ a.op ξ - c'))
    rw [map_sub, show (K.iCycles n).val.app _ ((K.cycles n).val.restrictₛₗ a.op ξ)
      = (K.X n).val.restrictₛₗ a.op ((K.iCycles n).val.app _ ξ) from
        PresheafOfModules.naturality_apply (K.iCycles n).val a.op ξ, hξ, map_sub, add_sub_cancel,
      op_comp]
    exact PresheafOfModules.map_comp_apply (K.X n).val a.op b.op z
  exact key

end HomologyLifts

/-! ### The theorem over a dense family -/

section Dense

variable {C : Type u'} [Category.{t} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {ι : Type t} (c : ι → C) [(inducedFunctor c).IsCoverDense J]

/-- **Löwenheim–Skolem for complexes of sheaves of modules, over a dense family** (a version of
Stacks 0GYY for a non-chaotic topology). Let `c : ι → C` be a dense family of objects such that
`ι`, the arrows between the `c i` and the rings of sections of `R` over the `c i` are bounded by
an infinite cardinal `ν`. Every cochain complex `K` of sheaves of `R`-modules whose homology
sheaves have at most `ν` sections over each `c i` contains a subcomplex with at most `2 ^ ν`
sections over each `c i`, whose inclusion is a quasi-isomorphism. -/
theorem exists_quasiIso_subcomplex_of_dense {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν) (hι : #ι ≤ ν)
    (hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν) (hR : ∀ i : ι, #(R.obj.obj (op (c i))) ≤ ν)
    (K : CochainComplex (_root_.SheafOfModules.{t} R) ℤ)
    (hK : ∀ (n : ℤ) (i : ι), #((K.homology n).val.obj (op (c i))) ≤ ν) :
    ∃ (K' : CochainComplex (_root_.SheafOfModules.{t} R) ℤ) (f : K' ⟶ K),
      Mono f ∧ QuasiIso f ∧ ∀ (n : ℤ) (i : ι), #((K'.X n).val.obj (op (c i))) ≤ 2 ^ ν := by
  have hGd := isDClosed_enlargement (HomologyLifts.cycleLifts c K)
  have hG : #(enlargement (HomologyLifts.cycleLifts c K)) ≤ ν :=
    mk_enlargement_le hν hι hHom hR _ (HomologyLifts.mk_cycleLifts_le c K hν hι hHom hK)
  have hνle : ν ≤ 2 ^ ν := (Cardinal.cantor ν).le
  refine ⟨subcomplex hGd, incl hGd, HomologicalComplex.mono_of_mono_f _ fun n => ?_,
    quasiIso_incl hGd
      (HomologyLifts.exists_mem_closure_of_cycleLifts_subset c K _ (subset_enlargement _))
      (exists_mem_closure_d_eq_of_enlargement _), fun n i => ?_⟩
  · show Mono (closure (enlargement (HomologyLifts.cycleLifts c K)) n).ι
    infer_instance
  · refine (Cardinal.mk_le_of_injective (injective_restrictSpan (c := c) n i)).trans ?_
    refine DenseCode.mk_pi_le_two_power hν (mk_sigma_le_of_le hν hι (fun j => hHom j i))
      (fun a => ?_)
    rw [Cardinal.mk_option]
    exact (Cardinal.add_le_of_le hν (mk_span_obj_le _ hν hG hι hHom hR n a.1)
      (Cardinal.one_le_aleph0.trans hν)).trans hνle

end Dense

/-! ### The theorem over an essentially small site -/

section EssentiallySmall

variable {C : Type u'} [Category.{max z w} C] {J : GrothendieckTopology C}

/-- The objects of a small model of an essentially small site form a dense family. -/
theorem isCoverDense_smallModel [EssentiallySmall.{z} C] :
    (inducedFunctor fun Y : ULift.{w} (SmallModel.{z} C) =>
      (equivSmallModel.{z} C).inverse.obj Y.down).IsCoverDense J :=
  Functor.isCoverDense_of_generate_singleton_functor_π_mem _ J fun B =>
    ⟨⟨(equivSmallModel.{z} C).functor.obj B⟩, ((equivSmallModel.{z} C).unitIso.app B).inv, by
      rw [Sieve.generate_of_singleton_isSplitEpi]
      exact J.top_mem B⟩

/-- A type in the universe `max z w` bounded by the universe lift of a cardinal of the universe
`z` is `z`-small. -/
theorem small_of_mk_le_lift {α : Type (max z w)} {κ : Cardinal.{z}}
    (h : #α ≤ Cardinal.lift.{w} κ) : Small.{z} α := by
  rw [← Cardinal.mk_out κ, ← Cardinal.mk_uLift, Cardinal.le_def] at h
  obtain ⟨e⟩ := h
  exact small_of_injective e.injective

/-- A type in the universe `max z w` injecting into a type of the universe `z` is bounded by the
lift of the cardinal of that type. -/
theorem mk_le_lift_of_injective {α : Type (max z w)} {β : Type z} {f : α → β}
    (hf : Function.Injective f) : #α ≤ Cardinal.lift.{w} #β := by
  rw [← Cardinal.mk_uLift]
  exact Cardinal.mk_le_of_injective (f := fun a => ULift.up.{w} (f a))
    fun a a' h => hf (congrArg ULift.down h)

variable {R : Sheaf J RingCat.{max z w}}
  [HasSheafify J AddCommGrpCat.{max z w}] [J.WEqualsLocallyBijective AddCommGrpCat.{max z w}]

omit [HasSheafify J AddCommGrpCat.{max z w}] [J.WEqualsLocallyBijective AddCommGrpCat.{max z w}] in
/-- Sections of a sheaf of modules over isomorphic objects have the same smallness. -/
theorem small_val_obj_of_iso (M : _root_.SheafOfModules.{max z w} R) {X Y : C} (φ : X ≅ Y)
    (hY : Small.{z} (M.val.obj (op Y))) : Small.{z} (M.val.obj (op X)) := by
  have key : ∀ x : M.val.obj (op X),
      M.val.restrictₛₗ φ.hom.op (M.val.restrictₛₗ φ.inv.op x) = x := fun x =>
    (PresheafOfModules.map_comp_apply M.val φ.inv.op φ.hom.op x).symm.trans (by
      rw [← op_comp, φ.hom_inv_id, op_id, M.val.map_id]
      rfl)
  exact small_of_injective (f := fun x => M.val.restrictₛₗ φ.inv.op x) fun x x' h =>
    (key x).symm.trans ((congrArg (M.val.restrictₛₗ φ.hom.op) h).trans (key x'))

/-- **Löwenheim–Skolem for complexes of sheaves of modules** (a version of Stacks 0GYY for a
non-chaotic topology). Let `(C, J)` be a site which is essentially small relative to a universe
`z`, and `R` a sheaf of rings with `z`-small rings of sections. Every cochain complex `K` of
sheaves of `R`-modules whose homology sheaves have `z`-small sections contains a subcomplex with
`z`-small sections whose inclusion is a quasi-isomorphism. -/
theorem exists_small_quasiIso_subcomplex_of_small_homology [EssentiallySmall.{z} C]
    [hR : ∀ X, Small.{z} (R.obj.obj X)]
    (K : CochainComplex (_root_.SheafOfModules.{max z w} R) ℤ)
    (hK : ∀ (n : ℤ) (X : Cᵒᵖ), Small.{z} ((K.homology n).val.obj X)) :
    ∃ (K' : CochainComplex (_root_.SheafOfModules.{max z w} R) ℤ) (f : K' ⟶ K),
      Mono f ∧ QuasiIso f ∧ ∀ (n : ℤ) (X : Cᵒᵖ), Small.{z} ((K'.X n).val.obj X) := by
  let e := equivSmallModel.{z} C
  let ι := ULift.{w} (SmallModel.{z} C)
  let c : ι → C := fun Y => e.inverse.obj Y.down
  have := isCoverDense_smallModel.{z, w} (C := C) (J := J)
  have : ∀ i j : ι, Small.{z} (c i ⟶ c j) := fun _ _ => LocallySmall.hom_small _ _
  -- one `z`-small type through which all the bounds factor
  let T : Type z := ULift.{z} ℕ ⊕ SmallModel.{z} C ⊕
    (Σ p : SmallModel.{z} C × SmallModel.{z} C, Shrink.{z} (c ⟨p.1⟩ ⟶ c ⟨p.2⟩)) ⊕
    (Σ Y : SmallModel.{z} C, Shrink.{z} (R.obj.obj (op (c ⟨Y⟩)))) ⊕
    (Σ p : ℤ × SmallModel.{z} C, Shrink.{z} ((K.homology p.1).val.obj (op (c ⟨p.2⟩))))
  let ν : Cardinal.{max z w} := Cardinal.lift.{w} #T
  have hν : ℵ₀ ≤ ν := by
    refine Cardinal.aleph0_le_lift.2 ?_
    have := Cardinal.mk_le_of_injective (f := fun n : ULift.{z} ℕ => (Sum.inl n : T))
      Sum.inl_injective
    rwa [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] at this
  have hι : #ι ≤ ν := by
    rw [Cardinal.mk_uLift]
    exact Cardinal.lift_le.2 (Cardinal.mk_le_of_injective (f := fun Y => (Sum.inr (Sum.inl Y) : T))
      fun _ _ h => Sum.inl_injective (Sum.inr_injective h))
  have bound : ∀ {α : Type (max z w)} [Small.{z} α] (s : Shrink.{z} α → T),
      Function.Injective s → #α ≤ ν := fun s hs =>
    mk_le_lift_of_injective (hs.comp (equivShrink _).injective)
  have hHom : ∀ i j : ι, #(c i ⟶ c j) ≤ ν := fun i j =>
    bound (fun y => Sum.inr (Sum.inr (Sum.inl ⟨(i.down, j.down), y⟩))) fun _ _ h =>
      sigma_mk_injective (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h)))
  have hRb : ∀ i : ι, #(R.obj.obj (op (c i))) ≤ ν := fun i =>
    bound (fun r => Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i.down, r⟩)))) fun _ _ h =>
      sigma_mk_injective
        (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h))))
  have hKb : ∀ (n : ℤ) (i : ι), #((K.homology n).val.obj (op (c i))) ≤ ν := fun n i =>
    bound (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨(n, i.down), x⟩)))) fun _ _ h =>
      sigma_mk_injective
        (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective (Sum.inr_injective h))))
  obtain ⟨K', f, hf, hq, hs⟩ := exists_quasiIso_subcomplex_of_dense c hν hι hHom hRb K hKb
  refine ⟨K', f, hf, hq, fun n X => ?_⟩
  have hY : Small.{z} ((K'.X n).val.obj (op (c ⟨e.functor.obj X.unop⟩))) :=
    small_of_mk_le_lift (κ := (2 : Cardinal.{z}) ^ #T)
      ((hs n ⟨e.functor.obj X.unop⟩).trans (Cardinal.lift_two_power.{w} #T).symm.le)
  exact small_val_obj_of_iso (K'.X n) (e.unitIso.app X.unop) hY

/-- **The bounded form of
`Stacks.SheafOfModules.exists_small_quasiIso_subcomplex_of_small_homology`.** The small
quasi-isomorphic subcomplex keeps every strict bound of the complex, and every cohomological
bound. -/
theorem exists_small_quasiIso_subcomplex_of_small_homology_bounded [EssentiallySmall.{z} C]
    [∀ X, Small.{z} (R.obj.obj X)] (K : CochainComplex (_root_.SheafOfModules.{max z w} R) ℤ)
    (hK : ∀ (n : ℤ) (X : Cᵒᵖ), Small.{z} ((K.homology n).val.obj X)) :
    ∃ (K' : CochainComplex (_root_.SheafOfModules.{max z w} R) ℤ) (i : K' ⟶ K),
      Mono i ∧ QuasiIso i ∧ (∀ (n : ℤ) (X : Cᵒᵖ), Small.{z} ((K'.X n).val.obj X)) ∧
        (∀ a : ℤ, K.IsStrictlyGE a → K'.IsStrictlyGE a) ∧
        (∀ b : ℤ, K.IsStrictlyLE b → K'.IsStrictlyLE b) ∧
        (∀ a : ℤ, K.IsGE a → K'.IsGE a) ∧ (∀ b : ℤ, K.IsLE b → K'.IsLE b) := by
  obtain ⟨K', i, hi, hq, hs⟩ := exists_small_quasiIso_subcomplex_of_small_homology.{z, w} K hK
  have hz : ∀ n, IsZero (K.homology n) → K'.ExactAt n := fun n h =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (h.of_iso (asIso (HomologicalComplex.homologyMap i n)))
  exact ⟨K', i, hi, hq, hs, fun a _ => isStrictlyGE_of_mono i a,
    fun b _ => isStrictlyLE_of_mono i b,
    fun a ha => (K'.isGE_iff a).2 fun n hn => hz n (K.isZero_of_isGE a n hn),
    fun b hb => (K'.isLE_iff b).2 fun n hn => hz n (K.isZero_of_isLE b n hn)⟩

end EssentiallySmall

end Stacks.SheafOfModules

end
