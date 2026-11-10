module

public import StacksFrontier.Algebra.MittagLeffler.Criteria
public import StacksFrontier.RingTheory.Module.DirectLimit.Countable
public import StacksFrontier.Algebra.MittagLeffler.InverseSystem

/-!
# Endomorphisms through finitely presented modules of a countably generated Mittag-Leffler module

Let `R` be a commutative ring and let `M` be an `R`-module which is Mittag-Leffler and countably
generated. Then for every `R`-module map `f : P → M` out of a finitely generated `R`-module `P`
there is an endomorphism `α : M → M` which factors through a finitely presented `R`-module and
satisfies `α ∘ f = f`.

## Main results

* `Module.exists_end_factorization_finitePresentation_of_countable_span_of_mittagLeffler`: the
  existence of such an endomorphism `α`.

## Implementation notes

The Mittag-Leffler hypothesis is condition (1) of Stacks 059E written out, that is
`Module.IsMittagLefflerKerEq R M` unfolded: every map `f : P → M` from a finitely presented module
dominates and is dominated by a map `g : P → Q` into a finitely presented module, domination
meaning `Ker (f ⊗ id_T) = Ker (g ⊗ id_T)` for every `R`-module `T`.

The test modules of the Mittag-Leffler condition live in the universe `v` of `M`, whence
`Small.{v} R`: without it a finitely presented `R`-module need not be isomorphic to one in
`Type v`, and the condition as written would not be the source's. With `Small.{v} R` the two
agree, by Stacks 059C, and the hypothesis holds automatically when `R` and `M` share a universe.
For the same reason the finitely presented module through which `α` factors is taken in `Type v`,
which is no restriction: a finitely presented `R`-module is a quotient of some `Rⁿ`, hence
`Small.{v}` once `R` is, hence isomorphic to one in `Type v`. The module `P` lives in its own
universe `w`.

Countable generation is written as the existence of a countable spanning set,
`∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤`. "Factors through a finitely presented
module" is the equation `α = v ∘ₗ u` for maps `u : M → Q` and `v : Q → M` with `Q` finitely
presented, the shape of `Module.Flat.exists_factorization_of_finitePresentation`.

The colimit presentation of `M` is packaged, in
`Stacks.MittagLeffler.Endomorphisms.exists_countable_fp_presentation`, as concrete data — a
countable directed preorder, a family of finitely presented modules, transition maps, legs, joint
surjectivity and the vanishing criterion — rather than as a cocone, so that the rest of the proof
is elementary module theory. Its universal property is
`Stacks.MittagLeffler.Endomorphisms.exists_lift`.

## References

* [StacksProject 05D2](https://stacks.math.columbia.edu/tag/05D2)
-/

@[expose] public section

universe u v w

namespace Stacks.MittagLeffler.Endomorphisms

/-- The universal property of a concrete directed colimit presentation of `M`: a family of maps
out of the members, compatible with the transition maps, descends to `M`. -/
private theorem exists_lift {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {J : Type w} [Preorder J] [IsDirected J (· ≤ ·)]
    {Q : J → Type v} [∀ i, AddCommGroup (Q i)] [∀ i, Module R (Q i)]
    {t : ∀ ⦃i i' : J⦄, i ≤ i' → (Q i →ₗ[R] Q i')} {g : ∀ i, Q i →ₗ[R] M}
    (ht : ∀ ⦃i i' i'' : J⦄ (h : i ≤ i') (h' : i' ≤ i'') (x : Q i),
      t h' (t h x) = t (h.trans h') x)
    (hg : ∀ ⦃i i' : J⦄ (h : i ≤ i') (x : Q i), g i' (t h x) = g i x)
    (hsurj : ∀ m : M, ∃ (i : J) (x : Q i), g i x = m)
    (hzero : ∀ (i : J) (x : Q i), g i x = 0 → ∃ (i' : J) (h : i ≤ i'), t h x = 0)
    {Z : Type*} [AddCommGroup Z] [Module R Z] (ψ : ∀ i, Q i →ₗ[R] Z)
    (hψ : ∀ ⦃i i' : J⦄ (h : i ≤ i') (x : Q i), ψ i' (t h x) = ψ i x) :
    ∃ ζ : M →ₗ[R] Z, ∀ (i : J) (x : Q i), ζ (g i x) = ψ i x := by
  classical
  have key : ∀ (i i' : J) (x : Q i) (x' : Q i'), g i x = g i' x' → ψ i x = ψ i' x' := by
    intro i i' x x' hx
    obtain ⟨l, hil, hi'l⟩ := directed_of (· ≤ ·) i i'
    have h0 : g l (t hil x - t hi'l x') = 0 := by
      rw [map_sub, hg, hg, hx, sub_self]
    obtain ⟨l', hll', hz⟩ := hzero l _ h0
    rw [map_sub, sub_eq_zero] at hz
    have e1 : ψ l' (t (hil.trans hll') x) = ψ l' (t (hi'l.trans hll') x') := by
      rw [← ht hil hll', ← ht hi'l hll', hz]
    rw [hψ, hψ] at e1
    exact e1
  choose idx elt helt using hsurj
  refine ⟨{ toFun := fun m => ψ (idx m) (elt m)
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro m m'
    obtain ⟨l, h1, h2⟩ := directed_of (· ≤ ·) (idx m) (idx m')
    have hl : g l (t h1 (elt m) + t h2 (elt m')) = m + m' := by
      rw [map_add, hg, hg, helt, helt]
    have hk := key _ l _ _ ((helt (m + m')).trans hl.symm)
    rw [hk, map_add, hψ, hψ]
  · intro r m
    have hl : g (idx m) (r • elt m) = r • m := by rw [map_smul, helt]
    have hk := key _ _ _ _ ((helt (r • m)).trans hl.symm)
    rw [hk, map_smul]
    rfl
  · intro i x
    exact key _ _ _ _ (helt (g i x))

open CategoryTheory Limits

noncomputable section Presentation

variable (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]

/-- A `v`-small copy of the free `R`-module on the underlying set of `M`. -/
private abbrev Fr : Type v := Shrink.{v} (M →₀ R)

/-- The identification of `Fr R M` with the free `R`-module on the set `M`. -/
private abbrev frEquiv : Fr R M ≃ₗ[R] (M →₀ R) := Shrink.linearEquiv R (M →₀ R)

/-- The canonical surjection of the free module on the set `M` onto `M`. -/
private def frProj : Fr R M →ₗ[R] M :=
  Finsupp.linearCombination R id ∘ₗ (frEquiv R M).toLinearMap

private lemma frProj_surjective : Function.Surjective (frProj R M) := by
  intro m
  exact ⟨(frEquiv R M).symm (Finsupp.single m 1), by simp [frProj]⟩

/-- The submodule of `Fr R M` spanned by the basis vectors indexed by a finite subset of `M`;
it is free of finite rank, hence finitely presented. -/
private def frSupp (S : Finset M) : Submodule R (Fr R M) :=
  (Finsupp.supported R R (S : Set M)).comap (frEquiv R M).toLinearMap

omit [AddCommGroup M] [Module R M] in
private lemma mem_frSupp {S : Finset M} {x : Fr R M} :
    x ∈ frSupp R M S ↔ ((frEquiv R M x).support : Set M) ⊆ (S : Set M) :=
  Finsupp.mem_supported R _

omit [AddCommGroup M] [Module R M] in
private lemma frSupp_mono {S S' : Finset M} (h : S ⊆ S') : frSupp R M S ≤ frSupp R M S' :=
  Submodule.comap_mono (Finsupp.supported_mono (by exact_mod_cast h))

omit [AddCommGroup M] [Module R M] in
private lemma exists_mem_frSupp (x : Fr R M) : ∃ S : Finset M, x ∈ frSupp R M S :=
  ⟨(frEquiv R M x).support, (mem_frSupp R M).mpr subset_rfl⟩

omit [AddCommGroup M] [Module R M] in
private lemma finitePresentation_frSupp (S : Finset M) :
    Module.FinitePresentation R ↥(frSupp R M S) := by
  have h : frSupp R M S
      = Submodule.map (frEquiv R M).symm.toLinearMap (Finsupp.supported R R (S : Set M)) :=
    Submodule.comap_equiv_eq_map_symm (frEquiv R M) _
  have e : ↥(Finsupp.supported R R (S : Set M)) ≃ₗ[R] ↥(frSupp R M S) :=
    ((frEquiv R M).symm.submoduleMap _).trans (LinearEquiv.ofEq _ _ h.symm)
  have e2 : ↥(Finsupp.supported R R (S : Set M)) ≃ₗ[R] (↥(S : Set M) → R) :=
    (Finsupp.supportedEquivFinsupp (M := R) (R := R) (S : Set M)).trans
      (Finsupp.linearEquivFunOnFinite R R ↥(S : Set M))
  have hfp : Module.FinitePresentation R ↥(Finsupp.supported R R (S : Set M)) :=
    e2.finitePresentation_iff.mpr inferInstance
  exact e.finitePresentation_iff.mp hfp

/-- The index type of the presenting system of `M`: a finite set of elements of `M`, to be the
generators, together with a finite set of relations among them. -/
private abbrev Idx : Type v :=
  {q : Finset M × Finset ↥(LinearMap.ker (frProj R M)) //
    ∀ t ∈ q.2, (t : Fr R M) ∈ frSupp R M q.1}

/-- The submodule of `Fr R M` generated by a finite set of relations. -/
private def relSpan (T : Finset ↥(LinearMap.ker (frProj R M))) : Submodule R (Fr R M) :=
  Submodule.span R (Subtype.val '' (T : Set ↥(LinearMap.ker (frProj R M))))

private lemma relSpan_le_ker (T : Finset ↥(LinearMap.ker (frProj R M))) :
    relSpan R M T ≤ LinearMap.ker (frProj R M) := by
  rw [relSpan, Submodule.span_le]
  rintro _ ⟨t, -, rfl⟩
  exact t.2

private lemma relSpan_mono {T T' : Finset ↥(LinearMap.ker (frProj R M))} (h : T ⊆ T') :
    relSpan R M T ≤ relSpan R M T' :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

private lemma mem_relSpan {T : Finset ↥(LinearMap.ker (frProj R M))}
    {t : ↥(LinearMap.ker (frProj R M))} (ht : t ∈ T) : (t : Fr R M) ∈ relSpan R M T :=
  Submodule.subset_span ⟨t, by exact_mod_cast ht, rfl⟩

/-- The relations of the stage `q`, as a submodule of the free module on its generators. -/
private def relSub (q : Idx R M) : Submodule R ↥(frSupp R M q.1.1) :=
  (relSpan R M q.1.2).comap (frSupp R M q.1.1).subtype

/-- The `q`-th member of the presenting system of `M`: the free module on the generators of `q`
modulo the relations of `q`. -/
private abbrev Stage (q : Idx R M) : Type v := ↥(frSupp R M q.1.1) ⧸ relSub R M q

private lemma relSub_fg (q : Idx R M) : (relSub R M q).FG := by
  have hsub : Subtype.val '' (q.1.2 : Set ↥(LinearMap.ker (frProj R M)))
      ⊆ (frSupp R M q.1.1 : Set (Fr R M)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact q.2 t (by exact_mod_cast ht)
  have hmap : Submodule.map (frSupp R M q.1.1).subtype
      (Submodule.span R ((frSupp R M q.1.1).subtype ⁻¹'
        (Subtype.val '' (q.1.2 : Set ↥(LinearMap.ker (frProj R M))))))
      = relSpan R M q.1.2 := by
    rw [relSpan, Submodule.map_span, Set.image_preimage_eq_inter_range]
    congr 1
    have hr : Set.range ((frSupp R M q.1.1).subtype : ↥(frSupp R M q.1.1) → Fr R M)
        = (frSupp R M q.1.1 : Set (Fr R M)) := by simp
    rw [hr]
    exact Set.inter_eq_self_of_subset_left hsub
  have hrel : relSub R M q = Submodule.span R ((frSupp R M q.1.1).subtype ⁻¹'
      (Subtype.val '' (q.1.2 : Set ↥(LinearMap.ker (frProj R M))))) := by
    rw [relSub, ← hmap, Submodule.comap_map_eq_self]
    simp
  rw [hrel]
  refine Submodule.fg_span (Set.Finite.preimage ?_ ?_)
  · exact Subtype.val_injective.injOn
  · exact (q.1.2.finite_toSet).image _

private lemma finitePresentation_stage (q : Idx R M) :
    Module.FinitePresentation R (Stage R M q) := by
  have := finitePresentation_frSupp R M q.1.1
  refine Module.finitePresentation_of_surjective (relSub R M q).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  exact relSub_fg R M q

private lemma relSub_le_comap {q q' : Idx R M} (h : q ≤ q') :
    relSub R M q ≤ (relSub R M q').comap (Submodule.inclusion (frSupp_mono R M h.1)) :=
  fun _ hy => relSpan_mono R M h.2 hy

/-- The transition map of the presenting system: adding generators and relations. -/
private def stageMap {q q' : Idx R M} (h : q ≤ q') : Stage R M q →ₗ[R] Stage R M q' :=
  Submodule.mapQ _ _ (Submodule.inclusion (frSupp_mono R M h.1)) (relSub_le_comap R M h)

private lemma stageMap_mk {q q' : Idx R M} (h : q ≤ q') (a : ↥(frSupp R M q.1.1)) :
    stageMap R M h (Submodule.Quotient.mk a)
      = Submodule.Quotient.mk (Submodule.inclusion (frSupp_mono R M h.1) a) := rfl

private lemma stageMap_self (q : Idx R M) (x : Stage R M q) : stageMap R M le_rfl x = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a => rw [stageMap_mk]; rfl

private lemma stageMap_stageMap {q q' q'' : Idx R M} (h : q ≤ q') (h' : q' ≤ q'')
    (x : Stage R M q) : stageMap R M h' (stageMap R M h x) = stageMap R M (h.trans h') x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a => rw [stageMap_mk, stageMap_mk, stageMap_mk]; rfl

/-- The canonical map from the `q`-th member of the presenting system to `M`. -/
private def stageLeg (q : Idx R M) : Stage R M q →ₗ[R] M :=
  Submodule.liftQ _ (frProj R M ∘ₗ (frSupp R M q.1.1).subtype)
    (fun _ hy => relSpan_le_ker R M q.1.2 hy)

private lemma stageLeg_mk (q : Idx R M) (a : ↥(frSupp R M q.1.1)) :
    stageLeg R M q (Submodule.Quotient.mk a) = frProj R M a := rfl

private lemma stageLeg_stageMap {q q' : Idx R M} (h : q ≤ q') (x : Stage R M q) :
    stageLeg R M q' (stageMap R M h x) = stageLeg R M q x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a => rw [stageMap_mk]; rfl

private lemma exists_stageLeg_eq (m : M) :
    ∃ (q : Idx R M) (x : Stage R M q), stageLeg R M q x = m := by
  obtain ⟨v, hv⟩ := frProj_surjective R M m
  obtain ⟨S, hS⟩ := exists_mem_frSupp R M v
  exact ⟨⟨(S, ∅), by simp⟩, Submodule.Quotient.mk ⟨v, hS⟩, hv⟩

private lemma exists_stageMap_eq_zero (q : Idx R M) (x : Stage R M q)
    (hx : stageLeg R M q x = 0) :
    ∃ (q' : Idx R M) (h : q ≤ q'), stageMap R M h x = 0 := by
  classical
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
    have ha : (a : Fr R M) ∈ LinearMap.ker (frProj R M) := hx
    refine ⟨⟨(q.1.1, insert ⟨(a : Fr R M), ha⟩ q.1.2), ?_⟩,
      ⟨le_rfl, Finset.subset_insert _ _⟩, ?_⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact a.2
      · exact q.2 t ht
    · rw [stageMap_mk, Submodule.Quotient.mk_eq_zero]
      exact mem_relSpan R M (Finset.mem_insert_self _ _)

private lemma idx_directed (q q' : Idx R M) : ∃ r : Idx R M, q ≤ r ∧ q' ≤ r := by
  classical
  refine ⟨⟨(q.1.1 ∪ q'.1.1, q.1.2 ∪ q'.1.2), ?_⟩,
    ⟨Finset.subset_union_left, Finset.subset_union_left⟩,
    ⟨Finset.subset_union_right, Finset.subset_union_right⟩⟩
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · exact frSupp_mono R M Finset.subset_union_left (q.2 t ht)
  · exact frSupp_mono R M Finset.subset_union_right (q'.2 t ht)

/-- The presenting system of `M` by finitely presented modules, as a functor. -/
private def presFunctor : Idx R M ⥤ ModuleCat.{v} R where
  obj q := ModuleCat.of R (Stage R M q)
  map {_ _} h := ModuleCat.ofHom (stageMap R M (leOfHom h))
  map_id q := ModuleCat.hom_ext <| LinearMap.ext fun x => stageMap_self R M q x
  map_comp {_ _ _} h h' := ModuleCat.hom_ext <| LinearMap.ext fun x =>
    (stageMap_stageMap R M (leOfHom h) (leOfHom h') x).symm

/-- The cocone on the presenting system of `M` with vertex `M`. -/
private def presCocone : Cocone (presFunctor R M) where
  pt := ModuleCat.of R M
  ι :=
    { app := fun q => ModuleCat.ofHom (stageLeg R M q)
      naturality := fun {_ _} h =>
        ModuleCat.hom_ext <| LinearMap.ext fun x => stageLeg_stageMap R M (leOfHom h) x }

/-- The presenting cocone is a colimit cocone. -/
private def presIsColimit : IsColimit (presCocone R M) := by
  have hdesc : ∀ s : Cocone (presFunctor R M), ∃ ζ : M →ₗ[R] ↥s.pt,
      ∀ (q : Idx R M) (x : Stage R M q), ζ (stageLeg R M q x) = (s.ι.app q).hom x := by
    intro s
    have : IsDirected (Idx R M) (· ≤ ·) := ⟨fun q q' => idx_directed R M q q'⟩
    have hnat : ∀ ⦃q q' : Idx R M⦄ (h : q ≤ q'),
        (presFunctor R M).map (homOfLE h) ≫ s.ι.app q' = s.ι.app q := by
      intro q q' h
      simp
    let ψ : ∀ q : Idx R M, Stage R M q →ₗ[R] ↥s.pt := fun q => (s.ι.app q).hom
    have hψ : ∀ ⦃q q' : Idx R M⦄ (h : q ≤ q') (x : Stage R M q),
        ψ q' (stageMap R M h x) = ψ q x := @fun q _ h x => ConcreteCategory.congr_hom (hnat h) x
    exact exists_lift (R := R) (M := M) (J := Idx R M) (Q := fun q => Stage R M q)
      (t := fun {_ _} h => stageMap R M h) (g := fun q => stageLeg R M q)
      (@fun _ _ _ h h' x => stageMap_stageMap R M h h' x)
      (@fun _ _ h x => stageLeg_stageMap R M h x)
      (exists_stageLeg_eq R M) (exists_stageMap_eq_zero R M)
      (Z := ↥s.pt) ψ hψ
  exact
    { desc := fun s => ModuleCat.ofHom (hdesc s).choose
      fac := fun s q => by
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun x => ?_
        exact (hdesc s).choose_spec q x
      uniq := fun s m hm => by
        apply ModuleCat.hom_ext
        refine LinearMap.ext fun y => ?_
        obtain ⟨q, x, rfl⟩ := exists_stageLeg_eq R M y
        exact (ConcreteCategory.congr_hom (hm q) x).trans ((hdesc s).choose_spec q x).symm }

omit [Small.{v} R] in
/-- The concrete data of a directed colimit presentation of a module, read off from an abstract
colimit cocone: the legs are jointly surjective, and an element killed by its leg is killed by
some transition map. -/
private lemma exists_rep_of_isColimit {J : Type v} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : J ⥤ ModuleCat.{v} R) {c : Cocone F} (hc : IsColimit c) :
    (∀ m : ↥c.pt, ∃ (i : J) (x : ↥(F.obj i)), (c.ι.app i).hom x = m) ∧
      ∀ (i : J) (x : ↥(F.obj i)), (c.ι.app i).hom x = 0 →
        ∃ (j : J) (h : i ≤ j), (F.map (homOfLE h)).hom x = 0 := by
  classical
  set G : J → Type v := fun i => ↥(F.obj i) with hG
  set fm : (i j : J) → i ≤ j → (G i →ₗ[R] G j) :=
    fun _ _ h => (F.map (homOfLE h)).hom with hfm
  have : DirectedSystem G fun i j h => fm i j h := by
    constructor
    · intro i x
      simp [hfm]
    · intro k j i hij hjk x
      have h1 : F.map (homOfLE hij) ≫ F.map (homOfLE hjk)
          = F.map (homOfLE (hij.trans hjk)) := (F.map_comp _ _).symm
      simpa [hfm] using ConcreteCategory.congr_hom h1 x
  set gl : ∀ i : J, G i →ₗ[R] ↥c.pt := fun i => (c.ι.app i).hom with hgl
  have hcompat : ∀ (i j : J) (h : i ≤ j) (x : G i), gl j (fm i j h x) = gl i x := by
    intro i j h x
    simp [hfm, hgl]
  set φ := Module.DirectLimit.lift R J G fm gl hcompat with hφ
  let d : Cocone F :=
    { pt := ModuleCat.of R (Module.DirectLimit G fm)
      ι :=
        { app := fun i => ModuleCat.ofHom (Module.DirectLimit.of R J G fm i)
          naturality := fun {i j} h => by
            apply ModuleCat.hom_ext
            refine LinearMap.ext fun x => ?_
            exact Module.DirectLimit.of_f (R := R) (ι := J) (G := G) (f := fm)
              (hij := leOfHom h) (x := x) } }
  have hψ : ∀ (i : J) (x : G i),
      (hc.desc d).hom ((c.ι.app i).hom x) = Module.DirectLimit.of R J G fm i x := by
    intro i x
    have h2 := ConcreteCategory.congr_hom (hc.fac d i) x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [h2]
    rfl
  have hφψ : ∀ m : ↥c.pt, φ ((hc.desc d).hom m) = m := by
    have hid : hc.desc d ≫ ModuleCat.ofHom φ = 𝟙 c.pt := by
      refine hc.hom_ext fun i => ?_
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        ModuleCat.hom_id, LinearMap.id_coe, id_eq]
      rw [hψ i x, hφ, Module.DirectLimit.lift_of]
    intro m
    simpa using ConcreteCategory.congr_hom hid m
  refine ⟨fun m => ?_, fun i x hx => ?_⟩
  · obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of ((hc.desc d).hom m)
    refine ⟨i, y, ?_⟩
    have h2 : φ (Module.DirectLimit.of R J G fm i y) = m := by rw [hy]; exact hφψ m
    rwa [hφ, Module.DirectLimit.lift_of] at h2
  · have h0 : Module.DirectLimit.of R J G fm i x = 0 := by
      rw [← hψ i x, hx, map_zero]
    obtain ⟨j, hij, hz⟩ := Module.DirectLimit.of.zero_exact h0
    exact ⟨j, hij, hz⟩

end Presentation

/-- A countably generated Mittag-Leffler module is the colimit of a directed system of finitely
presented modules, indexed by a countable directed preorder, whose transition maps factor
eventually. The colimit is given concretely: the legs are jointly surjective and an element killed
by its leg is killed by a transition map. -/
private theorem exists_countable_fp_presentation (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (hcg : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hML : _root_.Module.IsMittagLefflerKerEq R M) :
    ∃ (J : Type v) (_ : Preorder J) (_ : IsDirectedOrder J) (_ : Nonempty J) (_ : Countable J)
      (Q : J → Type v) (_ : ∀ i, AddCommGroup (Q i)) (_ : ∀ i, Module R (Q i))
      (_ : ∀ i, Module.FinitePresentation R (Q i))
      (t : ∀ ⦃i i' : J⦄, i ≤ i' → (Q i →ₗ[R] Q i')) (g : ∀ i, Q i →ₗ[R] M),
      (∀ (i : J) (x : Q i), t le_rfl x = x) ∧
      (∀ ⦃i i' i'' : J⦄ (h : i ≤ i') (h' : i' ≤ i'') (x : Q i),
        t h' (t h x) = t (h.trans h') x) ∧
      (∀ ⦃i i' : J⦄ (h : i ≤ i') (x : Q i), g i' (t h x) = g i x) ∧
      (∀ m : M, ∃ (i : J) (x : Q i), g i x = m) ∧
      (∀ (i : J) (x : Q i), g i x = 0 → ∃ (i' : J) (h : i ≤ i'), t h x = 0) ∧
      (∀ i : J, ∃ (i' : J) (h : i ≤ i'), ∀ (k : J) (hk : i ≤ k),
        ∃ φ : Q k →ₗ[R] Q i', ∀ x : Q i, t h x = φ (t hk x)) := by
  classical
  have : IsDirectedOrder (Idx R M) := ⟨fun q q' => idx_directed R M q q'⟩
  have : Nonempty (Idx R M) := ⟨⟨(∅, ∅), by simp⟩⟩
  have hfp : ∀ q : Idx R M, Module.FinitePresentation R ((presFunctor R M).obj q) :=
    fun q => finitePresentation_stage R M q
  have hML' : ∀ (P : ModuleCat.{v} R) [Module.FinitePresentation R P]
      (f : P ⟶ (presCocone R M).pt),
      ∃ (Q : ModuleCat.{v} R) (_ : Module.FinitePresentation R Q) (g : P ⟶ Q),
        ∀ T : ModuleCat.{v} R,
          LinearMap.ker (f.hom.rTensor T) = LinearMap.ker (g.hom.rTensor T) := by
    intro P _ f
    obtain ⟨Q, _, _, _, g, hg⟩ := hML ↥P f.hom
    exact ⟨ModuleCat.of R Q, inferInstance, ModuleCat.ofHom g, fun T => hg ↥T⟩
  have hfacBig := ((CategoryTheory.Functor.tfae_isMittagLefflerSystem
    (presFunctor R M) (presIsColimit R M)).out 1 3).mp hML'
  obtain ⟨s, hsne, hsct, hsdir, ⟨hcs⟩⟩ :=
    ModuleCat.exists_countable_directedOn_isColimit_whisker hfacBig (presIsColimit R M) hcg
  have : Nonempty ↥s := hsne.to_subtype
  have : Countable ↥s := hsct.to_subtype
  have : IsDirectedOrder ↥s := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨r, hr, har, hbr⟩ := hsdir a.1 a.2 b.1 b.2
    exact ⟨⟨r, hr⟩, har, hbr⟩
  have : ∀ i : ↥s,
      Module.FinitePresentation R (((Set.mono_coe s).functor ⋙ presFunctor R M).obj i) :=
    fun i => hfp i.1
  have hfacSmall := ((CategoryTheory.Functor.tfae_isMittagLefflerSystem
    ((Set.mono_coe s).functor ⋙ presFunctor R M) hcs).out 1 3).mp hML'
  obtain ⟨hsurj, hzero⟩ := exists_rep_of_isColimit R
    ((Set.mono_coe s).functor ⋙ presFunctor R M) hcs
  refine ⟨↥s, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i => Stage R M i.1, fun _ => inferInstance, fun _ => inferInstance,
    fun i => finitePresentation_stage R M i.1, fun {_ _} h => stageMap R M h,
    fun i => stageLeg R M i.1, fun i x => stageMap_self R M i.1 x,
    @fun _ _ _ h h' x => stageMap_stageMap R M h h' x,
    @fun _ _ h x => stageLeg_stageMap R M h x,
    fun m => hsurj m, fun i x hx => ?_, fun i => ?_⟩
  · obtain ⟨j, hij, hz⟩ := hzero i x hx
    exact ⟨j, hij, hz⟩
  · obtain ⟨j, u, hu⟩ := hfacSmall i
    refine ⟨j, leOfHom u, fun k hk => ?_⟩
    obtain ⟨ψ, hψ⟩ := hu k (homOfLE hk)
    refine ⟨ψ.hom, fun x => ?_⟩
    exact ConcreteCategory.congr_hom hψ x

/-- Let `M` be a countably generated module over a commutative ring `R` satisfying the
Mittag-Leffler condition `Module.IsMittagLefflerKerEq R M`, written out. Then for every map
`f : P →ₗ[R] M` out of a finitely generated module there is an endomorphism `α` of `M` with
`α = v ∘ₗ u` for maps `u : M →ₗ[R] Q` and `v : Q →ₗ[R] M` through a finitely presented module `Q`,
and `α ∘ₗ f = f`. -/
public theorem solution
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    (hcg : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T))
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P] (f : P →ₗ[R] M) :
    ∃ α : M →ₗ[R] M,
      (∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.FinitePresentation R Q)
        (u : M →ₗ[R] Q) (v : Q →ₗ[R] M), α = v ∘ₗ u) ∧ α ∘ₗ f = f := by
  classical
  obtain ⟨J, instP, instD, instN, instC, Q, instAG, instM, instFP, t, g,
    ht_id, ht, hg, hsurj, hzero, hfac⟩ := exists_countable_fp_presentation R M hcg hML
  let S : DirInvSystem (fun i : J => Q i →ₗ[R] (∀ s : J, Q s)) :=
    { φ := @fun i i' h a => a ∘ₗ t h
      φ_self := fun i a => LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, ht_id]
      φ_comp := @fun i i' i'' hij hjk a => LinearMap.ext fun x => by
        simp only [LinearMap.comp_apply, ht] }
  have hMLS : S.IsMittagLeffler := by
    intro i
    obtain ⟨i', hii', hφ⟩ := hfac i
    refine ⟨i', hii', fun k hk => ?_⟩
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨a, rfl⟩
      refine ⟨a ∘ₗ t hk, ?_⟩
      change (a ∘ₗ t hk) ∘ₗ t hii' = a ∘ₗ t (hii'.trans hk)
      ext x
      simp only [LinearMap.comp_apply]
      rw [ht]
    · rintro _ ⟨b, rfl⟩
      obtain ⟨φ₀, hφ₀⟩ := hφ k (hii'.trans hk)
      refine ⟨b ∘ₗ φ₀, ?_⟩
      change (b ∘ₗ φ₀) ∘ₗ t (hii'.trans hk) = b ∘ₗ t hii'
      ext x
      simp only [LinearMap.comp_apply]
      rw [hφ₀]
  choose idx elt helt using hsurj
  have hfgP : (⊤ : Submodule R P).FG := Module.finite_def.mp inferInstance
  obtain ⟨sP, hsPfin, hsPspan⟩ := Submodule.fg_def.mp hfgP
  obtain ⟨j0, hj0⟩ := Finset.exists_le (hsPfin.toFinset.image fun p => idx (f p))
  have hrange : LinearMap.range f ≤ LinearMap.range (g j0) := by
    rw [LinearMap.range_eq_map, ← hsPspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    have hle : idx (f p) ≤ j0 :=
      hj0 _ (Finset.mem_image.mpr ⟨p, hsPfin.mem_toFinset.mpr hp, rfl⟩)
    exact ⟨t hle (elt (f p)), by rw [hg]; exact helt (f p)⟩
  set k := S.stab hMLS j0 with hkdef
  have hjk : j0 ≤ k := S.le_stab hMLS j0
  set y : Q j0 →ₗ[R] (∀ s : J, Q s) := (LinearMap.single R Q k) ∘ₗ t hjk with hydef
  have hystable : S.Stable y := by
    have hmem : y ∈ Set.range (S.φ hjk) := ⟨LinearMap.single R Q k, rfl⟩
    rw [← S.stable_eq_range_stab hMLS j0] at hmem
    exact hmem
  let I' := {i : J // j0 ≤ i}
  have : Nonempty I' := ⟨⟨j0, le_rfl⟩⟩
  have hdir' : IsDirected I' (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨c, h1, h2⟩ := directed_of (· ≤ ·) x.1 y.1
    exact ⟨⟨c, x.2.trans h1⟩, h1, h2⟩
  let B : I' → Type v := fun i => {a : Q i.1 →ₗ[R] (∀ s : J, Q s) // S.Stable a ∧ S.φ i.2 a = y}
  let T : DirInvSystem B :=
    { φ := @fun i i' h a => ⟨S.φ h a.1, DirInvSystem.Stable.map S h a.2.1, by
        rw [S.φ_comp i.2 h a.1]; exact a.2.2⟩
      φ_self := fun i a => Subtype.ext (S.φ_self i.1 a.1)
      φ_comp := @fun i i' i'' hij hjk a => Subtype.ext (S.φ_comp hij hjk a.1) }
  have hTsurj : ∀ (i i' : I') (h : i ≤ i') (a : B i), ∃ b : B i', T.φ h b = a := by
    intro i i' h a
    obtain ⟨b, hbst, hb⟩ := S.stable_surjective hMLS (show i.1 ≤ i'.1 from h) a.2.1
    refine ⟨⟨b, hbst, ?_⟩, Subtype.ext hb⟩
    have hc := S.φ_comp i.2 (show i.1 ≤ i'.1 from h) b
    rw [hb] at hc
    exact hc.symm.trans a.2.2
  have hMLT : T.IsMittagLeffler := by
    intro i
    have h1 : ∀ (c : I') (h : i ≤ c), Set.range (T.φ h) = Set.univ := by
      intro c h
      rw [Set.eq_univ_iff_forall]
      intro a
      obtain ⟨b, hb⟩ := hTsurj i c h a
      exact ⟨b, hb⟩
    exact ⟨i, le_rfl, fun c hc => by rw [h1 c (le_rfl.trans hc), h1 i le_rfl]⟩
  have hBne : ∀ i : I', Nonempty (B i) := by
    intro i
    obtain ⟨b, hbst, hb⟩ := S.stable_surjective hMLS i.2 hystable
    exact ⟨⟨b, hbst, hb⟩⟩
  obtain ⟨a, ha⟩ := T.nonempty_limit_of_isMittagLeffler hMLT hBne
  set ψ : ∀ i : I', Q i.1 →ₗ[R] Q k := fun i => (LinearMap.proj k) ∘ₗ (a i).1 with hψdef
  have hψ : ∀ ⦃i i' : I'⦄ (h : i ≤ i') (x : Q i.1),
      ψ i' (t (show i.1 ≤ i'.1 from h) x) = ψ i x := by
    intro i i' h x
    have h2 : S.φ (show i.1 ≤ i'.1 from h) (a i').1 = (a i).1 := congrArg Subtype.val (ha h)
    simp only [hψdef, LinearMap.comp_apply]
    rw [← h2]
    rfl
  have hsurj' : ∀ m : M, ∃ (i : I') (x : Q i.1), g i.1 x = m := by
    intro m
    obtain ⟨l, h1, h2⟩ := directed_of (· ≤ ·) (idx m) j0
    exact ⟨⟨l, h2⟩, t h1 (elt m), by rw [hg]; exact helt m⟩
  have hzero' : ∀ (i : I') (x : Q i.1), g i.1 x = 0 →
      ∃ (i' : I') (h : i ≤ i'), t (show i.1 ≤ i'.1 from h) x = 0 := by
    intro i x hx
    obtain ⟨l, hl, hz⟩ := hzero i.1 x hx
    obtain ⟨m, hm1, hm2⟩ := directed_of (· ≤ ·) l j0
    refine ⟨⟨m, hm2⟩, hl.trans hm1, ?_⟩
    have hc := ht hl hm1 x
    rw [hz, map_zero] at hc
    exact hc.symm
  obtain ⟨ζ, hζ⟩ := exists_lift (R := R) (M := M) (J := I') (Q := fun i : I' => Q i.1)
      (t := fun {i i' : I'} (h : i ≤ i') => t (show i.1 ≤ i'.1 from h)) (g := fun i : I' => g i.1)
      (@fun _ _ _ h h' x => ht h h' x) (@fun _ _ h x => hg h x) hsurj' hzero' ψ hψ
  refine ⟨g k ∘ₗ ζ, ⟨Q k, inferInstance, inferInstance, inferInstance, ζ, g k, rfl⟩, ?_⟩
  ext p
  obtain ⟨x, hx⟩ : ∃ x : Q j0, g j0 x = f p := hrange ⟨p, rfl⟩
  have hay : (a ⟨j0, le_rfl⟩).1 = y :=
    (S.φ_self j0 _).symm.trans (a ⟨j0, le_rfl⟩).2.2
  have hψj : ψ ⟨j0, le_rfl⟩ x = t hjk x := by
    simp only [hψdef, LinearMap.comp_apply, hay, hydef]
    simp
  calc (g k ∘ₗ ζ) (f p) = g k (ζ (g j0 x)) := by rw [hx]; rfl
    _ = g k (t hjk x) := by rw [hζ ⟨j0, le_rfl⟩ x, hψj]
    _ = g j0 x := hg hjk x
    _ = f p := hx

end Stacks.MittagLeffler.Endomorphisms

/-- Let `R` be a commutative ring and let `M` be an `R`-module which is countably generated — it
admits a countable spanning set — and Mittag-Leffler, the latter in the intrinsic form 059E (1):
every map `f : P → M` from a finitely presented module dominates and is dominated by a map
`g : P → Q` into a finitely presented module, domination meaning `Ker (f ⊗ id_T) = Ker (g ⊗ id_T)`
for every `R`-module `T`. Then for every `R`-module map `f : P → M` with `P` finitely generated
there is an endomorphism `α : M → M` such that (1) `α` factors through a finitely presented
`R`-module, that is `α = v ∘ₗ u` for some `u : M → Q` and `v : Q → M` with `Q` finitely presented,
and (2) `α ∘ f = f`. -/
@[stacks 05D2 "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M, 059N,
059P, 059R, 05CQ, 059X and 05D6; countable generation as a countable spanning set, as in 0590.
Test data in the universe of `M`, whence `Small.{v} R`; the source's `P` keeps its own universe.
Factoring through a finitely presented module is the equation `α = v ∘ₗ u`, as in
`Module.Flat.exists_factorization_of_finitePresentation`. See the module docstring."]
public theorem Module.exists_end_factorization_finitePresentation_of_countable_span_of_mittagLeffler
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    (hcg : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hML : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (T : Type v) [AddCommGroup T]
          [Module R T], LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T))
    {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P] (f : P →ₗ[R] M) :
    ∃ α : M →ₗ[R] M,
      (∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q) (_ : Module.FinitePresentation R Q)
        (u : M →ₗ[R] Q) (v : Q →ₗ[R] M), α = v ∘ₗ u) ∧ α ∘ₗ f = f :=
  Stacks.MittagLeffler.Endomorphisms.solution R M hcg hML f

end
