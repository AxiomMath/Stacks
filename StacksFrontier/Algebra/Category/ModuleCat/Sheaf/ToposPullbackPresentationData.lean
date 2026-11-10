module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration

/-!
# The sheaf of finite presentations of a sheaf of modules

Let `(C, J)` be a site, let `O` be a sheaf of rings on it and let `F` be a sheaf of `O`-modules.
Stacks 03DL(7) calls `F` *of finite presentation* when every object of the site has a covering on
whose members `F` is the cokernel of a map of finite free modules `O^m → O^n`.  Written out in
sections, the data of such a presentation over an object `W` is a tuple `s : Fin n → F(W)` of
sections together with a matrix `t : Fin m → Fin n → O(W)` whose rows are the relations, subject
to three conditions:

* **(A)** every row of `t` is a relation among the `s`, that is `∑ i, t j i • s i = 0`;
* **(B)** the `s` generate `F` locally on `W`;
* **(C)** every relation among the `s`, over every object over `W`, is locally an `O`-linear
  combination of the rows of `t`.

Together (A) and (C) say that `O^m → O^n` has image the kernel of `O^n → F`, locally, and (B)
says that `O^n → F` is epi; so the three conditions say exactly that `F|_W` is presented by `t`
on the generators `s`.

This file assembles that data into a sheaf of sets `presDataSheaf F n m` on `C`: a subsheaf of
`F^n × (O^n)^m` cut out by (A), (B) and (C), whose sections over `W` are exactly the
presentations of `F|_W` with `n` generators and `m` relations.  Its purpose is to replace the
single "sheaf of generating `r`-tuples" of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration` — which carries
Stacks 03DL(4), local generation by a *fixed* number of sections — by the family indexed by the
pair `(n, m)` that Stacks 03DL(7) needs, the presentation sizes being allowed to vary over a
covering family.

## Main definitions

* `Stacks.Sheaves.LocalGeneration.relationSpanSieve` is the sieve on which a tuple of sections
  of `O^n` becomes an `O`-linear combination of a given finite family of such tuples.
* `Stacks.Sheaves.LocalGeneration.LocallySpansKernel` is condition (C): the rows of `t` span the
  kernel of `O^n → F` locally.
* `Stacks.Sheaves.LocalGeneration.IsPresentationData` is the conjunction of (A), (B) and (C).
* `Stacks.Sheaves.LocalGeneration.presTupleSheaf` is the sheaf of sets `F^n × (O^n)^m` of raw
  data; `presGenProjection`, `presRelProjection`, `dataGenerators`, `dataRelations` are its two
  projections, as morphisms of sheaves and on sections, and `dataMk` assembles a section out of
  a tuple and a matrix.
* `Stacks.Sheaves.LocalGeneration.presData` and `presDataSheaf` are the subfunctor of
  `presTupleSheaf` cut out by `IsPresentationData`, and that subfunctor read as a sheaf;
  `presDataMk` is a section of it built from presentation data and `presDataGenerators` is its
  first projection to the sheaf of generating tuples.

## Main results

* `Stacks.Sheaves.LocalGeneration.locallySpansKernel_map` and
  `isPresentationData_map`: the three conditions are stable under restriction, which is what
  makes `presData` a subfunctor.
* `Stacks.Sheaves.LocalGeneration.locallySpansKernel_of_cover`,
  `combinationValue_eq_zero_of_cover` and `isPresentationData_of_cover`: each of the three
  conditions is local on the object, which is what makes `presData` a *sheaf*.
* `Stacks.Sheaves.LocalGeneration.presData_isSheaf`.
* `Stacks.Sheaves.LocalGeneration.presDataMk`, `dataGenerators_dataMk` and
  `dataRelations_dataMk` together say that the sections of `presDataSheaf F n m` over `W` are
  exactly the presentations of `F|_W` by `n` generators and `m` relations: nothing satisfying
  the three conditions is missing from the sheaf, and nothing else is in it.

## Implementation notes

The three universes are the site's objects `u`, its homs `v` and the sections `w`, all
independent, exactly as in the file this one extends.  Nothing is narrowed: no sheafification,
no smallness and no limits on `C` are assumed, only the two `HasSheafCompose` instances needed
to speak of the underlying sheaves of sets of `O` and of `F`.

**No free sheaf appears.**  `SheafOfModules.free I` is a sheafification, so its sections are not
`I`-tuples, and a description of `ker (O^n → F)` as a sheaf of modules would have to cross that
wall.  Conditions (A) and (C) are therefore stated with explicit tuples of sections and the
`combinationValue` of the file this extends, and local surjectivity of `O^m → ker (O^n → F)` is
spelled as "every relation is locally a combination of the rows", which is the same assertion
evaluated on sections.

`relationSpanSieve` mentions only the sheaf of rings: the condition that a tuple of scalars is a
combination of other tuples of scalars does not involve `F`.  Restriction of scalars plays no
role on that side either, which is why — unlike `restr` for the sections of `F` — no `def` with
an ascribed type is needed for the restriction of a tuple of sections of `O`; it is written as
`R.obj.map g` throughout, the spelling `restr_combinationValue` produces.

`presData` is cut out of the *categorical* product of the two tuple sheaves rather than of a
hand-built sheaf of pairs, because the conditions are then equations between morphisms out of
the data sheaf, which is the form in which they can be transported along the inverse image of a
morphism of topoi.  Sections of a product of sheaves of types are not literally pairs, so the
two components are extracted with `prod.fst` and `prod.snd` and the restriction compatibility is
the naturality of those projections, `dataGenerators_map` and `dataRelations_map`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.LocalGeneration

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-! ### Restriction of the scalars of the site

The companion of `restr_restr` for the sections of the sheaf of rings.  No `def` with an ascribed
type is needed on this side, because there is no restriction of scalars to cross. -/

/-- Restricting a section of a sheaf of rings along a composite is restricting twice.  This is
`CategoryTheory.Functor.map_comp` in applied form for a `RingCat`-valued sheaf — the analogue of
`CategoryTheory.FunctorToTypes.map_comp_apply` and `PresheafOfModules.map_comp_apply` — written
in the direction `simp` normalises to, so that a composite restriction and a nested one always
meet.  `simp` proves it from the four lemmas `Functor.map_comp`, `RingCat.hom_comp`,
`RingHom.coe_comp`, `Function.comp_apply`; it is stated here only so that one name does that
unfolding in a `simp only`. -/
lemma ringMap_comp_apply (R : Sheaf J RingCat.{w}) {U V W : Cᵒᵖ} (g : U ⟶ V) (h : V ⟶ W)
    (x : R.obj.obj U) : R.obj.map (g ≫ h) x = R.obj.map h (R.obj.map g x) :=
  ConcreteCategory.congr_hom (R.obj.map_comp g h) x

/-- Restricting a section of a sheaf of rings along the identity does nothing.  As with
`ringMap_comp_apply`, `simp` proves this from `Functor.map_id`, `RingCat.hom_id` and
`RingHom.id_apply`; the name exists to do that unfolding in a `simp only`. -/
lemma ringMap_id_apply (R : Sheaf J RingCat.{w}) {U : Cᵒᵖ} (x : R.obj.obj U) :
    R.obj.map (𝟙 U) x = x :=
  ConcreteCategory.congr_hom (R.obj.map_id U) x

/-- Restricting the zero section of a sheaf of modules gives the zero section.  The third member
of the `restr_restr`, `restr_id` family of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration`: the ascribed type of
`restr` is what makes the right-hand side the zero of the sections of `M`, rather than the zero
of the scalar-restricted module `PresheafOfModules.map` lands in, and `simp` makes no progress on
the statement without it. -/
lemma restr_zero (M : SheafOfModules.{w} R) {U V : Cᵒᵖ} (g : U ⟶ V) :
    restr M g (0 : M.val.obj U) = (0 : M.val.obj V) :=
  map_zero (M.val.map g).hom

/-! ### Relations locally spanned by a finite family -/

/-- The sieve on `U` of those arrows along which the tuple `a` of sections of `O^n` becomes an
`O`-linear combination of the tuples `t j`. -/
def relationSpanSieve (R : Sheaf J RingCat.{w}) {n m : ℕ} {U : C}
    (t : Fin m → Fin n → R.obj.obj (op U)) (a : Fin n → R.obj.obj (op U)) : Sieve U where
  arrows V f := ∃ c : Fin m → R.obj.obj (op V),
    ∀ i, ∑ j, c j * R.obj.map f.op (t j i) = R.obj.map f.op (a i)
  downward_closed := by
    intro V W f hf g
    obtain ⟨c, hc⟩ := hf
    refine ⟨fun j => R.obj.map g.op (c j), fun i => ?_⟩
    have h := congrArg (R.obj.map g.op) (hc i)
    simpa only [map_sum, map_mul, op_comp, ringMap_comp_apply] using h

/-- **The relations among `s` are locally spanned by the rows of `t`.**  Over every object `V`
over `U`, every relation `a` among the restrictions of `s` becomes, on a covering of `V`, an
`O`-linear combination of the restricted rows of `t`.

This is local surjectivity of `O^m → ker (O^n → F)` written on sections, which is how it avoids
mentioning the free sheaf of modules, whose sections are not tuples. -/
def LocallySpansKernel (M : SheafOfModules.{w} R) {n m : ℕ} {U : C}
    (s : Fin n → M.val.obj (op U)) (t : Fin m → Fin n → R.obj.obj (op U)) : Prop :=
  ∀ (V : C) (f : V ⟶ U) (a : Fin n → R.obj.obj (op V)),
    combinationValue M a (fun i => restr M f.op (s i)) = 0 →
      relationSpanSieve R (fun j i => R.obj.map f.op (t j i)) a ∈ J V

/-- A vanishing linear combination of sections still vanishes after restriction. -/
private theorem combinationValue_restr_eq_zero {M : SheafOfModules.{w} R} {n : ℕ} {U V : Cᵒᵖ}
    {a : Fin n → R.obj.obj U} {s : Fin n → M.val.obj U} (g : U ⟶ V)
    (h : combinationValue M a s = 0) :
    combinationValue M (fun i => R.obj.map g (a i)) (fun i => restr M g (s i)) = 0 := by
  rw [← restr_combinationValue, h, restr_zero]

/-- Condition (C) is stable under restriction. -/
theorem locallySpansKernel_map {M : SheafOfModules.{w} R} {n m : ℕ} {U V : C}
    {s : Fin n → M.val.obj (op U)} {t : Fin m → Fin n → R.obj.obj (op U)}
    (h : LocallySpansKernel M s t) (f : V ⟶ U) :
    LocallySpansKernel M (fun i => restr M f.op (s i)) (fun j i => R.obj.map f.op (t j i)) := by
  intro W g a ha
  have ha' : combinationValue M a (fun i => restr M (g ≫ f).op (s i)) = 0 := by
    simpa only [restr_restr, ← op_comp] using ha
  simpa only [op_comp, ringMap_comp_apply] using h W (g ≫ f) a ha'

/-- A family satisfying (C) spans the relations over its own object, with no restriction in the
way.  Instantiating `LocallySpansKernel` at the identity leaves restrictions along `𝟙` that have
to be cleared once, here rather than at every use. -/
lemma relationSpanSieve_mem_of_locallySpansKernel {M : SheafOfModules.{w} R} {n m : ℕ} {U : C}
    {s : Fin n → M.val.obj (op U)} {t : Fin m → Fin n → R.obj.obj (op U)}
    (h : LocallySpansKernel M s t) {a : Fin n → R.obj.obj (op U)}
    (ha : combinationValue M a s = 0) : relationSpanSieve R t a ∈ J U := by
  have h1 := h U (𝟙 U) a (by simpa only [op_id, restr_id] using ha)
  simpa only [op_id, ringMap_id_apply] using h1

/-- Condition (C) is local on the object. -/
theorem locallySpansKernel_of_cover {M : SheafOfModules.{w} R} {n m : ℕ} {U : C}
    {s : Fin n → M.val.obj (op U)} {t : Fin m → Fin n → R.obj.obj (op U)}
    (S : Sieve U) (hS : S ∈ J U)
    (h : ∀ (V : C) (f : V ⟶ U), S f → LocallySpansKernel M (fun i => restr M f.op (s i))
      (fun j i => R.obj.map f.op (t j i))) : LocallySpansKernel M s t := by
  intro V f a ha
  apply J.transitive (J.pullback_stable f hS)
  intro W g hg
  have ha' : combinationValue M (fun i => R.obj.map g.op (a i))
      (fun i => restr M (g ≫ f).op (s i)) = 0 := by
    simpa only [restr_restr, ← op_comp] using combinationValue_restr_eq_zero g.op ha
  apply J.superset_covering _ (relationSpanSieve_mem_of_locallySpansKernel
    (h W (g ≫ f) hg) (a := fun i => R.obj.map g.op (a i)) ha')
  intro Z k hk
  obtain ⟨c, hc⟩ := hk
  refine ⟨c, fun i => ?_⟩
  simpa only [op_comp, ringMap_comp_apply] using hc i

/-! ### A relation that holds locally holds -/

/-- A linear combination of sections of a sheaf of modules which vanishes after restriction along
every member of a covering vanishes. -/
theorem combinationValue_eq_zero_of_cover [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    {M : SheafOfModules.{w} R} {n : ℕ} {U : C} (S : Sieve U) (hS : S ∈ J U)
    {a : Fin n → R.obj.obj (op U)} {s : Fin n → M.val.obj (op U)}
    (h : ∀ (V : C) (f : V ⟶ U), S f →
      combinationValue M (fun i => R.obj.map f.op (a i)) (fun i => restr M f.op (s i)) = 0) :
    combinationValue M a s = 0 := by
  have hA := (isSheaf_iff_isSheaf_of_type J _).1 (moduleUnderlying M).property S hS
  refine hA.isSeparatedFor.ext fun V f hf => ?_
  change underlyingSection M (restr M f.op (combinationValue M a s)) =
    underlyingSection M (restr M f.op 0)
  rw [restr_combinationValue, h V f hf, restr_zero]

/-! ### The three conditions -/

/-- **The section-level data of a finite presentation of `F` over `U`**: `n` sections `s` of `F`
and `m` tuples `t` of `n` sections of `O`, such that (A) each `t j` is a relation among the `s`,
(B) the `s` span `F` locally and (C) the relations among the `s` are locally spanned by the
`t j`. -/
def IsPresentationData (M : SheafOfModules.{w} R) {n m : ℕ} {U : C}
    (s : Fin n → M.val.obj (op U)) (t : Fin m → Fin n → R.obj.obj (op U)) : Prop :=
  (∀ j, combinationValue M (t j) s = 0) ∧ LocallySpans M s ∧ LocallySpansKernel M s t

/-- Presentation data restricts to presentation data. -/
theorem isPresentationData_map {M : SheafOfModules.{w} R} {n m : ℕ} {U V : C}
    {s : Fin n → M.val.obj (op U)} {t : Fin m → Fin n → R.obj.obj (op U)}
    (h : IsPresentationData M s t) (f : V ⟶ U) :
    IsPresentationData M (fun i => restr M f.op (s i)) (fun j i => R.obj.map f.op (t j i)) :=
  ⟨fun j => combinationValue_restr_eq_zero f.op (h.1 j),
   locallySpans_map h.2.1 f, locallySpansKernel_map h.2.2 f⟩

/-- Presentation data is local on the object: data over the members of a covering, all of it the
restriction of one tuple over the covered object, is data over that object. -/
theorem isPresentationData_of_cover [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    {M : SheafOfModules.{w} R} {n m : ℕ} {U : C}
    {s : Fin n → M.val.obj (op U)} {t : Fin m → Fin n → R.obj.obj (op U)}
    (S : Sieve U) (hS : S ∈ J U)
    (h : ∀ (V : C) (f : V ⟶ U), S f → IsPresentationData M (fun i => restr M f.op (s i))
      (fun j i => R.obj.map f.op (t j i))) : IsPresentationData M s t :=
  ⟨fun j => combinationValue_eq_zero_of_cover S hS fun V f hf => (h V f hf).1 j,
   locallySpans_of_cover S hS fun V f hf => (h V f hf).2.1,
   locallySpansKernel_of_cover S hS fun V f hf => (h V f hf).2.2⟩

/-! ### The sheaf of presentations -/

variable [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The sheaf of sets `F^n × (O^n)^m` of raw presentation data. -/
noncomputable abbrev presTupleSheaf (M : SheafOfModules.{w} R) (n m : ℕ) : Sheaf J (Type w) :=
  tupleSheaf (moduleUnderlying M) n ⨯ tupleSheaf (tupleSheaf (Sheaf.ringSheaf R) n) m

/-- The projection of the raw data sheaf onto the `n` sections of `F`. -/
noncomputable abbrev presGenProjection (M : SheafOfModules.{w} R) (n m : ℕ) :
    presTupleSheaf M n m ⟶ tupleSheaf (moduleUnderlying M) n := prod.fst

/-- The projection of the raw data sheaf onto the `m` relation tuples. -/
noncomputable abbrev presRelProjection (M : SheafOfModules.{w} R) (n m : ℕ) :
    presTupleSheaf M n m ⟶ tupleSheaf (tupleSheaf (Sheaf.ringSheaf R) n) m := prod.snd

/-- The generating sections carried by a section of the raw data sheaf.  The ascribed type is the
sections of `F`, which is what lets them be fed to `combinationValue` and `LocallySpans`. -/
noncomputable def dataGenerators (M : SheafOfModules.{w} R) {n m : ℕ} {U : Cᵒᵖ}
    (p : (presTupleSheaf M n m).obj.obj U) : Fin n → M.val.obj U :=
  (presGenProjection M n m).hom.app U p

/-- The relation tuples carried by a section of the raw data sheaf. -/
noncomputable def dataRelations (M : SheafOfModules.{w} R) {n m : ℕ} {U : Cᵒᵖ}
    (p : (presTupleSheaf M n m).obj.obj U) : Fin m → Fin n → R.obj.obj U :=
  (presRelProjection M n m).hom.app U p

/-- A section of the raw data sheaf assembled from `n` sections of `F` and `m` tuples of `n`
sections of `O`.  Sections of a product of sheaves of types are not literally pairs, so this goes
through `prodSectionEquiv`. -/
noncomputable def dataMk (M : SheafOfModules.{w} R) {n m : ℕ} {U : Cᵒᵖ}
    (s : Fin n → M.val.obj U) (t : Fin m → Fin n → R.obj.obj U) :
    (presTupleSheaf M n m).obj.obj U :=
  (prodSectionEquiv _ _ U).symm (tupleMk s, tupleMk fun j => tupleMk (t j))

/-- The generating sections of the section assembled by `dataMk` are the given ones. -/
@[simp]
lemma dataGenerators_dataMk (M : SheafOfModules.{w} R) {n m : ℕ} {U : Cᵒᵖ}
    (s : Fin n → M.val.obj U) (t : Fin m → Fin n → R.obj.obj U) :
    dataGenerators M (dataMk M s t) = s :=
  prodSectionEquiv_symm_fst (tupleSheaf (moduleUnderlying M) n)
    (tupleSheaf (tupleSheaf (Sheaf.ringSheaf R) n) m) U (tupleMk s) (tupleMk fun j => tupleMk (t j))

/-- The relation tuples of the section assembled by `dataMk` are the given ones. -/
@[simp]
lemma dataRelations_dataMk (M : SheafOfModules.{w} R) {n m : ℕ} {U : Cᵒᵖ}
    (s : Fin n → M.val.obj U) (t : Fin m → Fin n → R.obj.obj U) :
    dataRelations M (dataMk M s t) = t :=
  prodSectionEquiv_symm_snd (tupleSheaf (moduleUnderlying M) n)
    (tupleSheaf (tupleSheaf (Sheaf.ringSheaf R) n) m) U (tupleMk s) (tupleMk fun j => tupleMk (t j))

/-- Restricting a section of the raw data sheaf restricts its generating sections. -/
lemma dataGenerators_map (M : SheafOfModules.{w} R) {n m : ℕ} {U V : Cᵒᵖ} (g : U ⟶ V)
    (p : (presTupleSheaf M n m).obj.obj U) :
    dataGenerators M ((presTupleSheaf M n m).obj.map g p) =
      fun i => restr M g (dataGenerators M p i) :=
  ConcreteCategory.congr_hom ((presGenProjection M n m).hom.naturality g) p

/-- Restricting a section of the raw data sheaf restricts its relation tuples. -/
lemma dataRelations_map (M : SheafOfModules.{w} R) {n m : ℕ} {U V : Cᵒᵖ} (g : U ⟶ V)
    (p : (presTupleSheaf M n m).obj.obj U) :
    dataRelations M ((presTupleSheaf M n m).obj.map g p) =
      fun j i => R.obj.map g (dataRelations M p j i) :=
  ConcreteCategory.congr_hom ((presRelProjection M n m).hom.naturality g) p

/-- **The subfunctor of raw presentation data which really is a presentation.** -/
noncomputable def presData (M : SheafOfModules.{w} R) (n m : ℕ) :
    Subfunctor (presTupleSheaf M n m).obj where
  obj _ := { p | IsPresentationData M (dataGenerators M p) (dataRelations M p) }
  map g p hp := by
    have h : IsPresentationData M (dataGenerators M p) (dataRelations M p) := hp
    change IsPresentationData M (dataGenerators M ((presTupleSheaf M n m).obj.map g p))
      (dataRelations M ((presTupleSheaf M n m).obj.map g p))
    rw [dataGenerators_map, dataRelations_map]
    exact isPresentationData_map h g.unop

/-- **The subfunctor `presData` is a sheaf.** Each of the three conditions defining a presentation
is local on the object, so a section of the raw data sheaf that is a presentation on the members
of a covering is one. -/
theorem presData_isSheaf (M : SheafOfModules.{w} R) (n m : ℕ) :
    Presieve.IsSheaf J (presData M n m).toFunctor := by
  apply (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J _).1
    (presTupleSheaf M n m).property)).2
  intro U p hp
  refine isPresentationData_of_cover ((presData M n m).sieveOfSection p) hp fun V f hf => ?_
  have h : IsPresentationData M (dataGenerators M ((presTupleSheaf M n m).obj.map f.op p))
      (dataRelations M ((presTupleSheaf M n m).obj.map f.op p)) := hf
  rwa [dataGenerators_map, dataRelations_map] at h

/-- **The sheaf of presentations of `F` with `n` generators and `m` relations.** -/
noncomputable def presDataSheaf (M : SheafOfModules.{w} R) (n m : ℕ) : Sheaf J (Type w) :=
  ⟨(presData M n m).toFunctor, (isSheaf_iff_isSheaf_of_type J _).2 (presData_isSheaf M n m)⟩

/-- **Presentation data gives a section of the sheaf of presentations.**  With
`dataGenerators_dataMk` and `dataRelations_dataMk` this says that the sections of
`presDataSheaf F n m` over `W` are exactly the presentations of `F|_W` by `n` generators and `m`
relations: no section of the data sheaf is lost, and none is invented. -/
noncomputable def presDataMk (M : SheafOfModules.{w} R) {n m : ℕ} {U : Cᵒᵖ}
    {s : Fin n → M.val.obj U} {t : Fin m → Fin n → R.obj.obj U}
    (h : IsPresentationData M s t) : (presDataSheaf M n m).obj.obj U :=
  ⟨dataMk M s t, by
    change IsPresentationData M (dataGenerators M (dataMk M s t)) (dataRelations M (dataMk M s t))
    rw [dataGenerators_dataMk, dataRelations_dataMk]
    exact h⟩

/-- The generating sections of a presentation are a locally spanning tuple: condition (B) says
exactly that the first projection of the data sheaf factors through the sheaf of generating
tuples of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackLocalGeneration`. -/
noncomputable def presDataGenerators (M : SheafOfModules.{w} R) (n m : ℕ) :
    presDataSheaf M n m ⟶ generatingTupleSheaf M n where
  hom :=
    { app := fun U => ↾(fun p => ⟨dataGenerators M p.val, p.property.2.1⟩)
      naturality := by
        intro U V g
        ext p
        exact Subtype.ext (dataGenerators_map M g p.val) }

end Stacks.Sheaves.LocalGeneration

end
