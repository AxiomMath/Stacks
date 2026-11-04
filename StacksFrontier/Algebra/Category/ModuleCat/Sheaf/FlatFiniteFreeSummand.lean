module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSingleRelation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
import StacksCore.Tactic.StacksAttribute

/-!
# A flat, finitely presented sheaf of modules is locally a finite free summand

Let `(C, O)` be a ringed site and let `F` be a sheaf of `O`-modules which is flat and locally
of finite presentation. Then every object `U` of `C` carries a covering sieve on each member of
which `F` becomes a direct summand of a *finite free* sheaf of modules.

## Main results

* `Stacks.SheafOfModules.exists_coveringSieve_retract_free_of_presentation`: the form of the
  statement which starts from a finite presentation of `F` over a single object together with
  the finite-matrix equational criterion of Stacks 08FC.
* `Stacks.SheafOfModules.exists_coveringSieve_retract_free`: a flat sheaf of modules locally of
  finite presentation is locally a direct summand of a finite free sheaf of modules.

## Implementation notes

The argument is: shrink `U` so that `F|_U` has a finite presentation
`O_U^{⊕ r} → O_U^{⊕ n} → F|_U → 0`; by the equational criterion for flatness (Stacks 08FC,
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_of_isFlat` together with
`Stacks.SheafOfModules.hasLocalSingleRelationFactorizations_iff_finite`) shrink further so that
the `n` generating sections factor as `O_U^{⊕ n} → O_U^{⊕ n₁} → F|_U` by a matrix annihilating
all `r` relations; then the surjection `O_U^{⊕ n₁} → F|_U` has a section, so `F|_U` is a direct
summand of `O_U^{⊕ n₁}`.

The last step is `exists_section_of_isColimit_cokernelCofork`, pure additive category theory.
The dictionary between a morphism of finite free sheaves of modules and its matrix of sections
of the sheaf of rings is `freeMatrix`, whose basic properties (`ιFree_comp_freeMatrix`,
`freeMatrix_comp_eq_zero`, `map_freeMatrix`) are what let the equational data coming out of
Stacks 08FC be fed to that splitting criterion.

Sections of a sheaf of modules over an object `T` and morphisms out of the unit sheaf on the
slice site over `T` are interchangeable, because `Over.mk (𝟙 T)` is a terminal object of
`Over T`; that dictionary is `moduleHomOfSection`, `scalarHomOfSection` and their evaluation
lemmas. It converts the elementwise equations of Stacks 08FC into the equations between
morphisms that the splitting criterion consumes.

Of the restriction functor `SheafOfModules.overMap` only three things are used: it is additive
(`SheafOfModules.instAdditiveOverMap`), it preserves finite colimits
(`Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits`), and it carries the
unit sheaf to the unit sheaf (`SheafOfModules.overMapUnitIso`). Additivity alone already gives
preservation of coproducts indexed by a finite type in *any* universe, which is what the free
sheaves appearing here need. Preservation of finite colimits is used twice: to transport the
presentation, and to see that a retraction obtained over one object survives further
restriction — the latter is what makes the set of objects where `F` is a finite free summand a
sieve.

The universe of the sections of the final statement is `max v w` rather than a free `w`. This
is forced by the equational criterion for flatness and is mathematics, not an artifact: that
criterion is proved by testing the tensor functor against the free module on a representable,
whose sections live in `Type (max v w)` (see `Stacks.SheafOfModules.uliftYoneda` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FlatEquivalence.lean`).

A ringed site is written out as a site `(C, J)` together with a sheaf of commutative rings `O`,
rather than as a bundled `AlgebraicGeometry.RingedSite`, to match Stacks 08FC: the bundled form
presents the sheaf of rings as `AlgebraicGeometry.RingedSite.ringSheaf`, which carries its own
proof of `GrothendieckTopology.HasSheafCompose` and so is not syntactically the
`Stacks.commRingSheafToRingSheaf` that Stacks 08FC is stated with.

## References

* [Stacks Project, Tag 08FD](https://stacks.math.columbia.edu/tag/08FD)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v₁ u₁

namespace Stacks.SheafOfModules

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective

/-! ### Splitting a cokernel -/

/-- If `p : X ⟶ M` exhibits `M` as the cokernel of `d : W ⟶ X`, and `g : X ⟶ N` also kills `d`
and factors `p` as `g ≫ q`, then `q : N ⟶ M` has a section. So a presentation whose generators
factor through a finite free module by a matrix annihilating the relations is split. -/
private lemma exists_section_of_isColimit_cokernelCofork
    {A : Type u} [Category.{v} A] [Preadditive A] {W X M N : A}
    (d : W ⟶ X) (p : X ⟶ M) (hp : d ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p hp))
    (g : X ⟶ N) (q : N ⟶ M) (hg : d ≫ g = 0) (hgp : g ≫ q = p) :
    ∃ i : M ⟶ N, i ≫ q = 𝟙 M := by
  obtain ⟨i, hi : p ≫ i = g⟩ := CokernelCofork.IsColimit.desc' hc g hg
  have : Epi p := epi_of_isColimit_cofork hc
  exact ⟨i, (cancel_epi p).1 (by simp [reassoc_of% hi, hgp])⟩

/-! ### Morphisms between finite free sheaves of modules and their matrices -/

section FreeMatrix

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The morphism `free I ⟶ free L` of free sheaves of modules given by a matrix of
endomorphisms of the unit sheaf, that is, by a matrix of sections of the sheaf of rings. -/
private noncomputable def freeMatrix {I L : Type w} [Fintype I] [Fintype L]
    (A : I → L → (_root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)) :
    _root_.SheafOfModules.free (R := R) I ⟶ _root_.SheafOfModules.free (R := R) L :=
  (_root_.SheafOfModules.freeHomEquiv _).symm fun i ↦
    (_root_.SheafOfModules.free (R := R) L).unitHomEquiv
      (∑ l, A i l ≫ _root_.SheafOfModules.ιFree (R := R) l)

/-- The `i`-th row of `freeMatrix A` is the `i`-th row of `A`. -/
private lemma ιFree_comp_freeMatrix {I L : Type w} [Fintype I] [Fintype L]
    (A : I → L → (_root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)) (i : I) :
    _root_.SheafOfModules.ιFree (R := R) i ≫ freeMatrix A =
      ∑ l, A i l ≫ _root_.SheafOfModules.ιFree (R := R) l := by
  apply (_root_.SheafOfModules.unitHomEquiv
    (_root_.SheafOfModules.free (R := R) L)).injective
  show _root_.SheafOfModules.freeHomEquiv (_root_.SheafOfModules.free (R := R) L)
      (freeMatrix A) i =
    (_root_.SheafOfModules.free (R := R) L).unitHomEquiv
      (∑ l, A i l ≫ _root_.SheafOfModules.ιFree (R := R) l)
  simp [freeMatrix]

/-- Two morphisms out of a finite free sheaf of modules are equal if they agree on each `ιFree`. -/
private lemma free_hom_ext {I : Type w} {M : _root_.SheafOfModules.{w} R}
    {f g : _root_.SheafOfModules.free (R := R) I ⟶ M}
    (h : ∀ i, _root_.SheafOfModules.ιFree (R := R) i ≫ f =
      _root_.SheafOfModules.ιFree (R := R) i ≫ g) : f = g := by
  apply (_root_.SheafOfModules.freeHomEquiv _).injective
  funext i
  exact congrArg (_root_.SheafOfModules.unitHomEquiv _) (h i)

/-- Two matrices whose product vanishes give composable morphisms of free sheaves of modules
whose composite vanishes. -/
private lemma freeMatrix_comp_eq_zero {I L P : Type w} [Fintype I] [Fintype L] [Fintype P]
    (A : I → L → (_root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R))
    (B : L → P → (_root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R))
    (h : ∀ i p, ∑ l, A i l ≫ B l p = 0) :
    freeMatrix A ≫ freeMatrix B = 0 := by
  refine free_hom_ext fun i ↦ ?_
  rw [← Category.assoc, ιFree_comp_freeMatrix, Preadditive.sum_comp, comp_zero]
  simp_rw [Category.assoc, ιFree_comp_freeMatrix, Preadditive.comp_sum]
  rw [Finset.sum_comm]
  simp_rw [← Category.assoc, ← Preadditive.sum_comp, h, zero_comp, Finset.sum_const_zero]

end FreeMatrix

/-! ### Sections over an object as morphisms out of the unit sheaf on the slice -/

section Terminal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A section of a sheaf of modules over a *terminal* object of the site is a global section:
restrict it along the unique arrow to the terminal object. -/
private noncomputable def sectionsOfIsTerminal {M : _root_.SheafOfModules.{w} R}
    (T : C) (hT : IsTerminal T) (s : M.val.obj (op T)) : M.sections := by
  refine ⟨fun U ↦ (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).map (hT.from U.unop).op
    (show (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).obj (op T) from s), ?_⟩
  intro U V f
  have h : (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).map (hT.from U.unop).op ≫
      (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).map f.unop.op =
      (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).map (hT.from V.unop).op := by
    rw [← Functor.map_comp, ← op_comp]
    exact congrArg _ (congrArg Quiver.Hom.op (hT.hom_ext _ _))
  exact ConcreteCategory.congr_hom h
    (show (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).obj (op T) from s)

/-- The global section built from a section over a terminal object restricts to it. -/
private lemma sectionsOfIsTerminal_val {M : _root_.SheafOfModules.{w} R}
    (T : C) (hT : IsTerminal T) (s : M.val.obj (op T)) :
    (sectionsOfIsTerminal T hT s).val (op T) = s := by
  show (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).map (hT.from T).op
    (show (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).obj (op T) from s) = _
  rw [hT.from_self, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- A global section is determined by its value at a terminal object. -/
private lemma unitHom_ext_isTerminal {M : _root_.SheafOfModules.{w} R}
    (T : C) (hT : IsTerminal T) {f g : _root_.SheafOfModules.unit R ⟶ M}
    (h : (M.unitHomEquiv f).val (op T) = (M.unitHomEquiv g).val (op T)) : f = g := by
  apply M.unitHomEquiv.injective
  apply Subtype.ext
  funext V
  calc
    (M.unitHomEquiv f).val V =
        (M.val.presheaf ⋙ forget AddCommGrpCat.{w}).map (hT.from V.unop).op
          ((M.unitHomEquiv f).val (op T)) :=
      ((M.unitHomEquiv f).property (hT.from V.unop).op).symm
    _ = _ := congrArg _ h
    _ = _ := (M.unitHomEquiv g).property (hT.from V.unop).op

/-- Composing with an endomorphism of the unit sheaf acts on global sections by the scalar that
endomorphism represents. -/
private lemma unitHomEquiv_comp_val_smul {M : _root_.SheafOfModules.{w} R}
    (a : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)
    (g : _root_.SheafOfModules.unit R ⟶ M) (T : Cᵒᵖ)
    (r : R.obj.obj T) (m : M.val.obj T)
    (hr : r = ((_root_.SheafOfModules.unit R).unitHomEquiv a).val T)
    (hm : m = (M.unitHomEquiv g).val T) :
    ((M.unitHomEquiv (a ≫ g)).val T : M.val.obj T) = r • m := by
  have ha : ((a.val.app T).hom (show (_root_.SheafOfModules.unit R).val.obj T from
      (1 : R.obj.obj T)) : R.obj.obj T) = r := hr.symm
  have hg : ((g.val.app T).hom (show (_root_.SheafOfModules.unit R).val.obj T from
      (1 : R.obj.obj T)) : M.val.obj T) = m := hm.symm
  show (g.val.app T).hom ((a.val.app T).hom
    (show (_root_.SheafOfModules.unit R).val.obj T from (1 : R.obj.obj T))) = r • m
  calc
    (g.val.app T).hom ((a.val.app T).hom
          (show (_root_.SheafOfModules.unit R).val.obj T from (1 : R.obj.obj T)))
        = (g.val.app T).hom
            (r • show (_root_.SheafOfModules.unit R).val.obj T from (1 : R.obj.obj T)) := by
      congr 1
      show ((a.val.app T).hom (show (_root_.SheafOfModules.unit R).val.obj T from
        (1 : R.obj.obj T)) : R.obj.obj T) = r * (1 : R.obj.obj T)
      rw [ha, mul_one]
    _ = r • (g.val.app T).hom
            (show (_root_.SheafOfModules.unit R).val.obj T from (1 : R.obj.obj T)) :=
      (g.val.app T).hom.map_smul r _
    _ = r • m := by rw [hg]

/-- Global sections depend additively on the morphism they come from, for a finite sum. -/
private lemma unitHomEquiv_sum_val {M : _root_.SheafOfModules.{w} R} {I : Type*} [Fintype I]
    (f : I → (_root_.SheafOfModules.unit R ⟶ M)) (T : Cᵒᵖ) :
    (M.unitHomEquiv (∑ i, f i)).val T = ∑ i, (M.unitHomEquiv (f i)).val T := by
  classical
  have hmap (s : Finset I) : (s.sum f).val = s.sum fun i ↦ (f i).val := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, _root_.SheafOfModules.add_val, ih]
  have happ (s : Finset I) :
      (s.sum fun i ↦ (f i).val).app T = s.sum fun i ↦ (f i).val.app T := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, PresheafOfModules.add_app, ih]
  simp only [_root_.SheafOfModules.unitHomEquiv_apply_coe]
  rw [hmap Finset.univ, happ Finset.univ]
  simp only [ModuleCat.hom_sum]
  calc
    _ = ∑ i, ((f i).val.app T).hom
          (show (_root_.SheafOfModules.unit R).val.obj T from (1 : R.obj.obj T)) :=
      LinearMap.sum_apply Finset.univ (fun i ↦ ((f i).val.app T).hom) _
    _ = ∑ i, (ConcreteCategory.hom ((f i).val.app T)) (1 : R.obj.obj T) :=
      Finset.sum_congr rfl fun i _ ↦ rfl

/-- The morphism out of the unit sheaf on the slice site over `T` corresponding to a section of
a sheaf of modules over `T`. -/
private noncomputable def moduleHomOfSection {M : _root_.SheafOfModules.{w} R}
    (T : C) (s : M.val.obj (op T)) :
    _root_.SheafOfModules.unit (R.over T) ⟶ M.over T :=
  ((M.over T).unitHomEquiv).symm
    (sectionsOfIsTerminal (Over.mk (𝟙 T)) Over.mkIdTerminal
      (show (M.over T).val.obj (op (Over.mk (𝟙 T))) from s))

/-- The endomorphism of the unit sheaf on the slice site over `T` corresponding to a section of
the sheaf of rings over `T`. -/
private noncomputable def scalarHomOfSection (R : Sheaf J RingCat.{w}) (T : C)
    (r : R.obj.obj (op T)) :
    _root_.SheafOfModules.unit (R.over T) ⟶ _root_.SheafOfModules.unit (R.over T) :=
  ((_root_.SheafOfModules.unit (R.over T)).unitHomEquiv).symm
    (sectionsOfIsTerminal (Over.mk (𝟙 T)) Over.mkIdTerminal
      (show (_root_.SheafOfModules.unit (R.over T)).val.obj (op (Over.mk (𝟙 T))) from r))

/-- `moduleHomOfSection` recovers the section it was built from. -/
private lemma moduleHomOfSection_val {M : _root_.SheafOfModules.{w} R}
    (T : C) (s : M.val.obj (op T)) :
    ((M.over T).unitHomEquiv (moduleHomOfSection T s)).val (op (Over.mk (𝟙 T))) = s := by
  simpa only [moduleHomOfSection, Equiv.apply_symm_apply] using
    sectionsOfIsTerminal_val (Over.mk (𝟙 T)) Over.mkIdTerminal
      (show (M.over T).val.obj (op (Over.mk (𝟙 T))) from s)

/-- `scalarHomOfSection` recovers the section it was built from. -/
private lemma scalarHomOfSection_val (R : Sheaf J RingCat.{w}) (T : C)
    (r : R.obj.obj (op T)) :
    ((_root_.SheafOfModules.unit (R.over T)).unitHomEquiv
      (scalarHomOfSection R T r)).val (op (Over.mk (𝟙 T))) = r := by
  simpa only [scalarHomOfSection, Equiv.apply_symm_apply] using
    sectionsOfIsTerminal_val (Over.mk (𝟙 T)) Over.mkIdTerminal
      (show (_root_.SheafOfModules.unit (R.over T)).val.obj (op (Over.mk (𝟙 T))) from r)

/-- The dictionary carries the module action to composition: a scalar composed with a section
is the scaled section. -/
private lemma scalarHomOfSection_comp_moduleHomOfSection_val
    {M : _root_.SheafOfModules.{w} R} (T : C) (r : R.obj.obj (op T)) (m : M.val.obj (op T)) :
    ((M.over T).unitHomEquiv
      (scalarHomOfSection R T r ≫ moduleHomOfSection T m)).val
        (op (Over.mk (𝟙 T))) = r • m :=
  unitHomEquiv_comp_val_smul (scalarHomOfSection R T r) (moduleHomOfSection T m)
    (op (Over.mk (𝟙 T))) (show (R.over T).obj.obj (op (Over.mk (𝟙 T))) from r)
    (show (M.over T).val.obj (op (Over.mk (𝟙 T))) from m)
    (scalarHomOfSection_val R T r).symm (moduleHomOfSection_val T m).symm

/-- The dictionary carries the ring multiplication to composition. -/
private lemma scalarHomOfSection_comp_val (R : Sheaf J RingCat.{w}) (T : C)
    (r s : R.obj.obj (op T)) :
    ((_root_.SheafOfModules.unit (R.over T)).unitHomEquiv
      (scalarHomOfSection R T r ≫ scalarHomOfSection R T s)).val
        (op (Over.mk (𝟙 T))) = r * s := by
  refine (unitHomEquiv_comp_val_smul (scalarHomOfSection R T r) (scalarHomOfSection R T s)
    (op (Over.mk (𝟙 T))) (show (R.over T).obj.obj (op (Over.mk (𝟙 T))) from r)
    (show (_root_.SheafOfModules.unit (R.over T)).val.obj (op (Over.mk (𝟙 T))) from s)
    (scalarHomOfSection_val R T r).symm (scalarHomOfSection_val R T s).symm).trans ?_
  show r • s = r * s
  exact smul_eq_mul _ _

/-- Restricting the endomorphism of the unit sheaf given by a section of the sheaf of rings
over `W` along `f : V ⟶ W` gives the endomorphism given by the restricted section. -/
private lemma scalarHomOfSection_restrict (R : Sheaf J RingCat.{w}) {V W : C} (f : V ⟶ W)
    (a : _root_.SheafOfModules.unit (R.over W) ⟶ _root_.SheafOfModules.unit (R.over W)) :
    (_root_.SheafOfModules.overMapUnitIso (R := R) f).inv ≫
        (_root_.SheafOfModules.overMap R f).map a ≫
          (_root_.SheafOfModules.overMapUnitIso (R := R) f).hom =
      scalarHomOfSection R V ((R.obj.map f.op).hom
        (show R.obj.obj (op W) from
          ((_root_.SheafOfModules.unit (R.over W)).unitHomEquiv a).val
            (op (Over.mk (𝟙 W))))) := by
  apply unitHom_ext_isTerminal (Over.mk (𝟙 V)) Over.mkIdTerminal
  rw [scalarHomOfSection_val]
  have h := ((_root_.SheafOfModules.unit (R.over W)).unitHomEquiv a).property
    (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 W)).op
  show (a.val.app (op (Over.mk (𝟙 V ≫ f)))).hom (1 : R.obj.obj (op V)) = _
  rw [Category.id_comp]
  exact h.symm

/-- Restricting a morphism out of the unit sheaf along `f : V ⟶ W` restricts the section it
represents. -/
private lemma moduleHom_restrict_val (F : _root_.SheafOfModules.{w} R) {V W : C} (f : V ⟶ W)
    (g : _root_.SheafOfModules.unit (R.over W) ⟶ F.over W) :
    (((_root_.SheafOfModules.overMap R f).obj (F.over W)).unitHomEquiv
      ((_root_.SheafOfModules.overMapUnitIso (R := R) f).inv ≫
        (_root_.SheafOfModules.overMap R f).map g)).val (op (Over.mk (𝟙 V))) =
      (F.val.map f.op).hom
        (show F.val.obj (op W) from
          ((F.over W).unitHomEquiv g).val (op (Over.mk (𝟙 W)))) := by
  have h := (((F.over W).unitHomEquiv g).property
    (Over.homMk f (by simp) : Over.mk f ⟶ Over.mk (𝟙 W)).op).symm
  show (g.val.app (op (Over.mk (𝟙 V ≫ f)))).hom (1 : R.obj.obj (op V)) = _
  rw [Category.id_comp]
  exact h

end Terminal

/-! ### The matrix of a finite presentation -/

section Presentation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The matrix of a finite presentation: the `j`-th relation, read in the coordinates of the
free sheaf of modules on the generators. -/
private noncomputable def presentationMatrix {M : _root_.SheafOfModules.{w} R}
    (P : M.Presentation) [Fintype P.generators.I] [Fintype P.relations.I] :
    P.relations.I → P.generators.I →
      (_root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R) :=
  fun j i ↦ ((kernel P.generators.π).unitHomEquiv.symm (P.relations.s j) ≫
    kernel.ι P.generators.π) ≫ _root_.SheafOfModules.freeProjection (R := R) i

/-- The relation map of a finite presentation is the morphism given by its matrix. -/
private lemma presentation_relations_eq_freeMatrix {M : _root_.SheafOfModules.{w} R}
    (P : M.Presentation) [Fintype P.generators.I] [Fintype P.relations.I] :
    P.relations.π ≫ kernel.ι P.generators.π = freeMatrix (presentationMatrix P) := by
  refine free_hom_ext fun j ↦ ?_
  rw [← Category.assoc, ιFree_comp_freeMatrix]
  calc
    _ = (_root_.SheafOfModules.unitHomEquiv (kernel P.generators.π)).symm
          (P.relations.s j) ≫ kernel.ι P.generators.π := by
      rw [← _root_.SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simp [_root_.SheafOfModules.GeneratingSections.π]
    _ = _ := by
      simpa [presentationMatrix] using
        _root_.SheafOfModules.eq_sum_comp_freeProjection_comp_ιFree (R := R)
          ((_root_.SheafOfModules.unitHomEquiv (kernel P.generators.π)).symm
            (P.relations.s j) ≫ kernel.ι P.generators.π)

/-- The relation matrix of a finite presentation annihilates the generating sections. -/
private lemma presentationMatrix_smul_sum_eq_zero {M : _root_.SheafOfModules.{w} R}
    (P : M.Presentation) [Fintype P.generators.I] [Fintype P.relations.I]
    (j : P.relations.I) (T : Cᵒᵖ) :
    ∑ i, (show R.obj.obj T from ((_root_.SheafOfModules.unit R).unitHomEquiv
        (presentationMatrix P j i)).val T) •
      (show M.val.obj T from (M.unitHomEquiv
        (_root_.SheafOfModules.ιFree (R := R) i ≫ P.generators.π)).val T) = 0 := by
  classical
  have hsum : (∑ i, presentationMatrix P j i ≫
      _root_.SheafOfModules.ιFree (R := R) i ≫ P.generators.π) = 0 := by
    calc
      _ = (∑ i, presentationMatrix P j i ≫
            _root_.SheafOfModules.ιFree (R := R) i) ≫ P.generators.π := by
        rw [Preadditive.sum_comp]; simp only [Category.assoc]
      _ = _root_.SheafOfModules.ιFree (R := R) j ≫
            (P.relations.π ≫ kernel.ι P.generators.π) ≫ P.generators.π := by
        rw [← Category.assoc, presentation_relations_eq_freeMatrix,
          ιFree_comp_freeMatrix (R := R) (presentationMatrix P) j]
      _ = 0 := by simp
  have hval := congrArg (fun q ↦ (M.unitHomEquiv q).val T) hsum
  rw [unitHomEquiv_sum_val] at hval
  have hzero : (M.unitHomEquiv (0 : _root_.SheafOfModules.unit R ⟶ M)).val T = 0 := by
    rw [_root_.SheafOfModules.unitHomEquiv_apply_coe]; rfl
  have hterm (i : P.generators.I) :
      (M.unitHomEquiv (presentationMatrix P j i ≫
        _root_.SheafOfModules.ιFree (R := R) i ≫ P.generators.π)).val T =
        (show R.obj.obj T from ((_root_.SheafOfModules.unit R).unitHomEquiv
          (presentationMatrix P j i)).val T) •
        (show M.val.obj T from (M.unitHomEquiv
          (_root_.SheafOfModules.ιFree (R := R) i ≫ P.generators.π)).val T) := by
    simpa only [Category.assoc] using
      unitHomEquiv_comp_val_smul (presentationMatrix P j i)
        (_root_.SheafOfModules.ιFree (R := R) i ≫ P.generators.π) T
        (show R.obj.obj T from ((_root_.SheafOfModules.unit R).unitHomEquiv
          (presentationMatrix P j i)).val T)
        (show M.val.obj T from (M.unitHomEquiv
          (_root_.SheafOfModules.ιFree (R := R) i ≫ P.generators.π)).val T) rfl rfl
  have hval' : ∑ i, (M.unitHomEquiv
      (presentationMatrix P j i ≫ _root_.SheafOfModules.ιFree (R := R) i ≫
        P.generators.π)).val T = 0 := by
    simpa only [hzero] using hval
  change ∑ i, (show M.val.obj T from (M.unitHomEquiv
    (presentationMatrix P j i ≫ _root_.SheafOfModules.ιFree (R := R) i ≫
      P.generators.π)).val T) = 0 at hval'
  simpa only [hterm] using hval'

/-- `presentationMatrix_smul_sum_eq_zero`, reindexed over `Fin` so that it matches the shape of
the equational criterion of Stacks 08FC. -/
private lemma presentationMatrix_smul_sum_eq_zero_fin {M : _root_.SheafOfModules.{w} R}
    (P : M.Presentation) [Fintype P.generators.I] [Fintype P.relations.I]
    (j : Fin (Fintype.card P.relations.I)) (T : Cᵒᵖ) :
    ∑ i : Fin (Fintype.card P.generators.I),
        (show R.obj.obj T from ((_root_.SheafOfModules.unit R).unitHomEquiv
          (presentationMatrix P ((Fintype.equivFin P.relations.I).symm j)
            ((Fintype.equivFin P.generators.I).symm i))).val T) •
        (show M.val.obj T from (M.unitHomEquiv
          (_root_.SheafOfModules.ιFree (R := R)
            ((Fintype.equivFin P.generators.I).symm i) ≫ P.generators.π)).val T) = 0 :=
  (Equiv.sum_comp (Fintype.equivFin P.generators.I).symm
    (fun i : P.generators.I ↦
      (show R.obj.obj T from ((_root_.SheafOfModules.unit R).unitHomEquiv
        (presentationMatrix P ((Fintype.equivFin P.relations.I).symm j) i)).val T) •
      (show M.val.obj T from (M.unitHomEquiv
        (_root_.SheafOfModules.ιFree (R := R) i ≫ P.generators.π)).val T))).trans
    (presentationMatrix_smul_sum_eq_zero P ((Fintype.equivFin P.relations.I).symm j) T)

end Presentation

/-! ### Transporting a presentation along a functor -/

section Map

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u₁} [Category.{v₁} D] {K : GrothendieckTopology D}
  {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An additive functor between categories of sheaves of modules which carries the unit sheaf
to the unit sheaf carries the morphism of finite free sheaves given by a matrix to the morphism
given by the transported matrix. -/
private lemma map_freeMatrix
    (G : _root_.SheafOfModules.{w} R ⥤ _root_.SheafOfModules.{w} S) [G.Additive]
    (η : _root_.SheafOfModules.unit S ≅ G.obj (_root_.SheafOfModules.unit R))
    {I L : Type w} [Fintype I] [Fintype L]
    (A : I → L → (_root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R)) :
    (_root_.SheafOfModules.mapFreeIso G I η).hom ≫ G.map (freeMatrix A) ≫
        (_root_.SheafOfModules.mapFreeIso G L η).inv =
      freeMatrix (fun i l ↦ η.hom ≫ G.map (A i l) ≫ η.inv) := by
  refine free_hom_ext fun i ↦ ?_
  rw [← Category.assoc, ← Category.assoc, ιFree_comp_freeMatrix]
  calc
    _ = η.hom ≫ G.map (_root_.SheafOfModules.ιFree i ≫ freeMatrix A) ≫
        (_root_.SheafOfModules.mapFreeIso G L η).inv := by
      simp only [← Category.assoc, _root_.SheafOfModules.ιFree_mapFreeIso_hom, G.map_comp]
    _ = η.hom ≫ G.map (∑ l, A i l ≫ _root_.SheafOfModules.ιFree l) ≫
        (_root_.SheafOfModules.mapFreeIso G L η).inv := by rw [ιFree_comp_freeMatrix]
    _ = _ := by
      simp only [G.map_sum, G.map_comp, Preadditive.comp_sum, Preadditive.sum_comp,
        Category.assoc, _root_.SheafOfModules.map_ιFree_mapFreeIso_inv]

/-- The splitting criterion in categorical form. Let `G` be an additive functor preserving
finite colimits and carrying the unit sheaf to the unit sheaf, let `P` be a finite presentation
of `M`, and suppose the images under `G` of the generating sections of `P` factor through a
finite free sheaf by a matrix `B` which annihilates the transported relation matrix of `P`.
Then `G.obj M` is a direct summand of that finite free sheaf. -/
private lemma exists_retract_free_of_factorization
    (G : _root_.SheafOfModules.{w} R ⥤ _root_.SheafOfModules.{w} S) [G.Additive]
    [PreservesFiniteColimits G]
    (η : _root_.SheafOfModules.unit S ≅ G.obj (_root_.SheafOfModules.unit R))
    {M : _root_.SheafOfModules.{w} R} (P : M.Presentation)
    [Fintype P.generators.I] [Fintype P.relations.I] {L : Type w} [Fintype L]
    (B : L → P.generators.I →
      (_root_.SheafOfModules.unit S ⟶ _root_.SheafOfModules.unit S))
    (t : L → (_root_.SheafOfModules.unit S ⟶ G.obj M))
    (hfac : ∀ i, η.hom ≫ G.map (_root_.SheafOfModules.ιFree i ≫ P.generators.π) =
      ∑ l, B l i ≫ t l)
    (hmat : ∀ l j, ∑ i,
      (η.hom ≫ G.map (presentationMatrix P j i) ≫ η.inv) ≫ B l i = 0) :
    ∃ (i : G.obj M ⟶ _root_.SheafOfModules.free (R := S) L)
      (q : _root_.SheafOfModules.free (R := S) L ⟶ G.obj M), i ≫ q = 𝟙 _ := by
  let eI := _root_.SheafOfModules.mapFreeIso G P.generators.I η
  let eJ := _root_.SheafOfModules.mapFreeIso G P.relations.I η
  let g := eI.inv ≫ freeMatrix (fun i l ↦ B l i)
  let q := (G.obj M).freeHomEquiv.symm (fun l ↦ (G.obj M).unitHomEquiv (t l))
  have hq (l : L) : _root_.SheafOfModules.ιFree l ≫ q = t l := by
    apply (G.obj M).unitHomEquiv.injective
    show (G.obj M).freeHomEquiv q l = _
    simp [q]
  have hgp : g ≫ q = G.map P.generators.π := by
    apply (cancel_epi eI.hom).1
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
    refine free_hom_ext fun i ↦ ?_
    rw [← Category.assoc, ιFree_comp_freeMatrix, Preadditive.sum_comp]
    simp only [Category.assoc, hq]
    rw [← hfac i]
    simp only [eI, G.map_comp, ← Category.assoc,
      _root_.SheafOfModules.ιFree_mapFreeIso_hom]
  have hg : G.map (P.relations.π ≫ kernel.ι P.generators.π) ≫ g = 0 := by
    apply (cancel_epi eJ.hom).1
    simp only [comp_zero, g]
    rw [presentation_relations_eq_freeMatrix, ← Category.assoc, ← Category.assoc,
      Category.assoc eJ.hom,
      show eJ.hom ≫ G.map (freeMatrix (presentationMatrix P)) ≫ eI.inv =
        freeMatrix (fun j i ↦ η.hom ≫ G.map (presentationMatrix P j i) ≫ η.inv) from
          map_freeMatrix G η (presentationMatrix P)]
    exact freeMatrix_comp_eq_zero _ _ fun j l ↦ hmat l j
  obtain ⟨i, hi⟩ := exists_section_of_isColimit_cokernelCofork _ _
    (by rw [← G.map_comp]; simp) (CokernelCofork.mapIsColimit _ P.isColimit G) g q hg hgp
  exact ⟨i, q, hi⟩

end Map

/-! ### Restriction along a morphism of the site -/

section Restrict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [∀ T : C, HasWeakSheafify (J.over T) AddCommGrpCat.{w}]
  [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{w}]
  {R : Sheaf J RingCat.{w}}

/-- Restriction of sheaves of modules along a morphism of the site preserves finite
colimits. -/
private lemma overMap_preservesFiniteColimits {V W : C} (f : V ⟶ W) :
    PreservesFiniteColimits (_root_.SheafOfModules.overMap.{w} R f) :=
  LocalCokernel.overMap_preservesFiniteColimits f

/-- Being a direct summand of a finite free sheaf of modules is inherited by every further
restriction. This is what makes the objects over which `F` is a finite free summand a sieve. -/
private lemma exists_retract_free_over {F : _root_.SheafOfModules.{w} R} {V W : C} (f : V ⟶ W)
    {L : Type w} [Finite L]
    (i : F.over W ⟶ _root_.SheafOfModules.free (R := R.over W) L)
    (r : _root_.SheafOfModules.free (R := R.over W) L ⟶ F.over W)
    (hir : i ≫ r = 𝟙 (F.over W)) :
    ∃ (i' : F.over V ⟶ _root_.SheafOfModules.free (R := R.over V) L)
      (r' : _root_.SheafOfModules.free (R := R.over V) L ⟶ F.over V),
        i' ≫ r' = 𝟙 (F.over V) := by
  let G := _root_.SheafOfModules.overMap R f
  let eM := (_root_.SheafOfModules.overFunctorMap R f).app F
  let eL := _root_.SheafOfModules.mapFreeIso G L
    (_root_.SheafOfModules.overMapUnitIso f).symm
  refine ⟨eM.inv ≫ G.map i ≫ eL.inv, eL.hom ≫ G.map r ≫ eM.hom, ?_⟩
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← G.map_comp_assoc, hir,
    G.map_id, Category.id_comp, Iso.inv_hom_id]

end Restrict

/-! ### Stacks 08FD -/

section Local

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ T : C, HasWeakSheafify (J.over T) AddCommGrpCat.{w}]
  [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Given a finite presentation of `F` over an object `W` of the site, together with the
finite-matrix form of the equational criterion for flatness (Stacks 08FC), there is a covering
sieve of `W` on each member of which `F` is a direct summand of a finite free sheaf of
modules. -/
theorem exists_coveringSieve_retract_free_of_presentation
    (O : Sheaf J CommRingCat.{w})
    (F : _root_.SheafOfModules.{w} (commRingSheafToRingSheaf O))
    (hF : HasLocalFiniteRelationFactorizations O F)
    (W : C) (P : (F.over W).Presentation) [P.IsFinite] :
    ∃ S : Sieve W, S ∈ J W ∧ ∀ {V : C} (f : V ⟶ W), S f →
      ∃ I : Type w, Finite I ∧
        ∃ (i : F.over V ⟶ _root_.SheafOfModules.free
            (R := (commRingSheafToRingSheaf O).over V) I)
          (r : _root_.SheafOfModules.free (R := (commRingSheafToRingSheaf O).over V) I ⟶
            F.over V), i ≫ r = 𝟙 _ := by
  classical
  let : Fintype P.generators.I := Fintype.ofFinite _
  let : Fintype P.relations.I := Fintype.ofFinite _
  let eI := Fintype.equivFin P.generators.I
  let eJ := Fintype.equivFin P.relations.I
  let A : Fin (Fintype.card P.generators.I) → Fin (Fintype.card P.relations.I) →
      (commRingSheafToRingSheaf O).obj.obj (op W) := fun i j ↦
    ((_root_.SheafOfModules.unit ((commRingSheafToRingSheaf O).over W)).unitHomEquiv
      (presentationMatrix P (eJ.symm j) (eI.symm i))).val (op (Over.mk (𝟙 W)))
  let s : Fin (Fintype.card P.generators.I) → F.val.obj (op W) := fun i ↦
    ((F.over W).unitHomEquiv
      (_root_.SheafOfModules.ιFree (eI.symm i) ≫ P.generators.π)).val (op (Over.mk (𝟙 W)))
  have hrel (j) : ∑ i, A i j • s i = 0 :=
    presentationMatrix_smul_sum_eq_zero_fin P j (op (Over.mk (𝟙 W)))
  obtain ⟨S, hS, hloc⟩ := hF W _ _ A s hrel
  refine ⟨S, hS, fun {V} f hf ↦ ?_⟩
  obtain ⟨l, t, B, ht, hB⟩ := hloc f hf
  let L := ULift.{w} (Fin l)
  let G := _root_.SheafOfModules.overMap.{w} (commRingSheafToRingSheaf O) f
  let η := (_root_.SheafOfModules.overMapUnitIso
    (R := commRingSheafToRingSheaf O) f).symm
  let ε := (_root_.SheafOfModules.overFunctorMap (commRingSheafToRingSheaf O) f).app F
  let b : L → P.generators.I →
      (_root_.SheafOfModules.unit ((commRingSheafToRingSheaf O).over V) ⟶
        _root_.SheafOfModules.unit ((commRingSheafToRingSheaf O).over V)) :=
    fun k i ↦ scalarHomOfSection (commRingSheafToRingSheaf O) V (B k.down (eI i))
  let t' : L → (_root_.SheafOfModules.unit ((commRingSheafToRingSheaf O).over V) ⟶
      G.obj (F.over W)) :=
    fun k ↦ moduleHomOfSection V (t k.down) ≫ ε.inv
  let : PreservesFiniteColimits G := overMap_preservesFiniteColimits f
  have hfac (i : P.generators.I) :
      η.hom ≫ G.map (_root_.SheafOfModules.ιFree i ≫ P.generators.π) =
        ∑ k, b k i ≫ t' k := by
    apply unitHom_ext_isTerminal (Over.mk (𝟙 V)) Over.mkIdTerminal
    dsimp only [η, Iso.symm_hom, G]
    rw [moduleHom_restrict_val, unitHomEquiv_sum_val]
    have hterm (k : L) :
        ((G.obj (F.over W)).unitHomEquiv (b k i ≫ t' k)).val
          (op (Over.mk (𝟙 V))) = B k.down (eI i) • t k.down := by
      show ((F.over V).unitHomEquiv
        (scalarHomOfSection (commRingSheafToRingSheaf O) V (B k.down (eI i)) ≫
          moduleHomOfSection V (t k.down))).val (op (Over.mk (𝟙 V))) = _
      exact scalarHomOfSection_comp_moduleHomOfSection_val V _ _
    have hs : s (eI i) = ((F.over W).unitHomEquiv
        (_root_.SheafOfModules.ιFree i ≫ P.generators.π)).val (op (Over.mk (𝟙 W))) :=
      congrArg (fun j ↦ ((F.over W).unitHomEquiv
        (_root_.SheafOfModules.ιFree j ≫ P.generators.π)).val (op (Over.mk (𝟙 W))))
        (eI.symm_apply_apply i)
    have h := ht (eI i)
    rw [hs] at h
    refine Eq.trans ?_ (Finset.sum_congr rfl fun k _ ↦ (hterm k).symm)
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.ulift : L ≃ Fin l)
      (fun k ↦ B k (eI i) • t k)).symm
    exact h
  have hmat (k : L) (j : P.relations.I) :
      ∑ i, (η.hom ≫ G.map (presentationMatrix P j i) ≫ η.inv) ≫ b k i = 0 := by
    apply unitHom_ext_isTerminal (Over.mk (𝟙 V)) Over.mkIdTerminal
    rw [unitHomEquiv_sum_val]
    have hterm (i : P.generators.I) :
        ((_root_.SheafOfModules.unit ((commRingSheafToRingSheaf O).over V)).unitHomEquiv
          ((η.hom ≫ G.map (presentationMatrix P j i) ≫ η.inv) ≫ b k i)).val
            (op (Over.mk (𝟙 V))) =
          B k.down (eI i) *
            ((commRingSheafToRingSheaf O).obj.map f.op).hom (A (eI i) (eJ j)) := by
      dsimp only [η, G, Iso.symm_hom, Iso.symm_inv]
      rw [scalarHomOfSection_restrict, scalarHomOfSection_comp_val]
      simp only [A, Equiv.symm_apply_apply]
      exact ringSheaf_mul_comm O _ (B k.down (eI i))
    simp_rw [hterm]
    show (∑ i, B k.down (eI i) *
      ((commRingSheafToRingSheaf O).obj.map f.op).hom (A (eI i) (eJ j)) :
        (commRingSheafToRingSheaf O).obj.obj (op V)) = 0
    exact (Equiv.sum_comp eI (fun i ↦ B k.down i *
      ((commRingSheafToRingSheaf O).obj.map f.op).hom (A i (eJ j)))).trans
      (hB k.down (eJ j))
  obtain ⟨i, r, hir⟩ := exists_retract_free_of_factorization G η P b t' hfac hmat
  exact ⟨L, inferInstance, ε.inv ≫ i, r ≫ ε.hom, by
    simp only [Category.assoc, ← Category.assoc i r, hir, Category.id_comp, Iso.inv_hom_id]⟩

end Local

section Main

/-- On a ringed site, a sheaf of modules which is flat and locally of finite presentation is,
locally on the site, a direct summand of a finite free sheaf of modules: every object `U`
carries a covering sieve on each member `f : V ⟶ U` of which `F|_V` is a retract of
`O_V^{⊕ I}` for some finite `I`. -/
@[stacks 08FD]
theorem exists_coveringSieve_retract_free
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max v w} RingCat.{max v w})]
    [HasWeakSheafify J AddCommGrpCat.{max v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
    [∀ T : C, HasWeakSheafify (J.over T) AddCommGrpCat.{max v w}]
    [∀ T : C, (J.over T).WEqualsLocallyBijective AddCommGrpCat.{max v w}]
    (O : Sheaf J CommRingCat.{max v w})
    (F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O))
    [F.IsFinitePresentation] (hF : IsFlat F) (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧ ∀ {V : C} (f : V ⟶ U), S f →
      ∃ I : Type (max v w), Finite I ∧
        ∃ (i : F.over V ⟶ _root_.SheafOfModules.free
            (R := (commRingSheafToRingSheaf O).over V) I)
          (r : _root_.SheafOfModules.free (R := (commRingSheafToRingSheaf O).over V) I ⟶
            F.over V), i ≫ r = 𝟙 (F.over V) := by
  classical
  have hrel : HasLocalFiniteRelationFactorizations O F := by
    let : HasSheafify J AddCommGrpCat.{max v w} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    exact (hasLocalSingleRelationFactorizations_iff_finite O F).mp
      (hasLocalSingleRelationFactorizations_of_isFlat hF)
  obtain ⟨q, hq⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
  let := hq
  let S : Sieve U :=
    { arrows := fun V _ ↦ ∃ I : Type (max v w), Finite I ∧
        ∃ (i : F.over V ⟶ _root_.SheafOfModules.free
            (R := (commRingSheafToRingSheaf O).over V) I)
          (r : _root_.SheafOfModules.free (R := (commRingSheafToRingSheaf O).over V) I ⟶
            F.over V), i ≫ r = 𝟙 (F.over V)
      downward_closed := by
        intro V Z _ hf g
        obtain ⟨I, hI, i, r, hir⟩ := hf
        let := hI
        obtain ⟨i', r', h⟩ := exists_retract_free_over g i r hir
        exact ⟨I, hI, i', r', h⟩ }
  refine ⟨S, ?_, fun f hf ↦ hf⟩
  apply J.transitive (q.coversTop U)
  intro V f hf
  obtain ⟨a, ⟨g⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
  obtain ⟨T, hT, ht⟩ := exists_coveringSieve_retract_free_of_presentation O F hrel
    (q.X a) (q.presentation a)
  exact J.superset_covering (fun Z h hh ↦ ht (h ≫ g) hh) (J.pullback_stable g hT)

end Main

end Stacks.SheafOfModules

end
