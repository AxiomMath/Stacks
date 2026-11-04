module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceScalarRestriction
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.IteratedSliceSheafification

/-!
# Coherence on a site is the sectionwise finiteness of relations

There are two ways to say that the relations among the sections of a sheaf of modules `M` on a
site are finite, and they are not the same statement.

* The *categorical* form, `Stacks.SheafOfModules.Site.IsCoherent`, asks that the kernel of every
  morphism `free I ⟶ M.over U` out of a finite free sheaf of modules be of finite type. It is
  quantified over an index type `I` in the module universe and a morphism of sheaves of modules.
* The *sectionwise* form, which is how Stacks 03DL (10) states coherence, asks that for every
  finite family `s_1, …, s_n` of sections of `M` over an object `U` the presheaf of relations
  `Stacks.SheafOfModules.relationsPresheaf` be of finite type on the slice site over `U`. It is
  quantified over `Fin n` and a tuple of sections, and it mentions neither kernels nor the free
  sheaf of modules.

A finite family of sections of `M` over `U` is the same thing as a morphism out of a finite free
sheaf of modules, and the relations among the family are the kernel of that morphism. This file
turns that correspondence into an equivalence of the two conditions. `Stacks.SheafOfModules.
relationsPresheafIso` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceScalarRestriction`) already identifies the
kernel with the presheaf of relations *for one family at a time*; what is added here is the
reindexing that lets the two quantifiers be compared, and the resulting equivalence.

## Main definitions

* `Stacks.SheafOfModules.relationsSubmoduleCongr`: reindexing a finite family of sections along
  a bijection reindexes the submodule of relations among it. The index types may lie in
  different universes, because this is a statement about submodules and not about presheaves.
* `Stacks.SheafOfModules.relationsPresheafCongr` and
  `Stacks.SheafOfModules.relationsPresheafULiftIso`: the two presheaf-level consequences — the
  first for index types in a single universe, the second for `ULift`.

## Main results

* `Stacks.SheafOfModules.isFiniteTypeSections_of_iso'`,
  `isFiniteTypeSections_of_isFiniteType'`, `isFiniteType_of_isFiniteTypeSections'`,
  `isFiniteTypeSections_relationsPresheaf'` and
  `isFiniteType_kernel_of_isFiniteTypeSections'`: the explicit-hypothesis forms of the five
  finite-type bridges whose own statements take the hypothesis as an instance.
* `Stacks.SheafOfModules.Site.isFiniteTypeSections_relationsPresheaf_of_isCoherent` and
  `Stacks.SheafOfModules.Site.isCoherent_of_isFiniteTypeSections`: the two directions of the
  comparison.
* `Stacks.SheafOfModules.Site.isCoherent_iff_isFiniteTypeSections`: **the equivalence of the
  categorical and the sectionwise form of coherence on a site**, i.e. that
  `Stacks.SheafOfModules.Site.IsCoherent` is the predicate of Stacks 03DL (10).

## Implementation notes

**The level of the `ULift` is forced.** The index type of
`Stacks.SheafOfModules.relationsPresheaf` enters the module universe of the result as
`max w i`, where `w` is the universe of the ring. So `ULift.{w} I` is the only lift of the
index type that leaves that module universe unchanged, and
`Stacks.SheafOfModules.relationsPresheafULiftIso` is stated at that level rather than at a free
one. This is case 2 of the universe dichotomy: the index type computes a target universe, so no
free form exists. The *submodule*-level reindexing above it has no such constraint, which is why
it is factored out.

**Why the reindexing is needed at all.** `Stacks.SheafOfModules.Site.IsCoherent` quantifies over
index types in the module universe, Stacks 03DL (10) over `Fin n`. Neither quantifier contains
the other syntactically, and `Stacks.SheafOfModules.freeToOver` — the morphism attached to a
family of sections — requires its index type to be in the module universe. The two reindexing
isomorphisms are what close that gap, together with
`Stacks.SheafOfModules.freeHomEquiv_symm_eq_freeToOver`, which says that *every* morphism out of
a finite free sheaf of modules is the one attached to a family of sections.

**The module universe equals the ring universe.** Mathlib declares
`SheafOfModules.IsFiniteType` — and hence coherence — only for `SheafOfModules.{u} R` with
`R : Sheaf J RingCat.{u}`. Decoupling the two is a change to Mathlib. The two site universes
`u` and `v` stay independent throughout, and the submodule-level reindexing is stated at
independent index universes.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w i i' m

namespace Stacks.SheafOfModules

-- `Stacks.SheafOfModules.Site.IsCoherent` cannot be *stated* without sheafification and local
-- bijectivity at slice depth two, and the finite-type bridges below cannot be stated without
-- them at depth two over a fixed object. Those are theorems rather than hypotheses: each level
-- of the tower of slice sites inherits both from the level below
-- (`CategoryTheory.hasSheafify_over_over`, `CategoryTheory.wEqualsLocallyBijective_over_over`).
-- Attaching the two step lemmas as local instances is what lets everything below be stated
-- assuming only slice depth one. They are not global instances because their conclusion
-- `P ((J.over Y).over Z)` matches every level of the tower above the first, so globally they
-- would be tried on the way to resolving themselves.
attribute [local instance] hasSheafify_over_over wEqualsLocallyBijective_over_over

/-! ### Reindexing the presheaf of relations -/

section Reindex

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- Reindexing the family along a bijection reindexes the submodule of relations. -/
noncomputable def relationsSubmoduleCongr (M : PresheafOfModules.{m} R) {U : C}
    {I : Type i} {I' : Type i'} [Fintype I] [Fintype I'] (s : I → ToType (M.obj (op U)))
    (e : I' ≃ I) (V : Over U) :
    relationsSubmodule M (s ∘ e) V ≃ₗ[ToType (R.obj (op V.left))] relationsSubmodule M s V where
  toFun a := ⟨fun k => a.val (e.symm k),
    Eq.trans (Fintype.sum_equiv e (fun j => a.val j • M.restrictₛₗ V.hom.op (s (e j)))
      (fun k => a.val (e.symm k) • M.restrictₛₗ V.hom.op (s k))
      (fun j => by rw [e.symm_apply_apply])).symm a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun b := ⟨fun j => b.val (e j),
    Eq.trans (Fintype.sum_equiv e (fun j => b.val (e j) • M.restrictₛₗ V.hom.op (s (e j)))
      (fun k => b.val k • M.restrictₛₗ V.hom.op (s k)) (fun _ => rfl)) b.property⟩
  left_inv a := Subtype.ext (funext fun j => congrArg a.val (e.symm_apply_apply j))
  right_inv b := Subtype.ext (funext fun k => congrArg b.val (e.apply_symm_apply k))

/-- Reindexing a family of sections along a bijection of index types in a single universe
reindexes the presheaf of relations. -/
noncomputable def relationsPresheafCongr (M : PresheafOfModules.{m} R) {U : C}
    {I I' : Type i} [Fintype I] [Fintype I'] (s : I → ToType (M.obj (op U))) (e : I' ≃ I) :
    relationsPresheaf M (s ∘ e) ≅ relationsPresheaf M s :=
  PresheafOfModules.isoMk (fun V => (relationsSubmoduleCongr M s e V.unop).toModuleIso)
    fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl))

/-- Reindexing a family of sections along `ULift.down` reindexes the presheaf of relations.
The level of the `ULift` has to be the ring universe `w`: the index type of
`Stacks.SheafOfModules.relationsPresheaf` enters its module universe as `max w i`, so
`ULift.{w} I` is the only lift that leaves that universe unchanged. -/
noncomputable def relationsPresheafULiftIso (M : PresheafOfModules.{m} R) {U : C}
    {I : Type i} [Fintype I] (s : I → ToType (M.obj (op U))) :
    relationsPresheaf M (fun j : ULift.{w} I => s j.down) ≅ relationsPresheaf M s :=
  PresheafOfModules.isoMk
    (fun V => (relationsSubmoduleCongr M s Equiv.ulift.{w, i} V.unop).toModuleIso)
    fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl))

end Reindex

/-! ### Explicit-hypothesis forms -/

section Explicit

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- `Stacks.SheafOfModules.isFiniteTypeSections_of_iso` with the hypothesis explicit. -/
theorem isFiniteTypeSections_of_iso' {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M N : PresheafOfModules.{m} R} (e : M ≅ N) (h : IsFiniteTypeSections J M) :
    IsFiniteTypeSections J N :=
  have := h
  isFiniteTypeSections_of_iso e

variable {R : Sheaf J RingCat.{w}} [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- `Stacks.SheafOfModules.isFiniteTypeSections_of_isFiniteType` with the hypothesis
explicit. -/
theorem isFiniteTypeSections_of_isFiniteType' (M : SheafOfModules.{w} R) (h : M.IsFiniteType) :
    IsFiniteTypeSections J M.val :=
  have := h
  isFiniteTypeSections_of_isFiniteType M

/-- `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeSections` with the hypothesis
explicit. -/
theorem isFiniteType_of_isFiniteTypeSections' (M : SheafOfModules.{w} R)
    (h : IsFiniteTypeSections J M.val) : M.IsFiniteType :=
  have := h
  isFiniteType_of_isFiniteTypeSections M

variable (M : SheafOfModules.{w} R) {U : C} {I : Type w} [Fintype I]
  (s : I → ToType (M.val.obj (op U)))

/-- `Stacks.SheafOfModules.isFiniteTypeSections_relationsPresheaf` with the hypothesis
explicit. -/
theorem isFiniteTypeSections_relationsPresheaf' (h : (kernel (freeToOver M s)).IsFiniteType) :
    IsFiniteTypeSections (J.over U) (relationsPresheaf M.val s) :=
  have := h
  isFiniteTypeSections_relationsPresheaf M s

/-- `Stacks.SheafOfModules.isFiniteType_kernel_of_isFiniteTypeSections` with the hypothesis
explicit. -/
theorem isFiniteType_kernel_of_isFiniteTypeSections'
    (h : IsFiniteTypeSections (J.over U) (relationsPresheaf M.val s)) :
    (kernel (freeToOver M s)).IsFiniteType :=
  have := h
  isFiniteType_kernel_of_isFiniteTypeSections M s

end Explicit

/-! ### Coherence on a site is the sectionwise condition of Tag 03DL -/

namespace Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{w}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The relations among a finite family of sections of a coherent sheaf of modules are of
finite type.** This is the second half of Stacks 03DL (10) in its sectionwise form, deduced
from the categorical form `Stacks.SheafOfModules.Site.IsCoherent`. -/
theorem isFiniteTypeSections_relationsPresheaf_of_isCoherent {M : SheafOfModules.{w} R}
    (hM : IsCoherent M) (U : C) (n : ℕ) (s : Fin n → ToType (M.val.obj (op U))) :
    IsFiniteTypeSections (J.over U) (relationsPresheaf M.val s) :=
  isFiniteTypeSections_of_iso' (relationsPresheafULiftIso M.val s)
    (isFiniteTypeSections_relationsPresheaf' M (fun j : ULift.{w} (Fin n) => s j.down)
      (hM.kernel_isFiniteType U (ULift.{w} (Fin n)) inferInstance _))

/-- **The sectionwise form of Stacks 03DL (10) implies coherence on the site.** Every morphism
from a finite free sheaf of modules to `M.over U` is the one attached to a finite family of
sections of `M` over `U`, and reindexing that family by `Fin n` loses nothing. -/
theorem isCoherent_of_isFiniteTypeSections {M : SheafOfModules.{w} R}
    (hft : IsFiniteTypeSections J M.val)
    (hrel : ∀ (U : C) (n : ℕ) (s : Fin n → ToType (M.val.obj (op U))),
      IsFiniteTypeSections (J.over U) (relationsPresheaf M.val s)) :
    IsCoherent M := by
  classical
  refine { isFiniteType := isFiniteType_of_isFiniteTypeSections' M hft
           kernel_isFiniteType := fun U I hI φ => ?_ }
  have := hI
  cases nonempty_fintype I
  let e₀ : ULift.{w} (Fin (Fintype.card I)) ≃ I :=
    Equiv.ulift.trans (Fintype.equivFin I).symm
  let s : I → ToType (M.val.obj (op U)) :=
    fun j => ((M.over U).freeHomEquiv φ j).eval (op (Over.mk (𝟙 U)))
  have hφ : φ = freeToOver M s := by
    have h := freeHomEquiv_symm_eq_freeToOver M ((M.over U).freeHomEquiv φ)
    rwa [Equiv.symm_apply_apply] at h
  rw [hφ]
  exact isFiniteType_kernel_of_isFiniteTypeSections' M s
    (isFiniteTypeSections_of_iso' (relationsPresheafCongr M.val s e₀)
      (isFiniteTypeSections_of_iso'
        (relationsPresheafULiftIso M.val fun k => s (e₀ (ULift.up k))).symm
        (hrel U (Fintype.card I) fun k => s (e₀ (ULift.up k)))))

/-- **Coherence on a site is the sectionwise condition of Stacks 03DL (10).** The categorical
form — every kernel of a morphism out of a finite free sheaf of modules is of finite type — and
the sectionwise form — the relations among every finite family of sections over every object are
of finite type — define the same class of sheaves of modules. -/
theorem isCoherent_iff_isFiniteTypeSections {M : SheafOfModules.{w} R} :
    IsCoherent M ↔ IsFiniteTypeSections J M.val ∧
      ∀ (U : C) (n : ℕ) (s : Fin n → ToType (M.val.obj (op U))),
        IsFiniteTypeSections (J.over U) (relationsPresheaf M.val s) :=
  ⟨fun hM => ⟨isFiniteTypeSections_of_isFiniteType' M hM.isFiniteType,
      isFiniteTypeSections_relationsPresheaf_of_isCoherent hM⟩,
    fun h => isCoherent_of_isFiniteTypeSections h.1 h.2⟩

end Site

end Stacks.SheafOfModules

end
