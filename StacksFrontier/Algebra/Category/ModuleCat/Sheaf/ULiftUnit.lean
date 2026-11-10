module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Maps out of the universe-lifted unit object

Let `R : Sheaf J RingCat.{u}` be a sheaf of rings on a site and let
`Stacks.SheafOfModules.moduleULift` be the sectionwise universe lift of sheaves of modules. The
lift `uliftUnit R` of the unit object `SheafOfModules.unit R` to module universe `max u t` is free
of rank one: a morphism out of it is the same as a section of the target.

At an arbitrary module universe we also construct the local closure of a submodule of the
underlying presheaf of a sheaf of modules, the image factorisation of a morphism of sheaves of
modules through the local closure of its range, and the sectionwise kernel as a submodule of a
sheaf, and we give conditions under which the universe lift preserves cokernels and short exact
sequences.

## Main definitions

* `Stacks.SheafOfModules.moduleULiftFullyFaithful`: the sectionwise universe lift of sheaves of
  modules is fully faithful.
* `Stacks.SheafOfModules.uliftUnit`: the universe lift of the unit object.
* `Stacks.SheafOfModules.uliftUnitHom`: the morphism `uliftUnit R ⟶ M` determined by a section
  of `M`.
* `Stacks.SheafOfModules.uliftUnitSection`: the section of `M` determined by a morphism
  `uliftUnit R ⟶ M`.
* `Stacks.SheafOfModules.localClosure`: the local closure of a submodule of the underlying
  presheaf of a sheaf of modules, as a submodule of the sheaf.
* `Stacks.SheafOfModules.toLocalClosureRange`: the factorisation of a morphism of sheaves of
  modules through the local closure of its sectionwise range.
* `Stacks.SheafOfModules.kerSubmodule`: the sectionwise kernel of a morphism of sheaves of
  modules, as a submodule of the source.
* `Stacks.SheafOfModules.cokernelIsoMapCokernelModuleULift`: the universe lift of a cokernel is
  the cokernel of the universe lift, under a hypothesis on the kernel of the projection.

## Main results

* `Stacks.SheafOfModules.moduleULift_comp_overFunctor`: the universe lift commutes with
  restriction to a slice site.
* `Stacks.SheafOfModules.uliftUnitHom_uliftUnitSection`: every morphism out of `uliftUnit R` is
  `uliftUnitHom` of its section.
* `Stacks.SheafOfModules.uliftUnit_hom_ext`: two morphisms out of `uliftUnit R` agreeing on
  `ULift.up 1` are equal.
* `Stacks.SheafOfModules.isLocallySurjective_of_descends`: a cokernel projection of sheaves of
  modules is locally surjective, at an arbitrary module universe.
* `Stacks.SheafOfModules.epi_moduleULift_map_cokernel_π`: the universe lift of a cokernel
  projection is an epimorphism.
* `Stacks.SheafOfModules.isLocallySurjective_of_epi_of_isIso_submodule_ι` and
  `Stacks.SheafOfModules.isIso_submodule_ι_of_isLocallySurjective_of_epi`: every epimorphism of
  `SheafOfModules.{v} R` is locally surjective if and only if every epimorphic inclusion of a
  submodule of a sheaf of modules is an isomorphism.
* `Stacks.SheafOfModules.isColimitCokernelCoforkMapModuleULift`: the universe lift carries a
  locally surjective `π` killing `f` to a cokernel of the lift of `f`, provided every section
  killed by `π` lies in the local closure of the range of `f`.
* `Stacks.SheafOfModules.shortExact_map_moduleULift_of_epi_isLocallySurjective`: if epimorphisms
  of `SheafOfModules.{v} R` are locally surjective, the universe lift preserves short exact
  sequences.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.SheafOfModules

universe t v u u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- The `R(X)`-module structure on the universe-lifted sections of a presheaf of modules. -/
local instance moduleULiftModule (M : PresheafOfModules.{v} R.obj) (X : Cᵒᵖ) :
    Module (R.obj.obj X) ((M.presheaf ⋙ AddCommGrpCat.uliftFunctor.{t}).obj X) :=
  inferInstanceAs (Module _ (ULift.{t} (M.obj X)))

/-- Raising the universe of the sections of a sheaf of modules is additive. -/
instance : (moduleULift.{t, v} R).Additive where
  map_add := by intros; ext X x; rfl

/-- Raising the universe of the sections of a sheaf of modules is fully faithful. -/
def moduleULiftFullyFaithful : (moduleULift.{t, v} R).FullyFaithful where
  preimage f :=
    ⟨{ app := fun X => (ModuleCat.fullyFaithfulUliftFunctor _).preimage (f.val.app X)
       naturality := fun g => by
         ext x
         exact congrArg ULift.down
           (congrArg (fun φ => φ (ULift.up x)) (f.val.naturality g)) }⟩

/-- Raising the universe of the sections commutes with restriction to the slice site over an object
`V`. -/
lemma moduleULift_comp_overFunctor (V : C) :
    moduleULift.{t, v} R ⋙ _root_.SheafOfModules.overFunctor R V =
      _root_.SheafOfModules.overFunctor R V ⋙ moduleULift.{t, v} (R.over V) := rfl

/-- The unit object with its sections raised to universe `max u t`. -/
abbrev uliftUnit : _root_.SheafOfModules.{max u t} R :=
  (moduleULift.{t, u} R).obj (_root_.SheafOfModules.unit R)

/-- The restriction of `uliftUnit R` to the slice site over `V` is `uliftUnit (R.over V)`. -/
lemma overFunctor_obj_uliftUnit (V : C) :
    (_root_.SheafOfModules.overFunctor R V).obj (uliftUnit.{t} R) = uliftUnit.{t} (R.over V) :=
  rfl

variable {R}

/-- The restriction maps of a universe-lifted sheaf of modules are the restriction maps of the
original one, wrapped in `ULift`. -/
lemma moduleULift_obj_val_map_apply (M : _root_.SheafOfModules.{v} R) {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (y : ((moduleULift.{t, v} R).obj M).val.obj X) :
    ((moduleULift.{t, v} R).obj M).val.map g y = ULift.up (M.val.map g y.down) := rfl

/-- The universe lift of a morphism of sheaves of modules acts on sections by `ULift.up` of the
action of the morphism. -/
lemma moduleULift_map_val_app_apply {M N : _root_.SheafOfModules.{v} R} (q : M ⟶ N) (X : Cᵒᵖ)
    (y : ((moduleULift.{t, v} R).obj M).val.obj X) :
    ((moduleULift.{t, v} R).map q).val.app X y = ULift.up (q.val.app X y.down) := rfl

/-- Restricting a morphism of sheaves of modules to the slice site over `V` does not change its
components: the component at `W : Over V` is the component at the object `W.left`. -/
lemma overFunctor_map_val_app_apply {M N : _root_.SheafOfModules.{v} R} (V : C) (h : M ⟶ N)
    (W : (Over V)ᵒᵖ) (y : (M.over V).val.obj W) :
    ((_root_.SheafOfModules.overFunctor R V).map h).val.app W y =
      h.val.app (op W.unop.left) y := rfl

/-- Restricting to the slice site over `V` and raising the universe of the sections commute on
morphisms. -/
lemma moduleULift_map_overFunctor_map {M N : _root_.SheafOfModules.{v} R} (V : C) (h : M ⟶ N) :
    (moduleULift.{t, v} (R.over V)).map ((_root_.SheafOfModules.overFunctor R V).map h) =
      (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{t, v} R).map h) := rfl

/-- If the universe lift of the restriction of `q : B ⟶ D` to the slice site over `V` admits a
factorisation of the universe lift of the restriction of `h : A ⟶ D`, then the restriction of `q`
admits a factorisation of the restriction of `h`. -/
lemma exists_over_comp_eq_of_moduleULift (V : C) {A B D : _root_.SheafOfModules.{v} R}
    (q : B ⟶ D) (h : A ⟶ D)
    (l' : ((moduleULift.{t, v} R).obj A).over V ⟶ ((moduleULift.{t, v} R).obj B).over V)
    (hl' : l' ≫ (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{t, v} R).map q) =
      (_root_.SheafOfModules.overFunctor R V).map ((moduleULift.{t, v} R).map h)) :
    ∃ l : A.over V ⟶ B.over V,
      l ≫ (_root_.SheafOfModules.overFunctor R V).map q =
        (_root_.SheafOfModules.overFunctor R V).map h := by
  refine ⟨(moduleULiftFullyFaithful.{t, v} (R.over V)).preimage
    (X := A.over V) (Y := B.over V) l', ?_⟩
  refine (moduleULiftFullyFaithful.{t, v} (R.over V)).map_injective ?_
  rwa [CategoryTheory.Functor.map_comp,
    (moduleULiftFullyFaithful.{t, v} (R.over V)).map_preimage
      (X := A.over V) (Y := B.over V) l',
    moduleULift_map_overFunctor_map, moduleULift_map_overFunctor_map]

/-- The component at `X` of the morphism `uliftUnit R ⟶ M` determined by a section `s` of `M`:
it sends `x : ULift (R(X))` to `x.down • s X`. -/
def uliftUnitHomApp {M : _root_.SheafOfModules.{max u t} R} (s : M.sections) (X : Cᵒᵖ) :
    (uliftUnit.{t} R).val.obj X ⟶ M.val.obj X :=
  ModuleCat.ofHom
    { toFun := fun x : ULift.{t} (R.obj.obj X) => x.down • s.eval X
      map_add' := fun _ _ => add_smul _ _ _
      map_smul' := fun _ _ => mul_smul _ _ _ }

/-- `uliftUnitHomApp s X` sends `x` to `x.down • s.eval X`. -/
lemma uliftUnitHomApp_apply {M : _root_.SheafOfModules.{max u t} R} (s : M.sections) (X : Cᵒᵖ)
    (x : ULift.{t} (R.obj.obj X)) : uliftUnitHomApp s X x = x.down • s.eval X := rfl

/-- The morphism `uliftUnit R ⟶ M` determined by a section `s` of `M`, sending `x` over `X` to
`x.down • s.eval X`. -/
def uliftUnitHom {M : _root_.SheafOfModules.{max u t} R} (s : M.sections) :
    uliftUnit.{t} R ⟶ M :=
  ⟨{ app := uliftUnitHomApp s
     naturality := fun {X Y} g => by
       ext (x : ULift.{t} (R.obj.obj X))
       change R.obj.map g x.down • s.eval Y = M.val.map g (x.down • s.eval X)
       rw [PresheafOfModules.map_smul, PresheafOfModules.sections_property]
       rfl }⟩

/-- The components of `uliftUnitHom s` are the maps `uliftUnitHomApp s X`. -/
lemma uliftUnitHom_val_app {M : _root_.SheafOfModules.{max u t} R} (s : M.sections) (X : Cᵒᵖ) :
    (uliftUnitHom s).val.app X = uliftUnitHomApp s X := rfl

/-- The section of `M` determined by a morphism `uliftUnit R ⟶ M`: its value on `ULift.up 1` over
each object. -/
def uliftUnitSection {M : _root_.SheafOfModules.{max u t} R} (f : uliftUnit.{t} R ⟶ M) :
    M.sections :=
  PresheafOfModules.sectionsMk (fun X => f.val.app X (ULift.up (1 : R.obj.obj X)))
    (fun {X Y} g => by
      refine (PresheafOfModules.naturality_apply f.val g
        (ULift.up (1 : R.obj.obj X))).symm.trans ?_
      exact congrArg (f.val.app Y) (PresheafOfModules.unit_map_one (R := R.obj) g ▸ rfl))

/-- The value of `uliftUnitSection f` over `X` is `f` applied to `ULift.up 1`. -/
lemma uliftUnitSection_val {M : _root_.SheafOfModules.{max u t} R} (f : uliftUnit.{t} R ⟶ M)
    (X : Cᵒᵖ) : (uliftUnitSection f).val X = f.val.app X (ULift.up (1 : R.obj.obj X)) := rfl

/-- Every morphism out of `uliftUnit R` is the one determined by its section. -/
lemma uliftUnitHom_uliftUnitSection {M : _root_.SheafOfModules.{max u t} R}
    (f : uliftUnit.{t} R ⟶ M) : uliftUnitHom (uliftUnitSection f) = f := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X => ?_)
  ext (x : ULift.{t} (R.obj.obj X))
  change x.down • f.val.app X (ULift.up (1 : R.obj.obj X)) = f.val.app X x
  refine (map_smul (f.val.app X).hom x.down (ULift.up (1 : R.obj.obj X))).symm.trans ?_
  exact congrArg (f.val.app X) (congrArg ULift.up (mul_one x.down))

/-- Two morphisms out of `uliftUnit R` that agree on the canonical generator `ULift.up 1` over
every object are equal. -/
lemma uliftUnit_hom_ext {M : _root_.SheafOfModules.{max u t} R} {f g : uliftUnit.{t} R ⟶ M}
    (h : ∀ X : Cᵒᵖ, f.val.app X (ULift.up (1 : R.obj.obj X)) =
      g.val.app X (ULift.up (1 : R.obj.obj X))) : f = g := by
  rw [← uliftUnitHom_uliftUnitSection f, ← uliftUnitHom_uliftUnitSection g]
  exact congrArg uliftUnitHom (PresheafOfModules.sections_ext _ _ h)

/-! ### Local closures of submodules, and local surjectivity of cokernel projections -/

section LocalClosure

open CategoryTheory.Limits

/-- The underlying type-valued presheaf of a sheaf of modules is a sheaf of types. -/
theorem isSheaf_forgetPresheaf (M : _root_.SheafOfModules.{v} R) :
    Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) := by
  rw [← isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf

/-- The sectionwise range of a morphism of presheaves of modules, as a submodule of the target. -/
noncomputable def presheafRangeSubmodule {M N : PresheafOfModules.{v} R.obj} (f : M ⟶ N) :
    N.Submodule where
  obj X := LinearMap.range (f.app X).hom
  map {X Y} g := by
    rintro x ⟨m, rfl⟩
    exact ⟨M.map g m, PresheafOfModules.naturality_apply f g m⟩

/-- A section lies in `presheafRangeSubmodule f` if and only if it is a value of `f`. -/
lemma mem_presheafRangeSubmodule_obj {M N : PresheafOfModules.{v} R.obj} (f : M ⟶ N) (X : Cᵒᵖ)
    (x : N.obj X) : x ∈ (presheafRangeSubmodule f).obj X ↔ ∃ m, f.app X m = x :=
  Iff.rfl

/-- The local closure of a submodule `N` of the underlying presheaf of a sheaf of modules: the
sections lying in `N` after restriction along the arrows of some covering sieve. -/
noncomputable def localClosurePresheaf (M : _root_.SheafOfModules.{v} R)
    (N : M.val.Submodule) : M.val.Submodule where
  obj X :=
    { carrier := {s | N.toSubfunctor.sieveOfSection s ∈ J X.unop}
      zero_mem' := by
        refine J.superset_covering (fun Y g _ => ?_) (J.top_mem X.unop)
        change M.val.map g.op 0 ∈ N.obj (op Y)
        simp only [map_zero]
        exact (N.obj (op Y)).zero_mem
      add_mem' := fun {a b} ha hb => by
        refine J.superset_covering (fun Y g hg => ?_) (J.intersection_covering ha hb)
        change M.val.map g.op (a + b) ∈ N.obj (op Y)
        rw [map_add]
        exact (N.obj (op Y)).add_mem hg.1 hg.2
      smul_mem' := fun r a ha => by
        refine J.superset_covering (fun Y g hg => ?_) ha
        change M.val.map g.op (r • a) ∈ N.obj (op Y)
        rw [M.val.map_smul]
        exact (N.obj (op Y)).smul_mem _ hg }
  map {X Y} g := fun _ hs => (N.toSubfunctor.sheafify J).map g hs

/-- The underlying subfunctor of `localClosurePresheaf M N` is the sheafification of that of
`N`. -/
lemma toSubfunctor_localClosurePresheaf (M : _root_.SheafOfModules.{v} R)
    (N : M.val.Submodule) :
    (localClosurePresheaf M N).toSubfunctor = N.toSubfunctor.sheafify J := rfl

/-- The local closure of a submodule of the underlying presheaf of a sheaf of modules, as a
submodule of the sheaf. -/
noncomputable def localClosure (M : _root_.SheafOfModules.{v} R) (N : M.val.Submodule) :
    M.Submodule where
  toSubmodule := localClosurePresheaf M N
  isSheaf := ((N.toSubfunctor.sheafify J).isSheaf_iff (isSheaf_forgetPresheaf M)).1
    (N.toSubfunctor.sheafify_isSheaf (isSheaf_forgetPresheaf M))

/-- A section lies in `localClosure M N` if and only if its sieve of sections in `N` is
covering. -/
lemma mem_localClosure_obj {M : _root_.SheafOfModules.{v} R} (N : M.val.Submodule) (X : Cᵒᵖ)
    (s : M.val.obj X) :
    s ∈ (localClosure M N).obj X ↔ N.toSubfunctor.sieveOfSection s ∈ J X.unop :=
  Iff.rfl

/-- A morphism of presheaves of modules all of whose sectionwise values lie in a submodule of the
target factors through that submodule. -/
noncomputable def factorThruSubmodule {M N : PresheafOfModules.{v} R.obj} (f : M ⟶ N)
    (P : N.Submodule) (h : ∀ (X : Cᵒᵖ) (m : M.obj X), f.app X m ∈ P.obj X) :
    M ⟶ P.toPresheafOfModules where
  app X := ModuleCat.ofHom (LinearMap.codRestrict (P.obj X) (f.app X).hom (h X))
  naturality {X Y} g := by
    ext m
    apply Subtype.ext
    exact PresheafOfModules.naturality_apply f g m

/-- `factorThruSubmodule f P h` followed by the inclusion of `P` is `f`. -/
@[simp]
lemma factorThruSubmodule_ι {M N : PresheafOfModules.{v} R.obj} (f : M ⟶ N) (P : N.Submodule)
    (h : ∀ (X : Cᵒᵖ) (m : M.obj X), f.app X m ∈ P.obj X) :
    factorThruSubmodule f P h ≫ P.ι = f := by
  ext X m
  rfl

/-- A morphism of sheaves of modules all of whose sectionwise values lie in a submodule of the
target factors through that submodule. -/
noncomputable def sheafFactorThruSubmodule {G M : _root_.SheafOfModules.{v} R} (f : G ⟶ M)
    (P : M.Submodule) (h : ∀ (X : Cᵒᵖ) (m : G.val.obj X), f.val.app X m ∈ P.obj X) :
    G ⟶ P.toSheafOfModules :=
  ⟨factorThruSubmodule f.val P.toSubmodule h⟩

/-- `sheafFactorThruSubmodule f P h` followed by the inclusion of `P` is `f`. -/
@[simp]
lemma sheafFactorThruSubmodule_ι {G M : _root_.SheafOfModules.{v} R} (f : G ⟶ M)
    (P : M.Submodule) (h : ∀ (X : Cᵒᵖ) (m : G.val.obj X), f.val.app X m ∈ P.obj X) :
    sheafFactorThruSubmodule f P h ≫ P.ι = f :=
  _root_.SheafOfModules.Hom.ext (factorThruSubmodule_ι f.val P.toSubmodule h)

/-- A submodule of a sheaf of modules containing every section has invertible inclusion. -/
theorem isIso_ι_of_forall_mem {M : _root_.SheafOfModules.{v} R} (P : M.Submodule)
    (h : ∀ (X : Cᵒᵖ) (x : M.val.obj X), x ∈ P.obj X) : IsIso P.ι := by
  refine ⟨sheafFactorThruSubmodule (𝟙 M) P (fun X m => h X m), ?_,
    sheafFactorThruSubmodule_ι (𝟙 M) P (fun X m => h X m)⟩
  rw [← cancel_mono P.ι, Category.assoc, sheafFactorThruSubmodule_ι, Category.comp_id,
    Category.id_comp]

/-! ### The image factorisation at an arbitrary module universe -/

/-- Every value of `f` lies in the local closure of the sectionwise range of `f`. -/
theorem app_mem_localClosure_presheafRangeSubmodule {M N : _root_.SheafOfModules.{v} R}
    (f : M ⟶ N) (X : Cᵒᵖ) (m : M.val.obj X) :
    f.val.app X m ∈ (localClosure N (presheafRangeSubmodule f.val)).obj X := by
  refine J.superset_covering (fun Y g _ => ?_) (J.top_mem X.unop)
  exact ⟨M.val.map g.op m, PresheafOfModules.naturality_apply f.val g.op m⟩

/-- The factorisation of a morphism of sheaves of modules through the local closure of its
sectionwise range. -/
noncomputable def toLocalClosureRange {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) :
    M ⟶ (localClosure N (presheafRangeSubmodule f.val)).toSheafOfModules :=
  sheafFactorThruSubmodule f _ (app_mem_localClosure_presheafRangeSubmodule f)

/-- `toLocalClosureRange f` followed by the inclusion of the local closure of the range of `f` is
`f`. -/
@[simp]
lemma toLocalClosureRange_ι {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) :
    toLocalClosureRange f ≫ (localClosure N (presheafRangeSubmodule f.val)).ι = f :=
  sheafFactorThruSubmodule_ι f _ _

/-- The factorisation `toLocalClosureRange f` is locally surjective. -/
theorem isLocallySurjective_toLocalClosureRange {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (toLocalClosureRange f).val) := by
  refine ⟨fun {U} s => J.superset_covering (fun Y g hg => ?_) s.2⟩
  obtain ⟨m, hm⟩ := hg
  exact ⟨m, Subtype.ext hm⟩

/-- The factorisation `toLocalClosureRange f` is an epimorphism. -/
theorem epi_toLocalClosureRange {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) :
    Epi (toLocalClosureRange f) :=
  EpiMono.epi_of_isLocallySurjective _ (isLocallySurjective_toLocalClosureRange f)

/-- The inclusion of the local closure of the range of an epimorphism is an epimorphism. -/
theorem epi_localClosure_presheafRangeSubmodule_ι {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N)
    [Epi f] : Epi (localClosure N (presheafRangeSubmodule f.val)).ι := by
  have _ : Epi (toLocalClosureRange f ≫ (localClosure N (presheafRangeSubmodule f.val)).ι) := by
    rw [toLocalClosureRange_ι]; infer_instance
  exact epi_of_epi (toLocalClosureRange f) _

/-- If the inclusion of the local closure of the range of `f` is invertible, then `f` is locally
surjective. -/
private theorem isLocallySurjective_of_isIso_localClosure_ι {M N : _root_.SheafOfModules.{v} R}
    (f : M ⟶ N) [IsIso (localClosure N (presheafRangeSubmodule f.val)).ι] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
  have _ : IsIso (localClosure N (presheafRangeSubmodule f.val)).ι.val :=
    inferInstanceAs (IsIso ((_root_.SheafOfModules.forget R).map
      (localClosure N (presheafRangeSubmodule f.val)).ι))
  have _ : Epi (localClosure N (presheafRangeSubmodule f.val)).ι.val := inferInstance
  refine ⟨fun {U} s => ?_⟩
  obtain ⟨y, hy⟩ := PresheafOfModules.surjective_of_epi
    (localClosure N (presheafRangeSubmodule f.val)).ι.val (op U) s
  have hsmem : s ∈ (localClosure N (presheafRangeSubmodule f.val)).obj (op U) := by
    rw [← hy]; exact y.2
  exact J.superset_covering (fun _ _ hg => hg) hsmem

/-- If every epimorphic inclusion of a submodule of a sheaf of modules is an isomorphism, then
every epimorphism of `SheafOfModules.{v} R` is locally surjective. -/
theorem isLocallySurjective_of_epi_of_isIso_submodule_ι
    (hsub : ∀ (M' : _root_.SheafOfModules.{v} R) (P : M'.Submodule), Epi P.ι → IsIso P.ι)
    {M N : _root_.SheafOfModules.{v} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
  have _ : IsIso (localClosure N (presheafRangeSubmodule f.val)).ι :=
    hsub N _ (epi_localClosure_presheafRangeSubmodule_ι f)
  exact isLocallySurjective_of_isIso_localClosure_ι f

/-- If epimorphisms of `SheafOfModules.{v} R` are locally surjective, then an epimorphic inclusion
of a submodule of a sheaf of modules is an isomorphism. -/
theorem isIso_submodule_ι_of_isLocallySurjective_of_epi
    (hepi : ∀ {M' N' : _root_.SheafOfModules.{v} R} (ψ : M' ⟶ N'), Epi ψ →
      Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map ψ.val))
    (M : _root_.SheafOfModules.{v} R) (P : M.Submodule) (h : Epi P.ι) : IsIso P.ι := by
  have hls := hepi P.ι h
  refine isIso_ι_of_forall_mem P (fun X x => P.isSheaf x ?_)
  refine J.superset_covering (fun Y g hg => ?_)
    (Presheaf.imageSieve_mem J
      ((PresheafOfModules.toPresheaf R.obj).map P.ι.val) (U := X) x)
  obtain ⟨m, hm⟩ := hg
  change (((PresheafOfModules.toPresheaf R.obj).obj M.val).map g.op) x ∈ P.obj (op Y)
  rw [← hm]
  exact m.2

/-- Let `π : G ⟶ Q` be an epimorphism of sheaves of modules killing `f : F ⟶ G` such that every
morphism out of `G` killing `f` factors through `π`. Then `π` is locally surjective. -/
theorem isLocallySurjective_of_descends {F G Q : _root_.SheafOfModules.{v} R} (f : F ⟶ G)
    (π : G ⟶ Q) [Epi π] (w : f ≫ π = 0)
    (hdesc : ∀ (Z : _root_.SheafOfModules.{v} R) (h : G ⟶ Z), f ≫ h = 0 →
      ∃ σ : Q ⟶ Z, π ≫ σ = h) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map π.val) := by
  have hmem := app_mem_localClosure_presheafRangeSubmodule π
  set P : Q.Submodule := localClosure Q (presheafRangeSubmodule π.val)
  set π' : G ⟶ P.toSheafOfModules := sheafFactorThruSubmodule π P hmem
  have hπ' : π' ≫ P.ι = π := sheafFactorThruSubmodule_ι π P hmem
  have hfπ' : f ≫ π' = 0 := by
    rw [← cancel_mono P.ι, Category.assoc, hπ', w, zero_comp]
  obtain ⟨σ, hσ⟩ := hdesc _ π' hfπ'
  have hsplit : σ ≫ P.ι = 𝟙 Q := by
    rw [← cancel_epi π, ← Category.assoc, hσ, hπ', Category.comp_id]
  have _ : IsSplitEpi P.ι := IsSplitEpi.mk' ⟨σ, hsplit⟩
  have _ : IsIso P.ι := isIso_of_mono_of_isSplitEpi P.ι
  exact isLocallySurjective_of_isIso_localClosure_ι π

/-- A cokernel projection of sheaves of modules is locally surjective. -/
theorem isLocallySurjective_cokernel_π {F G : _root_.SheafOfModules.{v} R} (f : F ⟶ G)
    [HasCokernel f] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (cokernel.π f).val) :=
  isLocallySurjective_of_descends f (cokernel.π f) (cokernel.condition f)
    (fun _ h hh => ⟨cokernel.desc f h hh, cokernel.π_desc f h hh⟩)

/-- The universe lift of a locally surjective morphism of sheaves of modules is locally
surjective. -/
theorem isLocallySurjective_moduleULift_map {M N : _root_.SheafOfModules.{v} R} (φ : M ⟶ N)
    (h : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map φ.val)) :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map
      ((moduleULift.{t, v} R).map φ).val) := by
  refine ⟨fun {U} s => ?_⟩
  refine J.superset_covering (fun V g hg => ?_)
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R.obj).map φ.val) (U := op U)
      (ULift.down s))
  obtain ⟨u, hu⟩ := hg
  exact ⟨ULift.up u, congrArg ULift.up hu⟩

/-- Let `π : G ⟶ Q` be an epimorphism of sheaves of modules killing `f : F ⟶ G` such that every
morphism out of `G` killing `f` factors through `π`. Then the universe lift of `π` is an
epimorphism. -/
theorem epi_moduleULift_map_of_descends {F G Q : _root_.SheafOfModules.{v} R} (f : F ⟶ G)
    (π : G ⟶ Q) [Epi π] (w : f ≫ π = 0)
    (hdesc : ∀ (Z : _root_.SheafOfModules.{v} R) (h : G ⟶ Z), f ≫ h = 0 →
      ∃ σ : Q ⟶ Z, π ≫ σ = h) :
    Epi ((moduleULift.{t, v} R).map π) :=
  EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_moduleULift_map π (isLocallySurjective_of_descends f π w hdesc))

/-- The universe lift of a cokernel projection of sheaves of modules is an epimorphism. -/
theorem epi_moduleULift_map_cokernel_π {F G : _root_.SheafOfModules.{v} R} (f : F ⟶ G)
    [HasCokernel f] : Epi ((moduleULift.{t, v} R).map (cokernel.π f)) :=
  epi_moduleULift_map_of_descends f (cokernel.π f) (cokernel.condition f)
    (fun _ h hh => ⟨cokernel.desc f h hh, cokernel.π_desc f h hh⟩)

/-- Evaluation of a sheaf of modules at an object is an additive functor. -/
instance evaluationAdditive (X : Cᵒᵖ) : (_root_.SheafOfModules.evaluation.{v} R X).Additive := by
  dsimp [_root_.SheafOfModules.evaluation]
  infer_instance

/-- A monomorphism of sheaves of modules is sectionwise injective. -/
theorem injective_app_of_mono {M N : _root_.SheafOfModules.{v} R} (φ : M ⟶ N) [Mono φ]
    (X : Cᵒᵖ) : Function.Injective (φ.val.app X) := by
  have hz : kernel.ι φ = 0 :=
    (Preadditive.mono_iff_cancel_zero φ).1 inferInstance _ _ (kernel.condition φ)
  have hki : kernel.ι ((_root_.SheafOfModules.evaluation R X).map φ) = 0 := by
    rw [← PreservesKernel.iso_inv_ι (_root_.SheafOfModules.evaluation R X) φ, hz,
      Functor.map_zero, comp_zero]
  rw [← ModuleCat.mono_iff_injective, Preadditive.mono_iff_cancel_zero]
  intro _ g hg
  rw [← kernel.lift_ι ((_root_.SheafOfModules.evaluation R X).map φ) g hg, hki, comp_zero]
  rfl

/-- The universe lift of a monomorphism of sheaves of modules is a monomorphism. -/
theorem mono_moduleULift_map {M N : _root_.SheafOfModules.{v} R} (φ : M ⟶ N) [Mono φ] :
    Mono ((moduleULift.{t, v} R).map φ) :=
  (_root_.SheafOfModules.forget R).mono_of_mono_map
    (PresheafOfModules.mono_of_injective
      (f := ((moduleULift.{t, v} R).map φ).val)
      (fun {X} _ _ h => ULift.ext (injective_app_of_mono φ X (congrArg ULift.down h))))

/-! ### Separatedness, and killing the local closure of a range -/

/-- If `a ≫ b = 0`, then `b` kills every value of `a`. -/
lemma val_app_apply_eq_zero {A B D : _root_.SheafOfModules.{v} R} (a : A ⟶ B) (b : B ⟶ D)
    (h : a ≫ b = 0) (X : Cᵒᵖ) (x : A.val.obj X) : b.val.app X (a.val.app X x) = 0 := by
  change (a ≫ b).val.app X x = 0
  rw [h]
  rfl

/-- A section of a sheaf of modules that restricts to zero along every arrow of a covering sieve is
zero. -/
theorem eq_zero_of_locally_eq_zero {M : _root_.SheafOfModules.{v} R} {X : Cᵒᵖ}
    (s : M.val.obj X) {S : Sieve X.unop} (hS : S ∈ J X.unop)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop), S g → M.val.map g.op s = 0) : s = 0 := by
  refine (isSheaf_forgetPresheaf M S hS).isSeparatedFor.ext (t₁ := s) (t₂ := 0)
    fun Y g hg => ?_
  change M.val.map g.op s = M.val.map g.op 0
  rw [h g hg, map_zero]

/-- A morphism out of `G` that kills `f : F ⟶ G` kills the local closure of the range of `f`. -/
theorem app_eq_zero_of_mem_localClosure {F G Z : _root_.SheafOfModules.{v} R} (f : F ⟶ G)
    (k : G ⟶ Z) (hk : f ≫ k = 0) {X : Cᵒᵖ} (x : G.val.obj X)
    (hx : x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X) :
    k.val.app X x = 0 := by
  refine eq_zero_of_locally_eq_zero _ hx (fun {Y} g hg => ?_)
  obtain ⟨m, hm⟩ := hg
  exact (PresheafOfModules.naturality_apply k.val g.op x).symm.trans
    (hm ▸ val_app_apply_eq_zero f k hk (op Y) m)

/-- The cokernel projection of `f` kills the local closure of the range of `f`. -/
theorem app_cokernel_π_eq_zero_of_mem_localClosure {F G : _root_.SheafOfModules.{v} R}
    (f : F ⟶ G) [HasCokernel f] {X : Cᵒᵖ} (x : G.val.obj X)
    (hx : x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X) :
    (cokernel.π f).val.app X x = 0 :=
  app_eq_zero_of_mem_localClosure f (cokernel.π f) (cokernel.condition f) x hx

/-- Suppose that for every submodule `P` of a sheaf of modules `G'` and every epimorphism
`π : G' ⟶ Q'` killing the inclusion of `P` through which every morphism killing that inclusion
factors, every section killed by `π` lies in `P`. Then for every `f : F ⟶ G` and every such
`π : G ⟶ Q` for `f`, every section killed by `π` lies in the local closure of the range of `f`. -/
theorem mem_localClosure_of_descends_of_submodule
    (hsub : ∀ (G' Q' : _root_.SheafOfModules.{v} R) (P : G'.Submodule) (π : G' ⟶ Q'), Epi π →
      P.ι ≫ π = 0 →
      (∀ (Z : _root_.SheafOfModules.{v} R) (h : G' ⟶ Z), P.ι ≫ h = 0 → ∃ σ : Q' ⟶ Z, π ≫ σ = h) →
      ∀ (X : Cᵒᵖ) (x : G'.val.obj X), π.val.app X x = 0 → x ∈ P.obj X)
    {F G Q : _root_.SheafOfModules.{v} R} (f : F ⟶ G) (π : G ⟶ Q) [Epi π] (w : f ≫ π = 0)
    (hdesc : ∀ (Z : _root_.SheafOfModules.{v} R) (h : G ⟶ Z), f ≫ h = 0 →
      ∃ σ : Q ⟶ Z, π ≫ σ = h)
    (X : Cᵒᵖ) (x : G.val.obj X) (hx : π.val.app X x = 0) :
    x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X := by
  have hfac : ∀ (Z : _root_.SheafOfModules.{v} R) (h : G ⟶ Z),
      (localClosure G (presheafRangeSubmodule f.val)).ι ≫ h = 0 → f ≫ h = 0 := by
    intro Z h hh
    rw [← toLocalClosureRange_ι f, Category.assoc, hh, comp_zero]
  refine hsub G Q _ π inferInstance ?_ (fun Z h hh => hdesc Z h (hfac Z h hh)) X x hx
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun Y => ?_))
  ext y
  exact app_eq_zero_of_mem_localClosure f π w y.1 y.2

/-- Under the hypothesis of `mem_localClosure_of_descends_of_submodule`, every section killed by
the cokernel projection of `f` lies in the local closure of the range of `f`. -/
theorem mem_localClosure_cokernel_π_of_submodule
    (hsub : ∀ (G' Q' : _root_.SheafOfModules.{v} R) (P : G'.Submodule) (π : G' ⟶ Q'), Epi π →
      P.ι ≫ π = 0 →
      (∀ (Z : _root_.SheafOfModules.{v} R) (h : G' ⟶ Z), P.ι ≫ h = 0 → ∃ σ : Q' ⟶ Z, π ≫ σ = h) →
      ∀ (X : Cᵒᵖ) (x : G'.val.obj X), π.val.app X x = 0 → x ∈ P.obj X)
    {F G : _root_.SheafOfModules.{v} R} (f : F ⟶ G) [HasCokernel f] (X : Cᵒᵖ)
    (x : G.val.obj X) (hx : (cokernel.π f).val.app X x = 0) :
    x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X :=
  mem_localClosure_of_descends_of_submodule hsub f (cokernel.π f) (cokernel.condition f)
    (fun _ h hh => ⟨cokernel.desc f h hh, cokernel.π_desc f h hh⟩) X x hx

/-- The universe lift carries the local closure of the range of `f` into the local closure of the
range of the universe lift of `f`. -/
theorem mem_localClosure_moduleULift_map {F G : _root_.SheafOfModules.{v} R} (f : F ⟶ G)
    {X : Cᵒᵖ} (x : G.val.obj X)
    (hx : x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X) :
    (ULift.up x : ((moduleULift.{t, v} R).obj G).val.obj X) ∈
      (localClosure ((moduleULift.{t, v} R).obj G)
        (presheafRangeSubmodule ((moduleULift.{t, v} R).map f).val)).obj X := by
  refine J.superset_covering (fun Y g hg => ?_) hx
  obtain ⟨m, hm⟩ := hg
  exact ⟨ULift.up m, congrArg ULift.up hm⟩

/-! ### The sectionwise kernel as a submodule of the source sheaf -/

/-- The sectionwise kernel of a morphism of presheaves of modules, as a submodule of the source. -/
noncomputable def presheafKerSubmodule {M N : PresheafOfModules.{v} R.obj} (f : M ⟶ N) :
    M.Submodule where
  obj X := LinearMap.ker (f.app X).hom
  map {X Y} g := by
    intro x hx
    change f.app Y (M.map g x) = 0
    exact (PresheafOfModules.naturality_apply f g x).trans
      (congrArg (N.map g) hx |>.trans (map_zero (N.map g).hom))

/-- A section lies in `presheafKerSubmodule f` if and only if `f` kills it. -/
lemma mem_presheafKerSubmodule_obj {M N : PresheafOfModules.{v} R.obj} (f : M ⟶ N) (X : Cᵒᵖ)
    (x : M.obj X) : x ∈ (presheafKerSubmodule f).obj X ↔ f.app X x = 0 :=
  Iff.rfl

/-- The sectionwise kernel of a morphism of sheaves of modules, as a submodule of the source
sheaf. -/
noncomputable def kerSubmodule {M N : _root_.SheafOfModules.{v} R} (φ : M ⟶ N) : M.Submodule where
  toSubmodule := presheafKerSubmodule φ.val
  isSheaf {X} s hs :=
    eq_zero_of_locally_eq_zero (φ.val.app X s) hs
      (fun {_Y} g hg => (PresheafOfModules.naturality_apply φ.val g.op s).symm.trans hg)

/-- A section lies in `kerSubmodule φ` if and only if `φ` kills it. -/
lemma mem_kerSubmodule_obj {M N : _root_.SheafOfModules.{v} R} (φ : M ⟶ N) (X : Cᵒᵖ)
    (x : M.val.obj X) : x ∈ (kerSubmodule φ).obj X ↔ φ.val.app X x = 0 :=
  Iff.rfl

/-- The inclusion of `kerSubmodule φ` followed by `φ` is zero. -/
lemma kerSubmodule_ι_comp {M N : _root_.SheafOfModules.{v} R} (φ : M ⟶ N) :
    (kerSubmodule φ).ι ≫ φ = 0 := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun X => ?_))
  ext x
  exact x.2

/-- The inclusion of `kerSubmodule φ` is a kernel of `φ`. -/
noncomputable def isLimitKernelForkKerSubmodule {M N : _root_.SheafOfModules.{v} R} (φ : M ⟶ N) :
    IsLimit (KernelFork.ofι (kerSubmodule φ).ι (kerSubmodule_ι_comp φ)) :=
  KernelFork.IsLimit.ofι' _ _ (fun {_A} a ha =>
    ⟨sheafFactorThruSubmodule a (kerSubmodule φ)
      (fun X m => val_app_apply_eq_zero a φ ha X m),
      sheafFactorThruSubmodule_ι a _ _⟩)

/-- Let `a ≫ φ = 0` with `kernel.lift φ a` an epimorphism, and suppose epimorphisms of
`SheafOfModules.{v} R` are locally surjective. Then every section killed by `φ` lies in the local
closure of the range of `a`. -/
theorem mem_localClosure_of_epi_kernelLift {A M N : _root_.SheafOfModules.{v} R}
    (a : A ⟶ M) (φ : M ⟶ N) (ha : a ≫ φ = 0) (hlift : Epi (kernel.lift φ a ha))
    (hepi : ∀ {P Q : _root_.SheafOfModules.{v} R} (ψ : P ⟶ Q), Epi ψ →
      Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map ψ.val))
    (X : Cᵒᵖ) (x : M.val.obj X) (hx : φ.val.app X x = 0) :
    x ∈ (localClosure M (presheafRangeSubmodule a.val)).obj X := by
  set k := sheafFactorThruSubmodule a (kerSubmodule φ)
    (fun X m => val_app_apply_eq_zero a φ ha X m)
  have hk : k ≫ (kerSubmodule φ).ι = a := sheafFactorThruSubmodule_ι a _ _
  have he : Epi k := by
    have hcomp : (IsLimit.conePointUniqueUpToIso (kernelIsKernel φ)
        (isLimitKernelForkKerSubmodule φ)).hom ≫ (kerSubmodule φ).ι = kernel.ι φ := by
      simpa using IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsKernel φ)
        (isLimitKernelForkKerSubmodule φ) WalkingParallelPair.zero
    have h2 : kernel.lift φ a ha ≫ (IsLimit.conePointUniqueUpToIso (kernelIsKernel φ)
        (isLimitKernelForkKerSubmodule φ)).hom = k := by
      rw [← cancel_mono (kerSubmodule φ).ι, Category.assoc, hcomp, kernel.lift_ι, hk]
    rw [← h2]
    exact epi_comp _ _
  have := hepi k he
  refine J.superset_covering (fun Y g hg => ?_)
    (Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf R.obj).map k.val)
      (U := X) (⟨x, hx⟩ : (kerSubmodule φ).obj X))
  obtain ⟨m, hm⟩ := hg
  refine ⟨m, ?_⟩
  have h : (k ≫ (kerSubmodule φ).ι).val.app (op Y) m = M.val.map g.op x :=
    congrArg (fun z => (kerSubmodule φ).ι.val.app (op Y) z) hm
  rwa [hk] at h

/-! ### Transfer of a cokernel along the universe lift -/

section CokernelTransfer

variable [HasSheafify J AddCommGrpCat.{max v t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]

/-- Let `π : G ⟶ Q` be locally surjective and kill `f`, and assume that every section of `G` killed
by `π` lies in the local closure of the range of `f`. Then the universe lift of `π` is a cokernel
of the universe lift of `f`. -/
noncomputable def isColimitCokernelCoforkMapModuleULift
    {F G Q : _root_.SheafOfModules.{v} R} (f : F ⟶ G) (π : G ⟶ Q) (w : f ≫ π = 0)
    (hπ : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map π.val))
    (hker : ∀ (X : Cᵒᵖ) (x : G.val.obj X), π.val.app X x = 0 →
      x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X) :
    IsColimit (CokernelCofork.ofπ ((moduleULift.{t, v} R).map π)
      (show (moduleULift.{t, v} R).map f ≫ (moduleULift.{t, v} R).map π = 0 by
        rw [← Functor.map_comp, w, Functor.map_zero])) := by
  haveI hepi : Epi ((moduleULift.{t, v} R).map π) :=
    EpiMono.epi_of_isLocallySurjective _ (isLocallySurjective_moduleULift_map π hπ)
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => ?_)
  have hkill : ∀ (X : Cᵒᵖ) (y : ((moduleULift.{t, v} R).obj G).val.obj X),
      ((moduleULift.{t, v} R).map π).val.app X y = 0 → k.val.app X y = 0 := fun X y hy =>
    app_eq_zero_of_mem_localClosure ((moduleULift.{t, v} R).map f) k hk y
      (mem_localClosure_moduleULift_map f y.down (hker X y.down (congrArg ULift.down hy)))
  have hz : kernel.ι ((moduleULift.{t, v} R).map π) ≫ k = 0 := by
    refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext (fun X => ?_))
    ext z
    exact hkill X _ (val_app_apply_eq_zero _ _
      (kernel.condition ((moduleULift.{t, v} R).map π)) X z)
  exact ⟨Abelian.epiDesc _ k hz, Abelian.comp_epiDesc _ k hz⟩

/-- The cokernel of the universe lift of `f` is the universe lift of the cokernel of `f`, provided
every section killed by the cokernel projection lies in the local closure of the range of `f`. -/
noncomputable def cokernelIsoMapCokernelModuleULift {F G : _root_.SheafOfModules.{v} R}
    (f : F ⟶ G) [HasCokernel f]
    (hker : ∀ (X : Cᵒᵖ) (x : G.val.obj X), (cokernel.π f).val.app X x = 0 →
      x ∈ (localClosure G (presheafRangeSubmodule f.val)).obj X) :
    cokernel ((moduleULift.{t, v} R).map f) ≅ (moduleULift.{t, v} R).obj (cokernel f) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitCokernelCoforkMapModuleULift f (cokernel.π f) (cokernel.condition f)
      (isLocallySurjective_cokernel_π f) hker)

/-- The universe lift of a short exact sequence `E` is short exact, provided `E.g` is locally
surjective and every section killed by `E.g` lies in the local closure of the range of `E.f`. -/
theorem shortExact_map_moduleULift (E : ShortComplex (_root_.SheafOfModules.{v} R))
    (hE : E.ShortExact)
    (hg : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map E.g.val))
    (hker : ∀ (X : Cᵒᵖ) (x : E.X₂.val.obj X), E.g.val.app X x = 0 →
      x ∈ (localClosure E.X₂ (presheafRangeSubmodule E.f.val)).obj X) :
    (E.map (moduleULift.{t, v} R)).ShortExact where
  exact := by
    have := hE.mono_f
    exact ShortComplex.exact_of_g_is_cokernel _
      (isColimitCokernelCoforkMapModuleULift E.f E.g E.zero hg hker)
  mono_f := by
    have := hE.mono_f
    exact mono_moduleULift_map E.f
  epi_g :=
    EpiMono.epi_of_isLocallySurjective _ (isLocallySurjective_moduleULift_map E.g hg)

/-- If every epimorphism of `SheafOfModules.{v} R` is locally surjective, then the universe lift
carries a short exact sequence to a short exact sequence. -/
theorem shortExact_map_moduleULift_of_epi_isLocallySurjective
    (hepi : ∀ {P Q : _root_.SheafOfModules.{v} R} (ψ : P ⟶ Q), Epi ψ →
      Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map ψ.val))
    (E : ShortComplex (_root_.SheafOfModules.{v} R)) (hE : E.ShortExact) :
    (E.map (moduleULift.{t, v} R)).ShortExact := by
  have := hE.exact.hasHomology
  exact shortExact_map_moduleULift E hE (hepi E.g hE.epi_g)
    (mem_localClosure_of_epi_kernelLift E.f E.g E.zero hE.exact.epi_kernelLift hepi)

end CokernelTransfer

end LocalClosure

end Stacks.SheafOfModules

end
