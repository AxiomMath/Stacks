module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel

/-!
# A sheaf of modules on a slice site, with its scalars spelled in the base

Fix a site `(C, J)`, a sheaf of rings `R` and an object `U`. The structure sheaf of the slice
site has two spellings: `(R.over U).obj`, which is what `SheafOfModules.free`, `kernel` and the
whole Mathlib slice API produce, and `(Over.forget U).op ⋙ R.obj`, whose value at `V` is
`R(V.left)` — the spelling in which Stacks states every sectionwise condition on the slice site,
and the one `Stacks.SheafOfModules.relationsPresheaf` uses.

The two are definitionally equal. They are nevertheless *not* interchangeable, and the failure is
sharper than a failed `rw`: for `a : R(V.left)` and `e` a section over `V` of a sheaf of modules
on the slice site, `a • e` **has no `HSMul` instance at all**, because instance synthesis runs at
`instances` transparency and will not unfold `(R.over U).obj.obj (op V)` to `R.obj.obj
(op V.left)`. So elements respell freely — `Stacks.SheafOfModules.ofCoordsOver` and `coordsOver`
of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover` do exactly that — while the
module structure does not.

This file supplies the missing module structure, as a restriction of scalars along the identity.
`Stacks.SheafOfModules.overScalarsHom` is the identity morphism of presheaves of rings between
the two spellings, and `Stacks.SheafOfModules.overBase N` is
`PresheafOfModules.restrictScalars` of that morphism applied to `N`: the same presheaf of
modules, with the base spelling of the scalars. Its sections are the sections of `N`, retyped by
the pair of definitions `toOverBase` / `ofOverBase`, and the one lemma that makes the whole thing
work is `Stacks.SheafOfModules.ofOverBase_smul`, which is `rfl`.

The payoff is the isomorphism of presheaves of modules
`Stacks.SheafOfModules.relationsPresheafIso` and, through it,
`Stacks.SheafOfModules.isFiniteTypeSections_relationsPresheaf`.

## Main definitions

* `Stacks.SheafOfModules.overScalarsHom` : the identity morphism of presheaves of rings
  `(Over.forget U).op ⋙ R.obj ⟶ (R.over U).obj`.
* `Stacks.SheafOfModules.overBase` : a sheaf of modules on the slice site at `U`, read as a
  presheaf of modules over the base spelling of the structure sheaf of that site.
* `Stacks.SheafOfModules.toOverBase` and `ofOverBase` : the two retypings of a section across
  that boundary.
* `Stacks.SheafOfModules.coordsOverLinearEquiv` : the coordinates of a section of a finite free
  sheaf of modules on the slice site, **as a linear equivalence over `R(V.left)`**.
* `Stacks.SheafOfModules.kernelCoordsOver` and `kernelCoordsOverLinearEquiv` : the coordinates
  of a section of `kernel (freeToOver M s)`, as a linear map, resp. linear equivalence, onto the
  submodule of relations among the restricted family.

## Main results

* `Stacks.SheafOfModules.ofOverBase_smul` : **the scalar action crosses the boundary.** Acting
  by `a : R(V.left)` on a section of `overBase N` is acting by `a`, read in the slice spelling,
  on the corresponding section of `N`.
* `Stacks.SheafOfModules.coordsOver_smul` : taking coordinates in the base is linear.
* `Stacks.SheafOfModules.relationsPresheafIso` : **the presheaf of relations among a finite
  family of sections is the kernel of the map out of the free sheaf of modules, respelled.**
  This upgrades the elementwise bijection `Stacks.SheafOfModules.bijOn_coordsOver_kernel`.
* `Stacks.SheafOfModules.isFiniteTypeSections_overBase` : the sheafification-free finite type
  condition is unaffected by the respelling.
* `Stacks.SheafOfModules.isFiniteTypeSections_relationsPresheaf` and
  `isFiniteType_kernel_of_isFiniteTypeSections` : **the sectionwise relations are of finite type
  exactly when the kernel is**, which is the agreement of the two forms of the second half of
  the coherence condition of Tag 03DL.

## Implementation notes

**Why a `def` and not an `abbrev`, and why not an instance.** `overBase` must be a `def`: an
`abbrev` is reducible, so instance synthesis unfolds it and recovers the slice-spelled `Module`
instance, which is the structure one is trying to get away from. An `HSMul` or `Module` instance
for the base spelling directly on `ToType (N.val.obj (op V))` is *not* the right answer either:
at `V = Over.mk (𝟙 U)` and `N = M.over U` the carrier is `ToType (M.val.obj (op U))`, which
already carries `ModuleCat.isModule` over `R.obj.obj (op U)`, so such an instance would be a
second `Module R(U)`-structure on the same type — definitionally equal to the first and not
syntactically equal to it, i.e. a diamond. Restriction of scalars avoids this because it changes
the carrier's *spelling*: `ToType ((overBase N).obj (op V))` is a syntactically distinct type
expression, and only one `Module` instance is ever found for it.

**One spelling per statement.** Every statement here is written in a single spelling and the
boundary is crossed only in the `rfl`-lemmas `ofOverBase_toOverBase`, `toOverBase_ofOverBase`,
`ofOverBase_add`, `ofOverBase_zero`, `ofOverBase_smul`, `ofOverBase_map` and
`overScalarsHom_app_apply`, and in the three places where a term is handed across by `exact`. In
particular `coordsOver_smul` writes its scalar as `(overScalarsHom R U).app (op V) a` rather
than mixing `a : R(V.left)` with a slice-spelled product: the mixed form fails to synthesize
`HMul (ToType ((R.over U).obj.obj (op V))) (ToType (R.obj.obj (op V.left))) ?m`.

**Universes.** The bridge section leaves the module universe `w` free, independent of the ring
universe `u` and of the two site universes: nothing in it computes a target universe from the
module universe. The coordinate and relations sections are at `SheafOfModules.{u} R` with the
index type in `Type u`, which is what `SheafOfModules.free` forces and what
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelationsKernel` uses. Nothing is narrowed.

**Which sheafification hypotheses.** Only slice ones, and only for the single object `U` at
hand, exactly as in `RelationsKernel`: `HasWeakSheafify (J.over U)` for the coordinates and
`HasSheafify (J.over U)` where a kernel is taken. `isFiniteTypeSections_relationsPresheaf`
additionally assumes the hypotheses of `isFiniteTypeSections_of_isFiniteType` *for the site*
`Over U`, i.e. for every object `X` of `Over U` rather than of `C`, since that is the site its
conclusion is about.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u w v u'

namespace Stacks.SheafOfModules

/-! ### The identity restriction of scalars across the slice/base boundary -/

section Bridge

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- The identity morphism of presheaves of rings between the two spellings of the structure
sheaf of the slice site at `U`. -/
noncomputable def overScalarsHom (R : Sheaf J RingCat.{u}) (U : C) :
    (Over.forget U).op ⋙ R.obj ⟶ (R.over U).obj := 𝟙 _

/-- The component of `overScalarsHom R U` at `V` is the identity on `R(V.left)`. -/
@[simp]
lemma overScalarsHom_app_apply {U : C} (V : (Over U)ᵒᵖ)
    (a : ToType (R.obj.obj (op V.unop.left))) : (overScalarsHom R U).app V a = a := rfl

/-- A sheaf of modules on the slice site at `U`, read as a presheaf of modules over the base
spelling of the structure sheaf of that site. -/
noncomputable def overBase {U : C} (N : SheafOfModules.{w} (R.over U)) :
    PresheafOfModules.{w} ((Over.forget U).op ⋙ R.obj) :=
  (PresheafOfModules.restrictScalars (overScalarsHom R U)).obj N.val

/-- A section of `N` over an object of the slice site, read in the base spelling. -/
def toOverBase {U : C} {N : SheafOfModules.{w} (R.over U)} (V : Over U)
    (e : ToType (N.val.obj (op V))) : ToType ((overBase N).obj (op V)) := e

/-- A section of `overBase N`, read back in the slice spelling. -/
def ofOverBase {U : C} {N : SheafOfModules.{w} (R.over U)} (V : Over U)
    (e : ToType ((overBase N).obj (op V))) : ToType (N.val.obj (op V)) := e

/-- Reading a section in the base spelling and back returns it. -/
@[simp]
lemma ofOverBase_toOverBase {U : C} {N : SheafOfModules.{w} (R.over U)} (V : Over U)
    (e : ToType (N.val.obj (op V))) : ofOverBase V (toOverBase V e) = e := rfl

/-- Reading a section of `overBase N` in the slice spelling and back returns it. -/
@[simp]
lemma toOverBase_ofOverBase {U : C} {N : SheafOfModules.{w} (R.over U)} (V : Over U)
    (e : ToType ((overBase N).obj (op V))) : toOverBase V (ofOverBase V e) = e := rfl

/-- `ofOverBase` is additive. -/
lemma ofOverBase_add {U : C} {N : SheafOfModules.{w} (R.over U)} (V : Over U)
    (e e' : ToType ((overBase N).obj (op V))) :
    ofOverBase V (e + e') = ofOverBase V e + ofOverBase V e' := rfl

/-- `ofOverBase` sends zero to zero. -/
lemma ofOverBase_zero {U : C} {N : SheafOfModules.{w} (R.over U)} (V : Over U) :
    ofOverBase V (0 : ToType ((overBase N).obj (op V))) = 0 := rfl

/-- **The scalar action crosses the slice/base boundary.** Acting by `a : R(V.left)` on a
section of `overBase N` over `V` is acting by `a`, read in the slice spelling, on the
corresponding section of `N`. -/
lemma ofOverBase_smul {U : C} {N : SheafOfModules.{w} (R.over U)} (V : Over U)
    (a : ToType (R.obj.obj (op V.left))) (e : ToType ((overBase N).obj (op V))) :
    ofOverBase V (a • e) = (overScalarsHom R U).app (op V) a • ofOverBase V e := rfl

/-- The restriction maps of `overBase N` are those of `N`. -/
lemma ofOverBase_map {U : C} {N : SheafOfModules.{w} (R.over U)} {V W : Over U} (f : W ⟶ V)
    (e : ToType ((overBase N).obj (op V))) :
    ofOverBase W ((overBase N).map f.op e) = N.val.map f.op (ofOverBase V e) := rfl

end Bridge

/-! ### The sheafification-free finite type condition is unaffected -/

section Generates

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {U : C}

/-- Local generation of a sheaf of modules on the slice site by a finite family of sections is
unaffected by respelling the scalars in the base. -/
lemma generatesLocally_overBase {N : SheafOfModules.{u} (R.over U)} {V : Over U} {K : Type*}
    [Fintype K] (t : K → ToType (N.val.obj (op V))) :
    GeneratesLocally (J.over U) (overBase N) (fun k => toOverBase V (t k))
      ↔ GeneratesLocally (J.over U) N.val t :=
  Iff.rfl

/-- Finite type in the sheafification-free sense is unaffected by respelling the scalars in the
base. -/
lemma isFiniteTypeSections_overBase (N : SheafOfModules.{u} (R.over U))
    [IsFiniteTypeSections (J.over U) N.val] :
    IsFiniteTypeSections (J.over U) (overBase N) :=
  ⟨IsFiniteTypeSections.exists_generators (J := J.over U) (M := N.val)⟩

/-- The converse of `Stacks.SheafOfModules.isFiniteTypeSections_overBase`. -/
lemma isFiniteTypeSections_of_overBase (N : SheafOfModules.{u} (R.over U))
    [IsFiniteTypeSections (J.over U) (overBase N)] :
    IsFiniteTypeSections (J.over U) N.val :=
  ⟨IsFiniteTypeSections.exists_generators (J := J.over U) (M := overBase N)⟩

end Generates

/-! ### Coordinates on a finite free sheaf of modules, over the base scalars -/

section Coords

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {U : C} [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {ι : Type u} [DecidableEq ι]

/-- **Taking coordinates in the base is linear**, for the base scalars acting through
`Stacks.SheafOfModules.overScalarsHom`. -/
lemma coordsOver_smul (V : Over U) (a : ToType (R.obj.obj (op V.left)))
    (e : ToType ((free (R := R.over U) ι).val.obj (op V))) (i : ι) :
    coordsOver V ((overScalarsHom R U).app (op V) a • e) i = a * coordsOver V e i :=
  ((freeProj (S := R.over U) i).val.app (op V)).hom.map_smul _ _

/-- **The coordinates of a section of a finite free sheaf of modules on the slice site, as a
linear equivalence over the base scalars.** -/
noncomputable def coordsOverLinearEquiv [Fintype ι] (V : Over U) :
    ToType ((overBase (free (R := R.over U) ι)).obj (op V))
      ≃ₗ[ToType (R.obj.obj (op V.left))] (ι → ToType (R.obj.obj (op V.left))) where
  toFun e := coordsOver V (ofOverBase V e)
  map_add' e e' := funext fun i => coordsOver_add V (ofOverBase V e) (ofOverBase V e') i
  map_smul' a e := funext fun i => coordsOver_smul V a (ofOverBase V e) i
  invFun c := toOverBase V (ofCoordsOver V c)
  left_inv e :=
    (congrArg (toOverBase V) (ofCoordsOver_coordsOver V (ofOverBase V e))).trans
      (toOverBase_ofOverBase V e)
  right_inv c := coordsOver_ofCoordsOver V c

/-- `coordsOverLinearEquiv V e` is the family of coordinates of `ofOverBase V e`. -/
@[simp]
lemma coordsOverLinearEquiv_apply [Fintype ι] (V : Over U)
    (e : ToType ((overBase (free (R := R.over U) ι)).obj (op V))) :
    coordsOverLinearEquiv (R := R) (ι := ι) V e = coordsOver V (ofOverBase V e) := rfl

end Coords

/-! ### The relations presheaf is the kernel of the map out of the free sheaf, respelled -/

section Relations

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  (M : SheafOfModules.{u} R) {U : C} [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] {I : Type u} [Fintype I]
  (s : I → ToType (M.val.obj (op U)))

section

variable [DecidableEq I]

/-- The coordinates of a section of `kernel (freeToOver M s)` over `V`, as a linear map to the
submodule of relations among the restricted family. -/
noncomputable def kernelCoordsOver (V : Over U) :
    ToType ((overBase (kernel (freeToOver M s))).obj (op V)) →ₗ[ToType (R.obj.obj (op V.left))]
      relationsSubmodule M.val s V where
  toFun w := ⟨coordsOver V ((kernel.ι (freeToOver M s)).val.app (op V) (ofOverBase V w)),
    coordsOver_kernel_mem_relationsSubmodule M s V _⟩
  map_add' w w' := Subtype.ext (funext fun i =>
    (congrArg (fun z => coordsOver V z i)
      (map_add ((kernel.ι (freeToOver M s)).val.app (op V)).hom (ofOverBase V w)
        (ofOverBase V w'))).trans (coordsOver_add V _ _ i))
  map_smul' a w := Subtype.ext (funext fun i =>
    (congrArg (fun z => coordsOver V z i)
      (((kernel.ι (freeToOver M s)).val.app (op V)).hom.map_smul
        ((overScalarsHom R U).app (op V) a) (ofOverBase V w))).trans
      (coordsOver_smul V a _ i))

/-- The underlying family of `kernelCoordsOver M s V w` is the family of coordinates of the image
of `w` in the free sheaf of modules. -/
@[simp]
lemma kernelCoordsOver_apply_coe (V : Over U)
    (w : ToType ((overBase (kernel (freeToOver M s))).obj (op V))) :
    (kernelCoordsOver M s V w : I → ToType (R.obj.obj (op V.left)))
      = coordsOver V ((kernel.ι (freeToOver M s)).val.app (op V) (ofOverBase V w)) := rfl

/-- `Stacks.SheafOfModules.bijOn_coordsOver_kernel`, read as bijectivity of the linear map
`kernelCoordsOver`. -/
lemma bijective_kernelCoordsOver (V : Over U) :
    Function.Bijective (kernelCoordsOver M s V) := by
  obtain ⟨-, hinj, hsurj⟩ := bijOn_coordsOver_kernel M s V
  refine ⟨fun w w' hww => ?_, fun a => ?_⟩
  · exact (congrArg (toOverBase V)
      (hinj (Set.mem_univ _) (Set.mem_univ _) (Subtype.ext_iff.mp hww)) :
        toOverBase V (ofOverBase V w) = toOverBase V (ofOverBase V w'))
  · obtain ⟨z, -, hz⟩ := hsurj a.property
    exact ⟨toOverBase V z, Subtype.ext hz⟩

/-- **The coordinates of a section of the kernel, as a linear equivalence onto the relations.**
This is `Stacks.SheafOfModules.bijOn_coordsOver_kernel` as an isomorphism of modules over the
base scalars. -/
noncomputable def kernelCoordsOverLinearEquiv (V : Over U) :
    ToType ((overBase (kernel (freeToOver M s))).obj (op V)) ≃ₗ[ToType (R.obj.obj (op V.left))]
      relationsSubmodule M.val s V :=
  LinearEquiv.ofBijective (kernelCoordsOver M s V) (bijective_kernelCoordsOver M s V)

/-- **The presheaf of relations among a finite family of sections of `M` over `U` is the kernel
of the map out of the free sheaf of modules, with its scalars respelled in the base.**

The elementwise content is `Stacks.SheafOfModules.bijOn_coordsOver_kernel`; what is added is
the linearity, which is `kernelCoordsOver`, and the naturality, which is
`Stacks.SheafOfModules.coordsOver_map` after the naturality of the kernel inclusion. -/
noncomputable def relationsPresheafIso :
    overBase (kernel (freeToOver M s)) ≅ relationsPresheaf M.val s :=
  PresheafOfModules.isoMk (fun V => (kernelCoordsOverLinearEquiv M s V.unop).toModuleIso)
    (fun {X Y} f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun w => Subtype.ext (funext fun i => ?_))
      change coordsOver (unop Y) ((kernel.ι (freeToOver M s)).val.app Y
          ((kernel (freeToOver M s)).val.map f (ofOverBase (unop X) w))) i
        = R.obj.map f.unop.left.op (coordsOver (unop X)
            ((kernel.ι (freeToOver M s)).val.app X (ofOverBase (unop X) w)) i)
      refine Eq.trans (congrArg (fun z => coordsOver (unop Y) z i)
        (PresheafOfModules.naturality_apply (kernel.ι (freeToOver M s)).val f
          (ofOverBase (unop X) w))) ?_
      exact coordsOver_map f.unop _ i)

end

/-- **The sectionwise relations among a finite family of sections are of finite type as soon as
the kernel of the map out of the free sheaf of modules is.** This is the sectionwise form of the
second half of the coherence condition of Tag 03DL, deduced from the categorical form through
`Stacks.SheafOfModules.relationsPresheafIso`. -/
theorem isFiniteTypeSections_relationsPresheaf
    [∀ X : Over U, HasSheafify ((J.over U).over X) AddCommGrpCat.{u}]
    [∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(kernel (freeToOver M s)).IsFiniteType] :
    IsFiniteTypeSections (J.over U) (relationsPresheaf M.val s) := by
  classical
  have := isFiniteTypeSections_of_isFiniteType (kernel (freeToOver M s))
  have := isFiniteTypeSections_overBase (kernel (freeToOver M s))
  exact isFiniteTypeSections_of_iso (J := J.over U) (relationsPresheafIso M s)

/-- **Conversely, the kernel of the map out of the free sheaf of modules is of finite type as
soon as the sectionwise relations are.** Together with
`Stacks.SheafOfModules.isFiniteTypeSections_relationsPresheaf` this says that the two forms of
the second half of the coherence condition of Tag 03DL agree. -/
theorem isFiniteType_kernel_of_isFiniteTypeSections
    [∀ X : Over U, HasSheafify ((J.over U).over X) AddCommGrpCat.{u}]
    [∀ X : Over U, ((J.over U).over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [IsFiniteTypeSections (J.over U) (relationsPresheaf M.val s)] :
    (kernel (freeToOver M s)).IsFiniteType := by
  classical
  have := isFiniteTypeSections_of_iso (J := J.over U) (relationsPresheafIso M s).symm
  have := isFiniteTypeSections_of_overBase (kernel (freeToOver M s))
  exact isFiniteType_of_isFiniteTypeSections (kernel (freeToOver M s))

end Relations

end Stacks.SheafOfModules

end
