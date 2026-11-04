module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Rank-one endomorphisms, `F ⊗ F^∨ ≅ SheafHom(F, F)`, and the canonical coevaluation

Let `𝒪` be a presheaf of commutative rings on a site `(C, J)` whose underlying presheaf of rings
is a sheaf, and let `F` be a sheaf of `𝒪`-modules. The *rank-one operator* attached to a section
`f` of `F` over `U` and a section `lam` of the dual `F^∨ = SheafHom(F, 𝒪)` over `U` is the
endomorphism `g ↦ lam(g) • f` of `F|_U`. Assembling these over all objects gives a canonical
morphism of sheaves of `𝒪`-modules

  `F ⊗_𝒪 F^∨ ⟶ SheafHom(F, F)`.

[Stacks, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV) asserts that this morphism is an
isomorphism when `F` is locally a direct summand of a finite free sheaf of modules, and uses the
inverse image of the identity endomorphism as the *coevaluation* `𝒪 ⟶ F ⊗ F^∨` which, together
with the evaluation pairing of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom`, exhibits `F^∨` as a left dual of `F`.
This file builds the morphism, proves it is an isomorphism, constructs the coevaluation, and —
the point of the file — **computes the coevaluation on local sections**.

## Main definitions

* `Stacks.SheafOfModules.rankOneSection` is the rank-one operator `g ↦ lam(g) • f`, as a section
  of `SheafHom(F, F)` over `U`.
* `Stacks.SheafOfModules.endPresheaf` assembles the rank-one operators into a morphism
  `F ⊗ F^∨ ⟶ SheafHom(F, F)` out of the *pointwise* tensor product of presheaves of modules.
* `Stacks.SheafOfModules.FiniteDualBasis` is a finite dual basis for `F` over an object `U`: a
  finite family `e` of sections of `F` over `U` together with a family `lam` of sections of `F^∨`
  over `U` such that on every object `V` of the slice site `C/U` the restrictions of `e` generate
  with `lam` as coordinates. This is the `n`-ary form of
  `Stacks.SheafOfModules.DualBasisOne`, and it is what a retract of `F|_U` onto a finite free
  sheaf of modules provides.
* `Stacks.SheafOfModules.tensorDualToEndomorphism` is the induced morphism of *sheaves* of
  modules `F ⊗_𝒪 F^∨ ⟶ SheafHom(F, F)`, the tensor product of sheaves of modules being the
  sheafification of the pointwise one (Tag 05NA).
* `Stacks.SheafOfModules.toTensorSheafSection` is a local pure tensor, viewed in the tensor
  product sheaf through the sheafification unit.
* `Stacks.SheafOfModules.identityEndomorphism` is the global section of `SheafHom(F, F)` whose
  value over every object is the identity.
* `Stacks.SheafOfModules.coevaluation` is the canonical coevaluation `𝒪 ⟶ F ⊗ F^∨`.

## Main results

* `Stacks.SheafOfModules.tensorDualToEndomorphism_toTensorSheafSection`: **the canonical
  morphism sends the local pure tensor `f ⊗ lam` to the rank-one operator `g ↦ lam(g) • f`.**
  This pins the morphism down on sections, which is what makes the isomorphism below a
  statement about a *named* map rather than an existence claim.
* `Stacks.SheafOfModules.bijective_endPresheaf_app_of_finiteDualBasis`: a finite dual basis over
  `U` makes the rank-one map bijective on sections over `U`.
* `Stacks.SheafOfModules.isLocallyInjective_endPresheaf` and
  `isLocallySurjective_endPresheaf`: finite dual bases on a family covering the final object make
  the rank-one map locally bijective, hence inverted by sheafification
  (`isIso_sheafify_map_endPresheaf`).
* `Stacks.SheafOfModules.isIso_tensorDualToEndomorphism`: **`F ⊗ F^∨ ⟶ SheafHom(F, F)` is an
  isomorphism** when `F` has finite dual bases on a covering family.
* `Stacks.SheafOfModules.coevaluation_comp_tensorDualToEndomorphism`: coevaluation composed with
  that isomorphism is the identity endomorphism.
* `Stacks.SheafOfModules.coevaluation_app_one_eq_sum_of_dualBasis`: **the local formula for the
  coevaluation.** Over an object `U` carrying a finite dual basis `(e i, lam i)`, the value of
  the coevaluation at the unit section is `∑ i, e i ⊗ lam i`. Since the left-hand side does not
  mention the dual basis, this also says that the sum is independent of the chosen dual basis,
  equivalently of the chosen finite-free retract.

## Implementation notes

**The rank-one operator is a composite, not a raw construction.** A section of `SheafHom(F, F)`
over `U` *is* a morphism `F|_U ⟶ F|_U` of presheaves of modules on the slice site `C/U`, and a
section of `F^∨` over `U` *is* a morphism `F|_U ⟶ 𝒪|_U`; so `rankOneSection f lam` is literally
`lam ≫ (multiplication by f)`, the second factor coming from `PresheafOfModules.unitHomEquiv`.
Building the operator instead as an anonymous-constructor `LinearMap` in each component fails:
`ModuleCat.ofHom` unfolds `restrFun` to `PresheafOfModules.pushforward₀` and then cannot
synthesize the module structure of the restricted presheaf, even though the same instance is
found when asked for directly. The composite route needs no instance at all, and the defining
formula `rankOneSection_app` comes out as `rfl`.

**One spelling per statement.** The scalars of a section of `SheafHom(F, G)` over `U` are spelled
`fRestr 𝒪 U a V` by Tag 03EM and `resRing V a` by `...Sheaf.SheafHom`; a restricted section of `F`
is spelled `((restrFun 𝒪 U).obj F.val).obj V` on one side of the internal hom and
`F.val.obj (op V.left)` on the other. These are definitionally equal and are *not*
interchangeable for `rw` or for instance synthesis. Each statement here is therefore written in
the pinned spellings `resSection`, `resRing`, `dualApp`, `dualEval` of `...Sheaf.SheafHom`, and
the boundary is crossed only by `Eq.trans`/`congrArg`/`exact`, which tolerate defeq. The
`rfl`-lemmas `fRestr_eq_resRing`, `internalHom_add_app_apply`, `dualApp_add`,
`dualApp_smul_left`, `endEval_zero` and `endEval_add` exist exactly to make that crossing
explicit one place at a time.

**Universes.** The site is `C : Type u` with `Category.{v} C` and the module universe is
`max u v`. Two separate things are going on, and only the first is a typing constraint.

*What typing forces.* A section of `SheafHom(F, G)` over `U` is a morphism of presheaves of
modules on the slice site `Over U`, which lives in `Type (max u v)`; such a morphism is a family
indexed by the objects of that site, so for `F G : PresheafOfModules.{t}` the internal hom of
Tag 03EM lands in `PresheafOfModules.{max u v t}`. For `SheafHom(F, G)` to be an object of the
*same* category as `F` and `G` — which it must be, in order to form `F ⊗ F^∨` and to state
`F ⊗ F^∨ ⟶ SheafHom(F, F)` at all — one therefore needs `max u v ≤ t`. Indeed, at a free
module universe `t` the statement `internalHom 𝒪 F G : PresheafOfModules.{t} (Oforget 𝒪)` is
rejected with `failed to solve universe constraint t =?= max (max u v) t`, while the same
statement at `max u v t` elaborates. This is universe-lesson **case 2**: the module universe
indexes something whose target universe is computed from it.

*What is a choice.* Since `max u v t` elaborates, that form is strictly more general than
`max u v`, so the collapse to `max u v` is not forced by typing. It is forced by *reuse*: the
carriers `Stacks.SheafOfModules.dualSheaf` and `Stacks.SheafOfModules.evaluation` of
`...Sheaf.SheafHom` are stated at `max u v`, and Tag 0FNV's left-dual statement pairs the
coevaluation built here against that evaluation, so the two must share a module universe. A
`max u v t` version of this file would not compose with that evaluation and would be an
orphan. Nothing is narrowed relative to the files this one imports.

The index universe of `FiniteDualBasis` is left free: it is only summed over, never used to
compute a target universe, which is universe-lesson case 1.

**Hypotheses.** The rank-one operator, `endPresheaf` and `FiniteDualBasis` need no sheafification
hypothesis at all. The sheaf-level half assumes `J.WEqualsLocallyBijective AddCommGrpCat` and
`HasWeakSheafify J AddCommGrpCat`, which is what Tag 05NA's sheafification functor and the
locally-bijective criterion need; `J.HasSheafCompose (forget₂ CommRingCat RingCat)` is *not*
needed, since the structure presheaf of rings is already a sheaf by hypothesis. The local
hypothesis of Tag 0FNV — "locally a direct summand of a finite free sheaf of modules" — enters
as finite dual bases on a `J.CoversTop` family, which is the section-level form of that
condition and is what `Stacks.SheafOfModules.nonempty_retract_free_of_localDualBasis` converts
back into a retract.

**What is not here.** The construction turning a retract `i ≫ p = 𝟙` of `F|_U` onto
`SheafOfModules.free (Fin n)` into a `FiniteDualBasis` is not in this file. Its mathematical
input is the dual-basis identity for the free sheaf of modules, which is already available as
`Stacks.SheafOfModules.id_free_eq_sum`, `freeMk_freeCoord` and `app_eq_sum_smul_freeCoord`; what
is missing is only the bookkeeping across the `(F.over U).val` versus `(restrFun 𝒪 U).obj F.val`
boundary.

**That boundary is not a second one**, as this passage previously implied: it is the same
slice/base scalar boundary `...Sheaf.StalkFreeCover` records, and the two objects are *literally
equal* — `(restrFun 𝒪 U).obj F.val = overBase (F.over U)` holds by `rfl`, because
`ORestr 𝒪 U` is already the base spelling. So the bookkeeping is a change of scalars along the
identity, supplied by
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceScalarRestriction`. Note also that
`freeToOver_app_ofCoordsOver` already delivers the generation identity with scalars in
`R(V.left)` acting on `M.val.obj (op V.left)`, so the `span` field may need less than the note
above suggests. That has not been verified, and should not be recorded as closed until it is.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY) — the same example for a
  ringed site; the construction here is already at that generality.
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM) — the internal hom.
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA) — the tensor product
  sheaf as a sheafification.
* [Stacks Project, Tag 0FNZ](https://stacks.math.columbia.edu/tag/0FNZ) — the converse: an exact
  pairing makes `F` locally a finite free summand.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe v u

namespace Stacks.SheafOfModules

section RankOne

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  {F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

attribute [local instance] commRingStructureSheafObj moduleStructureSheafObj

/-- The section of `F|_U` on the slice site `C/U` determined by a section `f` of `F` over `U`:
its value at an object `V` of `C/U` is the restriction of `f`. -/
noncomputable def restrSections {U : C} (f : F.val.obj (op U)) :
    ((restrFun 𝒪 U).obj F.val).sections :=
  PresheafOfModules.sectionsMk (fun V => resSection V f) (by
    intro V W k
    change (F.val.map k.unop.left.op).hom ((F.val.map V.unop.hom.op).hom f) = resSection W f
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w k.unop]
    rfl)

/-- The value of `restrSections f` at an object `V` of `C/U` is the restriction of `f` to `V`. -/
@[simp]
lemma restrSections_eval {U : C} (f : F.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (restrSections 𝒪 h𝒪 f).eval V = resSection V f := rfl

/-- **Multiplication by a section**: the `𝒪|_U`-linear map `𝒪|_U ⟶ F|_U` sending a section `c`
of the structure sheaf to `c • f|_U`. -/
noncomputable def mulRestrSection {U : C} (f : F.val.obj (op U)) :
    (restrFun 𝒪 U).obj (SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)).val ⟶
      (restrFun 𝒪 U).obj F.val :=
  ((restrFun 𝒪 U).obj F.val).unitHomEquiv.symm (restrSections 𝒪 h𝒪 f)

/-- **The rank-one endomorphism `g ↦ lam(g) • f`** of `F|_U`, as a section of `SheafHom(F, F)`
over `U`.

A section of `SheafHom(F, F)` over `U` *is* a morphism `F|_U ⟶ F|_U` of presheaves of modules
on the slice site `C/U`, and a section of the dual `F^∨` over `U` *is* a morphism
`F|_U ⟶ 𝒪|_U`; so the rank-one operator is literally the composite of `lam` with
multiplication by `f`, and no raw construction is needed. -/
noncomputable def rankOneSection {U : C} (f : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    (sheafHom 𝒪 h𝒪 F F).val.obj (op U) :=
  lam ≫ mulRestrSection 𝒪 h𝒪 f

/-- **The defining formula for the rank-one operator**, read off at an object `V` of the slice
site `C/U`: it sends a section `g` of `F` over `V.left` to `lam(g) • f|_V`. -/
lemma rankOneSection_app {U : C} (f : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : F.val.obj (op V.unop.left)) :
    ((rankOneSection 𝒪 h𝒪 f lam).app V).hom g = dualApp lam V g • resSection V f := rfl

/-- Sections of the dual are added componentwise. -/
lemma dualApp_add {U : C} (lam mu : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : F.val.obj (op V.unop.left)) :
    dualApp (lam + mu) V g = dualApp lam V g + dualApp mu V g := rfl

/-- The structure sheaf acts on the dual componentwise, through restriction of the scalar. -/
lemma dualApp_smul_left {U : C} (a : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪).obj.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : F.val.obj (op V.unop.left)) :
    dualApp (a • lam) V g = resRing V a * dualApp lam V g := rfl

/-- Restriction is additive on sections. -/
lemma resSection_add {U : C} (x y : F.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    resSection (L := F) V (x + y) = resSection V x + resSection V y :=
  map_add (F.val.map V.unop.hom.op).hom x y

/-- Restriction is homogeneous on sections, through restriction of the scalar. -/
lemma resSection_smul {U : C} (a : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪).obj.obj (op U))
    (x : F.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    resSection (L := F) V (a • x) = resRing V a • resSection V x :=
  PresheafOfModules.map_smul F.val V.unop.hom.op a x

/-- Two sections of `SheafHom(F, G)` over `U` with the same components agree. -/
lemma internalHom_ext {U : C} {G : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (α β : (sheafHom 𝒪 h𝒪 F G).val.obj (op U))
    (h : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)),
      (α.app V).hom g = (β.app V).hom g) : α = β :=
  PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext (h V))

/-- Sections of `SheafHom(F, G)` are added componentwise. -/
lemma internalHom_add_app_apply {U : C}
    {G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (α β : (sheafHom 𝒪 h𝒪 F G).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : F.val.obj (op V.unop.left)) :
    ((α + β).app V).hom g = (α.app V).hom g + (β.app V).hom g := rfl

/-- The restriction of a scalar used by the module structure of `SheafHom(F, G)` is the
restriction map of the structure sheaf. -/
lemma fRestr_eq_resRing {U : C} (a : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
  h𝒪).obj.obj (op U))
    (V : (Over U)ᵒᵖ) : fRestr 𝒪 U a V = resRing (𝒪 := 𝒪) (h𝒪 := h𝒪) V a := rfl

/-- The rank-one operator is additive in the section. -/
lemma rankOneSection_add_left {U : C} (f f' : F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    rankOneSection 𝒪 h𝒪 (f + f') lam =
      rankOneSection 𝒪 h𝒪 f lam + rankOneSection 𝒪 h𝒪 f' lam :=
  internalHom_ext 𝒪 h𝒪 _ _ fun V g =>
    (rankOneSection_app 𝒪 h𝒪 (f + f') lam V g).trans
      (((congrArg (dualApp lam V g • ·) (resSection_add 𝒪 h𝒪 f f' V)).trans
        (smul_add (dualApp lam V g) (resSection V f) (resSection V f'))).trans
      ((internalHom_add_app_apply 𝒪 h𝒪 (rankOneSection 𝒪 h𝒪 f lam)
        (rankOneSection 𝒪 h𝒪 f' lam) V g).symm))

/-- Two restricted scalars commute in their action on a section, because the structure sheaf
is a sheaf of commutative rings. -/
lemma smul_comm_section {U : C} (V : (Over U)ᵒᵖ)
    (c d : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
      V.unop.left))
    (x : F.val.obj (op V.unop.left)) : c • d • x = d • c • x := by
  rw [smul_smul, smul_smul, mul_comm]

/-- The rank-one operator is homogeneous in the section. -/
lemma rankOneSection_smul_left {U : C}
    (a : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) (f :
      F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    rankOneSection 𝒪 h𝒪 (a • f) lam = a • rankOneSection 𝒪 h𝒪 f lam := by
  refine internalHom_ext 𝒪 h𝒪 _ _ fun V g => ?_
  refine Eq.trans ?_ (internalHom_smul_app_apply 𝒪 F.val F.val U a
    (rankOneSection 𝒪 h𝒪 f lam) V g).symm
  rw [fRestr_eq_resRing, rankOneSection_app, rankOneSection_app, resSection_smul]
  exact smul_comm_section 𝒪 h𝒪 V _ _ _

/-- The rank-one operator is additive in the functional. -/
lemma rankOneSection_add_right {U : C} (f : F.val.obj (op U))
    (lam mu : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    rankOneSection 𝒪 h𝒪 f (lam + mu) =
      rankOneSection 𝒪 h𝒪 f lam + rankOneSection 𝒪 h𝒪 f mu :=
  internalHom_ext 𝒪 h𝒪 _ _ fun V g =>
    (rankOneSection_app 𝒪 h𝒪 f (lam + mu) V g).trans
      (((congrArg (· • resSection V f) (dualApp_add 𝒪 h𝒪 lam mu V g)).trans
        (add_smul (dualApp lam V g) (dualApp mu V g) (resSection V f))).trans
      ((internalHom_add_app_apply 𝒪 h𝒪 (rankOneSection 𝒪 h𝒪 f lam)
        (rankOneSection 𝒪 h𝒪 f mu) V g).symm))

/-- The rank-one operator is homogeneous in the functional. -/
lemma rankOneSection_smul_right {U : C}
    (a : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) (f :
      F.val.obj (op U))
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    rankOneSection 𝒪 h𝒪 f (a • lam) = a • rankOneSection 𝒪 h𝒪 f lam := by
  refine internalHom_ext 𝒪 h𝒪 _ _ fun V g => ?_
  refine Eq.trans ?_ (internalHom_smul_app_apply 𝒪 F.val F.val U a
    (rankOneSection 𝒪 h𝒪 f lam) V g).symm
  rw [fRestr_eq_resRing, rankOneSection_app, rankOneSection_app, dualApp_smul_left, mul_smul]
  rfl

/-- **The rank-one operator is natural**: restricting the section and the functional from `X` to
`Y` and then forming the rank-one operator is restricting the rank-one operator. -/
lemma rankOneSection_naturality {X Y : Cᵒᵖ} (i : X ⟶ Y) (f : F.val.obj X)
    (lam : (dualSheaf 𝒪 h𝒪 F).val.obj X) :
    rankOneSection 𝒪 h𝒪 (U := Y.unop) ((F.val.map i).hom f)
        (ConcreteCategory.hom ((dualSheaf 𝒪 h𝒪 F).val.map i) lam) =
      ConcreteCategory.hom ((sheafHom 𝒪 h𝒪 F F).val.map i)
        (rankOneSection 𝒪 h𝒪 (U := X.unop) f lam) := by
  refine internalHom_ext 𝒪 h𝒪 _ _ fun V g => ?_
  refine (rankOneSection_app 𝒪 h𝒪 _ _ V g).trans ?_
  refine Eq.trans ?_ (internalHom_map_app_apply 𝒪 F.val F.val i
    (rankOneSection 𝒪 h𝒪 (U := X.unop) f lam) V g).symm
  refine Eq.trans ?_ (rankOneSection_app 𝒪 h𝒪 (U := X.unop) f lam
    (op ((Over.map i.unop).obj V.unop)) g).symm
  exact congrArg (@SMul.smul
    ((TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op V.unop.left))
    (F.val.obj (op V.unop.left)) inferInstance
    (dualApp lam (op ((Over.map i.unop).obj V.unop)) g))
    (resSection_map 𝒪 h𝒪 (L := F) i.unop V f)

attribute [local instance] monoidalCategoryPresheafOfModules

/-- **The rank-one map `F ⊗ F^∨ ⟶ SheafHom(F, F)`**, as a morphism out of the pointwise tensor
product of presheaves of modules. On sections it is `f ⊗ lam ↦ (g ↦ lam(g) • f)`. -/
noncomputable def endPresheaf (F : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    F.val ⊗ (dualSheaf 𝒪 h𝒪 F).val ⟶ (sheafHom 𝒪 h𝒪 F F).val := by
  refine PresheafOfModules.Hom.mk (fun X ↦ ?_) ?_
  · exact ModuleCat.MonoidalCategory.tensorLift
      (fun (f : F.val.obj X) (lam : (dualSheaf 𝒪 h𝒪 F).val.obj X) ↦
        rankOneSection 𝒪 h𝒪 (U := X.unop) f lam)
      (fun f f' lam => rankOneSection_add_left 𝒪 h𝒪 f f' lam)
      (fun a f lam => rankOneSection_smul_left 𝒪 h𝒪 a f lam)
      (fun f lam mu => rankOneSection_add_right 𝒪 h𝒪 f lam mu)
      (fun a f lam => rankOneSection_smul_right 𝒪 h𝒪 a f lam)
  · intro X Y i
    exact ModuleCat.MonoidalCategory.tensor_ext fun f lam =>
      rankOneSection_naturality 𝒪 h𝒪 i f lam

/-- The rank-one map sends the pure tensor `f ⊗ lam` to the rank-one operator
`g ↦ lam(g) • f`. -/
@[simp]
lemma endPresheaf_tmul (F : SheafOfModules.{max u v}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (U : Cᵒᵖ) (f : F.val.obj U) (lam : (dualSheaf 𝒪 h𝒪 F).val.obj U) :
    ((endPresheaf 𝒪 h𝒪 F).app U).hom
        (f ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] lam) =
      rankOneSection 𝒪 h𝒪 (U := U.unop) f lam := rfl

/-- The value of a section of `SheafHom(F, F)` over `U` on a section of `F` over `U`. -/
noncomputable def endEval {U : C} (a : (sheafHom 𝒪 h𝒪 F F).val.obj (op U))
    (x : F.val.obj (op U)) : F.val.obj (op U) :=
  evalSection 𝒪 F.val F.val (op U) a x

/-- The zero section of `SheafHom(F, F)` evaluates to zero on every section of `F`. -/
lemma endEval_zero {U : C} (x : F.val.obj (op U)) :
    endEval 𝒪 h𝒪 (0 : (sheafHom 𝒪 h𝒪 F F).val.obj (op U)) x = 0 := rfl

/-- Evaluation of sections of `SheafHom(F, F)` is additive in the endomorphism. -/
lemma endEval_add {U : C} (a a' : (sheafHom 𝒪 h𝒪 F F).val.obj (op U))
    (x : F.val.obj (op U)) :
    endEval 𝒪 h𝒪 (a + a') x = endEval 𝒪 h𝒪 a x + endEval 𝒪 h𝒪 a' x := rfl

/-- Components of a finite sum of sections of `SheafHom(F, G)`. -/
lemma internalHom_sum_app_apply {U : C}
    {G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
      {ι : Type*}
    (s : Finset ι) (a : ι → (sheafHom 𝒪 h𝒪 F G).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (g : F.val.obj (op V.unop.left)) :
    ((∑ i ∈ s, a i).app V).hom g = ∑ i ∈ s, ((a i).app V).hom g := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, internalHom_add_app_apply, ih]

variable (F)

/-- **A finite dual basis for `F` over an object `U` of the site.**

`e` is a finite family of sections of `F` over `U` and `lam` the dual family of sections of
`F^∨`; `span` says that on every object `V` of the slice site `C/U` the restrictions of `e`
generate, with `lam` as the coordinates. This is the `n`-ary form of
`Stacks.SheafOfModules.DualBasisOne`, and it is exactly the data that a retract of `F|_U` onto a
finite free sheaf of modules provides. -/
structure FiniteDualBasis (U : C) (I : Type*) [Fintype I] where
  /-- The basis sections of `F` over `U`. -/
  e : I → F.val.obj (op U)
  /-- The dual coordinates, sections of `F^∨` over `U`. -/
  lam : I → (dualSheaf 𝒪 h𝒪 F).val.obj (op U)
  /-- The dual-basis identity: on every object `V` of `C/U` the restrictions of `e` generate,
  with the components of `lam` as coordinates. -/
  span (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) :
    ∑ i, dualApp (lam i) V g • resSection V (e i) = g

variable {F}

namespace FiniteDualBasis

variable {U : C} {I : Type*} [Fintype I]

/-- `span` read off at the terminal object of `C/U`: a section of `F` over `U` is the
combination of the basis sections with its own coordinates. -/
lemma coord_smul (b : FiniteDualBasis 𝒪 h𝒪 F U I) (g : F.val.obj (op U)) :
    ∑ i, dualEval (b.lam i) g • b.e i = g := by
  refine Eq.trans ?_ (b.span (op (Over.mk (𝟙 U))) g)
  exact Finset.sum_congr rfl fun i _ =>
    (congrArg (dualEval (b.lam i) g • ·) (resSection_self (b.e i)).symm)

/-- A family of sections of `SheafHom(F, G)` whose components are those of `a` on the terms of
the dual-basis expansion sums to `a`. -/
private lemma sum_eq_of_span {G : SheafOfModules.{max u v}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}
    (b : FiniteDualBasis 𝒪 h𝒪 F U I) (a : (sheafHom 𝒪 h𝒪 F G).val.obj (op U))
    (σ : I → (sheafHom 𝒪 h𝒪 F G).val.obj (op U))
    (h : ∀ (V : (Over U)ᵒᵖ) (g : F.val.obj (op V.unop.left)) (i : I),
      ((σ i).app V).hom g = (a.app V).hom (dualApp (b.lam i) V g • resSection V (b.e i))) :
    ∑ i, σ i = a := by
  refine internalHom_ext 𝒪 h𝒪 _ _ fun V g => ?_
  refine (internalHom_sum_app_apply 𝒪 h𝒪 Finset.univ σ V g).trans ?_
  refine Eq.trans ?_ (congrArg (a.app V).hom (b.span V g))
  refine Eq.trans ?_ (map_sum (a.app V).hom _ Finset.univ).symm
  exact Finset.sum_congr rfl fun i _ => h V g i

/-- **A finite dual basis reproduces every section of the dual.** A section `l` of `F^∨` over
`U` is the combination of the dual basis with the values of `l` on the basis sections as
coefficients. -/
lemma eq_sum_smul_lam (b : FiniteDualBasis 𝒪 h𝒪 F U I)
    (l : (dualSheaf 𝒪 h𝒪 F).val.obj (op U)) :
    ∑ i, dualEval l (b.e i) • b.lam i = l := by
  refine sum_eq_of_span 𝒪 h𝒪 b l _ fun V g i => ?_
  refine Eq.trans ?_ (dualApp_smul l V (dualApp (b.lam i) V g) (resSection V (b.e i))).symm
  refine (dualApp_smul_left 𝒪 h𝒪 (dualEval l (b.e i)) (b.lam i) V g).trans ?_
  refine Eq.trans (congrArg (· * dualApp (b.lam i) V g)
    (dualApp_resSection l V (b.e i)).symm) ?_
  exact mul_comm _ _

/-- A finite dual basis restricts along any morphism of the site: being a summand of a finite
free sheaf of modules is stable under restriction. -/
noncomputable def restrict (b : FiniteDualBasis 𝒪 h𝒪 F U I) {W : C} (k : W ⟶ U) :
    FiniteDualBasis 𝒪 h𝒪 F W I where
  e i := (F.val.map k.op).hom (b.e i)
  lam i := ConcreteCategory.hom ((dualSheaf 𝒪 h𝒪 F).val.map k.op) (b.lam i)
  span V g := by
    refine Eq.trans ?_ (b.span (op ((Over.map k).obj V.unop)) g)
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg (@SMul.smul
      ((TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op V.unop.left))
      (F.val.obj (op V.unop.left)) inferInstance
      (dualApp (b.lam i) (op ((Over.map k).obj V.unop)) g))
      (resSection_map 𝒪 h𝒪 k V (b.e i))

/-- The rank-one map sends `∑ i, a (e i) ⊗ lam i` back to the endomorphism `a`. -/
private lemma endPresheaf_app_sum_endEval_tmul (b : FiniteDualBasis 𝒪 h𝒪 F U I)
    (a : (sheafHom 𝒪 h𝒪 F F).val.obj (op U)) :
    ((endPresheaf 𝒪 h𝒪 F).app (op U)).hom
        (∑ i, endEval 𝒪 h𝒪 a (b.e i)
          ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj (op U)]
          b.lam i) = a := by
  refine (map_sum ((endPresheaf 𝒪 h𝒪 F).app (op U)).hom _ Finset.univ).trans ?_
  refine sum_eq_of_span 𝒪 h𝒪 b a _ fun V g i => ?_
  refine (rankOneSection_app 𝒪 h𝒪 (endEval 𝒪 h𝒪 a (b.e i)) (b.lam i) V g).trans ?_
  refine Eq.trans ?_ ((a.app V).hom.map_smul _ _).symm
  exact congrArg (dualApp (b.lam i) V g • ·)
    (internalHom_app_restrict 𝒪 F.val F.val U a V (b.e i)).symm

/-- Every tensor `t` is recovered from its image `a` under the rank-one map as
`∑ i, a (e i) ⊗ lam i`. -/
private lemma sum_endEval_endPresheaf_app_tmul (b : FiniteDualBasis 𝒪 h𝒪 F U I)
    (t : (F.val ⊗ (dualSheaf 𝒪 h𝒪 F).val).obj (op U)) :
    (∑ i, endEval 𝒪 h𝒪 (((endPresheaf 𝒪 h𝒪 F).app (op U)).hom t) (b.e i)
      ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam i)
        = t := by
  induction t using TensorProduct.induction_on with
  | zero =>
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) Finset.sum_const_zero
    refine Eq.trans (congrArg
      (· ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam
        i)
      ((congrArg (fun z => endEval 𝒪 h𝒪 z (b.e i))
          (map_zero ((endPresheaf 𝒪 h𝒪 F).app (op U)).hom)).trans
        (endEval_zero 𝒪 h𝒪 (b.e i)))) ?_
    exact TensorProduct.zero_tmul _ _
  | tmul f l =>
    have hev : ∀ i, endEval 𝒪 h𝒪 (((endPresheaf 𝒪 h𝒪 F).app (op U)).hom
        (f ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj (op U)] l))
          (b.e i) =
          dualEval l (b.e i) • f := by
      intro i
      refine (rankOneSection_app 𝒪 h𝒪 f l (op (Over.mk (𝟙 U))) (b.e i)).trans ?_
      rw [dualApp_self, resSection_self]
    have hstep : ∀ i : I,
        endEval 𝒪 h𝒪 (((endPresheaf 𝒪 h𝒪 F).app (op U)).hom
              (f ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
                U)] l)) (b.e i)
            ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)]
              b.lam i =
          f ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)]
            (dualEval l (b.e i) • b.lam i) := fun i =>
      (congrArg (· ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op
        U)] b.lam i)
        (hev i)).trans (TensorProduct.smul_tmul _ _ _)
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hstep i) ?_
    refine Eq.trans (TensorProduct.tmul_sum f Finset.univ
      (fun i => dualEval l (b.e i) • b.lam i)).symm ?_
    exact congrArg (f ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj
      (op U)] ·)
      (b.eq_sum_smul_lam 𝒪 h𝒪 l)
  | add t s ht hs =>
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (Finset.sum_add_distrib.trans (congrArg₂ (· + ·) ht hs))
    refine Eq.trans (congrArg
      (· ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)] b.lam
        i)
      ((congrArg (fun z => endEval 𝒪 h𝒪 z (b.e i))
          (map_add ((endPresheaf 𝒪 h𝒪 F).app (op U)).hom t s)).trans
        (endEval_add 𝒪 h𝒪 _ _ (b.e i)))) ?_
    exact TensorProduct.add_tmul _ _ _

end FiniteDualBasis

/-- **A finite dual basis makes the rank-one map bijective on sections over `U`.**

Surjectivity: an endomorphism `a` of `F|_U` is the image of `∑ i, a(e i) ⊗ lam i`, because the
dual-basis identity turns `∑ i, lam i (g) • a(e i)` into `a(g)`. Injectivity: the same formula is
a two-sided inverse, computed on a pure tensor `f ⊗ l` by
`Stacks.SheafOfModules.FiniteDualBasis.eq_sum_smul_lam`. -/
theorem bijective_endPresheaf_app_of_finiteDualBasis {U : C} {I : Type*} [Fintype I]
    (b : FiniteDualBasis 𝒪 h𝒪 F U I) :
    Function.Bijective ((endPresheaf 𝒪 h𝒪 F).app (op U)).hom := by
  refine ⟨fun t t' h => ?_, fun a => ⟨_, b.endPresheaf_app_sum_endEval_tmul 𝒪 h𝒪 a⟩⟩
  rw [← b.sum_endEval_endPresheaf_app_tmul 𝒪 h𝒪 t, ← b.sum_endEval_endPresheaf_app_tmul 𝒪 h𝒪 t',
    h]

/-! ### Local bijectivity of the rank-one map -/

/-- The rank-one map is locally injective when `F` has finite dual bases on a family covering
the final object. -/
theorem isLocallyInjective_endPresheaf {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)]
    (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k)) :
    PresheafOfModules.IsLocallyInjective J (endPresheaf 𝒪 h𝒪 F) := by
  constructor
  intro Z x y h
  refine J.superset_covering ?_ (hX Z.unop)
  rintro W p ⟨k, ⟨q⟩⟩
  have hbij := bijective_endPresheaf_app_of_finiteDualBasis 𝒪 h𝒪 ((b k).restrict 𝒪 h𝒪 q)
  have hn : ∀ t : (F.val ⊗ (dualSheaf 𝒪 h𝒪 F).val).obj Z,
      ((endPresheaf 𝒪 h𝒪 F).app (op W)).hom
          (((F.val ⊗ (dualSheaf 𝒪 h𝒪 F).val).map p.op).hom t) =
        ConcreteCategory.hom ((sheafHom 𝒪 h𝒪 F F).val.map p.op)
          (((endPresheaf 𝒪 h𝒪 F).app Z).hom t) :=
    fun t => PresheafOfModules.naturality_apply (endPresheaf 𝒪 h𝒪 F) p.op t
  exact hbij.injective <| (hn x).trans <|
    (congrArg (ConcreteCategory.hom ((sheafHom 𝒪 h𝒪 F F).val.map p.op)) h).trans (hn y).symm

/-- The rank-one map is locally surjective when `F` has finite dual bases on a family covering
the final object. -/
theorem isLocallySurjective_endPresheaf {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)]
    (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k)) :
    PresheafOfModules.IsLocallySurjective J (endPresheaf 𝒪 h𝒪 F) := by
  constructor
  intro Z s
  refine J.superset_covering ?_ (hX Z)
  rintro W p ⟨k, ⟨q⟩⟩
  exact (bijective_endPresheaf_app_of_finiteDualBasis 𝒪 h𝒪
    ((b k).restrict 𝒪 h𝒪 q)).surjective _

/-! ### The canonical coevaluation -/

/-- The global section of `SheafHom(F, F)` whose value over every object is the identity. -/
noncomputable def identitySections
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      :
    (sheafHom 𝒪 h𝒪 F F).val.sections :=
  PresheafOfModules.sectionsMk (fun U => 𝟙 ((restrFun 𝒪 U.unop).obj F.val)) (by
    intro U W i
    exact internalHom_ext 𝒪 h𝒪 _ _ fun V g =>
      internalHom_map_app_apply 𝒪 F.val F.val i (𝟙 ((restrFun 𝒪 U.unop).obj F.val)) V g)

/-- **The identity endomorphism as a global section of `SheafHom(F, F)`**: the morphism
`𝒪 ⟶ SheafHom(F, F)` whose value on every object is the identity of the restricted sheaf. -/
noncomputable def identityEndomorphism
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      :
    SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⟶ sheafHom
      𝒪 h𝒪 F F :=
  (sheafHom 𝒪 h𝒪 F F).unitHomEquiv.symm (identitySections 𝒪 h𝒪 F)

/-- The value of the identity endomorphism at the unit section over `U` is the identity of
`F|_U`. -/
lemma identityEndomorphism_app_one
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (U : C) :
    ((identityEndomorphism 𝒪 h𝒪 F).val.app (op U)).hom
        (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) =
      𝟙 ((restrFun 𝒪 U).obj F.val) :=
  (SheafOfModules.unitHomEquiv_apply_coe (sheafHom 𝒪 h𝒪 F F)
    ((sheafHom 𝒪 h𝒪 F F).unitHomEquiv.symm (identitySections 𝒪 h𝒪 F)) (op U)).symm.trans
      (congrArg (fun t : (sheafHom 𝒪 h𝒪 F F).val.sections => t.eval (op U))
        ((sheafHom 𝒪 h𝒪 F F).unitHomEquiv.apply_symm_apply (identitySections 𝒪 h𝒪 F)))

section Sheafification

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- **The canonical rank-one morphism `F ⊗ F^∨ ⟶ SheafHom(F, F)`** of sheaves of modules. The
tensor product of sheaves of modules is the sheafification of the pointwise one (Tag 05NA), so
this is the morphism which `Stacks.SheafOfModules.endPresheaf` induces through the
sheafification adjunction. -/
noncomputable def tensorDualToEndomorphism
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj
        (dualSheaf 𝒪 h𝒪 F) ⟶ sheafHom 𝒪 h𝒪 F F :=
  ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv
    ((_root_.PresheafOfModules.tensorObj (O := 𝒪) (F.val) ((dualSheaf 𝒪 h𝒪 F).val)))
    (sheafHom 𝒪 h𝒪 F F)).symm (endPresheaf 𝒪 h𝒪 F)

/-- A local pure tensor, viewed in the tensor product sheaf through the sheafification unit. -/
noncomputable def toTensorSheafSection
    (F G : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)) (V : Cᵒᵖ)
    (t : ((_root_.PresheafOfModules.tensorObj (O := 𝒪) (F.val) (G.val))).obj V) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj
        G).val.obj V :=
  (Stacks.SheafOfModules.TensorSheafification.toSheafify 𝒪 h𝒪
    ((_root_.PresheafOfModules.tensorObj (O := 𝒪) (F.val) (G.val)))).app V t

/-- **The canonical morphism on a local pure tensor is the rank-one operator.** This pins the
morphism down: its value on the image of `f ⊗ lam` is the endomorphism `g ↦ lam(g) • f`. -/
@[stacks 0FNV "the rank-one map `ℱ ⊗ ℱ^∨ ⟶ 𝓗om(ℱ,ℱ)` read on sections: a local pure tensor \
`f ⊗ λ` goes to the endomorphism `g ↦ λ(g) • f`.  This pins the morphism down; the companion \
clause `isIso_tensorDualToEndomorphism` says it is an isomorphism",
  stacks 0FNY "the map `ℱ ⊗ 𝓗om(ℱ,𝒪) ⟶ 𝓗om(ℱ,ℱ)` read on sections, which pins it down"]
theorem tensorDualToEndomorphism_toTensorSheafSection
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
      (U : Cᵒᵖ)
    (f : F.val.obj U) (lam : (dualSheaf 𝒪 h𝒪 F).val.obj U) :
    ((tensorDualToEndomorphism 𝒪 h𝒪 F).val.app U).hom
        (toTensorSheafSection 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) U
          (f ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] lam)) =
      rankOneSection 𝒪 h𝒪 (U := U.unop) f lam :=
  congrArg (fun φ => ((φ.app U).hom (f
    ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj U] lam)))
    (((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).homEquiv
      ((_root_.PresheafOfModules.tensorObj (O := 𝒪) (F.val) ((dualSheaf 𝒪 h𝒪 F).val)))
      (sheafHom 𝒪 h𝒪 F F)).apply_symm_apply (endPresheaf 𝒪 h𝒪 F))

/-- **Sheafification inverts the rank-one map**, when `F` has finite dual bases on a family
covering the final object. -/
theorem isIso_sheafify_map_endPresheaf {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)]
    (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k)) :
    IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map (endPresheaf 𝒪 h𝒪 F)) :=
      by
  have hI := isLocallyInjective_endPresheaf 𝒪 h𝒪 hX b
  have hS := isLocallySurjective_endPresheaf 𝒪 h𝒪 hX b
  have := hI
  have := hS
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))]
  exact (J.W_iff _).mp (J.W_of_isLocallyBijective
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪).obj).map
      (endPresheaf 𝒪 h𝒪 F)))

/-- **`F ⊗ F^∨ ⟶ SheafHom(F, F)` is an isomorphism** when `F` has finite dual bases on a family
covering the final object — that is, when `F` is locally a direct summand of a finite free sheaf
of modules. -/
@[stacks 0FNV "the rank-one map `ℱ ⊗ ℱ^∨ ⟶ 𝓗om(ℱ,ℱ)` is an ISOMORPHISM when `ℱ` admits a \
finite dual basis on a covering family.  A different assertion from the section formula that \
pins the map down, which is carried by `tensorDualToEndomorphism_toTensorSheafSection`",
  sga "5 IIIB 5.0" "partial"]
theorem isIso_tensorDualToEndomorphism {K : Type*} {X : K → C} (hX : J.CoversTop X)
    {I : K → Type*} [∀ k, Fintype (I k)]
    (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k)) :
    IsIso (tensorDualToEndomorphism 𝒪 h𝒪 F) := by
  have hm : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify 𝒪 h𝒪).map (endPresheaf 𝒪 h𝒪
    F)) :=
    isIso_sheafify_map_endPresheaf 𝒪 h𝒪 hX b
  have hc : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit.app
    (sheafHom 𝒪 h𝒪 F F)) :=
    inferInstanceAs (IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).counit.app (sheafHom
        𝒪 h𝒪 F F)))
  have h := Adjunction.homEquiv_counit
    (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪)
    ((_root_.PresheafOfModules.tensorObj (O := 𝒪) (F.val) ((dualSheaf 𝒪 h𝒪 F).val)))
      (sheafHom 𝒪 h𝒪 F F)
    (endPresheaf 𝒪 h𝒪 F)
  rw [tensorDualToEndomorphism, h]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hm hc

/-- **The canonical coevaluation `𝒪 ⟶ F ⊗ F^∨`** of a sheaf of modules which is locally a
direct summand of a finite free sheaf of modules: the inverse image of the identity
endomorphism under the rank-one isomorphism `F ⊗ F^∨ ≅ SheafHom(F, F)`. -/
@[stacks 0FNV "EXISTENCE of the canonical coevaluation `𝒪 ⟶ ℱ ⊗ ℱ^∨`, as a named morphism.  \
Its value on local sections is a separate assertion, carried by \
`coevaluation_app_one_eq_sum_of_dualBasis`"]
noncomputable def coevaluation
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    {K : Type*} {X : K → C} (hX : J.CoversTop X) {I : K → Type*} [∀ k, Fintype (I k)]
    (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k)) :
    SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
        ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj
          (dualSheaf 𝒪 h𝒪 F) :=
  identityEndomorphism 𝒪 h𝒪 F ≫ inv (tensorDualToEndomorphism 𝒪 h𝒪 F)
    (I := isIso_tensorDualToEndomorphism 𝒪 h𝒪 (F := F) hX b)

/-- **Coevaluation composed with the rank-one isomorphism is the identity endomorphism.** -/
theorem coevaluation_comp_tensorDualToEndomorphism
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    {K : Type*} {X : K → C} (hX : J.CoversTop X) {I : K → Type*} [∀ k, Fintype (I k)]
    (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k)) :
    coevaluation 𝒪 h𝒪 F hX b ≫ tensorDualToEndomorphism 𝒪 h𝒪 F =
      identityEndomorphism 𝒪 h𝒪 F := by
  show (identityEndomorphism 𝒪 h𝒪 F ≫ inv (tensorDualToEndomorphism 𝒪 h𝒪 F)
    (I := isIso_tensorDualToEndomorphism 𝒪 h𝒪 (F := F) hX b)) ≫
      tensorDualToEndomorphism 𝒪 h𝒪 F = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun morphism ↦ identityEndomorphism 𝒪 h𝒪 F ≫ morphism)
      (IsIso.inv_hom_id (tensorDualToEndomorphism 𝒪 h𝒪 F)
        (I := isIso_tensorDualToEndomorphism 𝒪 h𝒪 (F := F) hX b))).trans (Category.comp_id _))

/-- **The local formula for the canonical coevaluation.** On an object `U` over which `F` has a
finite dual basis `(e i, lam i)`, the value of the coevaluation at the unit section is
`∑ i, e i ⊗ lam i`.

Because the left-hand side does not mention the dual basis, this also says that the displayed
sum is **independent of the chosen dual basis** — equivalently, of the chosen finite-free
retract, since a retract `i ≫ p = 𝟙` of `F|_U` onto a finite free sheaf of modules yields the
dual basis `e j = p(e_j)`, `lam j = e_j^* ∘ i`. -/
@[stacks 0FNV "the canonical coevaluation READ ON SECTIONS: over an object of the covering \
family it sends `1` to `∑ i, eᵢ ⊗ λᵢ` for a finite dual basis.  This is what makes the \
coevaluation canonical rather than `some morphism exists`"]
theorem coevaluation_app_one_eq_sum_of_dualBasis
    (F : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    {K : Type*} {X : K → C} (hX : J.CoversTop X) {I : K → Type*} [∀ k, Fintype (I k)]
    (b : ∀ k, FiniteDualBasis 𝒪 h𝒪 F (X k) (I k))
    (U : C) {I' : Type*} [Fintype I'] (c : FiniteDualBasis 𝒪 h𝒪 F U I') :
    ((coevaluation 𝒪 h𝒪 F hX b).val.app (op U)).hom
        (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)) =
      ∑ i : I', toTensorSheafSection 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) (op U)
        (c.e i ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj (op U)]
          c.lam i) := by
  have hval : IsIso (tensorDualToEndomorphism 𝒪 h𝒪 F).val :=
    @Functor.map_isIso _ _ _ _ _ _
      (SheafOfModules.forget (TensorSheafification.structureSheaf 𝒪 h𝒪))
      (tensorDualToEndomorphism 𝒪 h𝒪 F) (isIso_tensorDualToEndomorphism 𝒪 h𝒪 (F := F) hX b)
  refine PresheafOfModules.injective_of_mono (tensorDualToEndomorphism 𝒪 h𝒪 F).val (op U) ?_
  -- The left-hand side is sent to the identity endomorphism, by definition of coevaluation.
  have hcoev : ((tensorDualToEndomorphism 𝒪 h𝒪 F).val.app (op U)).hom
      (((coevaluation 𝒪 h𝒪 F hX b).val.app (op U)).hom
        (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U))) =
        𝟙 ((restrFun 𝒪 U).obj F.val) := by
    refine Eq.trans ?_ (identityEndomorphism_app_one 𝒪 h𝒪 F U)
    exact congrArg
      (fun φ : SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)
        ⟶ sheafHom 𝒪 h𝒪 F F =>
        (φ.val.app (op U)).hom (1 : (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
          h𝒪).obj.obj (op U)))
      (coevaluation_comp_tensorDualToEndomorphism 𝒪 h𝒪 F hX b)
  -- The right-hand side is sent to `∑ i, rankOneSection (e i) (lam i)`, which is the identity
  -- by the dual-basis identity.
  have hsum : ((tensorDualToEndomorphism 𝒪 h𝒪 F).val.app (op U)).hom
      (∑ i : I', toTensorSheafSection 𝒪 h𝒪 F (dualSheaf 𝒪 h𝒪 F) (op U)
        (c.e i ⊗ₜ[(Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪).obj (op U)]
          c.lam i)) =
        𝟙 ((restrFun 𝒪 U).obj F.val) := by
    refine (map_sum ((tensorDualToEndomorphism 𝒪 h𝒪 F).val.app (op U)).hom _ Finset.univ).trans ?_
    refine Eq.trans (Finset.sum_congr rfl fun i _ =>
      tensorDualToEndomorphism_toTensorSheafSection 𝒪 h𝒪 F (op U) (c.e i) (c.lam i)) ?_
    exact c.sum_eq_of_span 𝒪 h𝒪 _ _ fun V g i => rankOneSection_app 𝒪 h𝒪 (c.e i) (c.lam i) V g
  exact hcoev.trans hsum.symm

end Sheafification

end RankOne

end Stacks.SheafOfModules

end
