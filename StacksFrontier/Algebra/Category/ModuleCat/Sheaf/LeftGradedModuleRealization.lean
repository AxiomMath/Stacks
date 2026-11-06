module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationModule
public import Mathlib.Algebra.Module.GradedModule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The ungraded realization of a graded module over a sheaf of graded algebras

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedRealization.lean` realizes a sheaf of
graded algebras `A` as a sheaf of rings `SheafOfModules.GradedAlgebra.ungradedSheaf`. This file
does the same for a graded module over `A`: the direct sum of its homogeneous components is a
module over the direct sum of the homogeneous components of `A`, objectwise over the site, and
sheafifying that presheaf of modules over the sheafification unit of the algebra gives a sheaf
of modules over `A.ungradedSheaf`.

The module structure is not built by hand: the graded action is repackaged as Mathlib's
`DirectSum.Gmodule` and the module axioms of the realization are then
`DirectSum.Gmodule.module`. That is why the associativity and unit laws of
`SheafOfModules.LeftGradedModule` are stated with `HEq` — they are exactly the hypotheses
`GradedMonoid.GMulAction` wants, up to the identification of a heterogeneous equality with an
equality of `Sigma` types.

## Main definitions

* `SheafOfModules.LeftGradedModule.Total` is the module of sections of the ungraded realization
  over an object of the site, and `SheafOfModules.LeftGradedModule.incl` views a homogeneous
  section in it.
* `SheafOfModules.LeftGradedModule.ungradedPresheaf` is the ungraded realization as a presheaf
  of modules over `Stacks.GradedAlgebra.totalPresheaf`.
* `SheafOfModules.LeftGradedModule.ungradedSheafModule`: **the ungraded realization of a left
  graded module, as a sheaf of modules over `SheafOfModules.GradedAlgebra.ungradedSheaf`.** This
  is the module-side counterpart of `Stacks.RelativeSpec.gradedAlgebraSheaf`.
* `SheafOfModules.LeftGradedModule.directSumIsoUnderlyingModule`,
  `intCoprodIsoUnderlyingModule` and `coprodIsoUnderlyingModule`: the `𝒪`-module underlying the
  realization, as the sheafification of the objectwise direct sum of the homogeneous components,
  as the coproduct of the pieces over all of `ℤ`, and — for pieces concentrated in nonnegative
  degrees — as the coproduct of the nonnegative pieces.
* `SheafOfModules.GradedModule.toLeftGradedModuleOfComm` reads a *right* graded module as a left
  one when the homogeneous multiplication of the algebra commutes, which is the hypothesis `hc`
  the algebra-side construction already carries.

## Main results

* `SheafOfModules.LeftGradedModule.incl_smul_incl`: the action of the realization agrees with
  the graded action on homogeneous local sections.
* `SheafOfModules.LeftGradedModule.totalRestrict_smul`: restriction is semilinear over the
  restriction of the ungraded realization of the algebra. This is what makes the objectwise
  direct sum a presheaf of modules over `totalPresheaf`.
* `SheafOfModules.LeftGradedModule.base_smul_eq_structureMap_smul`: the action of the base ring
  on the objectwise direct sum is the action of the image of the structure map, which is what
  makes the sheafification unit semilinear over the base ring.
* `SheafOfModules.LeftGradedModule.ungradedPresheaf_presheaf`: the abelian presheaf underlying
  the realization is the objectwise direct sum `Stacks.directSumAb` of the homogeneous
  components — the same presheaf whose sheafification the algebra-side quasi-coherence argument
  identifies with the coproduct `∐`.
* `Stacks.ι_comp_sheafifyDirectSumIso_inv` and
  `SheafOfModules.LeftGradedModule.ι_comp_intCoprodIsoUnderlyingModule_hom`: **the value of those
  identifications on one homogeneous degree.** `Stacks.sheafifyDirectSumIso` is built from
  `IsColimit.coconePointUniqueUpToIso` and `intCoprodIsoUnderlyingModule` from it, so neither
  said anything about a coproduct inclusion; an equality of morphisms out of `∐ₙ ℱₙ` is checked
  summand by summand, so without these the identification cannot be compared with any action
  defined degreewise.

## Implementation notes

**Left, not right.** A `PresheafOfModules` is a presheaf of *left* modules, so the realization
of a graded module is a left module over the realization of the algebra, and the input is
`SheafOfModules.LeftGradedModule`. Tag 0FQZ's right graded modules —
`SheafOfModules.GradedModule`, the form the finiteness theorems of this chapter take — are read as
left ones by `SheafOfModules.GradedModule.toLeftGradedModuleOfComm`, which needs the homogeneous
multiplication of the algebra to commute. That is not a restriction in the intended application:
the algebra-side construction `Stacks.RelativeSpec.gradedAlgebraSheaf` carries exactly the same
hypothesis, since a relative spectrum is taken of a *commutative* algebra.

**Degree bookkeeping.** The right-to-left passage is where the degrees move: a right action lands
a section of degree `n` and a homogeneous element of degree `i` in degree `n + i`, while a left
action lands them in `i + n`. `SheafOfModules.GradedModule.smulOfEq` writes the target degree as
a free variable with an equation, so the transport is discharged by `subst` once and no cast
appears in any statement downstream.

**What is here and what is not.** This file produces the sheaf of modules and identifies its
underlying `𝒪`-module with the coproduct of the homogeneous pieces, which is the same
identification the algebra side makes. It does not prove quasi-coherence *over*
`A.ungradedSheaf`: `SheafOfModules.IsQuasicoherent` there asks for a local presentation by free
`A.ungradedSheaf`-modules, a different statement from quasi-coherence of the underlying
`𝒪`-module, and the passage between the two is [Stacks, Tag 0H88], which is available only over
a scheme. That step, and the consumer-facing form of the construction, are in
`StacksFrontier/AlgebraicGeometry/Constructions/GradedModuleToModuleSheaf.lean`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite DirectSum

universe v u t w

open CategoryTheory.Sheaf

universe a m

namespace Stacks

/-! ### The coproduct inclusions of a sheafified objectwise direct sum -/

section SheafifyDirectSumComponent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {ι : Type} [DecidableEq ι] (N : ι → SheafOfModules.{w} R) [HasCoproduct N]

/-- **The degree-`i` coproduct inclusion, read through the inverse of
`Stacks.sheafifyDirectSumIso`, is the sheafification of the degree-`i` inclusion into the
objectwise direct sum**, corrected by the sheafification counit at `N i` that
`Stacks.sheafificationDirectSumComponentIso` packages.

The two cocones `coconePointUniqueUpToIso` compares are the image of the objectwise direct sum's
cofan under sheafification and the coproduct cocone precomposed with that component
isomorphism, so this is `IsColimit.comp_coconePointUniqueUpToIso_inv` with the component
isomorphism cancelled off the left. -/
theorem ι_comp_sheafifyDirectSumIso_inv (i : ι) :
    Limits.Sigma.ι N i ≫ (sheafifyDirectSumIso N).inv =
      (sheafificationDirectSumComponentIso N).inv.app ⟨i⟩ ≫
        (PresheafOfModules.sheafification (𝟙 R.obj)).map (inclHom (fun j => (N j).val) i) :=
  (Iso.eq_inv_comp ((sheafificationDirectSumComponentIso N).app ⟨i⟩)).2
    (Eq.trans (Category.assoc _ _ _).symm
      (IsColimit.comp_coconePointUniqueUpToIso_inv
        (isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj))
          (directSumIsColimit fun j => (N j).val))
        ((IsColimit.precomposeHomEquiv (sheafificationDirectSumComponentIso N) _).symm
          (colimit.isColimit (Discrete.functor N)))
        (Discrete.mk i)))

end SheafifyDirectSumComponent

end Stacks

namespace SheafOfModules.LeftGradedModule

section Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R} (M : LeftGradedModule.{t, a, m} A)

/-- The module of sections of the ungraded realization of a left graded module over an object of
the site: the direct sum of the homogeneous components, as a type synonym carrying the module
structure over the ungraded realization of the algebra. -/
def Total (X : Cᵒᵖ) : Type m :=
  Stacks.DirectSumType (fun n : ℤ => (M.piece n).val) X

/-- The additive group structure on the sections of the ungraded realization. -/
noncomputable instance (X : Cᵒᵖ) : AddCommGroup (M.Total X) :=
  inferInstanceAs (AddCommGroup (Stacks.DirectSumType (fun n : ℤ => (M.piece n).val) X))

/-- The module structure on the sections of the ungraded realization over the base ring. -/
noncomputable instance (X : Cᵒᵖ) : Module (R.obj.obj X) (M.Total X) :=
  inferInstanceAs (Module (R.obj.obj X)
    (Stacks.DirectSumType (fun n : ℤ => (M.piece n).val) X))

/-- The graded action of the homogeneous components of the algebra on those of the module, over
a fixed object of the site. -/
@[instance_reducible]
def gsmul (X : Cᵒᵖ) :
    GradedMonoid.GSMul (fun i : ℤ => ((A.piece i).val.obj X : Type a))
      (fun n : ℤ => ((M.piece n).val.obj X : Type m)) :=
  ⟨fun {i n} x y => M.smul i n X x y⟩

/-- The graded ring structure on the homogeneous components of the algebra over an object of
the site. -/
local instance gringInstance (X : Cᵒᵖ) :
    DirectSum.GRing (fun i : ℤ => ((A.piece i).val.obj X : Type a)) :=
  A.toPresheafGradedAlgebra.gring X

/-- The graded action `gsmul`, as an instance. -/
local instance gsmulInstance (X : Cᵒᵖ) :
    GradedMonoid.GSMul (fun i : ℤ => ((A.piece i).val.obj X : Type a))
      (fun n : ℤ => ((M.piece n).val.obj X : Type m)) :=
  M.gsmul X

/-- The homogeneous components of the module form a graded module over the homogeneous
components of the algebra, over an object of the site. -/
local instance gmoduleInstance (X : Cᵒᵖ) :
    DirectSum.Gmodule (fun i : ℤ => ((A.piece i).val.obj X : Type a))
      (fun n : ℤ => ((M.piece n).val.obj X : Type m)) :=
  letI gmulaction : GradedMonoid.GMulAction
      (fun i : ℤ => ((A.piece i).val.obj X : Type a))
      (fun n : ℤ => ((M.piece n).val.obj X : Type m)) :=
    { M.gsmul X with
      one_smul := fun b => Sigma.ext (zero_vadd _ b.1) (M.one_smul b.1 X b.2)
      mul_smul := fun x y b =>
        Sigma.ext (add_vadd x.1 y.1 b.1) (M.mul_smul x.1 y.1 b.1 X x.2 y.2 b.2) }
  letI gdistrib : DirectSum.GdistribMulAction
      (fun i : ℤ => ((A.piece i).val.obj X : Type a))
      (fun n : ℤ => ((M.piece n).val.obj X : Type m)) :=
    { gmulaction with
      smul_add := fun {i n} x y z => map_add (M.smul i n X x) y z
      smul_zero := fun {i n} x => map_zero (M.smul i n X x) }
  { gdistrib with
    add_smul := fun {i n} x y z => by
      change M.smul i n X (x + y) z = M.smul i n X x z + M.smul i n X y z
      rw [map_add]
      rfl
    zero_smul := fun {i n} z => by
      change M.smul i n X 0 z = 0
      rw [map_zero]
      rfl }

/-- The sections of the ungraded realization of a left graded module form a module over the
sections of the ungraded realization of the algebra. -/
noncomputable instance moduleTotal (X : Cᵒᵖ) :
    Module (A.toPresheafGradedAlgebra.Total X) (M.Total X) :=
  inferInstanceAs (Module (DirectSum ℤ fun i => ((A.piece i).val.obj X : Type a))
    (DirectSum ℤ fun n => ((M.piece n).val.obj X : Type m)))

/-- A homogeneous local section of a left graded module, viewed in the ungraded realization. -/
def incl {X : Cᵒᵖ} (n : ℤ) (x : (M.piece n).val.obj X) : M.Total X := DirectSum.of _ n x

/-- `incl` sends zero to zero. -/
@[simp]
lemma incl_zero {X : Cᵒᵖ} (n : ℤ) : M.incl n (0 : (M.piece n).val.obj X) = 0 := map_zero _

/-- `incl` is additive. -/
@[simp]
lemma incl_add {X : Cᵒᵖ} (n : ℤ) (x y : (M.piece n).val.obj X) :
    M.incl n (x + y) = M.incl n x + M.incl n y := map_add _ x y

/-- `incl` commutes with the action of the base ring. -/
lemma incl_smul_base {X : Cᵒᵖ} (n : ℤ) (r : R.obj.obj X) (x : (M.piece n).val.obj X) :
    M.incl n (r • x) = r • M.incl n x := DirectSum.of_smul _ _ _ _

/-- Every section of the ungraded realization is a finite sum of homogeneous ones. -/
lemma incl_induction {X : Cᵒᵖ} {motive : M.Total X → Prop} (z : M.Total X) (zero : motive 0)
    (incl : ∀ (n : ℤ) (x : (M.piece n).val.obj X), motive (M.incl n x))
    (add : ∀ z z', motive z → motive z' → motive (z + z')) : motive z :=
  DirectSum.induction_on (β := fun n => ((M.piece n).val.obj X : Type m)) z zero incl add

/-- **The action of the ungraded realization agrees with the graded action on homogeneous local
sections.** -/
lemma incl_smul_incl {X : Cᵒᵖ} (i n : ℤ) (x : (A.piece i).val.obj X)
    (y : (M.piece n).val.obj X) :
    A.toPresheafGradedAlgebra.incl i x • M.incl n y = M.incl (i + n) (M.smul i n X x y) := by
  show DirectSum.of (fun k => ((A.piece k).val.obj X : Type a)) i x •
      DirectSum.of (fun k => ((M.piece k).val.obj X : Type m)) n y = _
  rw [DirectSum.Gmodule.of_smul_of]
  rfl

/-! ### The ungraded realization as a presheaf of modules -/

/-- Restriction of sections of the ungraded realization of a left graded module, as an additive
map. -/
noncomputable def totalRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.Total X →+ M.Total Y :=
  Stacks.directSumRestrict (fun n : ℤ => (M.piece n).val) f

/-- Restriction of a homogeneous section of the ungraded realization is the homogeneous section
given by its restriction. -/
@[simp]
lemma totalRestrict_incl {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ℤ) (x : (M.piece n).val.obj X) :
    M.totalRestrict f (M.incl n x) = M.incl n (Stacks.sectionRestrict (M.piece n).val f x) :=
  Stacks.directSumRestrict_of (fun k : ℤ => (M.piece k).val) f n x

/-- **Restriction of sections of the ungraded realization is semilinear** over the restriction of
the ungraded realization of the algebra. -/
lemma totalRestrict_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : A.toPresheafGradedAlgebra.Total X)
    (z : M.Total X) :
    M.totalRestrict f (r • z) =
      A.toPresheafGradedAlgebra.totalRestrict f r • M.totalRestrict f z := by
  induction r using Stacks.GradedAlgebra.incl_induction with
  | zero => simp
  | incl i x =>
    induction z using M.incl_induction with
    | zero => simp
    | incl n y =>
      have h : Stacks.sectionRestrict (M.piece (i + n)).val f (M.smul i n X x y) =
          M.smul i n Y (Stacks.sectionRestrict (A.piece i).val f x)
            (Stacks.sectionRestrict (M.piece n).val f y) :=
        M.smul_naturality i n f x y
      rw [M.incl_smul_incl, M.totalRestrict_incl, Stacks.GradedAlgebra.totalRestrict_incl,
        M.totalRestrict_incl, M.incl_smul_incl, h]
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | add r r' hr hr' => rw [add_smul, map_add, hr, hr', map_add, add_smul]

/-- The objectwise direct sum of the homogeneous components is a module over the sections of
`Stacks.GradedAlgebra.totalPresheaf`. -/
noncomputable instance moduleDirectSumAb (X : Cᵒᵖ) :
    Module (A.toPresheafGradedAlgebra.totalPresheaf.obj X)
      ((Stacks.directSumAb (fun n : ℤ => (M.piece n).val)).obj X) :=
  inferInstanceAs (Module (A.toPresheafGradedAlgebra.Total X) (M.Total X))

/-- **The ungraded realization of a left graded module, as a presheaf of modules over the
ungraded realization of the algebra.** Its sections over an object of the site are the direct sum
of the homogeneous components, acted on by the graded action. -/
noncomputable def ungradedPresheaf :
    PresheafOfModules.{m} A.toPresheafGradedAlgebra.totalPresheaf :=
  PresheafOfModules.ofPresheaf (Stacks.directSumAb (fun n : ℤ => (M.piece n).val))
    (fun _ _ f r z => M.totalRestrict_smul f r z)

/-- The abelian presheaf underlying the ungraded realization is the objectwise direct sum of the
homogeneous components. -/
@[simp]
lemma ungradedPresheaf_presheaf :
    M.ungradedPresheaf.presheaf = Stacks.directSumAb (fun n : ℤ => (M.piece n).val) := rfl

end Presheaf

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A : GradedAlgebra.{w, w} R} (M : LeftGradedModule.{w, w, m} A)
  [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- **The ungraded realization of a left graded module over a sheaf of graded algebras, as a
sheaf of modules over the ungraded realization of the algebra.**

This is the module-side counterpart of `Stacks.RelativeSpec.gradedAlgebraSheaf`: the objectwise
direct sum of the homogeneous components is in general only a presheaf, exactly as on the algebra
side, so the realization as a *sheaf* of modules is the sheafification of `ungradedPresheaf`
along the sheafification unit `Stacks.GradedAlgebra.toTotalSheaf` of the algebra.

Quasi-coherence is not asserted here. Over a scheme it follows from quasi-coherence of the
coproduct of the homogeneous pieces, by `coprodIsoUnderlyingModule` and [Stacks, Tag 0H88]; see
`Stacks.RelativeSpec.isQuasicoherent_gradedModuleSheaf`. -/
noncomputable def ungradedSheafModule : SheafOfModules.{m} A.ungradedSheaf :=
  (PresheafOfModules.sheafification (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj
    M.ungradedPresheaf

end Sheafify

section UnderlyingModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {A : GradedAlgebra.{w, w} R} (M : LeftGradedModule.{w, w, w} A)
  [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

omit [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The action of the ungraded realization and the action of the base ring on the objectwise
direct sum are compatible. -/
lemma smul_smul_total {X : Cᵒᵖ} (r : R.obj.obj X) (b : A.toPresheafGradedAlgebra.Total X)
    (z : M.Total X) : (r • b) • z = r • (b • z) := by
  induction b using Stacks.GradedAlgebra.incl_induction with
  | zero => simp
  | incl i x =>
    induction z using M.incl_induction with
    | zero => simp
    | incl n y =>
      rw [← Stacks.GradedAlgebra.incl_smul, M.incl_smul_incl, M.incl_smul_incl,
        M.smul_smul_left, M.incl_smul_base]
    | add z z' hz hz' => rw [smul_add, smul_add, hz, hz', ← smul_add]
  | add b b' hb hb' => rw [smul_add, add_smul, add_smul, hb, hb', smul_add]

omit [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The module structure of the objectwise direct sum over the base ring is the action of the
image of the structure map of the ungraded realization. -/
lemma base_smul_eq_structureMap_smul {X : Cᵒᵖ} (r : R.obj.obj X) (z : M.Total X) :
    r • z = A.toPresheafGradedAlgebra.structureMap X r • z := by
  have h : A.toPresheafGradedAlgebra.structureMap X r • z =
      (r • (1 : A.toPresheafGradedAlgebra.Total X)) • z := rfl
  rw [h, M.smul_smul_total, _root_.one_smul]

/-- The sheafification unit of the ungraded realization of a left graded module. -/
noncomputable def toUngradedSheafModule :
    M.ungradedPresheaf ⟶ (PresheafOfModules.restrictScalars
      (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj M.ungradedSheafModule.val :=
  (PresheafOfModules.sheafificationAdjunction
    (A.toPresheafGradedAlgebra.toTotalSheaf J)).unit.app M.ungradedPresheaf

/-- The comparison morphism from the objectwise direct sum of the homogeneous components of a
left graded module to the `𝒪`-module underlying its ungraded realization: the sheafification
unit, read as a morphism of presheaves of modules over the base ring. -/
noncomputable def ungradedDirectSumHom :
    Stacks.directSum (fun n : ℤ => (M.piece n).val) ⟶
      ((SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj
        M.ungradedSheafModule).val where
  app X := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (A.ungradedStructureMap.hom.app X).hom).obj
        (M.ungradedSheafModule.val.obj X))
    { toFun := fun z => (M.toUngradedSheafModule.app X) z
      map_add' := fun z z' => map_add (M.toUngradedSheafModule.app X).hom z z'
      map_smul' := fun r z => by
        refine Eq.trans (congrArg (fun y => (M.toUngradedSheafModule.app X).hom y)
          (M.base_smul_eq_structureMap_smul r z)) ?_
        exact (M.toUngradedSheafModule.app X).hom.map_smul _ z }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    exact PresheafOfModules.naturality_apply M.toUngradedSheafModule f z

/-- The comparison morphism is locally injective, being the sheafification unit. -/
lemma isLocallyInjective_ungradedDirectSumHom :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map M.ungradedDirectSumHom) :=
  ⟨fun x y h => Presheaf.equalizerSieve_mem J
    (CategoryTheory.toSheafify J M.ungradedPresheaf.presheaf) x y h⟩

/-- The comparison morphism is locally surjective, being the sheafification unit. -/
lemma isLocallySurjective_ungradedDirectSumHom :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map M.ungradedDirectSumHom) :=
  ⟨fun s => Presheaf.imageSieve_mem J
    (CategoryTheory.toSheafify J M.ungradedPresheaf.presheaf) s⟩

set_option synthInstance.maxHeartbeats 200000 in
omit [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}] in
/-- Shortcut instance: coproducts of sheaves of modules indexed by `ℤ` (the search times out
otherwise). -/
local instance hasColimitsOfShape_discrete_int :
    HasColimitsOfShape (Discrete ℤ) (SheafOfModules.{w} R) :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
omit [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}] in
/-- Shortcut instance: coproducts of sheaves of modules indexed by `ℕ`. -/
local instance hasColimitsOfShape_discrete_nat :
    HasColimitsOfShape (Discrete ℕ) (SheafOfModules.{w} R) :=
  inferInstance

/-- **The `𝒪`-module underlying the ungraded realization of a left graded module is the
sheafification of the objectwise direct sum of its homogeneous components.** -/
noncomputable def directSumIsoUnderlyingModule :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        (Stacks.directSum fun n : ℤ => (M.piece n).val) ≅
      (SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheafModule :=
  Stacks.sheafifyIsoOfLocallyBijective M.ungradedDirectSumHom
    M.isLocallyInjective_ungradedDirectSumHom M.isLocallySurjective_ungradedDirectSumHom

/-- `directSumIsoUnderlyingModule` is the sheafification transpose of the comparison morphism
`ungradedDirectSumHom`. -/
theorem directSumIsoUnderlyingModule_hom :
    M.directSumIsoUnderlyingModule.hom =
      Stacks.sheafifyHomOfPresheafHom M.ungradedDirectSumHom :=
  rfl

/-- **The `𝒪`-module underlying the ungraded realization of a left graded module is the
coproduct of its homogeneous pieces over all of `ℤ`.** Unlike `coprodIsoUnderlyingModule` this
needs no hypothesis on which degrees are occupied: the sheafification of the objectwise direct
sum over `ℤ` *is* the `ℤ`-indexed coproduct, by `Stacks.sheafifyDirectSumIso`. -/
noncomputable def intCoprodIsoUnderlyingModule :
    (∐ fun n : ℤ => M.piece n) ≅
      (SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheafModule :=
  (Stacks.sheafifyDirectSumIso (fun n : ℤ => M.piece n)).symm ≪≫
    M.directSumIsoUnderlyingModule

/-- **The value of `intCoprodIsoUnderlyingModule` on the degree-`n` summand.** The inclusion of
`ℱₙ` into `∐ₙ ℱₙ`, followed by the identification with the `𝒪`-module underlying the ungraded
realization, is the degree-`n` inclusion into the objectwise direct sum — sheafified, and
corrected by the sheafification counit at `ℱₙ` that
`Stacks.sheafificationDirectSumComponentIso` packages.

This is what makes the identification usable on one homogeneous degree at a time, which is the
only form in which it can be compared with a degreewise action: an equality of morphisms out of
`∐ₙ ℱₙ` is checked summand by summand. The counit factor is unavoidable — the coproduct is the
sheafification of the objectwise direct sum, so the degree-`n` summand reaches it only through
the sheafification of `ℱₙ`. -/
theorem ι_comp_intCoprodIsoUnderlyingModule_hom (n : ℤ) :
    Sigma.ι (fun k : ℤ => M.piece k) n ≫ M.intCoprodIsoUnderlyingModule.hom =
      (Stacks.sheafificationDirectSumComponentIso (fun k : ℤ => M.piece k)).inv.app ⟨n⟩ ≫
        (PresheafOfModules.sheafification (𝟙 R.obj)).map
            (Stacks.inclHom (fun k : ℤ => (M.piece k).val) n) ≫
          Stacks.sheafifyHomOfPresheafHom M.ungradedDirectSumHom :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun z => z ≫ Stacks.sheafifyHomOfPresheafHom M.ungradedDirectSumHom)
        (Stacks.ι_comp_sheafifyDirectSumIso_inv (fun k : ℤ => M.piece k) n))
      (Category.assoc _ _ _))

/-- `SheafOfModules.LeftGradedModule.ungradedDirectSumHom`, restricted to the nonnegative
degrees. -/
noncomputable def coprodDirectSumHom :
    Stacks.directSum (fun n : ℕ => (M.piece (n : ℤ)).val) ⟶
      ((SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj
        M.ungradedSheafModule).val :=
  Stacks.directSumNatToInt (fun n : ℤ => (M.piece n).val) ≫ M.ungradedDirectSumHom

/-- **The `𝒪`-module underlying the ungraded realization of a left graded module concentrated in
nonnegative degrees is the coproduct of its homogeneous pieces.** -/
noncomputable def coprodIsoUnderlyingModule (hzero : ∀ n : ℤ, n < 0 → IsZero (M.piece n)) :
    (∐ fun n : ℕ => M.piece (n : ℤ)) ≅
      (SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj M.ungradedSheafModule :=
  (Stacks.sheafifyDirectSumIso (fun n : ℕ => M.piece (n : ℤ))).symm ≪≫
    Stacks.sheafifyIsoOfLocallyBijective M.coprodDirectSumHom
      (Stacks.isLocallyInjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallyInjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        M.isLocallyInjective_ungradedDirectSumHom)
      (Stacks.isLocallySurjective_toPresheaf_map_comp _ _ _
        (Stacks.isLocallySurjective_directSumNatToInt _ _
          fun n hn U => Stacks.subsingleton_of_isZero (hzero n hn) U)
        M.isLocallySurjective_ungradedDirectSumHom)

end UnderlyingModule

end SheafOfModules.LeftGradedModule

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R} (M : GradedModule.{t, a, m} A)

/-- The right action of a graded module, with the degree of its target given by a free variable
and an equation. The right action of Tag 0FQZ lands a section of degree `n` and a homogeneous
element of degree `i` in degree `n + i`, while a left action lands them in `i + n`; writing the
target degree as a variable is what lets the two be compared without a cast appearing anywhere
downstream. -/
def smulOfEq (n i k : ℤ) (h : n + i = k) (X : Cᵒᵖ) :
    (M.piece n).val.obj X →+ (A.piece i).val.obj X →+ (M.piece k).val.obj X := by
  subst h
  exact M.smul n i X

/-- `smulOfEq` agrees with the right action, as a heterogeneous equality. -/
lemma heq_smulOfEq (n i k : ℤ) (h : n + i = k) (X : Cᵒᵖ) (x : (M.piece n).val.obj X)
    (y : (A.piece i).val.obj X) : HEq (M.smulOfEq n i k h X x y) (M.smul n i X x y) := by
  subst h
  rfl

/-- `smulOfEq` commutes with the action of the base ring on the module variable. -/
lemma smulOfEq_smul_left (n i k : ℤ) (h : n + i = k) (X : Cᵒᵖ) (r : R.obj.obj X)
    (x : (M.piece n).val.obj X) (y : (A.piece i).val.obj X) :
    M.smulOfEq n i k h X (r • x) y = r • M.smulOfEq n i k h X x y := by
  subst h
  exact M.smul_smul_left n i X r x y

/-- `smulOfEq` commutes with the action of the base ring on the algebra variable. -/
lemma smulOfEq_smul_right (n i k : ℤ) (h : n + i = k) (X : Cᵒᵖ) (r : R.obj.obj X)
    (x : (M.piece n).val.obj X) (y : (A.piece i).val.obj X) :
    M.smulOfEq n i k h X x (r • y) = r • M.smulOfEq n i k h X x y := by
  subst h
  exact M.smul_smul_right n i X r x y

/-- `smulOfEq` commutes with restriction. -/
lemma smulOfEq_naturality (n i k : ℤ) (h : n + i = k) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (M.piece n).val.obj X) (y : (A.piece i).val.obj X) :
    (M.piece k).val.map f (M.smulOfEq n i k h X x y) =
      M.smulOfEq n i k h Y ((M.piece n).val.map f x) ((A.piece i).val.map f y) := by
  subst h
  exact M.smul_naturality n i f x y

/-- The right action of a graded module, as a heterogeneous equality, is insensitive to the
degree of the algebra variable. -/
lemma smul_heq_right (n : ℤ) {i i' : ℤ} (h : i = i') (X : Cᵒᵖ) (x : (M.piece n).val.obj X)
    {y : (A.piece i).val.obj X} {y' : (A.piece i').val.obj X} (hy : HEq y y') :
    HEq (M.smul n i X x y) (M.smul n i' X x y') := by
  subst h
  rw [eq_of_heq hy]

/-- The right action of a graded module, as a heterogeneous equality, is insensitive to the
degree of the module variable. -/
lemma smul_heq_left {n n' : ℤ} (h : n = n') (i : ℤ) (X : Cᵒᵖ)
    {x : (M.piece n).val.obj X} {x' : (M.piece n').val.obj X} (hx : HEq x x')
    (y : (A.piece i).val.obj X) : HEq (M.smul n i X x y) (M.smul n' i X x' y) := by
  subst h
  rw [eq_of_heq hx]

variable (hc : ∀ (i j : ℤ) (W : Cᵒᵖ) (x : (A.piece i).val.obj W) (y : (A.piece j).val.obj W),
  HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x))

include hc in
/-- **A right graded module over a sheaf of graded algebras with commutative homogeneous
multiplication, read as a left graded module.** The hypothesis `hc` is the one the algebra-side
construction `Stacks.RelativeSpec.gradedAlgebraSheaf` already carries. -/
def toLeftGradedModuleOfComm : LeftGradedModule.{t, a, m} A where
  piece := M.piece
  smul i n X := AddMonoidHom.flip (M.smulOfEq n i (i + n) (add_comm n i) X)
  smul_smul_left i n X r x y := M.smulOfEq_smul_right n i (i + n) (add_comm n i) X r y x
  smul_smul_right i n X r x y := M.smulOfEq_smul_left n i (i + n) (add_comm n i) X r y x
  smul_naturality i n _U _V f x y := M.smulOfEq_naturality n i (i + n) (add_comm n i) f y x
  mul_smul i j n U x y z := by
    refine HEq.trans (M.heq_smulOfEq n (i + j) _ (add_comm n (i + j)) U z _) ?_
    refine HEq.trans (M.smul_heq_right n (add_comm i j) U z (hc i j U x y)) ?_
    refine HEq.trans (M.smul_mul n j i U z y x).symm ?_
    refine HEq.trans (M.smul_heq_left (add_comm n j) i U
      (M.heq_smulOfEq n j _ (add_comm n j) U z y).symm x) ?_
    exact (M.heq_smulOfEq (j + n) i _ (add_comm (j + n) i) U _ x).symm
  one_smul n U z :=
    (M.heq_smulOfEq n 0 _ (add_comm n 0) U z _).trans (M.smul_one n U z)

/-- The homogeneous pieces of `toLeftGradedModuleOfComm` are those of the right graded
module. -/
@[simp]
lemma toLeftGradedModuleOfComm_piece : (M.toLeftGradedModuleOfComm hc).piece = M.piece := rfl

end SheafOfModules.GradedModule

end
