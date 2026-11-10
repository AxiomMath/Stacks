module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The ungraded realization of a sheaf of graded algebras

Let `R` be a presheaf of rings on a site and let `P : ι → PresheafOfModules R` be a family of
presheaves of modules indexed by an additive monoid `ι`, carrying a restriction-compatible
bilinear multiplication `P i × P j ⟶ P (i + j)`, an associativity law and a global unit in
degree `0`. The *ungraded realization* of this graded algebra is the presheaf of rings whose
sections over an object of the site are the direct sum of the homogeneous components, with the
multiplication induced by the graded one.

The graded tensor, symmetric and exterior algebras of a module sheaf are examples of such graded
algebras. The realization is constructed here at the level of presheaves.

## Main definitions

* `Stacks.directSum` is the objectwise direct sum of a family of presheaves of modules, and
  `Stacks.inclHom` is the inclusion of a homogeneous component into it.
* `Stacks.GradedAlgebra` is a graded algebra structure on such a family: the presheaf-level,
  arbitrary-index form of `SheafOfModules.GradedAlgebra`.
* `Stacks.GradedAlgebra.gring` is the `DirectSum.GRing` structure it induces on the homogeneous
  components over a fixed object of the site.
* `Stacks.GradedAlgebra.Total` is the ring of sections of the ungraded realization over an
  object of the site, and `Stacks.GradedAlgebra.incl` views a homogeneous section in it.
* `Stacks.GradedAlgebra.totalPresheaf` is the ungraded realization as a presheaf of rings, and
  `Stacks.GradedAlgebra.structureMap` is the map `r ↦ r • 1` from the base ring into it.
* `SheafOfModules.GradedAlgebra.toPresheafGradedAlgebra` reads a sheaf of graded algebras as one
  of these, so that the realization applies to it.

## Main results

* `Stacks.directSumIsColimit`: the objectwise direct sum of a family of presheaves of modules is
  its coproduct, so the underlying module of the realization is the coproduct `∐ P`.
* `Stacks.GradedAlgebra.incl_mul_incl`, `one_eq_incl`, `totalRestrict_mul`,
  `totalRestrict_one`: the multiplication and unit of the realization agree with the graded
  multiplication and the graded unit, and restriction is a ring homomorphism.
* `Stacks.GradedAlgebra.structureMap_commutes`: the image of the base ring is central.
* `Stacks.GradedAlgebra.smul_mul_eq`, `mul_smul_eq`: the multiplication of the realization is
  bilinear over the base ring.

## Implementation notes

The ring structure is not built by hand: the graded data is repackaged as Mathlib's
`DirectSum.GRing`, and the ring axioms of the realization are then `DirectSum.ring`. That is why
`GradedAlgebra`'s associativity and unit laws are stated with `HEq` — they are exactly the
hypotheses `GradedMonoid.GMonoid` wants, up to the identification of a heterogeneous equality
with an equality of `Sigma` types.

**Universes.** The index type `ι` is in `Type 0`. That is a restriction relative to the rest of
the file, and it is deliberate: `DirectSum ι` of a family in `Type w` lands in `Type (max u₀ w)`
for `ι : Type u₀`, so a larger index would bump the module universe of the realization away from
that of the pieces. Every intended index — `ℕ` and `ℤ` — is in `Type 0`. The site universes and
the ring and module universes are independent.

**`RingCat` rather than `CommRingCat`.** The base `R` is a presheaf of possibly noncommutative
rings, and the realization is a presheaf of possibly noncommutative rings. Both the structure
map and its centrality hold at that generality, because they come from the two *separate* scalar
laws of a `Stacks.BilinearMap` and not from commutativity of `R`. A `BilinearMap` requires the
commutators of `R` to annihilate the target, so the notion is bilinearity exactly in the
commutative case.

**Presheaves and sheaves.** This file realizes a graded algebra of *presheaves* of modules
as a *presheaf* of rings. It does not sheafify. For a graded algebra whose pieces are sheaves,
the objectwise direct sum is in general only a presheaf, so the ungraded realization as a *sheaf*
of rings is the sheafification of `totalPresheaf`, and its multiplication is obtained from the one
here by `Stacks.BilinearMap.extend` along the sheafification unit — which is locally bijective, so
the extension exists and is unique by `Stacks.BilinearMap.existsUnique_extend`. The associativity
of that extended multiplication, and the identification of the underlying module sheaf with the
sheaf coproduct `∐`, are not proved here.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite DirectSum

universe v u t w

namespace Stacks

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι]

/-- Restriction along the identity is the identity on sections. -/
lemma _root_.PresheafOfModules.map_id_apply_ungraded (M : PresheafOfModules.{w} R) (X : Cᵒᵖ)
    (m : M.obj X) : M.map (𝟙 X) m = m := by
  rw [M.map_id]; rfl

/-! ### Restriction maps of sections -/

/-- The restriction map of a presheaf of modules as an additive map whose target type is
written as `M.obj Y` rather than as a restriction of scalars. -/
noncomputable def sectionRestrict (M : PresheafOfModules.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (M.obj X : Type w) →+ (M.obj Y : Type w) :=
  AddMonoidHom.mk' (fun m => M.map f m) (fun m m' => map_add (M.map f).hom m m')

/-- `sectionRestrict M f` sends a section `m` to `M.map f m`. -/
lemma sectionRestrict_apply (M : PresheafOfModules.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X) :
    sectionRestrict M f m = M.map f m := rfl

/-- Restriction along the identity is the identity. -/
@[simp]
lemma sectionRestrict_id (M : PresheafOfModules.{w} R) (X : Cᵒᵖ) (m : M.obj X) :
    sectionRestrict M (𝟙 X) m = m :=
  M.map_id_apply_ungraded X m

/-- Restriction along a composite is the composite of the restrictions. -/
lemma sectionRestrict_comp (M : PresheafOfModules.{w} R) {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (m : M.obj X) : sectionRestrict M (f ≫ g) m = sectionRestrict M g (sectionRestrict M f m) :=
  M.map_comp_apply f g m

/-- Restriction of sections is semilinear along `R.map f`. -/
lemma sectionRestrict_smul (M : PresheafOfModules.{w} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X)
    (m : M.obj X) : sectionRestrict M f (r • m) = R.map f r • sectionRestrict M f m :=
  M.map_smul f r m

section DirectSum

variable (P : ι → PresheafOfModules.{w} R)

/-- The carrier of the objectwise direct sum of a family of presheaves of modules. -/
abbrev DirectSumType (X : Cᵒᵖ) : Type w := DirectSum ι fun i => ((P i).obj X : Type w)

/-- The restriction map of the objectwise direct sum, as an additive map. -/
noncomputable def directSumRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    DirectSumType P X →+ DirectSumType P Y :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of (fun j => ((P j).obj Y : Type w)) i).comp (sectionRestrict (P i) f)

/-- Restriction of the direct sum restricts each homogeneous component. -/
@[simp]
lemma directSumRestrict_of {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : ι) (y : (P i).obj X) :
    directSumRestrict P f (DirectSum.of _ i y) = DirectSum.of _ i (sectionRestrict (P i) f y) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The objectwise direct sum of a family of presheaves of modules, as a presheaf of abelian
groups. -/
noncomputable def directSumAb : Cᵒᵖ ⥤ Ab.{w} where
  obj X := AddCommGrpCat.of (DirectSumType P X)
  map {X Y} f := AddCommGrpCat.ofHom (directSumRestrict P f)
  map_id X := by
    ext : 1
    refine DirectSum.addHom_ext fun i y => ?_
    change directSumRestrict P (𝟙 X) (DirectSum.of _ i y) = DirectSum.of _ i y
    rw [directSumRestrict_of, sectionRestrict_id]
  map_comp {X Y Z} f g := by
    ext : 1
    refine DirectSum.addHom_ext fun i y => ?_
    change directSumRestrict P (f ≫ g) (DirectSum.of _ i y) =
      directSumRestrict P g (directSumRestrict P f (DirectSum.of _ i y))
    rw [directSumRestrict_of, directSumRestrict_of, directSumRestrict_of, sectionRestrict_comp]

/-- The sections of `directSumAb P` over `X` form a module over `R.obj X`. -/
noncomputable instance directSumAbModule (X : Cᵒᵖ) : Module (R.obj X) ((directSumAb P).obj X) :=
  inferInstanceAs (Module (R.obj X) (DirectSumType P X))

/-- Restriction of the direct sum is semilinear along `R.map f`. -/
lemma directSumRestrict_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : DirectSumType P X) :
    directSumRestrict P f (r • m) = R.map f r • directSumRestrict P f m := by
  induction m using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [← DirectSum.of_smul, directSumRestrict_of, directSumRestrict_of, sectionRestrict_smul,
      DirectSum.of_smul]
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

/-- The objectwise direct sum of a family of presheaves of modules. -/
noncomputable def directSum : PresheafOfModules.{w} R :=
  PresheafOfModules.ofPresheaf (directSumAb P) (fun _ _ f r m => directSumRestrict_smul P f r m)

/-- Restriction in `directSum P` restricts each homogeneous component. -/
@[simp]
lemma directSum_sectionRestrict_of {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : ι) (y : (P i).obj X) :
    sectionRestrict (directSum P) f (DirectSum.of _ i y) =
      DirectSum.of _ i (sectionRestrict (P i) f y) :=
  directSumRestrict_of P f i y

/-! ### The objectwise direct sum is the coproduct -/

/-- The inclusion of a homogeneous component into the objectwise direct sum. -/
noncomputable def inclHom (i : ι) : P i ⟶ directSum P where
  app X := ModuleCat.ofHom
    { toFun := fun x => DirectSum.of (fun j => ((P j).obj X : Type w)) i x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun _ _ => DirectSum.of_smul _ _ _ _ }
  naturality {_X _Y} f :=
    ModuleCat.hom_ext (LinearMap.ext fun x => (directSumRestrict_of P f i x).symm)

/-- The morphism out of the objectwise direct sum determined by a family of morphisms out of the
homogeneous components. -/
noncomputable def directSumDesc {T : PresheafOfModules.{w} R} (g : ∀ i, P i ⟶ T) :
    directSum P ⟶ T where
  app X := ModuleCat.ofHom
    (DirectSum.toModule (R.obj X) ι ((T.obj X : Type w)) fun i => ((g i).app X).hom)
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (DirectSum.toModule (R.obj Y) ι ((T.obj Y : Type w)) fun k => ((g k).app Y).hom)
        (directSumRestrict P f x) =
      sectionRestrict T f ((DirectSum.toModule (R.obj X) ι ((T.obj X : Type w))
        fun k => ((g k).app X).hom) x)
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i y =>
      rw [directSumRestrict_of, ← DirectSum.lof_eq_of (R.obj Y), DirectSum.toModule_lof,
        ← DirectSum.lof_eq_of (R.obj X), DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply (g i) f y
    | add a b ha hb => simp only [map_add, ha, hb]

/-- A morphism out of the objectwise direct sum, as an additive map whose source type is written
as a direct sum. -/
noncomputable def homToAddMonoidHom {T : PresheafOfModules.{w} R} (h : directSum P ⟶ T)
    (X : Cᵒᵖ) : DirectSumType P X →+ (T.obj X : Type w) :=
  AddMonoidHom.mk' (fun z => h.app X z) (fun z z' => map_add (h.app X).hom z z')

/-- Two morphisms out of the objectwise direct sum agreeing on every homogeneous component are
equal. -/
lemma directSum_hom_ext {T : PresheafOfModules.{w} R} {h h' : directSum P ⟶ T}
    (hh : ∀ i, inclHom P i ≫ h = inclHom P i ≫ h') : h = h' := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine DFunLike.congr_fun (DirectSum.addHom_ext (f := homToAddMonoidHom P h X)
    (g := homToAddMonoidHom P h' X) fun i y => ?_) x
  exact congrArg (fun q : P i ⟶ T => q.app X y) (hh i)

/-- The morphism `directSumDesc P g` restricts to `g i` on the `i`-th component. -/
@[simp]
lemma inclHom_directSumDesc {T : PresheafOfModules.{w} R} (g : ∀ i, P i ⟶ T) (i : ι) :
    inclHom P i ≫ directSumDesc P g = g i := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change (DirectSum.toModule (R.obj X) ι ((T.obj X : Type w)) fun k => ((g k).app X).hom)
    (DirectSum.of (fun j => ((P j).obj X : Type w)) i x) = (g i).app X x
  rw [← DirectSum.lof_eq_of (R.obj X), DirectSum.toModule_lof]

/-- The objectwise direct sum, as a cofan on the family of homogeneous components. -/
noncomputable def directSumCofan : Cofan P := Cofan.mk (directSum P) (inclHom P)

/-- **The objectwise direct sum of a family of presheaves of modules is its coproduct.** -/
noncomputable def directSumIsColimit : IsColimit (directSumCofan P) :=
  Cofan.IsColimit.mk _ (fun s => directSumDesc P s.inj)
    (fun s i => inclHom_directSumDesc P s.inj i)
    (fun s m hm => directSum_hom_ext P fun i => by
      rw [inclHom_directSumDesc]
      exact hm i)

end DirectSum

section GradedAlgebra

variable [AddMonoid ι]

/-- An `ι`-graded algebra structure on a family `P` of presheaves of modules: a
restriction-compatible bilinear multiplication `P i × P j ⟶ P (i + j)`, an associativity law, and
a global unit in degree `0` which is a two-sided identity.

This is the presheaf-level, arbitrary-index form of `SheafOfModules.GradedAlgebra`. The
associativity and unit laws are heterogeneous equalities because the two sides of each live in
graded pieces whose degrees are propositionally but not definitionally equal. -/
structure GradedAlgebra (P : ι → PresheafOfModules.{w} R) where
  /-- Multiplication of homogeneous local sections. -/
  mul (i j : ι) : BilinearMap (P i) (P j) (P (i + j))
  /-- The global unit in degree `0`. -/
  one : (P 0).sections
  /-- Associativity of multiplication. -/
  mul_assoc (i j k : ι) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X) (z : (P k).obj X) :
    HEq ((mul (i + j) k).app X ((mul i j).app X x y) z)
      ((mul i (j + k)).app X x ((mul j k).app X y z))
  /-- The global unit is a left identity. -/
  one_mul (i : ι) (X : Cᵒᵖ) (x : (P i).obj X) : HEq ((mul 0 i).app X (one.eval X) x) x
  /-- The global unit is a right identity. -/
  mul_one (i : ι) (X : Cᵒᵖ) (x : (P i).obj X) : HEq ((mul i 0).app X x (one.eval X)) x

namespace GradedAlgebra

variable {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)

/-- The graded unit of the homogeneous components over an object of the site. -/
@[instance_reducible]
def gone (X : Cᵒᵖ) : GradedMonoid.GOne fun i => ((P i).obj X : Type w) := ⟨A.one.eval X⟩

/-- The graded multiplication of the homogeneous components over an object of the site. -/
@[instance_reducible]
def gmul (X : Cᵒᵖ) : GradedMonoid.GMul fun i => ((P i).obj X : Type w) :=
  ⟨fun {i j} x y => (A.mul i j).app X x y⟩

/-- The graded ring structure carried by the homogeneous components over a fixed object of the
site. -/
@[instance_reducible]
def gring (X : Cᵒᵖ) : DirectSum.GRing fun i => ((P i).obj X : Type w) :=
  letI _gone := A.gone X
  letI _gmul := A.gmul X
  letI gmonoid : GradedMonoid.GMonoid fun i => ((P i).obj X : Type w) :=
    { _gmul, _gone with
      one_mul := fun a => Sigma.ext (zero_add a.1) (A.one_mul a.1 X a.2)
      mul_one := fun a => Sigma.ext (add_zero a.1) (A.mul_one a.1 X a.2)
      mul_assoc := fun a b c =>
        Sigma.ext (_root_.add_assoc a.1 b.1 c.1) (A.mul_assoc a.1 b.1 c.1 X a.2 b.2 c.2)
      gnpow := GradedMonoid.GMonoid.gnpowRec
      gnpow_zero' := GradedMonoid.GMonoid.gnpowRec_zero
      gnpow_succ' := GradedMonoid.GMonoid.gnpowRec_succ }
  letI gnuas : DirectSum.GNonUnitalNonAssocSemiring fun i => ((P i).obj X : Type w) :=
    { _gmul with
      mul_zero := fun {i j} a => map_zero ((A.mul i j).app X a)
      zero_mul := fun {i j} b => by
        change (A.mul i j).app X 0 b = 0
        rw [map_zero]
        rfl
      mul_add := fun {i j} a b c => map_add ((A.mul i j).app X a) b c
      add_mul := fun {i j} a b c => (A.mul i j).map_add_left X a b c }
  letI gsemiring : DirectSum.GSemiring fun i => ((P i).obj X : Type w) :=
    { gnuas, gmonoid with
      natCast := fun n => n • A.one.eval X
      natCast_zero := zero_smul ℕ _
      natCast_succ := fun n => succ_nsmul _ n }
  { gsemiring with
    intCast := fun n => n • A.one.eval X
    intCast_ofNat := fun n => natCast_zsmul _ n
    intCast_negSucc_ofNat := fun n => negSucc_zsmul _ n }

/-- The sections of the ungraded realization of a graded algebra over an object of the site: the
direct sum of the homogeneous components, as a type synonym carrying the ring structure. -/
def Total (_A : GradedAlgebra P) (X : Cᵒᵖ) : Type w := DirectSumType P X

/-- The sections of the ungraded realization form an additive group. -/
noncomputable instance (X : Cᵒᵖ) : AddCommGroup (A.Total X) :=
  inferInstanceAs (AddCommGroup (DirectSumType P X))

/-- The sections of the ungraded realization over `X` form a module over `R.obj X`. -/
noncomputable instance (X : Cᵒᵖ) : Module (R.obj X) (A.Total X) :=
  inferInstanceAs (Module (R.obj X) (DirectSumType P X))

/-- The ring structure on the sections of the ungraded realization, given by `DirectSum.ring`. -/
noncomputable instance (X : Cᵒᵖ) : Ring (A.Total X) :=
  letI := A.gring X
  inferInstanceAs (Ring (DirectSum ι fun i => ((P i).obj X : Type w)))

/-- A homogeneous local section, viewed in the ungraded realization. -/
def incl {X : Cᵒᵖ} (i : ι) (x : (P i).obj X) : A.Total X := DirectSum.of _ i x

/-- The inclusion of a homogeneous component sends `0` to `0`. -/
@[simp]
lemma incl_zero {X : Cᵒᵖ} (i : ι) : A.incl i (0 : (P i).obj X) = 0 := map_zero _

/-- The inclusion of a homogeneous component is additive. -/
@[simp]
lemma incl_add {X : Cᵒᵖ} (i : ι) (x y : (P i).obj X) :
    A.incl i (x + y) = A.incl i x + A.incl i y := map_add _ x y

/-- The inclusion of a homogeneous component is `R.obj X`-linear. -/
lemma incl_smul {X : Cᵒᵖ} (i : ι) (r : R.obj X) (x : (P i).obj X) :
    A.incl i (r • x) = r • A.incl i x := DirectSum.of_smul _ _ _ _

/-- Every section of the ungraded realization is a finite sum of homogeneous ones. -/
lemma incl_induction {X : Cᵒᵖ} {motive : A.Total X → Prop} (x : A.Total X) (zero : motive 0)
    (incl : ∀ (i : ι) (y : (P i).obj X), motive (A.incl i y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x :=
  DirectSum.induction_on (β := fun i => ((P i).obj X : Type w)) x zero incl add

/-- The product of two homogeneous sections is the homogeneous section given by the graded
multiplication. -/
lemma incl_mul_incl {X : Cᵒᵖ} (i j : ι) (x : (P i).obj X) (y : (P j).obj X) :
    A.incl i x * A.incl j y = A.incl (i + j) ((A.mul i j).app X x y) := by
  let _gr := A.gring X
  change DirectSum.of (fun k => ((P k).obj X : Type w)) i x *
      DirectSum.of (fun k => ((P k).obj X : Type w)) j y = _
  rw [DirectSum.of_mul_of]
  rfl

/-- The unit of the ungraded realization is the graded unit, in degree `0`. -/
lemma one_eq_incl (X : Cᵒᵖ) : (1 : A.Total X) = A.incl 0 (A.one.eval X) := rfl

/-- Multiplication in the ungraded realization commutes with scalars in the left factor. -/
lemma smul_mul_eq {X : Cᵒᵖ} (r : R.obj X) (a b : A.Total X) : r • a * b = r • (a * b) := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i x =>
    induction b using A.incl_induction with
    | zero => simp
    | incl j y =>
      rw [← A.incl_smul, A.incl_mul_incl, A.incl_mul_incl, (A.mul i j).map_smul_left,
        A.incl_smul]
    | add b b' hb hb' => rw [mul_add, mul_add, hb, hb', smul_add]
  | add a a' ha ha' => rw [smul_add, add_mul, add_mul, ha, ha', smul_add]

/-- Multiplication in the ungraded realization commutes with scalars in the right factor. -/
lemma mul_smul_eq {X : Cᵒᵖ} (r : R.obj X) (a b : A.Total X) : a * (r • b) = r • (a * b) := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i x =>
    induction b using A.incl_induction with
    | zero => simp
    | incl j y =>
      rw [← A.incl_smul, A.incl_mul_incl, A.incl_mul_incl, (A.mul i j).map_smul_right,
        A.incl_smul]
    | add b b' hb hb' => rw [smul_add, mul_add, mul_add, hb, hb', smul_add]
  | add a a' ha ha' => rw [add_mul, add_mul, ha, ha', smul_add]

/-! ### The ungraded realization as a presheaf of rings -/

/-- Restriction of sections of the ungraded realization, as an additive map. -/
noncomputable def totalRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) : A.Total X →+ A.Total Y :=
  directSumRestrict P f

/-- Restriction sends a homogeneous section to the restriction of that section. -/
@[simp]
lemma totalRestrict_incl {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : ι) (x : (P i).obj X) :
    A.totalRestrict f (A.incl i x) = A.incl i (sectionRestrict (P i) f x) :=
  directSumRestrict_of P f i x

/-- Restriction of sections of the ungraded realization preserves the unit. -/
lemma totalRestrict_one {X Y : Cᵒᵖ} (f : X ⟶ Y) : A.totalRestrict f 1 = 1 := by
  have h : sectionRestrict (P 0) f (A.one.eval X) = A.one.eval Y :=
    PresheafOfModules.sections_property A.one f
  rw [A.one_eq_incl, A.totalRestrict_incl, h, A.one_eq_incl]

/-- Restriction of sections of the ungraded realization preserves multiplication. -/
lemma totalRestrict_mul {X Y : Cᵒᵖ} (f : X ⟶ Y) (a b : A.Total X) :
    A.totalRestrict f (a * b) = A.totalRestrict f a * A.totalRestrict f b := by
  induction a using A.incl_induction with
  | zero => simp
  | incl i x =>
    induction b using A.incl_induction with
    | zero => simp
    | incl j y =>
      have h : sectionRestrict (P (i + j)) f ((A.mul i j).app X x y) =
          (A.mul i j).app Y (sectionRestrict (P i) f x) (sectionRestrict (P j) f y) :=
        (A.mul i j).naturality f x y
      rw [A.incl_mul_incl, A.totalRestrict_incl, A.totalRestrict_incl, A.totalRestrict_incl,
        A.incl_mul_incl, h]
    | add b b' hb hb' => rw [mul_add, map_add, hb, hb', map_add, mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add, add_mul]

/-- Restriction of sections of the ungraded realization is semilinear along `R.map f`. -/
lemma totalRestrict_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (a : A.Total X) :
    A.totalRestrict f (r • a) = R.map f r • A.totalRestrict f a :=
  directSumRestrict_smul P f r a

/-- Restriction of sections of the ungraded realization, as a ring homomorphism. -/
noncomputable def totalRestrictRingHom {X Y : Cᵒᵖ} (f : X ⟶ Y) : A.Total X →+* A.Total Y where
  toFun := A.totalRestrict f
  map_one' := A.totalRestrict_one f
  map_mul' := A.totalRestrict_mul f
  map_zero' := map_zero _
  map_add' := map_add _

/-- The ring homomorphism `totalRestrictRingHom f` agrees with `totalRestrict f`. -/
@[simp]
lemma totalRestrictRingHom_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : A.Total X) :
    A.totalRestrictRingHom f a = A.totalRestrict f a := rfl

/-- **The ungraded realization of a graded algebra of presheaves of modules**, as a presheaf of
rings: over each object of the site its sections are the direct sum of the homogeneous
components, multiplied by the graded multiplication. -/
noncomputable def totalPresheaf : Cᵒᵖ ⥤ RingCat.{w} where
  obj X := RingCat.of (A.Total X)
  map f := RingCat.ofHom (A.totalRestrictRingHom f)
  map_id X := by
    refine RingCat.hom_ext (RingHom.ext fun a => ?_)
    change A.totalRestrict (𝟙 X) a = a
    induction a using A.incl_induction with
    | zero => simp
    | incl i y => rw [A.totalRestrict_incl, sectionRestrict_id]
    | add a a' ha ha' => rw [map_add, ha, ha']
  map_comp {X Y Z} f g := by
    refine RingCat.hom_ext (RingHom.ext fun a => ?_)
    change A.totalRestrict (f ≫ g) a = A.totalRestrict g (A.totalRestrict f a)
    induction a using A.incl_induction with
    | zero => simp
    | incl i y =>
      rw [A.totalRestrict_incl, A.totalRestrict_incl, A.totalRestrict_incl, sectionRestrict_comp]
    | add a a' ha ha' => rw [map_add, map_add, map_add, ha, ha']

/-! ### The structure map

The base ring maps into the ungraded realization by `r ↦ r • 1`, and its image is central. Both
facts hold for an arbitrary, not necessarily commutative, `R`: they come from the two separate
scalar laws of a `BilinearMap`, not from commutativity of `R`. -/

/-- The structure map of the ungraded realization, `r ↦ r • 1`. -/
noncomputable def structureMap (X : Cᵒᵖ) : R.obj X →+* A.Total X where
  toFun r := r • (1 : A.Total X)
  map_one' := one_smul _ _
  map_mul' r s := by rw [A.smul_mul_eq, _root_.one_mul, smul_smul]
  map_zero' := zero_smul _ _
  map_add' r s := add_smul r s _

/-- The image of the structure map is central. -/
lemma structureMap_commutes (X : Cᵒᵖ) (r : R.obj X) (a : A.Total X) :
    A.structureMap X r * a = a * A.structureMap X r := by
  change r • (1 : A.Total X) * a = a * r • (1 : A.Total X)
  rw [A.smul_mul_eq, _root_.one_mul, A.mul_smul_eq, _root_.mul_one]

/-- The structure map is compatible with restriction. -/
lemma structureMap_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) :
    A.totalRestrict f (A.structureMap X r) = A.structureMap Y (R.map f r) := by
  change A.totalRestrict f (r • (1 : A.Total X)) = R.map f r • (1 : A.Total Y)
  rw [A.totalRestrict_smul, A.totalRestrict_one]

end GradedAlgebra

end GradedAlgebra

end Stacks

namespace SheafOfModules

open CategoryTheory

universe t' a' v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t'}}

/-- A sheaf of graded algebras read as a graded algebra of presheaves of modules, so that the
ungraded realization applies to it. The multiplication, unit and laws are the same data: only
the sheaf conditions on the pieces are forgotten, and they play no part in the realization. -/
def GradedAlgebra.toPresheafGradedAlgebra (A : GradedAlgebra.{t', a'} R) :
    Stacks.GradedAlgebra fun i : ℤ => (A.piece i).val where
  mul := A.mul
  one := A.one
  mul_assoc := A.mul_assoc
  one_mul := A.one_mul
  mul_one := A.mul_one

end SheafOfModules
