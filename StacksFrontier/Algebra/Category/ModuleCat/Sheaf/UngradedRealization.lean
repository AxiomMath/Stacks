module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksCore.Tactic.StacksAttribute

/-!
# The ungraded realization of a sheaf of graded algebras, as a sheaf of rings

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of graded `R`-algebras, as
in `SheafOfModules.GradedAlgebra`. Stacks Section 17.21 passes from such a graded object to the
*ungraded* sheaf of rings it presents. `StacksDraft.Algebra.Category.ModuleCat.Sheaf.
UngradedAlgebras` carries that passage out at the presheaf level: `Stacks.GradedAlgebra.Total` is
the direct sum of the homogeneous components over an object of the site and
`Stacks.GradedAlgebra.totalPresheaf` is the resulting *presheaf* of rings. That presheaf is in
general not a sheaf — an infinite direct sum of sheaves is only a presheaf, since a section with
locally finite support need not have globally finite support — so the ungraded realization as a
*sheaf* of rings is its sheafification. This file takes that step and transports the structure
map along it.

## Main definitions

* `Stacks.GradedAlgebra.totalSheaf`: **the ungraded realization of a graded algebra of presheaves
  of modules, as a sheaf of rings** — the sheafification of `totalPresheaf`.
* `Stacks.GradedAlgebra.toTotalSheaf` and `totalUnit`: the sheafification unit, and its value
  over an object of the site as a ring homomorphism out of `Total`.
* `Stacks.GradedAlgebra.inclSheaf`: a homogeneous local section, viewed in the ungraded ring
  sheaf.
* `Stacks.GradedAlgebra.structureHom`, `structureSheafHom` and `structureSheafMap`: the structure
  map `r ↦ r • 1` of the realization, as a morphism of presheaves of rings into `totalPresheaf`,
  into `totalSheaf`, and over a single object of the site.
* `Stacks.GradedAlgebra.totalSheafLift`: the morphism out of `totalSheaf` determined by a
  morphism of presheaves of rings out of `totalPresheaf` into a sheaf of rings.
* `SheafOfModules.GradedAlgebra.ungradedSheaf` and `ungradedStructureMap`: the same realization
  for a sheaf of graded algebras, with the structure map read as a morphism of *sheaves* of
  rings `R ⟶ ungradedSheaf`.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.tensorRingSheaf`, `exteriorRingSheaf` and
  `symmetricRingSheaf`: the three ungraded sheaves of rings of Section 17.21, obtained by
  instantiating the above at the three graded algebras of a bundle, each with its structure map
  `tensorRingStructureMap`, `exteriorRingStructureMap`, `symmetricRingStructureMap`.

## Main results

* `Stacks.GradedAlgebra.inclSheaf_mul` and `inclSheaf_one`: the multiplication and unit of the
  ungraded ring sheaf agree with the graded multiplication and the graded unit on homogeneous
  local sections.
* `Stacks.GradedAlgebra.structureSheafMap_commutes`: **the image of the structure map of the
  ungraded ring sheaf is central.** This is not inherited from the presheaf statement
  `Stacks.GradedAlgebra.structureMap_commutes`: a section of the sheafification is only locally
  the image of a section of `totalPresheaf`, so the proof restricts to a covering sieve of local
  lifts and appeals to separatedness of the target.
* `Stacks.GradedAlgebra.mul_comm_totalSheaf`: if the realization is commutative on sections of
  the presheaf then it is commutative on sections of the sheaf. Here *two* sections must be
  lifted at once, so the covering sieve is the intersection of two sieves of local lifts.
* **The three hypotheses of this file hold on the site of opens of a topological space**, which
  is the setting Section 17.21 works in, so nothing below is vacuous: there Mathlib's instances
  supply `HasSheafify`, `WEqualsLocallyBijective` and `HasSheafCompose (forget RingCat)`.
* `SheafOfModules.sectionwiseTensorRingSheaf`, `sectionwiseExteriorRingSheaf` and
  `sectionwiseSymmetricRingSheaf`, with their three structure maps: the whole development
  instantiated at the bundle `SheafOfModules.tensorExteriorSymmetricAlgebras`, so the
  bundle hypothesis is witnessed in this file rather than assumed.

## Implementation notes

**The sheafification hypotheses are hypotheses, not a narrowing.** Sheafification of
`RingCat`-valued presheaves is not available on an arbitrary site: the concrete-category instance
`CategoryTheory.hasSheafify` of `Mathlib/CategoryTheory/Sites/LeftExact.lean` needs the covers of
`J` to be small relative to the ring universe. This file therefore carries
`[HasSheafify J RingCat.{w}]`, and — for separatedness of the target, which is what
`CategoryTheory.Sheaf.isSeparated` needs — `[J.HasSheafCompose (CategoryTheory.forget RingCat)]`,
and `[J.WEqualsLocallyBijective RingCat.{w}]`, which is what makes the sheafification unit locally
bijective and hence lets a section of the sheafification be lifted locally. All three are instance
hypotheses in exactly the style of the `[J.HasSheafCompose (forget₂ CommRingCat RingCat)]`,
`[J.WEqualsLocallyBijective AddCommGrpCat.{w}]` and `[HasWeakSheafify J AddCommGrpCat.{w}]` that
`TensorExteriorSymmetricAlgebras` already carries, and all three are discharged on the site of
opens of a topological space by Mathlib's instances, which instance search finds there.

**Universes.** `totalSheaf` and everything about the sheafification unit are stated with the ring
universe `t` of the base presheaf independent of the module universe `w`, as in `UngradedAlgebras`.
The structure map is not: `structureHom` is a morphism of presheaves of `RingCat`-valued functors
from `R` into `totalPresheaf`, and `totalPresheaf` is `RingCat.{w}`-valued, so `R` must be too.
That is forced by what the structure map *is*, not chosen — the underlying ring homomorphism
`Stacks.GradedAlgebra.structureMap` is already universe-heterogeneous and is used unchanged. The
index type of a `Stacks.GradedAlgebra` is in `Type 0`, which is the restriction documented in
`UngradedAlgebras`; `ℤ`, the index of a `SheafOfModules.GradedAlgebra`, is in `Type 0`.

**The defeq-spelling discipline.** `((toTotalSheaf J).app X).hom` has source type
`↑(A.totalPresheaf.obj X)`, which is `A.Total X` up to unfolding but not syntactically it, and
`rw` with any lemma mentioning a section of `A.Total X` fails against it with a type-correctness
error at `implicit` transparency. Every use of the unit here therefore goes through `totalUnit`,
`totalSheafRestrict` and `structureSheafMap`, whose *ascribed* types are the folded ones, and the
leaf identities are proved by `:=` or `exact`, which are defeq-tolerant. The same applies to a
local lift obtained from `Presheaf.imageSieve`: it is rebound at the ascribed type before any
rewriting.

**What is here and what is not.** This file produces the ungraded sheaf of rings and its central
structure map. It does **not** identify the underlying sheaf of modules of `totalSheaf` with the
sheaf coproduct `∐ (A.piece ·)`, and it does not prove that the ungraded tensor, exterior and
symmetric ring sheaves satisfy the corresponding *ungraded* universal properties, nor that the
symmetric one is commutative — commutativity of `symmetricRingSheaf` needs the symmetric algebra
to be generated in degree one, which does not follow from the graded universal property alone.
`mul_comm_totalSheaf` is the transfer step that such a proof would end with.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe v u t w

namespace Stacks.GradedAlgebra

section Realization

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)
  (J : GrothendieckTopology C) [HasSheafify J RingCat.{w}]

/-- **The ungraded realization of a graded algebra of presheaves of modules, as a sheaf of
rings**: the sheafification of the presheaf of rings `Stacks.GradedAlgebra.totalPresheaf`. -/
noncomputable def totalSheaf : Sheaf J RingCat.{w} :=
  (presheafToSheaf J RingCat.{w}).obj A.totalPresheaf

/-- The sheafification unit of the ungraded realization. -/
noncomputable def toTotalSheaf : A.totalPresheaf ⟶ (A.totalSheaf J).obj :=
  toSheafify J A.totalPresheaf

/-- The sheafification unit over an object of the site, as a ring homomorphism whose source type
is written as `A.Total X` rather than as the sections of `A.totalPresheaf`. -/
noncomputable def totalUnit (X : Cᵒᵖ) : A.Total X →+* (A.totalSheaf J).obj.obj X :=
  ((A.toTotalSheaf J).app X).hom

/-- The restriction map of the ungraded ring sheaf, as a ring homomorphism whose source and
target types are written as sections of `A.totalSheaf J`. -/
noncomputable def totalSheafRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (A.totalSheaf J).obj.obj X →+* (A.totalSheaf J).obj.obj Y :=
  ((A.totalSheaf J).obj.map f).hom

/-- The sheafification unit `Stacks.GradedAlgebra.totalUnit` commutes with restriction. -/
lemma totalUnit_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : A.Total X) :
    A.totalSheafRestrict J f (A.totalUnit J X a) = A.totalUnit J Y (A.totalRestrict f a) :=
  (NatTrans.naturality_apply (A.toTotalSheaf J) f a).symm

/-- A homogeneous local section, viewed in the ungraded ring sheaf. -/
noncomputable def inclSheaf {X : Cᵒᵖ} (i : ι) (x : (P i).obj X) :
    (A.totalSheaf J).obj.obj X :=
  A.totalUnit J X (A.incl i x)

/-- The multiplication of the ungraded ring sheaf agrees with the graded multiplication on
homogeneous local sections. -/
lemma inclSheaf_mul {X : Cᵒᵖ} (i j : ι) (x : (P i).obj X) (y : (P j).obj X) :
    A.inclSheaf J i x * A.inclSheaf J j y =
      A.inclSheaf J (i + j) ((A.mul i j).app X x y) := by
  rw [inclSheaf, inclSheaf, inclSheaf, ← map_mul, A.incl_mul_incl]

/-- The unit of the ungraded ring sheaf is the image of the graded unit. -/
lemma inclSheaf_one (X : Cᵒᵖ) :
    A.inclSheaf J 0 (A.one.eval X) = (1 : (A.totalSheaf J).obj.obj X) := by
  rw [inclSheaf, ← A.one_eq_incl, map_one]

/-- The zero homogeneous section is zero in the ungraded ring sheaf. -/
@[simp]
lemma inclSheaf_zero {X : Cᵒᵖ} (i : ι) :
    A.inclSheaf J i (0 : (P i).obj X) = 0 := by
  rw [inclSheaf, A.incl_zero, map_zero]

/-- `Stacks.GradedAlgebra.inclSheaf` is additive in the homogeneous section. -/
lemma inclSheaf_add {X : Cᵒᵖ} (i : ι) (x y : (P i).obj X) :
    A.inclSheaf J i (x + y) = A.inclSheaf J i x + A.inclSheaf J i y := by
  rw [inclSheaf, inclSheaf, inclSheaf, A.incl_add, map_add]

/-- Restriction of a homogeneous local section of the ungraded ring sheaf. -/
lemma totalSheafRestrict_inclSheaf {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : ι) (x : (P i).obj X) :
    A.totalSheafRestrict J f (A.inclSheaf J i x) =
      A.inclSheaf J i (sectionRestrict (P i) f x) := by
  rw [inclSheaf, A.totalUnit_naturality, A.totalRestrict_incl, inclSheaf]

/-- The morphism out of the ungraded ring sheaf determined by a morphism of presheaves of rings
out of `totalPresheaf` into a sheaf of rings. -/
noncomputable def totalSheafLift (S : Sheaf J RingCat.{w}) (φ : A.totalPresheaf ⟶ S.obj) :
    A.totalSheaf J ⟶ S :=
  ObjectProperty.homMk (sheafifyLift J φ S.property)

/-- The lift `Stacks.GradedAlgebra.totalSheafLift` composed with the sheafification unit is the
given morphism of presheaves of rings. -/
@[simp]
lemma toTotalSheaf_totalSheafLift (S : Sheaf J RingCat.{w}) (φ : A.totalPresheaf ⟶ S.obj) :
    A.toTotalSheaf J ≫ (A.totalSheafLift J S φ).hom = φ :=
  toSheafify_sheafifyLift J φ S.property

section LocallyBijective

variable [J.WEqualsLocallyBijective RingCat.{w}]

/-- The sheafification unit of the ungraded realization is locally surjective. -/
instance : Presheaf.IsLocallySurjective J (A.toTotalSheaf J) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (toSheafify J A.totalPresheaf))

/-- The sheafification unit of the ungraded realization is locally injective. -/
instance : Presheaf.IsLocallyInjective J (A.toTotalSheaf J) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J A.totalPresheaf))

end LocallyBijective

/-- A section in the image sieve of the sheafification unit is the unit applied to a section of
`A.Total`, after restriction. -/
private theorem exists_totalUnit_eq_restrict {X : Cᵒᵖ} {t : (A.totalSheaf J).obj.obj X} {Y : C}
    {f : Y ⟶ X.unop} (hf : Presheaf.imageSieve (A.toTotalSheaf J) t f) :
    ∃ t₀ : A.Total (op Y), A.totalUnit J (op Y) t₀ = A.totalSheafRestrict J f.op t := hf

end Realization

section StructureMap

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)
  (J : GrothendieckTopology C) [HasSheafify J RingCat.{w}]

/-- The structure map `r ↦ r • 1` of the ungraded realization, as a morphism of presheaves of
rings. -/
noncomputable def structureHom : R ⟶ A.totalPresheaf where
  app X := RingCat.ofHom (A.structureMap X)
  naturality _ _ f :=
    RingCat.hom_ext (RingHom.ext fun r => (A.structureMap_naturality f r).symm)

/-- The structure map of the ungraded ring sheaf, as a morphism of presheaves of rings. -/
noncomputable def structureSheafHom : R ⟶ (A.totalSheaf J).obj :=
  A.structureHom ≫ A.toTotalSheaf J

/-- The structure map of the ungraded ring sheaf over an object of the site. -/
noncomputable def structureSheafMap (X : Cᵒᵖ) : R.obj X →+* (A.totalSheaf J).obj.obj X :=
  ((A.structureSheafHom J).app X).hom

/-- The structure map of the ungraded ring sheaf is the sheafification unit applied to the
structure map of the presheaf. -/
lemma structureSheafMap_eq (X : Cᵒᵖ) (r : R.obj X) :
    A.structureSheafMap J X r = A.totalUnit J X (A.structureMap X r) := rfl

/-- The structure map of the ungraded ring sheaf commutes with restriction. -/
lemma structureSheafMap_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) :
    A.totalSheafRestrict J f (A.structureSheafMap J X r) =
      A.structureSheafMap J Y ((R.map f).hom r) :=
  (NatTrans.naturality_apply (A.structureSheafHom J) f r).symm

variable [J.WEqualsLocallyBijective RingCat.{w}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- **The image of the structure map of the ungraded ring sheaf is central.**

This does not follow from the presheaf statement `Stacks.GradedAlgebra.structureMap_commutes` by
functoriality: a section of the sheafification is only *locally* the image of a section of
`totalPresheaf`. The proof restricts to the covering sieve of local lifts and uses that the
target is separated. -/
lemma structureSheafMap_commutes (X : Cᵒᵖ) (r : R.obj X) (t : (A.totalSheaf J).obj.obj X) :
    A.structureSheafMap J X r * t = t * A.structureSheafMap J X r := by
  refine (A.totalSheaf J).isSeparated _ _
    (Presheaf.imageSieve_mem J (A.toTotalSheaf J) t) _ _ fun Y f hf => ?_
  obtain ⟨t₀, ht₀⟩ := A.exists_totalUnit_eq_restrict J hf
  show A.totalSheafRestrict J f.op (A.structureSheafMap J X r * t) =
    A.totalSheafRestrict J f.op (t * A.structureSheafMap J X r)
  rw [map_mul, map_mul, ← ht₀, A.structureSheafMap_naturality, A.structureSheafMap_eq,
    ← map_mul, ← map_mul, A.structureMap_commutes]

end StructureMap

section Commutativity

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)
  (J : GrothendieckTopology C) [HasSheafify J RingCat.{w}]
  [J.WEqualsLocallyBijective RingCat.{w}] [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- **Commutativity of the ungraded realization passes from the presheaf to the sheaf.** Two
sections of the sheafification must be lifted at once, so the covering sieve used here is the
intersection of the two sieves of local lifts. -/
lemma mul_comm_totalSheaf (h : ∀ (X : Cᵒᵖ) (a b : A.Total X), a * b = b * a) (X : Cᵒᵖ)
    (s t : (A.totalSheaf J).obj.obj X) : s * t = t * s := by
  refine (A.totalSheaf J).isSeparated _ _
    (J.intersection_covering (Presheaf.imageSieve_mem J (A.toTotalSheaf J) s)
      (Presheaf.imageSieve_mem J (A.toTotalSheaf J) t)) _ _ fun Y f hf => ?_
  obtain ⟨s₀, hs₀⟩ := A.exists_totalUnit_eq_restrict J hf.1
  obtain ⟨t₀, ht₀⟩ := A.exists_totalUnit_eq_restrict J hf.2
  show A.totalSheafRestrict J f.op (s * t) = A.totalSheafRestrict J f.op (t * s)
  rw [map_mul, map_mul, ← hs₀, ← ht₀, ← map_mul, ← map_mul, h (op Y) s₀ t₀]

end Commutativity

end Stacks.GradedAlgebra

namespace SheafOfModules

section Ungraded

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J RingCat.{w}]

/-- **The ungraded realization of a sheaf of graded algebras, as a sheaf of rings.** -/
noncomputable def GradedAlgebra.ungradedSheaf (A : GradedAlgebra.{w, w} R) :
    Sheaf J RingCat.{w} :=
  A.toPresheafGradedAlgebra.totalSheaf J

/-- A homogeneous local section of a sheaf of graded algebras, viewed in its ungraded
realization. -/
noncomputable def GradedAlgebra.ungradedIncl (A : GradedAlgebra.{w, w} R) {X : Cᵒᵖ} (i : ℤ)
    (x : (A.piece i).val.obj X) : A.ungradedSheaf.obj.obj X :=
  A.toPresheafGradedAlgebra.inclSheaf J i x

/-- The multiplication of the ungraded realization agrees with the graded multiplication on
homogeneous local sections. -/
lemma GradedAlgebra.ungradedIncl_mul (A : GradedAlgebra.{w, w} R) {X : Cᵒᵖ} (i j : ℤ)
    (x : (A.piece i).val.obj X) (y : (A.piece j).val.obj X) :
    A.ungradedIncl i x * A.ungradedIncl j y =
      A.ungradedIncl (i + j) ((A.mul i j).app X x y) :=
  A.toPresheafGradedAlgebra.inclSheaf_mul J i j x y

/-- The unit of the ungraded realization is the image of the graded unit. -/
lemma GradedAlgebra.ungradedIncl_one (A : GradedAlgebra.{w, w} R) (X : Cᵒᵖ) :
    A.ungradedIncl 0 (A.one.eval X) = (1 : A.ungradedSheaf.obj.obj X) :=
  A.toPresheafGradedAlgebra.inclSheaf_one J X

/-- **The structure map of the ungraded realization, as a morphism of sheaves of rings.** -/
noncomputable def GradedAlgebra.ungradedStructureMap (A : GradedAlgebra.{w, w} R) :
    R ⟶ A.ungradedSheaf :=
  ObjectProperty.homMk (A.toPresheafGradedAlgebra.structureSheafHom J)

variable [J.WEqualsLocallyBijective RingCat.{w}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- The image of the structure map of the ungraded realization of a sheaf of graded algebras is
central. -/
lemma GradedAlgebra.ungradedStructureMap_commutes (A : GradedAlgebra.{w, w} R) (X : Cᵒᵖ)
    (r : R.obj.obj X) (a : A.ungradedSheaf.obj.obj X) :
    (A.ungradedStructureMap.hom.app X).hom r * a =
      a * (A.ungradedStructureMap.hom.app X).hom r :=
  A.toPresheafGradedAlgebra.structureSheafMap_commutes J X r a

end Ungraded

namespace TensorExteriorSymmetricAlgebras

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J RingCat.{w}]
  {F : SheafOfModules.{w} (toRingCat J Osharp)} (A : TensorExteriorSymmetricAlgebras J F)

/-- **The ungraded tensor algebra of a sheaf of modules, as a sheaf of rings.** -/
noncomputable def tensorRingSheaf : Sheaf J RingCat.{w} := A.tensor.ungradedSheaf

/-- **The ungraded exterior algebra of a sheaf of modules, as a sheaf of rings.** -/
noncomputable def exteriorRingSheaf : Sheaf J RingCat.{w} := A.exterior.ungradedSheaf

/-- **The ungraded symmetric algebra of a sheaf of modules, as a sheaf of rings.** -/
noncomputable def symmetricRingSheaf : Sheaf J RingCat.{w} := A.symmetric.ungradedSheaf

/-- The structure map of the ungraded tensor algebra. -/
noncomputable def tensorRingStructureMap : toRingCat J Osharp ⟶ A.tensorRingSheaf :=
  A.tensor.ungradedStructureMap

/-- The structure map of the ungraded exterior algebra. -/
noncomputable def exteriorRingStructureMap : toRingCat J Osharp ⟶ A.exteriorRingSheaf :=
  A.exterior.ungradedStructureMap

/-- The structure map of the ungraded symmetric algebra. -/
noncomputable def symmetricRingStructureMap : toRingCat J Osharp ⟶ A.symmetricRingSheaf :=
  A.symmetric.ungradedStructureMap

/-- The degree-one generator of the ungraded tensor algebra: a local section of `F`, viewed in
the ungraded tensor ring sheaf. -/
noncomputable def tensorRingGen {X : Cᵒᵖ} (s : F.val.obj X) : A.tensorRingSheaf.obj.obj X :=
  A.tensor.ungradedIncl 1 (A.tensorGenerator.val.app X s)

/-- The degree-one generator of the ungraded exterior algebra. -/
noncomputable def exteriorRingGen {X : Cᵒᵖ} (s : F.val.obj X) : A.exteriorRingSheaf.obj.obj X :=
  A.exterior.ungradedIncl 1 (A.exteriorGenerator.val.app X s)

/-- The degree-one generator of the ungraded symmetric algebra. -/
noncomputable def symmetricRingGen {X : Cᵒᵖ} (s : F.val.obj X) : A.symmetricRingSheaf.obj.obj X :=
  A.symmetric.ungradedIncl 1 (A.symmetricGenerator.val.app X s)

/-- The product of two degree-one generators of the ungraded tensor algebra is the image of their
graded product. -/
lemma tensorRingGen_mul {X : Cᵒᵖ} (s t : F.val.obj X) :
    A.tensorRingGen s * A.tensorRingGen t =
      A.tensor.ungradedIncl (1 + 1)
        ((A.tensor.mul 1 1).app X (A.tensorGenerator.val.app X s)
          (A.tensorGenerator.val.app X t)) :=
  A.tensor.ungradedIncl_mul 1 1 _ _

/-- The product of two degree-one generators of the ungraded exterior algebra. -/
lemma exteriorRingGen_mul {X : Cᵒᵖ} (s t : F.val.obj X) :
    A.exteriorRingGen s * A.exteriorRingGen t =
      A.exterior.ungradedIncl (1 + 1)
        ((A.exterior.mul 1 1).app X (A.exteriorGenerator.val.app X s)
          (A.exteriorGenerator.val.app X t)) :=
  A.exterior.ungradedIncl_mul 1 1 _ _

/-- The product of two degree-one generators of the ungraded symmetric algebra. -/
lemma symmetricRingGen_mul {X : Cᵒᵖ} (s t : F.val.obj X) :
    A.symmetricRingGen s * A.symmetricRingGen t =
      A.symmetric.ungradedIncl (1 + 1)
        ((A.symmetric.mul 1 1).app X (A.symmetricGenerator.val.app X s)
          (A.symmetricGenerator.val.app X t)) :=
  A.symmetric.ungradedIncl_mul 1 1 _ _

end TensorExteriorSymmetricAlgebras

section Inhabitant

open CategoryTheory.Sheaf PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (toRingCatMap J a)]
  [Presheaf.IsLocallySurjective J (toRingCatMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [HasSheafify J RingCat.{w}]
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat))

/-- **The ungraded tensor algebra of the sheafification of a presheaf of modules, as a sheaf of
rings.** This instantiates `TensorExteriorSymmetricAlgebras.tensorRingSheaf` at the
bundle `SheafOfModules.tensorExteriorSymmetricAlgebras`, which is what shows the hypothesis of
the previous section to be satisfiable rather than vacuous. -/
noncomputable def sectionwiseTensorRingSheaf : Sheaf J RingCat.{w} :=
  (tensorExteriorSymmetricAlgebras J a F).tensorRingSheaf

/-- The ungraded exterior algebra of the sheafification of a presheaf of modules, as a sheaf of
rings. -/
noncomputable def sectionwiseExteriorRingSheaf : Sheaf J RingCat.{w} :=
  (tensorExteriorSymmetricAlgebras J a F).exteriorRingSheaf

/-- The ungraded symmetric algebra of the sheafification of a presheaf of modules, as a sheaf of
rings. -/
noncomputable def sectionwiseSymmetricRingSheaf : Sheaf J RingCat.{w} :=
  (tensorExteriorSymmetricAlgebras J a F).symmetricRingSheaf

/-- The structure map of the ungraded tensor algebra of the sheafification of a presheaf of
modules. -/
noncomputable def sectionwiseTensorRingStructureMap :
    toRingCat J Osharp ⟶ sectionwiseTensorRingSheaf J a F :=
  (tensorExteriorSymmetricAlgebras J a F).tensorRingStructureMap

/-- The structure map of the ungraded exterior algebra of the sheafification of a presheaf of
modules. -/
noncomputable def sectionwiseExteriorRingStructureMap :
    toRingCat J Osharp ⟶ sectionwiseExteriorRingSheaf J a F :=
  (tensorExteriorSymmetricAlgebras J a F).exteriorRingStructureMap

/-- The structure map of the ungraded symmetric algebra of the sheafification of a presheaf of
modules. -/
noncomputable def sectionwiseSymmetricRingStructureMap :
    toRingCat J Osharp ⟶ sectionwiseSymmetricRingSheaf J a F :=
  (tensorExteriorSymmetricAlgebras J a F).symmetricRingStructureMap

end Inhabitant

end SheafOfModules

end
