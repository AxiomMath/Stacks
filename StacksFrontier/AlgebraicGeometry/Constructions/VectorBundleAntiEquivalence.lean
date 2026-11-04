module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafModuleFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEquivalence
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.UngradedFunctorial
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct image of a cone is the ungraded realization of its grading

Let `S` be a scheme and `π : C ⟶ S` a cone over `S` in the sense of Tag 062R: an affine morphism
together with a nonnegative grading of `π_* 𝒪_C` whose degree-zero piece is `𝒪_S`. The two
decomposition axioms of a cone say exactly that the sheaf of rings `π_* 𝒪_C` is the ungraded
realization of the sheaf of graded algebras that grades it, i.e. the sheafification in `RingCat`
of `U ↦ ⨁_n ℰ_n(U)`. This file proves that, and draws the consequence that a unital homomorphism
of the gradings of two cones comes from a morphism of cones, which is the **fullness** clause of
Tag 062N.

The passage is the one `StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEquivalence`
carries out on *modules* — there `π_* 𝒪_C` is identified with the coproduct of the homogeneous
pieces — done instead on *rings*: the inclusions `ℰ_n ⟶ π_* 𝒪_C` of a cone assemble into a
morphism of presheaves of rings out of `⨁_n ℰ_n` precisely because of the axioms `ι_mul` and
`ι_zero`, and `decomposition_unique` and `decomposition_locally` make it locally bijective.

## Main definitions

* `Stacks.GradedAlgebra.totalPresheafDesc` is the morphism of presheaves of rings out of the
  ungraded realization of a graded algebra determined by a natural additive map on each
  homogeneous component which turns the graded multiplication and unit into those of the target,
  and `Stacks.GradedAlgebra.totalRingMap` is the morphism of presheaves of rings between two
  ungraded realizations induced by a unital homomorphism.
* `Stacks.RelativeSpec.AlgebraSheaf.homOfRingSheafHom` reads a morphism of the underlying sheaves
  of rings of two algebra sheaves which commutes with their structure morphisms as a morphism of
  algebra sheaves.
* `AlgebraicGeometry.AbstractCone.totalPresheafHom` is the morphism of presheaves of rings from
  the ungraded realization of the grading of a cone into `π_* 𝒪_C`, and
  `AlgebraicGeometry.AbstractCone.ringSheafIso` is the resulting identification of `π_* 𝒪_C` with
  that realization as a sheaf of rings.
* `AlgebraicGeometry.AbstractCone.gradedPullbackRingHom`,
  `AlgebraicGeometry.AbstractCone.gradedPullbackAlgebraMap` and
  `AlgebraicGeometry.AbstractCone.gradedPullbackOverHom` are the morphism of direct images, of
  sheaves of `𝒪_S`-algebras and of total spaces over `S` induced by a unital homomorphism of the
  gradings of two cones.
* `AlgebraicGeometry.AbstractCone.homOfGradedUnitalHom` is the resulting morphism of cones.

## Main results

* `AlgebraicGeometry.AbstractCone.isIso_ringSheafHom`: **the direct image `π_* 𝒪_C` of a cone is
  the ungraded realization of its grading.**
* `AlgebraicGeometry.AbstractCone.ungradedStructureMap_comp_ringSheafHom`: that identification is
  one of sheaves of `𝒪_S`-algebras, the structure map `r ↦ r • 1` of the realization being the
  pullback of functions along `π`.
* `AlgebraicGeometry.AbstractCone.gradedPullbackRingHom_ι`: the induced morphism of direct images
  realizes the given homomorphism on every homogeneous piece, which is what makes
  `AlgebraicGeometry.AbstractCone.homOfGradedUnitalHom` a morphism of cones with the given graded
  part.
* `AlgebraicGeometry.VectorBundle.full_degreeOneModules` and
  `AlgebraicGeometry.VectorBundle.full_degreeOneFunctor`: **the functor `V ↦ ℰ_1` is full**, which
  is the fullness clause of Tag 062N.

## Implementation notes

### Why the identification is made in `RingCat` and not in `CommRingCat`

`AlgebraicGeometry.AbstractCone` does not record commutativity of its homogeneous
multiplication: it follows from `ι_mul` and the injectivity of the inclusions on sections, but
only as a heterogeneous equality between the two degrees `i + j` and `j + i`. The ungraded
realization in `CommRingCat`, `Stacks.RelativeSpec.ungradedAlgebraSheaf`, takes that heterogeneous
commutativity as an argument, whereas `SheafOfModules.GradedAlgebra.ungradedSheaf` — the
sheafification in `RingCat` — takes nothing. Everything here is therefore done with the latter,
and a morphism of sheaves of commutative rings is recovered from a morphism of the underlying
sheaves of rings by `Stacks.RelativeSpec.AlgebraSheaf.homOfRingSheafHom`, a ring homomorphism
between commutative rings being a homomorphism of commutative rings.

### How fullness is proved

A morphism `g : ℰ_1 ⟶ ℱ_1` extends to a unital homomorphism `ψ` of the direct-image algebras by
the universal property of the symmetric algebra, `AlgebraicGeometry.VectorBundle`
`.isSymmetricAlgebra`. The identification above turns `ψ` into a morphism of the sheaves of rings
`π_* 𝒪_V ⟶ π_* 𝒪_W`: the realization of the source is identified with `π_* 𝒪_V`, and the
realization of `ψ` followed by the realization of the target is a morphism out of the source's
realization. It is a morphism over `𝒪_S` because `ψ` is unital, so
`Stacks.AffineAlgebraEquivalence.overHomEquivAlgebraHom` — the universal property of the relative
spectrum, available because the projection of a cone is affine — supplies a morphism of the total
spaces over `S`, and that morphism induces back the algebra morphism it came from. The three
remaining fields of a morphism of cones are then the given `ψ`, the underlying morphism of
`𝒪_S`-modules, and the identification of that morphism with the pullback of functions, which is
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_app`.

### What was open here, and where it went

Essential surjectivity is now proved and Tag 062N's anti-equivalence is assembled, in
`StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEssSurj`:
`AlgebraicGeometry.VectorBundle.essSurj_degreeOneFunctor'` and `degreeOneEquivalence`.

The obstruction this note identified was the right one and was decisive: the cone axiom
`decomposition_unique` needs the sum map injective over *every* open, not merely locally, and
the repository had only bijectivity of the sheafification unit over a quasi-compact object.
The resolution is that bijectivity is not what is needed -- it genuinely fails over a general
open, since sections of a sheafified direct sum need not be finitely supported, while
injectivity does not fail. It is now `Stacks.isSeparated_directSum_sheaves` and
`SheafOfModules.GradedAlgebra.injective_ungradedUnit` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated`, proved by component
extraction and separatedness of each piece, with no quasi-compactness.

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe w v u

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R} (A : GradedAlgebra P)
  {T : Cᵒᵖ ⥤ RingCat.{w}} (g : ∀ (i : ι) (U : Cᵒᵖ), (P i).obj U →+ T.obj U)

/-- The additive map out of the ungraded realization of a graded algebra determined by an
additive map on each homogeneous component. -/
def totalDescAddHom (U : Cᵒᵖ) : A.Total U →+ T.obj U :=
  DirectSum.toAddMonoid fun i => g i U

/-- The additive map `Stacks.GradedAlgebra.totalDescAddHom` sends a homogeneous section `x` of
degree `i` to its image under the given map in degree `i`. -/
@[simp] lemma totalDescAddHom_incl (U : Cᵒᵖ) (i : ι) (x : (P i).obj U) :
    A.totalDescAddHom g U (A.incl i x) = g i U x :=
  DirectSum.toAddMonoid_of _ _ _

variable (hmul : ∀ (i j : ι) (U : Cᵒᵖ) (x : (P i).obj U) (y : (P j).obj U),
    g (i + j) U ((A.mul i j).app U x y) = g i U x * g j U y)
  (hone : ∀ U : Cᵒᵖ, g 0 U (A.one.eval U) = 1)

include hmul in
/-- The additive map `Stacks.GradedAlgebra.totalDescAddHom` is multiplicative when the given
maps turn the graded multiplication into the multiplication of the target. -/
lemma totalDescAddHom_mul (U : Cᵒᵖ) (a b : A.Total U) :
    A.totalDescAddHom g U (a * b) =
      A.totalDescAddHom g U a * A.totalDescAddHom g U b := by
  induction a using A.incl_induction with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | incl i x =>
    induction b using A.incl_induction with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | incl j y =>
      rw [A.incl_mul_incl, totalDescAddHom_incl, totalDescAddHom_incl, totalDescAddHom_incl,
        hmul]
    | add b b' hb hb' => rw [mul_add, map_add, map_add, hb, hb', mul_add]
  | add a a' ha ha' => rw [add_mul, map_add, map_add, ha, ha', add_mul]

include hone in
/-- The additive map `Stacks.GradedAlgebra.totalDescAddHom` sends `1` to `1` when the given
map in degree `0` sends the graded unit to `1`. -/
lemma totalDescAddHom_one (U : Cᵒᵖ) : A.totalDescAddHom g U (1 : A.Total U) = 1 := by
  rw [A.one_eq_incl, totalDescAddHom_incl, hone]

/-- **The ring homomorphism out of the ungraded realization of a graded algebra** determined by
an additive map on each homogeneous component which turns the graded multiplication into the
multiplication of the target and the graded unit into its unit. -/
def totalDescRingHom (U : Cᵒᵖ) : A.Total U →+* T.obj U where
  toFun := A.totalDescAddHom g U
  map_zero' := map_zero _
  map_add' a b := map_add _ a b
  map_one' := A.totalDescAddHom_one g hone U
  map_mul' := A.totalDescAddHom_mul g hmul U

/-- The ring homomorphism `Stacks.GradedAlgebra.totalDescRingHom` sends a homogeneous section `x`
of degree `i` to its image under the given map in degree `i`. -/
@[simp] lemma totalDescRingHom_incl (U : Cᵒᵖ) (i : ι) (x : (P i).obj U) :
    A.totalDescRingHom g hmul hone U (A.incl i x) = g i U x :=
  A.totalDescAddHom_incl g U i x

variable (hnat : ∀ (U V : Cᵒᵖ) (f : U ⟶ V) (i : ι) (x : (P i).obj U),
    g i V (sectionRestrict (P i) f x) = (T.map f).hom (g i U x))

include hnat in
/-- **The morphism of presheaves of rings out of the ungraded realization of a graded algebra**
determined by a natural additive map on each homogeneous component which turns the graded
multiplication and unit into the multiplication and unit of the target. -/
def totalPresheafDesc : A.totalPresheaf ⟶ T where
  app U := RingCat.ofHom (A.totalDescRingHom g hmul hone U)
  naturality U V f := by
    refine RingCat.hom_ext (RingHom.ext fun a => ?_)
    change A.totalDescRingHom g hmul hone V (A.totalRestrict f a) =
      (T.map f).hom (A.totalDescRingHom g hmul hone U a)
    induction a using A.incl_induction with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | incl i x =>
      rw [A.totalRestrict_incl, totalDescRingHom_incl, totalDescRingHom_incl, hnat]
    | add a a' ha ha' =>
      rw [map_add, map_add, ha, ha', map_add]
      exact (map_add (T.map f).hom _ _).symm

/-- On sections over `U`, the morphism `Stacks.GradedAlgebra.totalPresheafDesc` sends a homogeneous
section `x` of degree `i` to its image under the given map in degree `i`. -/
@[simp] lemma totalPresheafDesc_app_incl (U : Cᵒᵖ) (i : ι) (x : (P i).obj U) :
    ((A.totalPresheafDesc g hmul hone hnat).app U).hom (A.incl i x) = g i U x :=
  A.totalDescAddHom_incl g U i x

end Stacks.GradedAlgebra

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddCommMonoid ι] {P Q : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P}
  {B : GradedAlgebra Q}

/-- **The morphism of presheaves of rings between the ungraded realizations of two graded
algebras induced by a unital homomorphism**, acting on a homogeneous local section by the
homomorphism in that degree. -/
def totalRingMap (φ : UnitalHom A B) : A.totalPresheaf ⟶ B.totalPresheaf where
  app U := RingCat.ofHom (totalMap φ U)
  naturality _ _ f := RingCat.hom_ext (RingHom.ext fun b => totalAddMap_totalRestrict φ f b)

/-- On sections over `U`, the morphism `Stacks.GradedAlgebra.totalRingMap φ` sends a homogeneous
section `x` of degree `i` to the homogeneous section of degree `i` given by `φ` applied to `x`. -/
@[simp] lemma totalRingMap_app_incl (φ : UnitalHom A B) (U : Cᵒᵖ) (i : ι) (x : (P i).obj U) :
    ((totalRingMap φ).app U).hom (A.incl i x) = B.incl i ((φ.app i).app U x) :=
  totalAddMap_incl φ U i x

/-- The ungraded realization of a unital homomorphism is a morphism over the base: it commutes
with the structure maps `r ↦ r • 1`. -/
lemma structureHom_comp_totalRingMap (φ : UnitalHom A B) :
    A.structureHom ≫ totalRingMap φ = B.structureHom :=
  NatTrans.ext (funext fun U =>
    RingCat.hom_ext (RingHom.ext fun r => totalAddMap_structureMap φ U r))

end Stacks.GradedAlgebra

namespace Stacks.RelativeSpec.AlgebraSheaf

open _root_.AlgebraicGeometry

/-- **A morphism of the underlying sheaves of rings of two algebra sheaves which commutes with
their structure morphisms is a morphism of algebra sheaves.** A ring homomorphism between
commutative rings is a homomorphism of commutative rings, so only the triangle over the
structure sheaf has to be supplied. -/
def homOfRingSheafHom {X : Scheme.{u}} (A B : AlgebraSheaf X) (f : ringSheaf A ⟶ ringSheaf B)
    (h : structureMap A ≫ f = structureMap B) : A ⟶ B :=
  Under.homMk
    (ObjectProperty.homMk
      { app := fun U => CommRingCat.ofHom (f.hom.app U).hom
        naturality := fun _ _ g => CommRingCat.hom_ext (RingHom.ext fun x =>
          congrArg (fun φ => RingCat.Hom.hom φ x) (f.hom.naturality g)) })
    (CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U =>
      CommRingCat.hom_ext (RingHom.ext fun r =>
        congrArg (fun φ : X.ringCatSheaf ⟶ ringSheaf B => (φ.hom.app U).hom r) h))))

/-- The morphism of underlying sheaves of rings of
`Stacks.RelativeSpec.AlgebraSheaf.homOfRingSheafHom A B f h` is `f`. -/
@[simp] theorem ringSheafMap_homOfRingSheafHom {X : Scheme.{u}} (A B : AlgebraSheaf X)
    (f : ringSheaf A ⟶ ringSheaf B) (h : structureMap A ≫ f = structureMap B) :
    ringSheafMap (homOfRingSheafHom A B f h) = f := rfl

end Stacks.RelativeSpec.AlgebraSheaf

namespace AlgebraicGeometry

namespace AbstractCone

variable {S : Scheme.{u}} (X : AbstractCone S)

/-- The sheaf of rings `π_* 𝒪_C` of a cone, as the target of the inclusions of the homogeneous
pieces. -/
abbrev ringSheaf : Sheaf (Opens.grothendieckTopology (S : TopCat)) RingCat.{u} :=
  AlgebraSheaf.ringSheaf (pushforwardAlgebra X.π)

/-- The inclusion of the homogeneous piece of degree `n` of a cone, as an additive map into the
sections of `π_* 𝒪_C` viewed as a ring. -/
def ιAddHom (n : ℤ) (U : (S.Opens)ᵒᵖ) :
    (X.grading.piece n).val.obj U →+ X.ringSheaf.obj.obj U :=
  AddMonoidHom.mk' (fun x => (X.ι n).val.app U x) fun x y => map_add _ x y

/-- **The ungraded realization of the grading of a cone maps into `π_* 𝒪_C`**, as a morphism of
presheaves of rings: a homogeneous local section goes to the function it is. -/
def totalPresheafHom :
    X.grading.toPresheafGradedAlgebra.totalPresheaf ⟶ X.ringSheaf.obj :=
  X.grading.toPresheafGradedAlgebra.totalPresheafDesc X.ιAddHom
    (fun i j U x y => X.ι_mul i j U.unop x y)
    (fun U => X.ι_zero_one U.unop)
    (fun _U _V f n x => PresheafOfModules.naturality_apply (X.ι n).val f x)

/-- The sum of a one-term family of homogeneous local sections is that section. -/
theorem pushforwardHomogeneousSum_incl (U : S.Opens) (n : ℤ)
    (x : (X.grading.piece n).val.obj (op U)) :
    pushforwardHomogeneousSum X.π X.grading X.ι U
        (X.grading.toPresheafGradedAlgebra.incl n x) =
      (X.ι n).val.app (op U) x :=
  (DFunLike.congr_fun (X.pushforwardHomogeneousSum_eq U)
      (X.grading.toPresheafGradedAlgebra.incl n x)).trans
    (congrArg (fun f : (X.grading.piece n).val ⟶
        (Stacks.Morphisms.pushforwardStructureSheaf X.π).val => f.app (op U) x)
      (X.inclHom_directSumHom n))

/-- The sum of a finitely supported family of homogeneous local sections, read through the
morphism of presheaves of rings `AlgebraicGeometry.AbstractCone.totalPresheafHom`. -/
theorem totalPresheafHom_app_apply (U : S.Opens)
    (a : X.grading.toPresheafGradedAlgebra.Total (op U)) :
    (X.totalPresheafHom.app (op U)).hom a =
      pushforwardHomogeneousSum X.π X.grading X.ι U a := by
  induction a using X.grading.toPresheafGradedAlgebra.incl_induction with
  | zero =>
    exact (map_zero (X.totalPresheafHom.app (op U)).hom).trans
      (map_zero (pushforwardHomogeneousSum X.π X.grading X.ι U)).symm
  | incl n x =>
    exact (X.grading.toPresheafGradedAlgebra.totalPresheafDesc_app_incl _ _ _ _ (op U) n x).trans
      (X.pushforwardHomogeneousSum_incl U n x).symm
  | add a a' ha ha' =>
    exact (map_add (X.totalPresheafHom.app (op U)).hom a a').trans
      ((congrArg₂ (fun u v => u + v) ha ha').trans
        (map_add (pushforwardHomogeneousSum X.π X.grading X.ι U) a a').symm)

/-- The ungraded realization of the grading of a cone is injective on sections into `π_* 𝒪_C`:
that is the uniqueness of a finite homogeneous decomposition. -/
theorem injective_totalPresheafHom_app (U : S.Opens) :
    Function.Injective (X.totalPresheafHom.app (op U)) := fun a b h =>
  X.decomposition_unique U
    ((X.totalPresheafHom_app_apply U a).symm.trans
      (h.trans (X.totalPresheafHom_app_apply U b)))

/-- The ungraded realization of the grading of a cone is locally injective into `π_* 𝒪_C`,
being injective. -/
theorem isLocallyInjective_totalPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (S : TopCat))
      X.totalPresheafHom :=
  Presheaf.isLocallyInjective_of_injective _ _ fun W => by
    induction W with
    | op U => exact X.injective_totalPresheafHom_app U

/-- The ungraded realization of the grading of a cone is locally surjective onto `π_* 𝒪_C`:
that is the local existence of a finite homogeneous decomposition. -/
theorem isLocallySurjective_totalPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (S : TopCat))
      X.totalPresheafHom where
  imageSieve_mem {U} a := fun x hx => by
    obtain ⟨V, hVU, hxV, s, hs⟩ := X.decomposition_locally U a x hx
    exact ⟨V, homOfLE hVU, ⟨s, (X.totalPresheafHom_app_apply V s).trans hs⟩, hxV⟩

/-- The lift of a morphism of presheaves of rings out of the ungraded realization of a grading
sends a homogeneous local section to the image of that section. -/
private theorem totalSheafLift_ungradedIncl (𝒜 : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)
    (T : Sheaf (Opens.grothendieckTopology (S : TopCat)) RingCat.{u})
    (k : 𝒜.toPresheafGradedAlgebra.totalPresheaf ⟶ T.obj) (n : ℤ) (U : S.Opens)
    (x : (𝒜.piece n).val.obj (op U)) :
    ((𝒜.toPresheafGradedAlgebra.totalSheafLift _ T k).hom.app (op U)).hom (𝒜.ungradedIncl n x) =
      (k.app (op U)).hom (𝒜.toPresheafGradedAlgebra.incl n x) :=
  congrArg (fun k' : 𝒜.toPresheafGradedAlgebra.totalPresheaf ⟶ T.obj =>
    (k'.app (op U)).hom (𝒜.toPresheafGradedAlgebra.incl n x))
    (Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift _ _ _ _)

/-- The lift of a morphism of presheaves of rings out of the ungraded realization of a grading is
a morphism over the structure sheaf as soon as the morphism is. -/
private theorem ungradedStructureMap_comp_totalSheafLift
    (𝒜 : SheafOfModules.GradedAlgebra.{u, u} S.ringCatSheaf)
    (T : Sheaf (Opens.grothendieckTopology (S : TopCat)) RingCat.{u})
    (k : 𝒜.toPresheafGradedAlgebra.totalPresheaf ⟶ T.obj) (t : S.ringCatSheaf ⟶ T)
    (h : 𝒜.toPresheafGradedAlgebra.structureHom ≫ k = t.hom) :
    𝒜.ungradedStructureMap ≫ 𝒜.toPresheafGradedAlgebra.totalSheafLift _ T k = t :=
  Sheaf.hom_ext
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k' => 𝒜.toPresheafGradedAlgebra.structureHom ≫ k')
          (Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift _ _ _ _)).trans h))

/-- **The ungraded realization of the grading of a cone, as a morphism of sheaves of rings into
`π_* 𝒪_C`.** -/
def ringSheafHom : X.grading.ungradedSheaf ⟶ X.ringSheaf :=
  X.grading.toPresheafGradedAlgebra.totalSheafLift _ X.ringSheaf X.totalPresheafHom

/-- The morphism `AlgebraicGeometry.AbstractCone.ringSheafHom` restricts, along the map from the
presheaf of rings to its sheafification, to `AlgebraicGeometry.AbstractCone.totalPresheafHom`. -/
theorem toTotalSheaf_comp_ringSheafHom :
    X.grading.toPresheafGradedAlgebra.toTotalSheaf (Opens.grothendieckTopology (S : TopCat)) ≫
        X.ringSheafHom.hom =
      X.totalPresheafHom :=
  Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift _ _ _ _

/-- The ungraded realization of the grading of a cone, as the sheafification of its presheaf of
rings followed by the counit of the sheafification adjunction. -/
theorem ringSheafHom_eq :
    X.ringSheafHom =
      (presheafToSheaf (Opens.grothendieckTopology (S : TopCat)) RingCat.{u}).map
          X.totalPresheafHom ≫
        (sheafificationAdjunction (Opens.grothendieckTopology (S : TopCat))
          RingCat.{u}).counit.app X.ringSheaf :=
  by
  refine Sheaf.hom_ext ?_
  rw [show X.ringSheafHom.hom = CategoryTheory.sheafifyLift
      (Opens.grothendieckTopology (S : TopCat)) X.totalPresheafHom X.ringSheaf.property from rfl,
    CategoryTheory.sheafifyLift, Adjunction.homEquiv_counit]

/-- **The direct image `π_* 𝒪_C` of a cone is the ungraded realization of its grading.** The two
decomposition axioms say that the realization maps locally bijectively into `π_* 𝒪_C`, and a
presheaf mapping locally bijectively into a sheaf exhibits that sheaf as its sheafification. -/
instance isIso_ringSheafHom : IsIso X.ringSheafHom := by
  have h1 := X.isLocallyInjective_totalPresheafHom
  have h2 := X.isLocallySurjective_totalPresheafHom
  have hmap : IsIso ((presheafToSheaf (Opens.grothendieckTopology (S : TopCat))
      RingCat.{u}).map X.totalPresheafHom) :=
    ((Opens.grothendieckTopology (S : TopCat)).W_iff _).mp
      (GrothendieckTopology.W_of_isLocallyBijective _ X.totalPresheafHom)
  rw [X.ringSheafHom_eq]
  exact IsIso.comp_isIso' hmap (isIso_sheafificationAdjunction_counit _)

/-- **The direct image `π_* 𝒪_C` of a cone, as the ungraded realization of its grading.** -/
def ringSheafIso : X.grading.ungradedSheaf ≅ X.ringSheaf :=
  asIso X.ringSheafHom

/-- The ungraded realization carries a homogeneous local section to the function it is. -/
theorem ringSheafHom_ungradedIncl (n : ℤ) (U : S.Opens)
    (x : (X.grading.piece n).val.obj (op U)) :
    (X.ringSheafHom.hom.app (op U)).hom (X.grading.ungradedIncl n x) =
      (X.ι n).val.app (op U) x :=
  (totalSheafLift_ungradedIncl X.grading _ _ n U x).trans
    (X.grading.toPresheafGradedAlgebra.totalPresheafDesc_app_incl _ _ _ _ (op U) n x)

/-- The inverse identification carries a function of the form `ι_n x` back to the homogeneous
local section it comes from. -/
theorem ringSheafIso_inv_app_ι (n : ℤ) (U : S.Opens)
    (x : (X.grading.piece n).val.obj (op U)) :
    (X.ringSheafIso.inv.hom.app (op U)).hom ((X.ι n).val.app (op U) x) =
      X.grading.ungradedIncl n x :=
  ((congrArg (fun a => (X.ringSheafIso.inv.hom.app (op U)).hom a)
      (X.ringSheafHom_ungradedIncl n U x)).symm).trans
    (congrArg
      (fun k : X.grading.ungradedSheaf ⟶ X.grading.ungradedSheaf =>
        (k.hom.app (op U)).hom (X.grading.ungradedIncl n x))
      X.ringSheafIso.hom_inv_id)

/-- The degree-zero identification carries a multiple of the algebra unit to that scalar. -/
theorem degreeZero_smul_one (U : S.Opens) (r : S.ringCatSheaf.obj.obj (op U)) :
    (X.degreeZero.hom.val.app (op U) (r • X.grading.one.eval (op U)) :
        S.presheaf.obj (op U)) = r := by
  refine Eq.trans ((X.degreeZero.hom.val.app (op U)).hom.map_smul r _) ?_
  rw [X.degreeZero_one U]
  exact mul_one r

/-- **The ungraded realization of the grading of a cone is a morphism over the structure
sheaf**: its structure map `r ↦ r • 1` is carried to the pullback of functions along `π`, which
is the structure map of `π_* 𝒪_C`. -/
theorem totalPresheafHom_structureMap (U : S.Opens) (r : S.ringCatSheaf.obj.obj (op U)) :
    (X.totalPresheafHom.app (op U)).hom
        (X.grading.toPresheafGradedAlgebra.structureMap (op U) r) =
      X.π.c.app (op U) r :=
  (congrArg (fun z => (X.totalPresheafHom.app (op U)).hom z)
      (X.grading.toPresheafGradedAlgebra.incl_smul 0 r (X.grading.one.eval (op U))).symm).trans
    ((X.grading.toPresheafGradedAlgebra.totalPresheafDesc_app_incl _ _ _ _ (op U) 0 _).trans
      ((X.ι_zero U _).trans
        (congrArg (fun z : S.presheaf.obj (op U) => X.π.c.app (op U) z)
          (X.degreeZero_smul_one U r))))

/-- **The ungraded realization of the grading of a cone is a morphism over the structure
sheaf**, as an identity of morphisms of presheaves of rings. -/
theorem structureHom_comp_totalPresheafHom :
    X.grading.toPresheafGradedAlgebra.structureHom ≫ X.totalPresheafHom =
      (AlgebraSheaf.structureMap (pushforwardAlgebra X.π)).hom :=
  NatTrans.ext (funext fun U => RingCat.hom_ext (RingHom.ext fun r => by
    induction U with
    | op U => exact X.totalPresheafHom_structureMap U r))

/-- **The identification of `π_* 𝒪_C` with the ungraded realization of the grading is a morphism
over the structure sheaf.** -/
theorem ungradedStructureMap_comp_ringSheafHom :
    X.grading.ungradedStructureMap ≫ X.ringSheafHom =
      AlgebraSheaf.structureMap (pushforwardAlgebra X.π) :=
  ungradedStructureMap_comp_totalSheafLift X.grading _ _ _ X.structureHom_comp_totalPresheafHom

end AbstractCone

/-! ### The morphism of direct images induced by a homomorphism of gradings -/

namespace AbstractCone

variable {S : Scheme.{u}} (V W : AbstractCone S)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom V.grading W.grading)

/-- **A unital homomorphism of the gradings of two cones induces a morphism of the sheaves of
rings they are the direct images of**, in the same direction. The direct image of a cone is the
ungraded realization of its grading, and the ungraded realization is functorial. -/
def gradedPullbackRingHom : V.ringSheaf ⟶ W.ringSheaf :=
  V.ringSheafIso.inv ≫ V.grading.toPresheafGradedAlgebra.totalSheafLift _ W.ringSheaf
    (Stacks.GradedAlgebra.totalRingMap ψ.toPresheafUnitalHom ≫ W.totalPresheafHom)

/-- **The induced morphism of direct images realizes the given homomorphism on every homogeneous
piece.** -/
theorem gradedPullbackRingHom_ι (n : ℤ) (U : S.Opens)
    (x : (V.grading.piece n).val.obj (op U)) :
    ((gradedPullbackRingHom V W ψ).hom.app (op U)).hom ((V.ι n).val.app (op U) x) =
      (W.ι n).val.app (op U) ((ψ.app n).val.app (op U) x) := by
  refine Eq.trans (congrArg
    (fun a => ((V.grading.toPresheafGradedAlgebra.totalSheafLift _ W.ringSheaf
        (Stacks.GradedAlgebra.totalRingMap ψ.toPresheafUnitalHom ≫
          W.totalPresheafHom)).hom.app (op U)).hom a)
    (V.ringSheafIso_inv_app_ι n U x)) ?_
  refine Eq.trans (totalSheafLift_ungradedIncl V.grading _ _ n U x) ?_
  refine Eq.trans (congrArg (fun a => (W.totalPresheafHom.app (op U)).hom a)
    (Stacks.GradedAlgebra.totalRingMap_app_incl ψ.toPresheafUnitalHom (op U) n x)) ?_
  exact W.grading.toPresheafGradedAlgebra.totalPresheafDesc_app_incl _ _ _ _ (op U) n _

/-- The induced morphism of direct images, by definition. -/
theorem gradedPullbackRingHom_eq :
    gradedPullbackRingHom V W ψ =
      V.ringSheafIso.inv ≫ V.grading.toPresheafGradedAlgebra.totalSheafLift _ W.ringSheaf
        (Stacks.GradedAlgebra.totalRingMap ψ.toPresheafUnitalHom ≫ W.totalPresheafHom) :=
  rfl

/-- The lift of the induced morphism is a morphism over the structure sheaf. -/
theorem ungradedStructureMap_comp_lift :
    V.grading.ungradedStructureMap ≫ V.grading.toPresheafGradedAlgebra.totalSheafLift _
        W.ringSheaf (Stacks.GradedAlgebra.totalRingMap ψ.toPresheafUnitalHom ≫
          W.totalPresheafHom) =
      AlgebraSheaf.structureMap (pushforwardAlgebra W.π) := by
  refine ungradedStructureMap_comp_totalSheafLift V.grading _ _ _ ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun k => k ≫ W.totalPresheafHom)
    (Stacks.GradedAlgebra.structureHom_comp_totalRingMap ψ.toPresheafUnitalHom)) ?_
  exact W.structureHom_comp_totalPresheafHom

/-- Cancelling the identification of `π_* 𝒪_C` with the ungraded realization on the left of the
induced morphism leaves the lift it was built from. -/
theorem ringSheafHom_comp_gradedPullbackRingHom :
    V.ringSheafHom ≫ gradedPullbackRingHom V W ψ =
      V.grading.toPresheafGradedAlgebra.totalSheafLift _ W.ringSheaf
        (Stacks.GradedAlgebra.totalRingMap ψ.toPresheafUnitalHom ≫ W.totalPresheafHom) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k : V.grading.ungradedSheaf ⟶ V.grading.ungradedSheaf =>
          k ≫ V.grading.toPresheafGradedAlgebra.totalSheafLift _ W.ringSheaf
            (Stacks.GradedAlgebra.totalRingMap ψ.toPresheafUnitalHom ≫ W.totalPresheafHom))
        V.ringSheafIso.hom_inv_id).trans
      (Category.id_comp _))

/-- **The induced morphism of direct images is a morphism over the structure sheaf**, so it is a
morphism of sheaves of `𝒪_S`-algebras. -/
theorem structureMap_comp_gradedPullbackRingHom :
    AlgebraSheaf.structureMap (pushforwardAlgebra V.π) ≫ gradedPullbackRingHom V W ψ =
      AlgebraSheaf.structureMap (pushforwardAlgebra W.π) :=
  (congrArg (fun k : S.ringCatSheaf ⟶ V.ringSheaf => k ≫ gradedPullbackRingHom V W ψ)
      V.ungradedStructureMap_comp_ringSheafHom.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg
          (fun k : V.grading.ungradedSheaf ⟶ W.ringSheaf =>
            V.grading.ungradedStructureMap ≫ k)
          (ringSheafHom_comp_gradedPullbackRingHom V W ψ)).trans
        (ungradedStructureMap_comp_lift V W ψ)))

/-- Alias of `AlgebraicGeometry.AbstractCone.Hom.c_app_eq_appLE`. -/
alias cApp_eq_appLE := AlgebraicGeometry.AbstractCone.Hom.c_app_eq_appLE

/-- **The morphism of sheaves of `𝒪_S`-algebras `π_* 𝒪_{C_V} ⟶ π_* 𝒪_{C_W}` induced by a unital
homomorphism of the gradings of two cones.** -/
def gradedPullbackAlgebraMap : pushforwardAlgebra V.π ⟶ pushforwardAlgebra W.π :=
  AlgebraSheaf.homOfRingSheafHom _ _ (gradedPullbackRingHom V W ψ)
    (structureMap_comp_gradedPullbackRingHom V W ψ)

/-- **The morphism of total spaces over `S` induced by a unital homomorphism of the gradings of
two cones**, by the universal property of the relative spectrum: the projection of a cone is
affine. -/
@[ega "II 8.5.1" "special case"]
def gradedPullbackOverHom : Over.mk W.π ⟶ Over.mk V.π :=
  haveI : IsAffineHom (Over.mk V.π).hom := V.isAffine
  (overHomEquivAlgebraHom (Over.mk W.π) (Over.mk V.π)).symm (gradedPullbackAlgebraMap V W ψ)

/-- The induced morphism of total spaces induces back the morphism of algebras it came from. -/
theorem pushforwardAlgebraMap_gradedPullbackOverHom :
    pushforwardAlgebraMap (gradedPullbackOverHom V W ψ) = gradedPullbackAlgebraMap V W ψ :=
  have : IsAffineHom (Over.mk V.π).hom := V.isAffine
  (overHomEquivAlgebraHom_apply _).symm.trans
    ((overHomEquivAlgebraHom (Over.mk W.π) (Over.mk V.π)).apply_symm_apply _)

/-- **Every unital homomorphism of the gradings of two cones is the graded part of a morphism of
cones.** The homomorphism induces a morphism of the direct images as sheaves of `𝒪_S`-algebras,
the universal property of the relative spectrum turns that into a morphism of the total spaces
over `S`, and on every homogeneous piece the resulting pullback of functions is the given
homomorphism. -/
def homOfGradedUnitalHom : Hom W V where
  f := (gradedPullbackOverHom V W ψ).left
  comm := Over.w (gradedPullbackOverHom V W ψ)
  pullback := AlgebraSheaf.underlyingModuleMap (gradedPullbackAlgebraMap V W ψ)
  pullback_app U a := by
    refine Eq.trans (congrArg (fun Φ : pushforwardAlgebra V.π ⟶ pushforwardAlgebra W.π =>
        ((AlgebraSheaf.ringSheafMap Φ).hom.app (op U)).hom a)
      (pushforwardAlgebraMap_gradedPullbackOverHom V W ψ).symm) ?_
    refine Eq.trans (congrArg
      (fun φ : (pushforwardAlgebra V.π).right.obj.obj (op U) ⟶
          (pushforwardAlgebra W.π).right.obj.obj (op U) => φ.hom a)
      (pushforwardAlgebraMap_app (gradedPullbackOverHom V W ψ) U
        (preimage_le_preimage_preimage _ _))) ?_
    exact (cApp_eq_appLE (Over.w (gradedPullbackOverHom V W ψ)) U _ a).symm
  graded := ψ.toHom
  ι_naturality n := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T => ?_)
    induction T with
    | op U =>
      exact ModuleCat.hom_ext (LinearMap.ext fun x => gradedPullbackRingHom_ι V W ψ n U x)

/-- The graded part of the morphism of cones
`AlgebraicGeometry.AbstractCone.homOfGradedUnitalHom V W ψ` is `ψ`. -/
@[simp] theorem graded_homOfGradedUnitalHom :
    (homOfGradedUnitalHom V W ψ).graded = ψ.toHom := rfl

end AbstractCone

/-! ### Fullness of the functor `V ↦ ℰ_1` -/

namespace VectorBundle

variable {S : Scheme.{u}}

/-- **The functor `V ↦ ℰ_1` is full**, which in the contravariant reading is the fullness of the
anti-equivalence of Tag 062N. A morphism `ℰ_1 ⟶ ℱ_1` of the degree-one pieces extends, by the
universal property of the symmetric algebra, to a unital homomorphism of the direct-image
algebras, which is the graded part of a morphism of the total spaces in the opposite
direction. -/
instance full_degreeOneModules (S : Scheme.{u}) : (degreeOneModules S).Full where
  map_surjective {V W} g :=
    have hκ : SheafOfModules.GradedAlgebra.PairwiseCommutes
        (A := W.unop.grading) g :=
      fun U s t => W.unop.pairwiseCommutes U (g.val.app U s) (g.val.app U t)
    ⟨Quiver.Hom.op (AbstractCone.homOfGradedUnitalHom V.unop.toAbstractCone
        W.unop.toAbstractCone
        (V.unop.isSymmetricAlgebra.isUniversal.desc W.unop.grading g hκ)),
      (Category.id_comp _).symm.trans
        (V.unop.isSymmetricAlgebra.isUniversal.desc_extends W.unop.grading g hκ)⟩

/-- **The functor `V ↦ ℰ_1` into the quasi-coherent modules is full.** -/
instance full_degreeOneFunctor (S : Scheme.{u}) : (degreeOneFunctor S).Full where
  map_surjective {V W} g :=
    have h := (full_degreeOneModules S).map_surjective
      (X := V) (Y := W) ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map g)
    ⟨h.choose, ObjectProperty.hom_ext _ h.choose_spec⟩

end VectorBundle

end AlgebraicGeometry

end
