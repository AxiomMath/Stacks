module

public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsInverseImage
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem
import StacksCore.Tactic.StacksAttribute

/-!
# The trivial solution `𝒪 ⋉ 𝒢` of a square-zero extension problem of ringed topoi

Let `S : RingedToposExtensionProblem X B` be the square-zero extension problem of
**Stacks 08UF** whose bottom row is trivial, that is, whose base reduction
`𝒪_{B'} ⟶ 𝒪_B` is invertible: the instance of equation 91.13.0.1 with bottom row
`0 ⟶ 0 ⟶ f⁻¹𝒪_B ⟶ f⁻¹𝒪_B ⟶ 0`. A solution of that problem is a square-zero extension
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `f⁻¹𝒪_B`-algebras. This file exhibits one, the *trivial* one
`𝒪' = 𝒪 ⋉ 𝒢`, which is the source's "there exists a solution, namely `𝒢 ⊕ 𝒪`" in the proof of
**Stacks 0GQ5**.

The sheaf of rings `𝒪 ⋉ 𝒢` is `Stacks.Sheaves.Differentials.sqZeroExtSheaf`; what is added here
is everything the extension problem asks of it — local surjectivity and square-zeroness of the
projection, the identification of `𝒢` with the kernel of the projection, the map from the
inverse image of the thickened base through the zero section, and the compatibility with the
prescribed map `c` on ideals.

## Main definitions

* `Stacks.Sheaves.Differentials.sqZeroExtSheafInr`: the inclusion `𝒢 ⟶ 𝒪 ⋉ 𝒢` of the ideal,
  as a morphism of `(𝒪 ⋉ 𝒢)`-modules out of `𝒢` with scalars restricted along the projection.
* `Deformation.ToposThickening.RingedToposExtensionProblem.trivialSolution`: the solution
  `𝒪 ⋉ 𝒢` of a problem with invertible base reduction.

## Main results

* `Stacks.Sheaves.Differentials.sqZeroExtSheafInl_comp_sqZeroExtSheafProj`: the zero section
  splits the projection.
* `Stacks.Sheaves.Differentials.isLocallySurjective_sqZeroExtSheafProj` and
  `Stacks.Sheaves.Differentials.sq_ker_sqZeroExtSheafProj`: the projection is (even sectionwise)
  surjective, and its kernel has square zero.
* `Deformation.ToposThickening.RingedToposExtensionProblem.subsingleton_ideal` and
  `.c_val_app_eq_zero`: when the base reduction is invertible the inverse-image base ideal has
  no nonzero sections, so the prescribed map `c` vanishes. This is the Lean form of "the bottom
  row is `0 ⟶ 0 ⟶ f⁻¹𝒪_B ⟶ f⁻¹𝒪_B ⟶ 0`".
* `Deformation.ToposThickening.RingedToposExtensionProblem.nonempty_compatibleFirstOrderThickening`:
  such a problem has a solution. This is the base point that the torsor statement of
  **Stacks 08UK** needs in order to become a bijection; the bijection itself is
  `StacksFrontier/Deformation/ToposThickening/SquareZeroExtensionClasses.lean`.

## Implementation notes

**Hypotheses carried.** Exactly one, `IsIso S.baseReduction`, and it is not a restriction on
what is proved but the identification of the problem: **Stacks 0GQ5** is the instance of
equation 91.13.0.1 whose bottom row is `0 ⟶ 0 ⟶ f⁻¹𝒪_B ⟶ f⁻¹𝒪_B ⟶ 0`, and a
`Deformation.ToposThickening.RingedToposExtensionProblem` is that instance exactly when its
base reduction is invertible. Nothing about `Ext¹` occurs in this file, so the restriction of
the acting group to the `Ext¹` of a fixed presentation — forced because **Stacks 08TY** and
**Stacks 08TL** are not available on a general site — concerns only the companion file
`StacksFrontier/Deformation/ToposThickening/SquareZeroExtensionClasses.lean`, whose implementation
notes record it.

The invertibility of the base reduction is used only through `subsingleton_ideal`: an invertible
morphism of sheaves of commutative rings is injective on sections after taking inverse images,
so the field `idealZero` forces the inclusion of the inverse-image base ideal to vanish on every
section, and then the uniqueness half of `idealUniversal` makes that ideal subsingleton on
sections. The field `baseMap_ideal` of the trivial solution is then automatic: both sides are
the image of `0`.

**Universes.** `Stacks.Sheaves.Differentials.sqZeroExtSheaf` is available for a small site whose
sheaves of rings have sections in the universe of the site, so the source ringed topos is taken
to be `AlgebraicGeometry.RingedTopos.{u, u, u}` wherever that sheaf appears. The base ringed
topos is unconstrained, and the lemmas about an invertible base reduction are stated at
unconstrained universes for both.

**Sections of `𝒪 ⋉ 𝒢`.** The ring of sections is Mathlib's `TrivSqZeroExt`, and the two
algebraic identities that the ideal inclusion needs — additivity of `m ↦ (0, m)` and
`a · (0, m) = (0, a₁ · m)` — are proved in this file at the level of presheaves, in
`sqZeroExtMk_zero_add` and `mul_sqZeroExtMk_zero`, because the ring of sections reaches the
extension problem through `CategoryTheory.sheafCompose` and the resulting spelling of its
multiplication is not the one the `PresheafOfModules.sqZeroExt*` simp set is stated for.

## References

* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open PresheafOfModules (sqZeroExtMk sqZeroExtFst sqZeroExtSnd sqZeroExt_ext sqZeroExtObj)

universe u v' u' w'

namespace Stacks.Sheaves.Differentials

/-! ### The sections of a trivial square-zero extension -/

section Sections

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)} {U : Cᵒᵖ}

/-- The inclusion `m ↦ (0, m)` of the module component of a trivial square-zero extension is
additive. -/
theorem sqZeroExtMk_zero_add (m m' : M.obj U) :
    sqZeroExtMk (M := M) 0 (m + m') = sqZeroExtMk 0 m + sqZeroExtMk 0 m' :=
  sqZeroExt_ext (by simp) (by simp)

/-- Multiplying `(0, m)` by a section of a trivial square-zero extension multiplies `m` by the
ring component: this is the `(𝒪 ⋉ 𝒢)`-linearity of the inclusion of the ideal. -/
theorem mul_sqZeroExtMk_zero (a : sqZeroExtObj M U) (m : M.obj U) :
    a * sqZeroExtMk (M := M) 0 m = sqZeroExtMk 0 (sqZeroExtFst a • m) :=
  sqZeroExt_ext (by simp) (by simp)

end Sections

/-! ### The trivial square-zero extension of a sheaf of commutative rings -/

section Sheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u}) (N : SheafOfModules.{u} (underlyingRingSheaf O))

/-- The zero section splits the projection of a trivial square-zero extension. -/
theorem sqZeroExtSheafInl_comp_sqZeroExtSheafProj :
    sqZeroExtSheafInl O N ≫ sqZeroExtSheafProj O N = 𝟙 O :=
  rfl

/-- The projection of a trivial square-zero extension is surjective on sections, hence locally
surjective: the zero section is a section of it. -/
theorem isLocallySurjective_sqZeroExtSheafProj :
    Presheaf.IsLocallySurjective J (sqZeroExtSheafProj O N).hom := by
  apply Presheaf.isLocallySurjective_of_surjective
  intro U b
  exact ⟨sqZeroExtMk b 0, rfl⟩

/-- The kernel of the projection of a trivial square-zero extension has square zero: the product
of two sections with vanishing ring component vanishes. -/
theorem sq_ker_sqZeroExtSheafProj (U : Cᵒᵖ) :
    (RingHom.ker ((sqZeroExtSheafProj O N).hom.app U).hom) ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  have hx' : sqZeroExtFst x = 0 := hx
  have hy' : sqZeroExtFst y = 0 := hy
  refine Ideal.mem_bot.2 (sqZeroExt_ext ?_ ?_)
  · change sqZeroExtFst x * sqZeroExtFst y = 0
    rw [hx', zero_mul]
  · change sqZeroExtFst x • sqZeroExtSnd y + sqZeroExtFst y • sqZeroExtSnd x = _
    rw [hx', hy', zero_smul, zero_smul, add_zero]
    rfl

/-- The inclusion `𝒢 ⟶ 𝒪 ⋉ 𝒢` of the ideal of a trivial square-zero extension, as a morphism of
`(𝒪 ⋉ 𝒢)`-modules out of `𝒢` with its scalars restricted along the projection. -/
def sqZeroExtSheafInr :
    (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        (sqZeroExtSheafProj O N))).obj N ⟶
      SheafOfModules.unit (underlyingRingSheaf (sqZeroExtSheaf O N)) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
              (sqZeroExtSheafProj O N))).obj N).val.obj U)
        (Y := (SheafOfModules.unit (underlyingRingSheaf (sqZeroExtSheaf O N))).val.obj U)
        { toFun := fun m => sqZeroExtMk (M := N.val) 0 m
          map_add' := fun m m' =>
            sqZeroExtMk_zero_add (R := (sheafToPresheaf J CommRingCat.{u}).obj O) (M := N.val) m m'
          map_smul' := fun a m =>
            (mul_sqZeroExtMk_zero (R := (sheafToPresheaf J CommRingCat.{u}).obj O)
              (M := N.val) a m).symm }
      naturality := fun {_ _} _ => by
        ext m
        exact sqZeroExt_ext (map_zero _).symm rfl }

/-- On sections, the inclusion of the ideal of a trivial square-zero extension is
`m ↦ (0, m)`. -/
@[simp]
theorem sqZeroExtSheafInr_val_app_apply (U : Cᵒᵖ) (m : N.val.obj U) :
    (sqZeroExtSheafInr O N).val.app U m = sqZeroExtMk (M := N.val) 0 m :=
  rfl

end Sheaf

end Stacks.Sheaves.Differentials

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open Stacks.Sheaves.Differentials

/-! ### Problems whose bottom row is `0 ⟶ 0 ⟶ f⁻¹𝒪_B ⟶ f⁻¹𝒪_B ⟶ 0` -/

section TrivialBase

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)

/-- When the base reduction is invertible, so is its inverse image, hence that inverse image is
injective on sections. -/
theorem injective_inverseImage_baseReduction_app (h : IsIso S.baseReduction) (U : X.Cᵒᵖ) :
    Function.Injective
      (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U) := by
  have hf : IsIso ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction) :=
    have := h; inferInstance
  have hp : IsIso (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom) :=
    have := hf
    Functor.map_isIso (sheafToPresheaf X.J CommRingCat.{u})
      ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
  have ha : IsIso ((((inverseImageCommRingFunctor S.f.toToposHom).map
      S.baseReduction).hom).app U) :=
    have := hp; NatIso.isIso_app_of_isIso _ _
  have := ha
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- When the base reduction is invertible, the inclusion of the inverse-image base ideal vanishes
on every section. -/
theorem idealInclusion_val_app_eq_zero (h : IsIso S.baseReduction) (U : X.Cᵒᵖ)
    (a : S.I.val.obj U) :
    (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
      S.idealInclusion.val.app U a) = 0 :=
  S.injective_inverseImage_baseReduction_app h U ((S.idealZero U a).trans (map_zero _).symm)

/-- **The bottom row of a problem with invertible base reduction is
`0 ⟶ 0 ⟶ f⁻¹𝒪_B ⟶ f⁻¹𝒪_B ⟶ 0`**: the inverse-image base ideal has exactly one section over
every object of the site. -/
theorem subsingleton_ideal (h : IsIso S.baseReduction) (U : X.Cᵒᵖ) :
    Subsingleton (S.I.val.obj U) := by
  obtain ⟨x, -, hx⟩ := S.idealUniversal U 0 (map_zero _)
  exact ⟨fun a b => (hx a (S.idealInclusion_val_app_eq_zero h U a)).trans
    (hx b (S.idealInclusion_val_app_eq_zero h U b)).symm⟩

/-- When the base reduction is invertible the prescribed map on ideals vanishes, since its source
has no nonzero sections. -/
theorem c_val_app_eq_zero (h : IsIso S.baseReduction) (U : X.Cᵒᵖ) (a : S.I.val.obj U) :
    S.c.val.app U a = 0 := by
  have := S.subsingleton_ideal h U
  rw [Subsingleton.elim a 0]
  exact map_zero _

/-! ### The trivial solution -/

/-- **The trivial square-zero extension is a solution** of the square-zero extension problem of
[Stacks 08UF] whose base reduction is invertible: `𝒪' = 𝒪 ⋉ 𝒢`, with the projection as reduction,
the inclusion `m ↦ (0, m)` as the identification of `𝒢` with the kernel, and the zero section
composed with the structure map of `f` as the map from the inverse image of the thickened base.

This is the existence of a solution in the proof of [Stacks 0GQ5] — the source's "a solution
exists, take `𝒢 ⊕ 𝒪`". It is not the bijection with `Ext¹`, which needs the torsor statement of
[Stacks 08UK]; see
`StacksFrontier/Deformation/ToposThickening/SquareZeroExtensionClasses.lean`. -/
@[stacks 0GQ5 "the existence of a solution: the trivial extension 𝒪 ⋉ 𝒢; not the bijection \
with Ext¹, which needs the torsor statement of 08UK", ega "0 18.2.3" "partial"]
def trivialSolution (h : IsIso S.baseReduction) : S.CompatibleFirstOrderThickening where
  extension := sqZeroExtSheaf X.O S.G
  reduction := sqZeroExtSheafProj X.O S.G
  locallySurjective := isLocallySurjective_sqZeroExtSheafProj X.O S.G
  squareZero := sq_ker_sqZeroExtSheafProj X.O S.G
  baseMap := (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
    S.f.fSharpInverseImage ≫ sqZeroExtSheafInl X.O S.G
  baseMap_reduction := by
    rw [Category.assoc, Category.assoc, sqZeroExtSheafInl_comp_sqZeroExtSheafProj,
      Category.comp_id]
  kernelInclusion := sqZeroExtSheafInr X.O S.G
  kernelZero := fun _ _ => rfl
  kernelUniversal := fun U a ha => by
    refine ⟨sqZeroExtSnd a, sqZeroExt_ext ?_ rfl, fun g hg => ?_⟩
    · exact ha.symm
    · exact congrArg sqZeroExtSnd hg
  baseMap_ideal := fun U a => by
    rw [S.idealInclusion_val_app_eq_zero h U a, S.c_val_app_eq_zero h U a, map_zero]
    exact (map_zero _).symm

/-- **A square-zero extension problem of ringed topoi whose bottom row is
`0 ⟶ 0 ⟶ f⁻¹𝒪_B ⟶ f⁻¹𝒪_B ⟶ 0` has a solution**, namely the trivial extension `𝒪 ⋉ 𝒢`. This is
the base point the torsor statement of [Stacks 08UK] needs in order to turn into the bijection of
[Stacks 0GQ5]. -/
@[stacks 0GQ5 "the existence of a solution, as the base point the torsor of 08UK needs; not the \
bijection with Ext¹"]
theorem nonempty_compatibleFirstOrderThickening (h : IsIso S.baseReduction) :
    Nonempty S.CompatibleFirstOrderThickening :=
  ⟨S.trivialSolution h⟩

end TrivialBase

end Deformation.ToposThickening.RingedToposExtensionProblem

end
