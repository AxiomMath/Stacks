module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionTorsor
public import StacksFrontier.Deformation.RingedSpaceThickening.TrivialSquareZeroThickening
import StacksCore.Tactic.StacksAttribute

/-!
# Isomorphism classes of square-zero extensions of `f⁻¹𝒪_S`-algebras (Stacks 0GPZ)

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. A
square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras is a first order
thickening `i : X ⟶ X'` over `S` with `Ker(i^♯) ≅ 𝒢`, that is, a solution of the deformation
problem (91.7.0.1) of **Stacks 08U7** for the bottom row `0 ⟶ 0 ⟶ 𝒪_S --id--> 𝒪_S ⟶ 0`: the
base thickening is `𝟙 S`, its ideal is zero, and the prescribed map `c` is zero.

**Stacks 0GPZ** says those solutions have exactly `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` many isomorphism
classes. Its proof is the torsor statement of **Stacks 08UC** together with the existence of a
solution — the trivial extension `𝒪_X ⋉ 𝒢` — and a torsor with no base point carries no
bijection. This file supplies the base point: `𝟙 S` is a first order thickening with zero ideal,
so the trivial square-zero thickening of
`StacksFrontier/Deformation/RingedSpaceThickening/TrivialSquareZeroThickening.lean` is a solution,
and the type of solutions is nonempty. That is what `[Nonempty Sol]` asks of
`SolutionObstruction.addTorsor`, so the torsor of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionTorsor.lean` fires, and a torsor with a
base point is a bijection.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.trivialSolution`: the trivial solution `𝒪_X ⋉ 𝒢` of
  the deformation problem of **Stacks 08U7** over the identity thickening of the base.
* `SolutionObstruction.isomorphismClassesEquiv`: the bijection between isomorphism classes of
  solutions and the coefficient group, given a base point.
* `AlgebraicGeometry.RingedSpaceThickening.classesEquivExt`: the bijection of **Stacks 0GPZ**
  between the isomorphism classes of square-zero extensions and `Ext¹(NL(α), 𝒢)`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.isFirstOrderThickening_id`: the identity is a first
  order thickening, with zero ideal (`isZero_idealSheaf_id`).
* `AlgebraicGeometry.RingedSpaceThickening.nonempty_deformationSolution`: the deformation
  problem over the identity thickening of the base has a solution.

## No unrestricted `@[stacks 0GPZ]`

The bijection `classesEquivExt` is proved subject to four conditions on the type of solutions,
the fields of `AlgebraicGeometry.RingedSpaceThickening.SolutionObstruction`, which remain
inputs and are where **Stacks 08UC** is still owed: the difference cocycle `xi` of two
solutions with its additivity `hxi`, the pushout construction `pushout` realizing every class
as a difference, and the representation `rep` of every class of `Ext¹(NL(α), 𝒢)` by a
homomorphism out of the conormal module (**Stacks 08UB**, whose change of presentation is
**Stacks 08TL**). None of the four can be proved as stated: the two-term complex `P` is an
arbitrary one in an arbitrary triangulated category, so nothing relates its conormal term to
the geometry of the solutions, and for the same reason the acting group is the `Ext¹` of `P` —
for `P` the complex of a fixed presentation `α`, that of `α` rather than `Ext¹(NL_{X/S}, 𝒢)`,
identifying the two being again **Stacks 08TL**. Finally, isomorphism of solutions is here the
vanishing of the obstruction class of **Stacks 08U8**, which is the existence of a morphism of
solutions by that tag's clause (1); that such a morphism is invertible is
`AlgebraicGeometry.RingedSpaceThickening.SolutionHom.isIso_hom` of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionIsomorphism.lean`, but the identification
of the two relations needs that tag's clause (1) as an input too.

What is *not* restricted is the base point: `nonempty_deformationSolution` is proved outright,
and so is `trivialSolution`, which exhibits it.

## Implementation notes

The compatibility equation of a solution over the identity thickening is automatic: both of its
sides are maps out of `MorphismOfThickenings.reducedPullbackIdeal`, which for a base thickening
with zero ideal is a zero object, since module pullback and module pushforward have adjoints on
the appropriate side and therefore preserve zero objects.

The ideal of `𝟙 S` is zero because the comorphism of `𝟙 S` is the identity on sections, hence a
monomorphism of sheaves of modules: monomorphisms of presheaves of modules are detected on
sections, and `SheafOfModules.forget` is faithful.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe w v' u' u

namespace RingedSpaceModuleAdjunction

/-- Module pullback preserves zero objects: it is a left adjoint. -/
theorem isZero_modulePullback_obj {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z)
    {M : SheafOfModules.{u} (structureSheafRing Z)} (hM : IsZero M) :
    IsZero ((modulePullback g).obj M) := by
  let _hl : (modulePullback g).IsLeftAdjoint :=
    (modulePullbackPushforwardAdjunction g).isLeftAdjoint
  exact Functor.map_isZero _ hM

/-- Module pushforward preserves zero objects: it is a right adjoint. -/
theorem isZero_modulePushforward_obj {Y Z : RingedSpace.{u, u}} (g : Y ⟶ Z)
    {M : SheafOfModules.{u} (structureSheafRing Y)} (hM : IsZero M) :
    IsZero ((modulePushforward g).obj M) := by
  let _hr : (modulePushforward g).IsRightAdjoint := modulePushforward_isRightAdjoint g
  exact Functor.map_isZero _ hM

end RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpaceThickening

/-! ### The identity as a first order thickening -/

/-- The identity of a ringed space is a thickening: it is a homeomorphism, its comorphism is the
identity and the kernel of the identity is zero. -/
theorem isThickening_id (S : RingedSpace.{u, u}) : IsThickening (𝟙 S) := by
  refine ⟨?_, ?_, ?_⟩
  · change IsIso (𝟙 S.carrier)
    infer_instance
  · have hp : Presheaf.IsLocallySurjective (Opens.grothendieckTopology S.carrier)
        (structureSheafHom (𝟙 S)).hom := by
      apply Presheaf.isLocallySurjective_of_surjective
      exact fun _ b => ⟨b, rfl⟩
    have h2 : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (𝟙 S)))) :=
      ⟨fun s => hp.imageSieve_mem s⟩
    exact (SheafOfModules.toSheaf _).epi_of_epi_map inferInstance
  · intro U a ha x hx
    refine ⟨U, le_rfl, hx, 1, ?_⟩
    have hid : ((structureSheafRing S).obj.map (homOfLE (le_rfl (a := U))).op) a = a := by
      rw [show (homOfLE (le_rfl (a := U))).op = 𝟙 (op U) from rfl,
        CategoryTheory.Functor.map_id]
      rfl
    rwa [hid, pow_one]

/-- The kernel ideal of the identity is zero on every open, since its comorphism is the identity
on sections. -/
theorem ker_structureSheafHom_id_app (S : RingedSpace.{u, u}) (U : Opens S.carrier) :
    RingHom.ker ((structureSheafHom (𝟙 S)).hom.app (op U)).hom = ⊥ := by
  refine le_antisymm (fun a ha => ?_) bot_le
  exact Ideal.mem_bot.2 (show a = 0 from ha)

/-- The identity of a ringed space is a first order thickening: its kernel ideal is zero. -/
theorem isFirstOrderThickening_id (S : RingedSpace.{u, u}) :
    IsFirstOrderThickening (𝟙 S) := by
  refine ⟨isThickening_id S, fun U => ?_⟩
  rw [ker_structureSheafHom_id_app S U]
  simp

/-- The comorphism of the identity is a monomorphism of sheaves of modules: it is the identity
on sections, and monomorphisms of presheaves of modules are detected on sections. -/
theorem mono_unitToPushforwardObjUnit_id (S : RingedSpace.{u, u}) :
    Mono (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (𝟙 S))) :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective fun _ _ _ h => h)

/-- The ideal sheaf of the identity is a zero object: it is the kernel of a monomorphism. -/
theorem isZero_idealSheaf_id (S : RingedSpace.{u, u}) :
    IsZero (AlgebraicGeometry.SheafOfModules.idealSheaf (𝟙 S)) :=
  have := mono_unitToPushforwardObjUnit_id S
  isZero_kernel_of_mono _

/-! ### The trivial solution of the deformation problem over the identity -/

variable {X S : RingedSpace.{u, u}}

/-- **The trivial square-zero extension is a solution of the problem of Stacks 08U7** over the
identity thickening of the base: `X' = (X, 𝒪_X ⋉ 𝒢)` is a first order thickening of `X` over
`S` whose ideal is `𝒢`. This is the base point the torsor of **Stacks 08UC** needs. -/
@[stacks 0GPZ "the existence of a solution: the trivial extension 𝒪_X ⋉ 𝒢; not the bijection \
with Ext¹, which needs the torsor statement of 08UC"]
def trivialSolution (ht : IsFirstOrderThickening (𝟙 S)) (f : X ⟶ S)
    (G : SheafOfModules.{u} (structureSheafRing X)) :
    DeformationSolution (𝟙 S) ht f G 0 where
  X' := Stacks.Deformation.TrivialSqZero.space X G
  i := Stacks.Deformation.TrivialSqZero.thickening X G
  f' := Stacks.Deformation.TrivialSqZero.over (G := G) f
  i_firstOrder := Stacks.Deformation.TrivialSqZero.isFirstOrderThickening_thickening X G
  comm := (Stacks.Deformation.TrivialSqZero.thickening_comp_over (G := G) f).trans
    (Category.comp_id f).symm
  kernelIso := Stacks.Deformation.TrivialSqZero.idealSheafIso X G
  compatibility := by
    intro D
    exact IsZero.eq_of_src (isZero_modulePushforward_obj _
      (isZero_modulePullback_obj _ (isZero_modulePullback_obj _ (isZero_idealSheaf_id S)))) _ _

/-- **The deformation problem of Stacks 08U7 over the identity thickening of the base has a
solution**, namely the trivial square-zero extension. This is the source's "there exists a
solution", i.e. what `[Nonempty Sol]` asks of `SolutionObstruction.addTorsor`. -/
@[stacks 0GPZ "the existence of a solution, which is what the torsor of 08UC requires of the \
type of solutions; not the bijection with Ext¹"]
instance nonempty_deformationSolution {ht : IsFirstOrderThickening (𝟙 S)} {f : X ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X)} :
    Nonempty (DeformationSolution (𝟙 S) ht f G 0) :=
  ⟨trivialSolution ht f G⟩

/-! ### The bijection -/

/-- A principal homogeneous space with a base point is a bijection: for obstruction data on a
type of solutions and a chosen solution `Q`, the isomorphism classes of solutions are in
bijection with the coefficient group, by `q ↦ q - [Q]`. -/
def SolutionObstruction.isomorphismClassesEquiv {Sol : Type u} {E : Type w} [AddCommGroup E]
    (T : SolutionObstruction Sol E) (Q : Sol) : T.IsomorphismClasses ≃ E :=
  haveI : Nonempty Sol := ⟨Q⟩
  (Equiv.vaddConst (T.isoClass Q)).symm

variable (ht : IsFirstOrderThickening (𝟙 S)) (f : X ⟶ S)
  (G : SheafOfModules.{u} (structureSheafRing X))
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {single : SheafOfModules.{u} (structureSheafRing X) ⥤ D} [single.Full] [single.Faithful]
  [single.Additive]

/-- **Stacks Project, Tag 0GPZ.** The isomorphism classes of square-zero extensions
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras — equivalently, of first order thickenings
`i : X ⟶ X'` over `S` with `Ker(i^♯) ≅ 𝒢`, i.e. of solutions of the problem of **Stacks 08U7**
over the identity thickening of the base — are in bijection with `Ext¹(NL(α), 𝒢)`.

The bijection is the torsor of **Stacks 08UC** evaluated at the base point supplied by the
trivial extension `𝒪_X ⋉ 𝒢`: a class `q` goes to the obstruction class separating it from the
class of `𝒪_X ⋉ 𝒢`, and a class `ξ` of `Ext¹` goes to the class of the solution obtained from
`𝒪_X ⋉ 𝒢` by twisting with `ξ`. The four fields of `SolutionObstruction` remain inputs; see
the implementation notes of this file and of
`StacksFrontier/Deformation/RingedSpaceThickening/SolutionTorsor.lean`. -/
@[stacks 0GPZ "the bijection, subject to four conditions on the type of solutions that remain \
inputs — the fields of SolutionObstruction: the difference cocycle xi of two solutions, its \
additivity hxi, the pushout construction realizing every class as a difference, and the \
representation rep of every class by a conormal homomorphism (08UB, whose change of \
presentation is 08TL). The two-term complex P is arbitrary, so the acting group is the Ext¹ of \
P — for P the complex of a fixed presentation α, that of α rather than Ext¹(NL_{X/S}, 𝒢), \
whose identification is 08TL"]
def classesEquivExt (P : NaiveCotangentTwoTerm single)
    (xi : DeformationSolution (𝟙 S) ht f G 0 → DeformationSolution (𝟙 S) ht f G 0 →
      (P.conormal ⟶ G))
    (hxi : ∀ Q₁ Q₂ Q₃ : DeformationSolution (𝟙 S) ht f G 0, xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ξ : P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ G // liftingObstruction P G δ = ξ })
    (pushout : ∀ (Q : DeformationSolution (𝟙 S) ht f G 0) (δ : P.conormal ⟶ G),
      { Q' : DeformationSolution (𝟙 S) ht f G 0 // xi Q Q' = δ }) :
    (liftingObstructionSolution P G xi hxi rep pushout).IsomorphismClasses ≃
      (P.obj ⟶ (single.obj G)⟦(1 : ℤ)⟧) :=
  (liftingObstructionSolution P G xi hxi rep pushout).isomorphismClassesEquiv
    (trivialSolution ht f G)

end AlgebraicGeometry.RingedSpaceThickening

end
