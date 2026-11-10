module

public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionClasses
import StacksCore.Tactic.StacksAttribute

/-!
# Parametrizing the solutions of a deformation problem of ringed topoi (Stacks 0GQ9)

Let `t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` be a first order thickening of the base with ideal
`𝒥 = Ker(t^♯)`, let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, let `𝒢` be an `𝒪`-module and let
`c : f⁻¹𝒥 ⟶ 𝒢` be the prescribed map on ideals — the data of the square-zero extension problem
of **Stacks 08UF**. Let `ξ ∈ Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)` be the class of the extension
`𝒪_{ℬ'}` of `𝒪_ℬ` by `𝒥` of **Stacks 0GQ5**. **Stacks 0GQ9** says the isomorphism classes of
solutions of that problem are canonically bijective to the fibre of

`Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)`

over the image of `ξ`.

The source's proof has two steps. First, **Stacks 0GQ5** applied to `t ∘ f` and `𝒢` identifies
`Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢)` with the isomorphism classes of square-zero extensions
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `f⁻¹𝒪_{ℬ'}`-algebras. Second, **Stacks 0GQ7** applied to
`(Sh(𝒞), 𝒪) → (Sh(ℬ), 𝒪_ℬ) → (Sh(ℬ'), 𝒪_{ℬ'})` and `c` says such an `𝒪'` carries a morphism
`f' : (Sh(𝒞), 𝒪') ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` compatible with `f` and `c` exactly when its class maps
to the image of `ξ`; and — the source's "of course this is the same thing" — carrying such an
`f'` is exactly being a solution of (08UF).

Both steps are available here in the fixed-site presentation
`Deformation.ToposThickening.RingedToposExtensionProblem`, where the thickening of the base is the
pair `(baseExtension, baseReduction)` on the site of `ℬ`. The first step is `squareZeroProblem`, the
problem posed over the *thickened* base `(Sh(ℬ), 𝒪_{ℬ'})` whose bottom row is
`0 ⟶ 0 ⟶ f⁻¹𝒪_{ℬ'} ⟶ f⁻¹𝒪_{ℬ'} ⟶ 0`, and `classesEquivExt` of **Stacks 0GQ5** applies to it. The
second step is `solutionEquivSquareZero`: a solution of the original problem is a solution of
`squareZeroProblem` together with `IsCompatibleWithIdeal`, the assertion that its map from the
thickened base induces `c` on the base ideal.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.thickenedBase` and
  `.toThickenedBase`: the base ringed topos with the thickened structure sheaf, and the
  composite `t ∘ f` into it.
* `Deformation.ToposThickening.RingedToposExtensionProblem.squareZeroProblem`: the instance of
  the problem over the thickened base whose ideal vanishes — the one **Stacks 0GQ5** is about.
* `Deformation.ToposThickening.RingedToposExtensionProblem.IsCompatibleWithIdeal`: the
  condition on such a solution that its map from the thickened base induces `c`, together with
  `.IsCompatibleWithIdealClass`, the same condition on isomorphism classes.
* `Deformation.ToposThickening.RingedToposExtensionProblem.idealObstruction`: the obstruction to
  that condition — the section of `𝒢` by which the two images of a section of the base ideal
  differ — together with `.idealObstructionClass`, the same obstruction on isomorphism classes,
  and `.compatibilityObstruction`, that obstruction read on `Ext¹` along `classesEquivExt`.

## Main results

* `Deformation.ToposThickening.RingedToposExtensionProblem.solutionEquivSquareZero` and
  `.classesEquivCompatible`: solutions of the problem of **Stacks 08UF**, respectively their
  isomorphism classes, are the solutions of `squareZeroProblem` satisfying
  `IsCompatibleWithIdeal`, respectively their isomorphism classes.
* `RingedToposExtensionProblem.isCompatibleWithIdeal_iff_idealObstruction_eq_zero` and
  `.idealObstruction_of_iso`: the condition is the vanishing of the obstruction, and the
  obstruction depends only on the isomorphism class of the solution.
* `Deformation.ToposThickening.RingedToposExtensionProblem.classesEquivFibre`: **Stacks 0GQ9**,
  the canonical bijection with the fibre.

## Implementation notes

**What is proved, and from what.** `squareZeroProblem` is built, not quantified over: its base
is the ringed topos `(Sh(ℬ), 𝒪_{ℬ'})` on the site of `ℬ`, its structure morphism is `t ∘ f`
(whose inverse-image structure map is `f⁻¹(t^♯) ≫ f^♯`, by `toThickenedBase_fSharpInverseImage`),
its base reduction is the identity and its ideal is the zero sheaf of modules. The bijection
`solutionEquivSquareZero` is then an identification of data, not a transport: both solution
types have the same thickened structure sheaf, reduction, map from the thickened base and
kernel identification, the two right-hand squares agree by `toThickenedBase_map_id_comp`, and
the *only* difference is the compatibility with `c` on the base ideal, which is vacuous for
`squareZeroProblem` and is `IsCompatibleWithIdeal` for the original problem. Isomorphisms of
solutions are the same on both sides (`isoSquareZero`, `isoOfSquareZero`), so the bijection
descends to isomorphism classes. `classesEquivFibre` composes this with `classesEquivExt` of
**Stacks 0GQ5** at `squareZeroProblem`.

**The cutting-out condition.** `IsCompatibleWithIdeal` is the equality of two sections of the
thickened structure sheaf of the solution, both of which the upper reduction kills
(`reduction_idealDifference`, from `idealZero` and `kernelZero`); so their difference is the image
of a unique section of `𝒢`, the obstruction `idealObstruction`, and the condition is its vanishing
(`isCompatibleWithIdeal_iff_idealObstruction_eq_zero`). An isomorphism of solutions is the identity
on `𝒢` and commutes with the maps from the thickened base, so it carries one difference to the other
and the obstruction is an invariant of the isomorphism class (`idealObstruction_of_iso`);
transported along `classesEquivExt` it becomes `compatibilityObstruction`, a function on `Ext¹`, and
the fibre of `classesEquivFibre` is its zero locus.

**Hypotheses.** Only the five inputs of `classesEquivExt` — the two-term presentation `P` of the
naive cotangent complex, the difference cocycle `xi` with its additivity `hxi`, the representation
`rep`, the pushout construction `pushout` and the lift bijection `ee` — inherited unchanged from
**Stacks 0GQ5**. Because of them the source group is the `Ext¹` of a *fixed* presentation `α`, not
of `NL_{𝒪/𝒪_{ℬ'}}`; identifying the two is **Stacks 08TY** and **Stacks 08TL**.

**Comparison with the source.** The source cuts the fibre out by the comparison map
`Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)` and the image `ξ` of the class of
the base thickening, whereas `compatibilityObstruction` takes values in the section-wise maps
`f⁻¹𝒥 ⟶ 𝒢` and the fibre is taken over `0`; the source's target involves the derived pullback
`Lf^*` of a naive cotangent complex, whose inverse-image half is
`Stacks.SheafOfModules.inverseImageNaiveCotangentComplexIso` (**Stacks 08TZ**). The statement
`Deformation.ToposThickening.LiftDiagram.nonempty_lift_iff_eq_restrictExtClass` of
**Stacks 0GQ7** concerns a `LiftDiagram`, with both thickenings presented on *one* site following
the reduction of **Stacks 08UG**, while here the base thickening lives on the site of `ℬ` and the
source thickening on the site of `𝒞`, with `f` between them.

**Universes.** The source ringed topos is `AlgebraicGeometry.RingedTopos.{u, u, u}`, inherited
from `classesEquivExt`; the base ringed topos, the ambient pretriangulated category and the
comparison group are unconstrained.

## References

* [Stacks Project, Tag 0GQ9](https://stacks.math.columbia.edu/tag/0GQ9)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 0GQ7](https://stacks.math.columbia.edu/tag/0GQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u v' u' w' v₃ u₃

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)

/-! ### The problem over the thickened base -/

/-- The base ringed topos `(Sh(ℬ), 𝒪_{ℬ'})` carrying the thickened structure sheaf: the site of
the base with `baseExtension` as its sheaf of rings. -/
abbrev thickenedBase : RingedTopos.{v', u', w'} :=
  { C := B.C, J := B.J, O := S.baseExtension }

/-- The composite `t ∘ f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_{ℬ'})`: the morphism of the problem followed
by the thickening of the base, whose structure map is `baseReduction ≫ f^♯`. -/
def toThickenedBase : RingedToposHom X S.thickenedBase where
  toToposHom := S.f.toToposHom
  fSharp := S.baseReduction ≫ S.f.fSharp

/-- The inverse-image structure map of `t ∘ f` is `f⁻¹(t^♯) ≫ f^♯`. -/
theorem toThickenedBase_fSharpInverseImage :
    S.toThickenedBase.fSharpInverseImage =
      (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
        S.f.fSharpInverseImage :=
  (Stacks.Sheaves.ToposPushforward.commRingImageAdjunction
    S.f.toToposHom).homEquiv_naturality_left_symm _ _

/-- The right-hand square over the thickened base, whose base reduction is the identity, is the
right-hand square of the original problem. -/
theorem toThickenedBase_map_id_comp :
    (inverseImageCommRingFunctor S.toThickenedBase.toToposHom).map (𝟙 S.thickenedBase.O) ≫
        S.toThickenedBase.fSharpInverseImage =
      (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
        S.f.fSharpInverseImage := by
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact S.toThickenedBase_fSharpInverseImage

/-- The square-zero extension problem over the thickened base with vanishing ideal: the bottom
row `0 ⟶ 0 ⟶ f⁻¹𝒪_{ℬ'} ⟶ f⁻¹𝒪_{ℬ'} ⟶ 0`, whose solutions are the square-zero extensions of
`𝒪` by `𝒢` as `f⁻¹𝒪_{ℬ'}`-algebras. -/
def squareZeroProblem : RingedToposExtensionProblem X S.thickenedBase where
  f := S.toThickenedBase
  baseExtension := S.baseExtension
  baseReduction := 𝟙 _
  baseLocallySurjective := by infer_instance
  baseSquareZero := by
    intro U
    have h : RingHom.ker
        ((𝟙 S.baseExtension : S.baseExtension ⟶ S.baseExtension).hom.app U).hom = ⊥ := by
      rw [RingHom.ker_eq_bot_iff_eq_zero]
      exact fun x hx => hx
    rw [h]
    exact Ideal.bot_pow (by norm_num)
  I := 0
  G := S.G
  idealInclusion := 0
  c := 0
  idealZero := by
    intro U a
    show _ = (0 : _)
    rw [show (0 : (SheafOfModules.restrictScalars _).obj 0 ⟶ _).val.app U a = 0 from rfl]
    exact map_zero _
  idealUniversal := by
    intro U a ha
    have hsub : Subsingleton ((0 : SheafOfModules.{u}
        ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
          ((inverseImageCommRingFunctor S.toThickenedBase.toToposHom).obj
            S.thickenedBase.O))).val.obj U) :=
      ModuleCat.subsingleton_of_isZero
        (Functor.map_isZero (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U)
          (isZero_zero _))
    have hid : ((inverseImageCommRingFunctor S.toThickenedBase.toToposHom).map
        (𝟙 S.baseExtension)).hom.app U a = a := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    have ha0 : a = 0 := hid.symm.trans ha
    refine ⟨0, ?_, fun y _ => Subsingleton.elim _ _⟩
    rw [ha0]
    rfl

/-- The base reduction of the problem over the thickened base is invertible, as
`classesEquivExt` of [Stacks 0GQ5] requires. -/
theorem isIso_squareZeroProblem_baseReduction : IsIso S.squareZeroProblem.baseReduction :=
  IsIso.id S.baseExtension

/-! ### Solutions of the original problem among those of the trivial-ideal problem -/

/-- A solution of the problem over the thickened base induces the prescribed map `c` on the base
ideal: the condition that makes it a solution of the original problem. -/
def IsCompatibleWithIdeal
    (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) : Prop :=
  ∀ (U : X.Cᵒᵖ) (a : S.I.val.obj U),
    Q.baseMap.hom.app U
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
        S.idealInclusion.val.app U a) =
      (show Q.extension.obj.obj U from
        Q.kernelInclusion.val.app U (S.c.val.app U a))

/-- **The solutions of [Stacks 08UF] are exactly the square-zero extensions of
`f⁻¹𝒪_{ℬ'}`-algebras that induce `c`.** The two solution types carry the same thickened
structure sheaf, reduction, map from the thickened base and kernel identification. -/
@[stacks 0GQ9 "the step the source states as -- of course this is the same thing as saying that
O' is a solution of 08UF: a solution of the problem of Tag 08UF is exactly a square-zero
extension of f⁻¹O_B'-algebras whose map from the thickened base induces the prescribed c on the
base ideal. Fixed-site presentation of 08UF, as in Tag 0GQ5"]
def solutionEquivSquareZero :
    S.CompatibleFirstOrderThickening ≃
      { Q : S.squareZeroProblem.CompatibleFirstOrderThickening // S.IsCompatibleWithIdeal Q } where
  toFun P :=
    ⟨{ extension := P.extension
       reduction := P.reduction
       locallySurjective := P.locallySurjective
       squareZero := P.squareZero
       baseMap := P.baseMap
       baseMap_reduction :=
         P.baseMap_reduction.trans S.toThickenedBase_map_id_comp.symm
       kernelInclusion := P.kernelInclusion
       kernelZero := P.kernelZero
       kernelUniversal := P.kernelUniversal
       baseMap_ideal := by
         intro U a
         change P.baseMap.hom.app U (0 : _) = P.kernelInclusion.val.app U (0 : _)
         rw [map_zero, map_zero]
         rfl }, P.baseMap_ideal⟩
  invFun Q :=
    { extension := Q.1.extension
      reduction := Q.1.reduction
      locallySurjective := Q.1.locallySurjective
      squareZero := Q.1.squareZero
      baseMap := Q.1.baseMap
      baseMap_reduction :=
        Q.1.baseMap_reduction.trans S.toThickenedBase_map_id_comp
      kernelInclusion := Q.1.kernelInclusion
      kernelZero := Q.1.kernelZero
      kernelUniversal := Q.1.kernelUniversal
      baseMap_ideal := Q.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- An isomorphism of solutions of the original problem, read as one of the corresponding
solutions over the thickened base. -/
def isoSquareZero {P₁ P₂ : S.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso P₁ P₂) :
    CompatibleFirstOrderThickening.Iso (S.solutionEquivSquareZero P₁).1
      (S.solutionEquivSquareZero P₂).1 where
  hom := e.hom
  reduction_comm := e.reduction_comm
  baseMap_comm := e.baseMap_comm
  kernel_comm := e.kernel_comm

/-- An isomorphism of the solutions over the thickened base, read as one of the solutions of the
original problem. -/
def isoOfSquareZero {P₁ P₂ : S.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso (S.solutionEquivSquareZero P₁).1
      (S.solutionEquivSquareZero P₂).1) :
    CompatibleFirstOrderThickening.Iso P₁ P₂ where
  hom := e.hom
  reduction_comm := e.reduction_comm
  baseMap_comm := e.baseMap_comm
  kernel_comm := e.kernel_comm

/-- Two solutions of the original problem are isomorphic exactly when the corresponding
solutions over the thickened base are. -/
theorem isomorphic_iff_squareZero (P₁ P₂ : S.CompatibleFirstOrderThickening) :
    CompatibleFirstOrderThickening.Isomorphic P₁ P₂ ↔
      CompatibleFirstOrderThickening.Isomorphic (S.solutionEquivSquareZero P₁).1
        (S.solutionEquivSquareZero P₂).1 :=
  ⟨fun h => h.elim fun e => ⟨S.isoSquareZero e⟩,
    fun h => h.elim fun e => ⟨S.isoOfSquareZero e⟩⟩

/-- An isomorphism of solutions commutes with the maps from the thickened base, on sections. -/
private theorem iso_baseMap_apply
    {Q₁ Q₂ : S.squareZeroProblem.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso Q₁ Q₂) (U : X.Cᵒᵖ)
    (x : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    e.hom.hom.hom.app U (Q₁.baseMap.hom.app U x) = Q₂.baseMap.hom.app U x :=
  congrArg
    (fun m : (inverseImageCommRingFunctor S.squareZeroProblem.f.toToposHom).obj
        S.squareZeroProblem.baseExtension ⟶ Q₂.extension => m.hom.app U x)
    e.baseMap_comm

/-- Inducing the prescribed map on the base ideal is invariant under isomorphism of solutions. -/
theorem isCompatibleWithIdeal_of_iso
    {Q₁ Q₂ : S.squareZeroProblem.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso Q₁ Q₂)
    (h : S.IsCompatibleWithIdeal Q₁) : S.IsCompatibleWithIdeal Q₂ := by
  intro U a
  rw [← S.iso_baseMap_apply e U, h U a]
  exact e.kernel_comm U (S.c.val.app U a)

/-- Inducing the prescribed map on the base ideal, as a condition on isomorphism classes of
solutions over the thickened base. -/
def IsCompatibleWithIdealClass :
    CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem → Prop :=
  Quotient.lift S.IsCompatibleWithIdeal fun _ _ h => h.elim fun e => propext
    ⟨fun hc => S.isCompatibleWithIdeal_of_iso e hc,
      fun hc => S.isCompatibleWithIdeal_of_iso (CompatibleFirstOrderThickening.Iso.symm e) hc⟩

/-- Isomorphism of solutions, restricted to those that induce the prescribed map on the base
ideal. -/
def compatibleSetoid : Setoid { Q : S.squareZeroProblem.CompatibleFirstOrderThickening //
    S.IsCompatibleWithIdeal Q } :=
  Setoid.comap Subtype.val (CompatibleFirstOrderThickening.isomorphicSetoid S.squareZeroProblem)

/-- **Isomorphism classes of solutions of [Stacks 08UF] are the isomorphism classes of
square-zero extensions of `f⁻¹𝒪_{ℬ'}`-algebras that induce `c`.** The identification of
solutions descends, because the isomorphisms of solutions are the same on both sides. -/
def classesEquivCompatible :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      { q : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem //
        S.IsCompatibleWithIdealClass q } :=
  (Quotient.congr (ra := CompatibleFirstOrderThickening.isomorphicSetoid S)
      (rb := S.compatibleSetoid) S.solutionEquivSquareZero S.isomorphic_iff_squareZero).trans
    (Equiv.subtypeQuotientEquivQuotientSubtype (s₂ := S.compatibleSetoid)
      S.IsCompatibleWithIdeal S.IsCompatibleWithIdealClass (fun _ => Iff.rfl)
      (fun _ _ => Iff.rfl)).symm

/-! ### The obstruction to inducing the prescribed map on the base ideal -/

/-- The section of the thickened structure sheaf of a solution over the thickened base attached
to a section of `𝒢` by the chosen identification of `𝒢` with the upper kernel. -/
def kincl (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (g : S.G.val.obj U) : Q.extension.obj.obj U :=
  Q.kernelInclusion.val.app U g

/-- The identification of `𝒢` with the upper kernel sends `0` to `0`. -/
theorem kincl_zero (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) (U : X.Cᵒᵖ) :
    S.kincl Q (0 : S.G.val.obj U) = 0 :=
  map_zero (Q.kernelInclusion.val.app U).hom

/-- The identification of `𝒢` with the upper kernel is injective on sections: this is the
uniqueness half of `kernelUniversal`. -/
theorem kincl_injective (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) (U : X.Cᵒᵖ)
    {g h : S.G.val.obj U} (hgh : S.kincl Q g = S.kincl Q h) : g = h := by
  obtain ⟨p, -, hp⟩ := Q.kernelUniversal U (S.kincl Q g) (Q.kernelZero U g)
  exact (hp g rfl).trans (hp h hgh.symm).symm

/-- An isomorphism of solutions over the thickened base is the identity on `𝒢`. -/
theorem kincl_comm {Q₁ Q₂ : S.squareZeroProblem.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso Q₁ Q₂) {U : X.Cᵒᵖ} (g : S.G.val.obj U) :
    e.hom.hom.hom.app U (S.kincl Q₁ g) = S.kincl Q₂ g :=
  e.kernel_comm U g

/-- The section of the thickened structure sheaf of a solution over the thickened base by which
the image of a section of the base ideal differs from its prescribed image in `𝒢`. -/
def idealDifference (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) (U : X.Cᵒᵖ)
    (a : S.I.val.obj U) : Q.extension.obj.obj U :=
  Q.baseMap.hom.app U
      (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
        S.idealInclusion.val.app U a) -
    (show Q.extension.obj.obj U from Q.kernelInclusion.val.app U (S.c.val.app U a))

/-- The defining formula for the difference of the two images of a section of the base ideal. -/
theorem idealDifference_eq (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) (U : X.Cᵒᵖ)
    (a : S.I.val.obj U) :
    S.idealDifference Q U a =
      Q.baseMap.hom.app U
          (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
            S.idealInclusion.val.app U a) -
        (show Q.extension.obj.obj U from Q.kernelInclusion.val.app U (S.c.val.app U a)) :=
  rfl

/-- The upper reduction of a solution over the thickened base kills that difference: both
images of a section of the base ideal lie in the identified kernel. -/
theorem reduction_idealDifference (Q : S.squareZeroProblem.CompatibleFirstOrderThickening)
    (U : X.Cᵒᵖ) (a : S.I.val.obj U) :
    Q.reduction.hom.app U (S.idealDifference Q U a) = 0 := by
  have hred : Q.baseMap ≫ Q.reduction =
      (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
        S.f.fSharpInverseImage :=
    Q.baseMap_reduction.trans S.toThickenedBase_map_id_comp
  have hb := congrArg
    (fun m : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ X.O =>
      m.hom.app U
        (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
          S.idealInclusion.val.app U a))
    hred
  change Q.reduction.hom.app U (Q.baseMap.hom.app U _) =
    S.f.fSharpInverseImage.hom.app U
      (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U _) at hb
  rw [S.idealDifference_eq, map_sub, hb, S.idealZero U a, map_zero,
    Q.kernelZero U (S.c.val.app U a), sub_zero]

/-- **The obstruction to a solution over the thickened base inducing the prescribed map `c` on
the base ideal.** The difference of the two images of a section of the base ideal lies in the
identified kernel `𝒢`, so it is the image of a unique section of `𝒢`; that section is the
obstruction. -/
def idealObstruction (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) :
    ∀ U : X.Cᵒᵖ, S.I.val.obj U → S.G.val.obj U :=
  fun U a =>
    (Q.kernelUniversal U (S.idealDifference Q U a) (S.reduction_idealDifference Q U a)).choose

/-- The defining property of the obstruction: its image in the thickened structure sheaf is the
difference of the two images of the section of the base ideal. -/
theorem kincl_idealObstruction
    (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) (U : X.Cᵒᵖ)
    (a : S.I.val.obj U) :
    S.kincl Q (S.idealObstruction Q U a) = S.idealDifference Q U a :=
  (Q.kernelUniversal U (S.idealDifference Q U a)
    (S.reduction_idealDifference Q U a)).choose_spec.1

/-- **A solution over the thickened base induces the prescribed map on the base ideal exactly
when its obstruction vanishes.** -/
theorem isCompatibleWithIdeal_iff_idealObstruction_eq_zero
    (Q : S.squareZeroProblem.CompatibleFirstOrderThickening) :
    S.IsCompatibleWithIdeal Q ↔ S.idealObstruction Q = 0 := by
  constructor
  · intro hc
    refine funext fun U => funext fun a => ?_
    change S.idealObstruction Q U a = (0 : S.G.val.obj U)
    refine S.kincl_injective Q U ?_
    rw [S.kincl_idealObstruction Q U a, S.kincl_zero, S.idealDifference_eq, hc U a, sub_self]
  · intro hz U a
    have ha : S.idealObstruction Q U a = (0 : S.G.val.obj U) := congrFun (congrFun hz U) a
    have hk := S.kincl_idealObstruction Q U a
    rw [ha, S.kincl_zero, S.idealDifference_eq] at hk
    exact sub_eq_zero.1 hk.symm

/-- **The obstruction depends only on the isomorphism class of the solution.** An isomorphism of
solutions is the identity on the identified kernel and commutes with the maps from the thickened
base, so it carries the difference of the two images to the difference of the two images. -/
theorem idealObstruction_of_iso
    {Q₁ Q₂ : S.squareZeroProblem.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso Q₁ Q₂) :
    S.idealObstruction Q₁ = S.idealObstruction Q₂ := by
  refine funext fun U => funext fun a => ?_
  refine S.kincl_injective Q₂ U ?_
  rw [S.kincl_idealObstruction Q₂ U a, S.idealDifference_eq,
    ← S.kincl_comm e (S.idealObstruction Q₁ U a),
    S.kincl_idealObstruction Q₁ U a, S.idealDifference_eq, map_sub,
    e.kernel_comm U (S.c.val.app U a), S.iso_baseMap_apply e U]

/-- **The obstruction as a function on isomorphism classes** of solutions over the thickened
base, by `idealObstruction_of_iso`. -/
def idealObstructionClass :
    CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem →
      ∀ U : X.Cᵒᵖ, S.I.val.obj U → S.G.val.obj U :=
  Quotient.lift S.idealObstruction fun _ _ h => h.elim fun e => S.idealObstruction_of_iso e

/-- Inducing the prescribed map on the base ideal is the vanishing of the obstruction, as a
condition on isomorphism classes. -/
theorem isCompatibleWithIdealClass_iff_idealObstructionClass_eq_zero
    (q : CompatibleFirstOrderThickening.IsomorphismClasses S.squareZeroProblem) :
    S.IsCompatibleWithIdealClass q ↔ S.idealObstructionClass q = 0 := by
  induction q using Quotient.ind
  exact S.isCompatibleWithIdeal_iff_idealObstruction_eq_zero _

/-! ### Stacks 0GQ9 -/

section Fibre

variable [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  {D : Type u₃} [Category.{v₃} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {single : SheafOfModules.{u} (underlyingRingSheaf X.O) ⥤ D}
  [single.Full] [single.Faithful] [single.Additive]

/-- The compatibility obstruction read on `Ext¹`: the obstruction `idealObstructionClass` of the
isomorphism class of square-zero extensions of `f⁻¹𝒪_{ℬ'}`-algebras that the bijection
`classesEquivExt` of [Stacks 0GQ5] attaches to a class of `Ext¹`. -/
def compatibilityObstruction
    (P : NaiveCotangentTwoTerm single)
    (xi : S.squareZeroProblem.CompatibleFirstOrderThickening →
      S.squareZeroProblem.CompatibleFirstOrderThickening → (P.conormal ⟶ S.G))
    (hxi : ∀ Q₁ Q₂ Q₃ : S.squareZeroProblem.CompatibleFirstOrderThickening,
      xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ζ : P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ S.G // liftingObstruction P S.G δ = ζ })
    (pushout : ∀ (Q : S.squareZeroProblem.CompatibleFirstOrderThickening)
        (δ : P.conormal ⟶ S.G),
      { Q' : S.squareZeroProblem.CompatibleFirstOrderThickening // xi Q Q' = δ })
    (ee : ∀ Q₁ Q₂ : S.squareZeroProblem.CompatibleFirstOrderThickening,
      CompatibleFirstOrderThickening.Hom Q₁ Q₂ ≃
        { θ : P.base ⟶ S.G // P.d ≫ θ = xi Q₁ Q₂ }) :
    (P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧) → ∀ U : X.Cᵒᵖ, S.I.val.obj U → S.G.val.obj U :=
  fun ζ => S.idealObstructionClass ((S.squareZeroProblem.classesEquivExt
    S.isIso_squareZeroProblem_baseReduction P xi hxi rep pushout ee).symm ζ)

/-- **Stacks Project, Tag 0GQ9.** The isomorphism classes of solutions of the square-zero
extension problem of [Stacks 08UF] are canonically bijective to the fibre over `0` of the
compatibility obstruction on the first `Ext` group of the presentation.

The bijection is `classesEquivCompatible`, which identifies the solutions with the square-zero
extensions of `f⁻¹𝒪_{ℬ'}`-algebras inducing `c`, followed by the bijection `classesEquivExt` of
[Stacks 0GQ5] for the problem `squareZeroProblem` over the thickened base. That such an
extension induces `c` exactly when its obstruction vanishes is
`isCompatibleWithIdeal_iff_idealObstruction_eq_zero`, and the obstruction descends to `Ext¹`
through `idealObstruction_of_iso`. The hypotheses are exactly those of `classesEquivExt`; see the
implementation notes of this file. -/
@[stacks 0GQ9 "the canonical bijection between the isomorphism classes of solutions of the problem \
of 08UF and the fibre over 0 of `compatibilityObstruction` on Ext¹ of a FIXED presentation. \
Carried: ONLY the five inputs of Tag 0GQ5 at the trivial-ideal problem. The cutting-out condition \
is PROVED, not assumed: the obstruction is the sectionwise difference between the map a \
square-zero extension of f⁻¹O_B'-algebras induces on f⁻¹J and the prescribed c, read in G, and it \
is shown to depend only on the Ext class. It is NOT the source's comparison map, whose target \
Ext¹(Lf^*NL_{O_B/O_B'}, G) needs the derived pullback Lf^*, absent from the library"]
def classesEquivFibre
    (P : NaiveCotangentTwoTerm single)
    (xi : S.squareZeroProblem.CompatibleFirstOrderThickening →
      S.squareZeroProblem.CompatibleFirstOrderThickening → (P.conormal ⟶ S.G))
    (hxi : ∀ Q₁ Q₂ Q₃ : S.squareZeroProblem.CompatibleFirstOrderThickening,
      xi Q₁ Q₂ + xi Q₂ Q₃ = xi Q₁ Q₃)
    (rep : ∀ ζ : P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧,
      { δ : P.conormal ⟶ S.G // liftingObstruction P S.G δ = ζ })
    (pushout : ∀ (Q : S.squareZeroProblem.CompatibleFirstOrderThickening)
        (δ : P.conormal ⟶ S.G),
      { Q' : S.squareZeroProblem.CompatibleFirstOrderThickening // xi Q Q' = δ })
    (ee : ∀ Q₁ Q₂ : S.squareZeroProblem.CompatibleFirstOrderThickening,
      CompatibleFirstOrderThickening.Hom Q₁ Q₂ ≃
        { θ : P.base ⟶ S.G // P.d ≫ θ = xi Q₁ Q₂ }) :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      { ζ : P.obj ⟶ (single.obj S.G)⟦(1 : ℤ)⟧ //
        S.compatibilityObstruction P xi hxi rep pushout ee ζ = 0 } :=
  S.classesEquivCompatible.trans
    ((S.squareZeroProblem.classesEquivExt
      S.isIso_squareZeroProblem_baseReduction P xi hxi rep pushout ee).subtypeEquiv (by
        intro q
        rw [S.isCompatibleWithIdealClass_iff_idealObstructionClass_eq_zero]
        change S.idealObstructionClass q = 0 ↔
          S.idealObstructionClass ((S.squareZeroProblem.classesEquivExt
            S.isIso_squareZeroProblem_baseReduction P xi hxi rep pushout ee).symm
              ((S.squareZeroProblem.classesEquivExt
                S.isIso_squareZeroProblem_baseReduction P xi hxi rep pushout ee) q)) = 0
        rw [Equiv.symm_apply_apply]))

end Fibre

end Deformation.ToposThickening.RingedToposExtensionProblem

end
