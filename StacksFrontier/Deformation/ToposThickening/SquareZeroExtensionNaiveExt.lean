module

public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCanonicalExtZero
public import StacksFrontier.Deformation.ToposThickening.SolutionClassesTorsor
public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphismClassesExt
public import StacksFrontier.Deformation.ToposThickening.SolutionPairCocycle
public import StacksFrontier.Deformation.ToposThickening.SolutionPairSeparation
public import StacksFrontier.Deformation.ToposThickening.SolutionPushoutRealization
public import StacksFrontier.Deformation.ToposThickening.SquareZeroExtensionClasses
import StacksCore.Tactic.StacksAttribute

/-!
# Square-zero extensions of `f⁻¹𝒪_ℬ`-algebras and `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` (Stacks 0GQ5)

Let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` be a morphism of ringed topoi and `𝒢` an `𝒪`-module.
**Stacks 0GQ5** says that the set of isomorphism classes of extensions of
`f⁻¹𝒪_ℬ`-algebras `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` in which `𝒢` is an ideal of square zero is canonically
bijective to `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)`.

Such an extension is exactly a solution of the square-zero extension problem (91.13.0.1) of
**Stacks 08UF** whose bottom row is `0 ⟶ 0 ⟶ f⁻¹𝒪_ℬ ⟶ f⁻¹𝒪_ℬ ⟶ 0`. This file builds that
problem, `RingedToposExtensionProblem.ofTrivialBase f 𝒢`, from `f` and `𝒢` alone, and then
follows the source's proof: by **Stacks 08UK** the isomorphism classes of solutions are a
principal homogeneous space under `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` as soon as one solution exists, and
the trivial extension `𝒪 ⊕ 𝒢` is one. The bijection sends the class of an extension `𝒪'` to
the obstruction class `o(𝒪 ⊕ 𝒢, 𝒪')` of **Stacks 08UG** separating it from the trivial
extension, and a class `ξ` to the class of the pushout extension `(𝒪 ⊕ 𝒢)_ξ` of the proof of
**Stacks 08UK**.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.ofTrivialBase`: the problem attached
  to `f` and `𝒢`, whose solutions are the square-zero extensions of `𝒪` by `𝒢` as
  `f⁻¹𝒪_ℬ`-algebras.
* `Deformation.ToposThickening.RingedToposExtensionProblem.isomorphismClassesEquivNaiveExt`: for
  any problem of **Stacks 08UF** with invertible base reduction, the bijection between the
  isomorphism classes of solutions and `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` with base point `𝒪 ⊕ 𝒢`.
* `Deformation.ToposThickening.RingedToposExtensionProblem.squareZeroExtensionClassesEquiv`:
  **Stacks 0GQ5**, the bijection for `ofTrivialBase f 𝒢`.

## Main results

* `squareZeroExtensionClassesEquiv_mk`: the class of an extension `𝒪'` goes to `o(𝒪 ⊕ 𝒢, 𝒪')`.
* `squareZeroExtensionClassesEquiv_symm_apply`: a class `ξ` goes back to the class of the
  pushout extension `(𝒪 ⊕ 𝒢)_ξ`.
* `squareZeroExtensionClassesEquiv_trivialSolution`: the trivial extension goes to `0`.

## Implementation notes

**The objects of the statement.** The left-hand side is
`CompatibleFirstOrderThickening.IsomorphismClasses (ofTrivialBase f 𝒢)`: a solution is a sheaf of
commutative rings `𝒪'` with a locally surjective map `𝒪' ⟶ 𝒪` whose kernel has square zero and
is identified, `𝒪'`-linearly, with `𝒢`, together with a structure map `f⁻¹𝒪_ℬ ⟶ 𝒪'` of
`f⁻¹𝒪_ℬ`-algebras over `𝒪`; two solutions are isomorphic when there is an isomorphism of sheaves
of rings over `𝒪`, under `f⁻¹𝒪_ℬ` and inducing the identity on `𝒢`. This is the source's
footnote: first order thickenings over `(Sh(ℬ), 𝒪_ℬ)` with an identification of `𝒢` with
`Ker(i^♯)`. The right-hand side is `Stacks.SheafOfModules.naiveCotangentExt` of
`f^♯ : f⁻¹𝒪_ℬ ⟶ 𝒪`, that is `Ext¹` in the derived category of `𝒪`-modules out of the naive
cotangent complex `NL_{𝒪/𝒪_ℬ}` of **Stacks 08TW**, built from the canonical presentation.

**Universes.** The source ringed topos is `AlgebraicGeometry.RingedTopos.{u, u, u}`, a small site
whose sheaves of rings have sections in the universe of the site, as in the trivial extension
`StacksFrontier/Deformation/ToposThickening/TrivialSquareZeroSolution.lean` and the pushout of
`StacksFrontier/Deformation/ToposThickening/SolutionPushoutRealization.lean`. The base ringed topos
is unconstrained.

## References

* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.RingedSpaceThickening (SolutionObstruction)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

/-! ### The problem attached to `f` and `𝒢` -/

section OfTrivialBase

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- **The square-zero extension problem of a morphism of ringed topoi and a module.** For
`f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` and an `𝒪`-module `𝒢`, the problem (91.13.0.1) of
[Stacks 08UF] for the trivial thickening `𝒪_ℬ = 𝒪_ℬ` of the base: its bottom row is
`0 ⟶ 0 ⟶ f⁻¹𝒪_ℬ ⟶ f⁻¹𝒪_ℬ ⟶ 0` and its solutions are the extensions of `f⁻¹𝒪_ℬ`-algebras
`0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` with `𝒢` an ideal of square zero. -/
def ofTrivialBase (f : RingedToposHom X B)
    (G : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O)) :
    RingedToposExtensionProblem X B where
  f := f
  baseExtension := B.O
  baseReduction := 𝟙 _
  baseLocallySurjective := by infer_instance
  baseSquareZero := by
    intro U
    have h : RingHom.ker ((𝟙 B.O : B.O ⟶ B.O).hom.app U).hom = ⊥ := by
      rw [RingHom.ker_eq_bot_iff_eq_zero]
      exact fun x hx => hx
    rw [h]
    exact Ideal.bot_pow (by norm_num)
  I := 0
  G := G
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
          ((inverseImageCommRingFunctor f.toToposHom).obj B.O))).val.obj U) :=
      ModuleCat.subsingleton_of_isZero
        (Functor.map_isZero (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U)
          (isZero_zero _))
    have hid : ((inverseImageCommRingFunctor f.toToposHom).map (𝟙 B.O)).hom.app U a = a := by
      rw [CategoryTheory.Functor.map_id]
      rfl
    have ha0 : a = 0 := hid.symm.trans ha
    refine ⟨0, ?_, fun y _ => Subsingleton.elim _ _⟩
    rw [ha0]
    rfl

variable (f : RingedToposHom X B)
  (G : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O))

/-- The ringed topos morphism of `ofTrivialBase f G` is `f`. -/
@[simp]
theorem ofTrivialBase_f : (ofTrivialBase f G).f = f := rfl

/-- The module of `ofTrivialBase f G` is `G`. -/
@[simp]
theorem ofTrivialBase_G : (ofTrivialBase f G).G = G := rfl

/-- The base reduction of the problem attached to `f` and `𝒢` is the identity of `𝒪_ℬ`. -/
instance isIso_ofTrivialBase_baseReduction : IsIso (ofTrivialBase f G).baseReduction :=
  IsIso.id B.O

end OfTrivialBase

/-! ### The bijection for a problem with invertible base reduction -/

section General

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]
  (S : RingedToposExtensionProblem X B) [IsIso S.baseReduction]

/-- For a square-zero extension problem of [Stacks 08UF] whose base reduction is invertible, the
bijection between the isomorphism classes of solutions and `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` given by the
torsor of [Stacks 08UK] with base point the trivial extension `𝒪 ⊕ 𝒢`: the class of `𝒪'` goes
to `o(𝒪 ⊕ 𝒢, 𝒪')`. -/
def isomorphismClassesEquivNaiveExt :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage S.G 1 :=
  (CompatibleFirstOrderThickening.obstructionClassesEquiv
      (CompatibleFirstOrderThickening.pairObstructionData S)
      CompatibleFirstOrderThickening.pairObstruction_eq_zero_iff).symm.trans
    ((CompatibleFirstOrderThickening.pairObstructionData S).isomorphismClassesEquiv
      (S.trivialSolution inferInstance))

/-- The bijection sends the class of a solution `𝒪'` to the obstruction class `o(𝒪 ⊕ 𝒢, 𝒪')`. -/
theorem isomorphismClassesEquivNaiveExt_mk (Q : S.CompatibleFirstOrderThickening) :
    S.isomorphismClassesEquivNaiveExt
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S) Q) =
      CompatibleFirstOrderThickening.pairObstruction (S.trivialSolution inferInstance) Q :=
  rfl

/-- The inverse bijection sends a class `ξ` to the class of the pushout solution
`(𝒪 ⊕ 𝒢)_ξ`. -/
theorem isomorphismClassesEquivNaiveExt_symm_apply
    (ξ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage S.G 1) :
    S.isomorphismClassesEquivNaiveExt.symm ξ =
      Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S)
        ((S.trivialSolution inferInstance).twist ξ) :=
  rfl

/-- The bijection sends the class of the trivial extension `𝒪 ⊕ 𝒢` to `0`. -/
theorem isomorphismClassesEquivNaiveExt_trivialSolution :
    S.isomorphismClassesEquivNaiveExt
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid S)
          (S.trivialSolution inferInstance)) = 0 :=
  (CompatibleFirstOrderThickening.pairObstructionData S).o_self _

end General

/-! ### Stacks 0GQ5 -/

section Bijection

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]
  (f : RingedToposHom X B)
  (G : SheafOfModules.{u} ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj X.O))

/-- **Stacks Project, Tag 0GQ5.** Let `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)` be a morphism of ringed
topoi and `𝒢` an `𝒪`-module. The set of isomorphism classes of extensions of
`f⁻¹𝒪_ℬ`-algebras `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` with `𝒢` an ideal of square zero — the solutions of the
problem `ofTrivialBase f 𝒢` — is canonically bijective to `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)`.

The bijection is the one of the source's proof: the torsor of [Stacks 08UK] under
`Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` with base point the trivial extension `𝒪 ⊕ 𝒢`. The class of `𝒪'` goes
to the obstruction class `o(𝒪 ⊕ 𝒢, 𝒪')` (`squareZeroExtensionClassesEquiv_mk`), and `ξ` goes to
the class of the pushout extension `(𝒪 ⊕ 𝒢)_ξ` (`squareZeroExtensionClassesEquiv_symm_apply`). -/
@[stacks 0GQ5]
def squareZeroExtensionClassesEquiv :
    CompatibleFirstOrderThickening.IsomorphismClasses (ofTrivialBase f G) ≃
      Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
        ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage G 1 :=
  (ofTrivialBase f G).isomorphismClassesEquivNaiveExt

/-- **The bijection of [Stacks 0GQ5] is the canonical one**: it sends the isomorphism class of
an extension `𝒪'` to the obstruction class `o(𝒪 ⊕ 𝒢, 𝒪')` of [Stacks 08UG] separating it from
the trivial extension, that is the element of `Ext¹_𝒪(NL_{𝒪/𝒪_ℬ}, 𝒢)` carrying the class of
`𝒪 ⊕ 𝒢` to that of `𝒪'` in the torsor of [Stacks 08UK]. -/
@[stacks 0GQ5]
theorem squareZeroExtensionClassesEquiv_mk
    (Q : (ofTrivialBase f G).CompatibleFirstOrderThickening) :
    squareZeroExtensionClassesEquiv f G
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) Q) =
      CompatibleFirstOrderThickening.pairObstruction
        ((ofTrivialBase f G).trivialSolution (IsIso.id B.O)) Q :=
  rfl

/-- The inverse of the bijection of [Stacks 0GQ5] sends a class `ξ` to the isomorphism class of
the pushout extension `(𝒪 ⊕ 𝒢)_ξ` of the proof of [Stacks 08UK]. -/
theorem squareZeroExtensionClassesEquiv_symm_apply
    (ξ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u, t} X.J
      ((inverseImageCommRingFunctor f.toToposHom).obj B.O) X.O f.fSharpInverseImage G 1) :
    (squareZeroExtensionClassesEquiv f G).symm ξ =
      Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _)
        (((ofTrivialBase f G).trivialSolution (IsIso.id B.O)).twist ξ) :=
  rfl

/-- The bijection of [Stacks 0GQ5] sends the trivial extension `𝒪 ⊕ 𝒢` to `0`. -/
theorem squareZeroExtensionClassesEquiv_trivialSolution :
    squareZeroExtensionClassesEquiv f G
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _)
          ((ofTrivialBase f G).trivialSolution (IsIso.id B.O))) = 0 :=
  (ofTrivialBase f G).isomorphismClassesEquivNaiveExt_trivialSolution

end Bijection

end Deformation.ToposThickening.RingedToposExtensionProblem

end
