module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCanonicalExtZero
public import StacksFrontier.Deformation.ToposThickening.InverseImageKernelIdeal
public import StacksFrontier.Deformation.ToposThickening.LiftingDerivationGroup
public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphisms

/-!
# Automorphisms of a solution of a square-zero extension problem of ringed topoi

Fix the square-zero extension problem `S` of [Stacks Project, Tag 08UF] for a morphism of ringed
topoi `f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, a first order thickening `𝒪_{ℬ'} ⟶ 𝒪_ℬ`, an
`𝒪`-module `𝒢` and `c : f⁻¹𝒥 ⟶ 𝒢`, and a solution `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0`. This file identifies
the automorphisms of the solution (isomorphisms over the fixed diagram which are the identity on
`𝒢`) with the relative derivations of `𝒪` over `f⁻¹𝒪_ℬ` with values in `𝒢`, hence with
`Hom_𝒪(Ω_{𝒪/f⁻¹𝒪_ℬ}, 𝒢) = Ext⁰_𝒪(NL_{𝒪/f⁻¹𝒪_ℬ}, 𝒢)`. This is clause (2) of
[Stacks Project, Tag 08UG] for the diagram whose two layers are the same solution and whose
comparison maps are identities: an automorphism is a morphism fitting into (08UH) for that
diagram, and the identity is one of them.

## Main definitions

* `...CompatibleFirstOrderThickening.liftSquare`: the solution as a layer of the diagram of
  [Stacks 08UG], and `...selfFirstOrderLiftDiagram` the diagram with two equal layers.
* `...CompatibleFirstOrderThickening.derivationEquivRelative`: the derivations of a solution (the
  group `autEquivDerivation` identifies with its automorphisms) are the relative derivations
  `𝒪 ⟶ 𝒢` over `f⁻¹𝒪_ℬ`.
* `...CompatibleFirstOrderThickening.derivationEquivDifferentialsHom`: they are the homomorphisms
  `Ω_{𝒪/f⁻¹𝒪_ℬ} ⟶ 𝒢`, `𝒢` read in the module universe in which `Ω` is formed.
* `...CompatibleFirstOrderThickening.derivationEquivNaiveCotangentExtZero`: they are
  `Ext⁰_𝒪(NL_{𝒪/f⁻¹𝒪_ℬ}, 𝒢)`, at any model of the derived category.
* `...CompatibleFirstOrderThickening.autMulEquivNaiveCotangentExtZero`: the automorphism group of a
  solution is `Ext⁰_𝒪(NL_{𝒪/f⁻¹𝒪_ℬ}, 𝒢)`, as a group.

## Implementation notes

The sheaf of differentials `Ω_{𝒪/f⁻¹𝒪_ℬ}` and the naive cotangent complex are formed with
sections in a universe containing the universes of the site (`moduleOfDifferentialsOfSite`
corepresents derivations into such modules only), so `𝒢` enters them through the universe lift
`Stacks.SheafOfModules.moduleULift`; relative derivations into `𝒢` and into its lift are the same
thing (`Deformation.ToposThickening.derivationULiftAddEquiv`). On a small site whose sections
are in the universe of the site the lift is trivial up to `ULift`.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe t v u w v' u' w' t'

namespace Deformation.ToposThickening

/-! ### Two generic identifications -/

section Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The identity of a sheaf of modules, read as a map into its restriction of scalars along a
ring map equal to the identity. -/
def toRestrictScalarsOfEqId (α : R ⟶ R) (hα : α = 𝟙 R) (M : _root_.SheafOfModules.{t} R) :
    M ⟶ (SheafOfModules.restrictScalars α).obj M := by
  subst hα
  exact (SheafOfModules.fullyFaithfulForget R).preimage
    (PresheafOfModules.isoMk (fun X => (ModuleCat.restrictScalarsId'App _ rfl (M.val.obj X)))
      (fun _ _ _ => by ext; rfl)).inv

/-- `toRestrictScalarsOfEqId α hα M` is the identity on sections. -/
theorem toRestrictScalarsOfEqId_val_app_apply (α : R ⟶ R) (hα : α = 𝟙 R)
    (M : _root_.SheafOfModules.{t} R) (U : Cᵒᵖ) (m : M.val.obj U) :
    (toRestrictScalarsOfEqId α hα M).val.app U m = m := by
  subst hα
  rfl

variable {Rc Sc : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : Sc ⟶ Rc)

/-- **Relative derivations do not see the universe of the module.** A relative derivation with
values in a presheaf of modules is the same thing as one with values in its universe lift
`U ↦ ULift (M(U))`. -/
def derivationULiftAddEquiv (M : PresheafOfModules.{t'} (Rc ⋙ forget₂ _ _)) :
    M.Derivation' φ ≃+
      ((Stacks.SheafOfModules.presheafULift.{t} (Rc ⋙ forget₂ _ _)).obj M).Derivation' φ where
  toFun d :=
    { d := fun {X} => AddMonoidHom.mk' (fun x => ULift.up (d.d (X := X) x))
        (fun x y => by rw [map_add]; rfl)
      d_mul := fun a b => by
        change ULift.up (d.d (a * b)) = _
        rw [d.d_mul]
        rfl
      d_map := fun f x => by
        change ULift.up (d.d _) = _
        rw [d.d_map]
        rfl
      d_app := fun a => congrArg ULift.up (d.d_app a) }
  invFun d :=
    { d := fun {X} => AddMonoidHom.mk' (fun x => (d.d (X := X) x).down)
        (fun x y => by rw [map_add]; rfl)
      d_mul := fun a b => by
        change (d.d (a * b)).down = _
        rw [d.d_mul]
        rfl
      d_map := fun f x => by
        change (d.d _).down = _
        rw [d.d_map]
        rfl
      d_app := fun a => by
        have h := d.d_app a
        exact congrArg ULift.down h }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end Generic

namespace RingedToposExtensionProblem.CompatibleFirstOrderThickening

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B} (P : S.CompatibleFirstOrderThickening)
  (hbase : Presheaf.IsLocallySurjective X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom)

/-! ### The solution as a layer of the diagram of Stacks 08UG -/

/-- **The solution as a layer of the diagram of [Stacks 08UG]**: the base thickening
`f⁻¹𝒪_{ℬ'} ⟶ f⁻¹𝒪_ℬ`, the thickening `𝒪' ⟶ 𝒪` of the solution, the structure maps `f^♯` and
the base map of the solution, and `𝒢` with its identification with the ideal of `𝒪'`. -/
def liftSquare : LiftSquare X.J where
  OB := (inverseImageCommRingFunctor S.f.toToposHom).obj B.O
  OB' := (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension
  O := X.O
  O' := P.extension
  baseReduction := (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction
  reduction := P.reduction
  f := S.f.fSharpInverseImage
  f' := P.baseMap
  comm := P.baseMap_reduction
  baseLocallySurjective := hbase
  baseSquareZero := sq_ker_eq_bot_of_kernelIncl
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)
    S.idealInclusion S.idealZero S.idealUniversal
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  G := S.G
  kernelInclusion := P.kernelInclusion
  kernelZero := P.kernelZero
  kernelUniversal := P.kernelUniversal

/-- The identity of `𝒢`, read as the comparison `ν` of the diagram whose two layers are the
solution and whose comparison maps are identities. -/
abbrev selfNu : S.G ⟶ (SheafOfModules.restrictScalars
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).map (𝟙 X.O))).obj S.G :=
  toRestrictScalarsOfEqId _ (CategoryTheory.Functor.map_id _ _) S.G

/-- `selfNu` is the identity on sections of `𝒢`. -/
theorem selfNu_val_app_apply (U : X.Cᵒᵖ) (m : S.G.val.obj U) :
    (selfNu (S := S)).val.app U m = m :=
  toRestrictScalarsOfEqId_val_app_apply _ _ _ U m

/-- **The diagram of [Stacks 08UG] whose two layers are the solution** and whose comparison maps
are identities. Its derivations are the derivations of the solution, and are identified with
relative derivations by `FirstOrderLiftDiagram.relativeEquivDerivation`. -/
def selfFirstOrderLiftDiagram : FirstOrderLiftDiagram X.J where
  front := P.liftSquare hbase
  back := P.liftSquare hbase
  g := 𝟙 _
  gB := 𝟙 _
  gB' := 𝟙 _
  g_comm := by rw [Category.id_comp, Category.comp_id]
  gB_comm := by rw [Category.id_comp, Category.comp_id]
  nu := selfNu
  nu_base U a m _ h := h.trans
    (congrArg (fun x => P.kernelInclusion.val.app U x) (selfNu_val_app_apply U m).symm)

/-- **The derivations of a solution are the relative derivations `𝒪 ⟶ 𝒢` over `f⁻¹𝒪_ℬ`**: a
derivation of `𝒪'` killing the ideal `𝒢` and the image of `f⁻¹𝒪_{ℬ'}` descends along the locally
surjective reduction `𝒪' ⟶ 𝒪`, and kills the image of `f⁻¹𝒪_ℬ` because `f⁻¹𝒪_{ℬ'} ⟶ f⁻¹𝒪_ℬ` is
locally surjective. -/
def derivationEquivRelative :
    Derivation P ≃+ (FirstOrderLiftDiagram.pushedPresheaf
      (P.selfFirstOrderLiftDiagram hbase)).Derivation'
        (P.selfFirstOrderLiftDiagram hbase).front.f.hom :=
  (FirstOrderLiftDiagram.relativeEquivDerivation (D := P.selfFirstOrderLiftDiagram hbase)).symm

/-- `𝒢`, read with sections in the universe `max w u v` in which `Ω_{𝒪/f⁻¹𝒪_ℬ}` and the naive
cotangent complex of `f^♯ : f⁻¹𝒪_ℬ ⟶ 𝒪` are formed: its universe lift. -/
abbrev liftedModule (S : RingedToposExtensionProblem X B) :
    _root_.SheafOfModules.{max w u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (Stacks.SheafOfModules.moduleULift.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
    S.G

/-- **The derivations of a solution are the homomorphisms `Ω_{𝒪/f⁻¹𝒪_ℬ} ⟶ 𝒢`** (Stacks 04BL):
the descended relative derivation corresponds to the homomorphism out of the sheaf of relative
differentials through which it factors. -/
def derivationEquivDifferentialsHom :
    Derivation P ≃+ (moduleOfDifferentialsOfSite.{v, u, w, w}
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage ⟶
        liftedModule S) :=
  ((P.derivationEquivRelative hbase).trans (derivationULiftAddEquiv.{max u v} _ _)).trans
    (differentialsHomAddEquiv.{v, u, w, w} _ _ _ (liftedModule S)).symm

variable [HasWeakSheafify X.J CommRingCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{max w u v}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w u v}]
  [HasDerivedCategory.{t}
    (_root_.SheafOfModules.{max w u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The derivations of a solution are `Ext⁰_𝒪(NL_{𝒪/f⁻¹𝒪_ℬ}, 𝒢)`**, at any model of the
derived category: `Ext⁰` out of the naive cotangent complex is `Hom(Ω_{𝒪/f⁻¹𝒪_ℬ}, 𝒢)`. -/
def derivationEquivNaiveCotangentExtZero :
    Derivation P ≃+ Stacks.SheafOfModules.naiveCotangentExt.{v, u, w, w, t} X.J
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
      (liftedModule S) 0 :=
  (P.derivationEquivDifferentialsHom hbase).trans
    (Stacks.SheafOfModules.naiveCotangentExtZeroAddEquiv.{v, u, w, w, t} X.J _ _ _
      (liftedModule S)).symm

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms]

/-- **The automorphism group of a solution is `Ext⁰_𝒪(NL_{𝒪/f⁻¹𝒪_ℬ}, 𝒢)`**, as a group, at any
model of the derived category. This is clause (2) of [Stacks 08UG] for the diagram whose two
layers are the solution and whose comparison maps are identities: an automorphism `φ` is
`id + δ` for the derivation `δ = φ - id` (`autEquivDerivation`, with `φψ ↦ δ_φ + δ_ψ`), and the
derivations are `Hom(Ω_{𝒪/f⁻¹𝒪_ℬ}, 𝒢) = Ext⁰_𝒪(NL_{𝒪/f⁻¹𝒪_ℬ}, 𝒢)`. -/
def autMulEquivNaiveCotangentExtZero :
    P.AutomorphismGroup ≃* Multiplicative (Stacks.SheafOfModules.naiveCotangentExt.{v, u, w, w, t}
      X.J ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) X.O S.f.fSharpInverseImage
      (liftedModule S) 0) where
  toFun a := Multiplicative.ofAdd (P.derivationEquivNaiveCotangentExtZero hbase
    (autEquivDerivation P a))
  invFun ξ := (autEquivDerivation P).symm
    ((P.derivationEquivNaiveCotangentExtZero hbase).symm ξ.toAdd)
  left_inv a := by
    change (autEquivDerivation P).symm ((P.derivationEquivNaiveCotangentExtZero hbase).symm
      (P.derivationEquivNaiveCotangentExtZero hbase (autEquivDerivation P a))) = a
    rw [AddEquiv.symm_apply_apply, Equiv.symm_apply_apply]
  right_inv ξ := by
    change Multiplicative.ofAdd (P.derivationEquivNaiveCotangentExtZero hbase
      (autEquivDerivation P ((autEquivDerivation P).symm
        ((P.derivationEquivNaiveCotangentExtZero hbase).symm ξ.toAdd)))) = ξ
    rw [Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    rfl
  map_mul' a b := by
    rw [← ofAdd_add, autEquivDerivation_mul, map_add]

end RingedToposExtensionProblem.CompatibleFirstOrderThickening

end Deformation.ToposThickening

end
