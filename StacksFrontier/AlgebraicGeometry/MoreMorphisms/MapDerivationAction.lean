module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDerivation
public import StacksFrontier.AlgebraicGeometry.Smooth.TildeTransport
public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Infinitesimal deformations of maps: the action of a derivation on a lift

Let `S` be a scheme and let `(a, a') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a morphism of first-order
thickenings over `S`. An `𝒪_X`-linear map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}` moves `a'` to a second
lift `b'` of `a`, and it is the only lift whose difference derivation from `a'` is `d_{Y/S} ∘ θ`.
This file proves that statement on global sections over affine ambient schemes, which is the
affine case of [Stacks Project, Tag 02H5]; the general statement is
`Stacks.Thickenings.existsUnique_derivationActionGlobal`. These maps `θ` therefore act on the
lifts of `a` inducing one fixed map of conormal modules, and the action is simply transitive as
soon as one such lift exists: the affine case of [Stacks Project, Tag 04FJ], whose two clauses are
`Stacks.Thickenings.exists_addAction_compatibleLifts` and
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq` in general.

With `X'`, `Y'` and `S` affine, the three objects of the source become rings and modules:
`𝒞_{X/X'}` is the ideal `RingHom.ker i.appTop.hom`, `Ω_{Y/S}` is `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]` —
Mathlib's `KaehlerDifferential` — and an `𝒪_X`-linear map out of the pullback `a^*Ω_{Y/S}` is a
`Γ(Y, ⊤)`-linear map into the conormal module for the module structure
`Stacks.Thickenings.conormalModuleAlong hi a` read off `a`. So the datum `θ` of the source is a
`Γ(Y, ⊤)`-linear map
```
θ : Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)] →ₗ[Γ(Y, ⊤)] RingHom.ker i.appTop.hom
```
and Equation [Stacks Project, Tag 04BV], `D = d_{Y/S} ∘ θ`, reads
`D f = θ (KaehlerDifferential.D _ _ f)`.

## Main definitions

* `Stacks.Thickenings.homOfAppTop`: the morphism into an affine scheme determined by a map of
  global sections.
* `Stacks.Thickenings.derivationActionAppTop`: the comorphism `(a')^♯ + θ ∘ d_{Y/S} ∘ j^♯` of the
  modified lift, as a ring homomorphism `Γ(Y', ⊤) ⟶ Γ(X', ⊤)`.
* `Stacks.Thickenings.derivationAction`: the modified lift `b' : X' ⟶ Y'` itself.
* `Stacks.Thickenings.Deformation`: a lift of `a` over `S` inducing a prescribed map `A` of
  conormal modules, the affine form over all of `X'` of the set of [Stacks Project, Tag 04FI],
  with `Stacks.Thickenings.Deformation.act` the lift it is moved to by `θ`.
* `Stacks.Thickenings.deformationAddAction`: the action of [Stacks Project, Tag 04FJ].
* `Stacks.Thickenings.pullbackDTop`: the universal differential of the *sheaf* `Ω_{Y/S}` of
  `Stacks.Smooth.cotangentSheaf`, pulled back along `a` and read on global sections, which is
  `d_{Y/S}` in the form in which the datum `θ` of the source consumes it.
* `Stacks.Thickenings.cotangentSheafDerivation`: the derivation `D = θ ∘ d_{Y/S}` of Equation
  [Stacks Project, Tag 04BV] attached to a map `θ` out of `a^*Ω_{Y/S}`.

## Main results

* `Stacks.Thickenings.derivationAction_comm`, `Stacks.Thickenings.derivationAction_comp`,
  `Stacks.Thickenings.derivationAction_conormalMap`: the modified lift is a morphism of
  thickenings over `S` with the same reduction `a` and the same conormal map as `a'`, that is,
  conditions (1) and (2) of [Stacks Project, Tag 04FG] hold for the pair `(a', b')`.
* `Stacks.Thickenings.derivationAction_mapDifferenceDerivation`: its difference derivation from
  `a'` is `d_{Y/S} ∘ θ`, which is Equation [Stacks Project, Tag 04BV] and, read as the
  characterisation of the notation `θ ⬝ a'`, [Stacks Project, Tag 0CK1] — over affine ambient
  schemes and with the datum read on global sections. The general form of that tag is
  `Stacks.Thickenings.differenceDerivation_derivationActionSheaf`.
* `Stacks.Thickenings.eq_derivationAction`: no other lift has these properties.
* `Stacks.Thickenings.existsUnique_derivationAction`: the three previous results assembled into
  the existence-and-uniqueness statement of the source, over affine ambient schemes and with the
  datum read on global sections. The general [Stacks Project, Tag 02H5], for arbitrary
  schemes and with the datum a morphism of sheaves out of `a^*Ω_{Y/S}`, is
  `Stacks.Thickenings.existsUnique_derivationActionGlobal`.
* `Stacks.Thickenings.derivationAction_zero` and `Stacks.Thickenings.derivationAction_add`: the
  action laws, that `0` fixes a lift and that a sum acts as the composite of the two actions.
* `Stacks.Thickenings.existsUnique_act_eq`: the action is simply transitive on the deformations
  of `a` with a fixed conormal map, given one such deformation — the affine case of the
  transitivity clause of [Stacks Project, Tag 04FJ].
* `Stacks.Thickenings.existsUnique_derivationAction_cotangentSheaf`: the same
  existence-and-uniqueness statement with the datum of the source itself — an `𝒪_X`-linear map
  out of the pulled-back **sheaf** of relative differentials `a^*Ω_{Y/S}`, rather than out of
  Mathlib's `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]`. Over an affine base the two data agree, and the translation is
  the universal property of `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]` applied to
  `Stacks.Thickenings.cotangentSheafDerivation`. As before, `X'`, `Y'` and `S` are affine.
* `Stacks.Thickenings.isScalarTower_conormalModuleAlong`: the `Γ(Y, ⊤)`-action and the
  `Γ(S, ⊤)`-action on the conormal module form a scalar tower, which is what makes the universal
  property of `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]` available for the difference derivation.

## Implementation notes

The modified comorphism is *constructed*: `Stacks.Thickenings.derivationActionAppTop` is the
ring homomorphism `x ↦ a'.appTop x + θ (d (j.appTop x))`, and the verification that it is a ring
homomorphism is the one the source omits. Multiplicativity is where the square-zero condition
enters: the cross term `θ (d (j.appTop x)) * θ (d (j.appTop y))` is a product of two sections of
the defining ideal of `i`, hence zero by
`Stacks.Thickenings.mul_eq_zero_of_mem_ker_appTop`, and the two surviving terms are the two
halves of the Leibniz rule for `d` after the scalar action of `Γ(Y, ⊤)` on the conormal module is
rewritten as multiplication by `a'.appTop` using `Stacks.Thickenings.conormalModuleAlong_smul`.

The scheme morphism is then recovered from its comorphism by `Stacks.Thickenings.homOfAppTop`,
which is legitimate because `Y'` is affine, and uniqueness of the lift comes from
`AlgebraicGeometry.ext_of_isAffine`: two morphisms into an affine scheme agreeing on global
sections are equal. Affineness of `S` is used only once, to promote the equality of comorphisms
`b'.appTop ∘ q.appTop = p.appTop` to the equality of morphisms `b' ≫ q = p` that makes `b'` a
morphism over `S`; that equality of comorphisms holds because `θ ∘ d` kills the image of
`(j ≫ q).appTop`, which is the structure map of the `Γ(S, ⊤)`-algebra `Γ(Y, ⊤)`.

The module and algebra structures involved are not instances — they are produced from the
first-order thickening hypotheses by `Stacks.Thickenings.conormalModuleAlong` and from the
structure morphisms by `Stacks.Thickenings.appTopAlgebra` — so they are introduced by `letI` in
the statements, as in `Stacks.Thickenings.mapDifferenceDerivation`. Since `θ` is typed in terms
of them, it is quantified *inside* the `letI`-prefixed type rather than bound as a parameter.

The simple transitivity of the action is the universal property of `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]`,
`Derivation.liftKaehlerDifferential`, applied to the difference derivation of
`Stacks.Thickenings.mapDifferenceDerivation` for the two deformations: a `θ` with
`θ ⬝ b = c` is the same thing as a linear map whose composite with `d_{Y/S}` is that derivation.
The universal property needs the two scalar actions on the conormal module to form a tower,
which holds because `a` is a morphism over `S`; that is
`Stacks.Thickenings.isScalarTower_conormalModuleAlong`.

Everything here is the affine case only; see the section on the general statements below.

### The general statements

The statements of this file are the affine cases of results proved for arbitrary schemes, with the
datum of the source a morphism of sheaves `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`.

* [Stacks Project, Tag 02H5] is `Stacks.Thickenings.existsUnique_derivationActionGlobal`. There
  the modified lift is built directly, its comorphism being defined over every open of `Y'` at
  once, and not by gluing the affine case proved here.
* [Stacks Project, Tag 0CK1] is `Stacks.Thickenings.differenceDerivation_derivationActionSheaf`,
  which characterises the lift `θ ⬝ a'` by the difference derivation
  `Stacks.Thickenings.differenceDerivation` of the general [Stacks Project, Tag 04FG] rather than
  by the sectionwise formula of `Stacks.Thickenings.derivationActionGlobal_appLE`.
* The **action** clause of [Stacks Project, Tag 04FJ], that
  `SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` acts on `Stacks.Thickenings.compatibleLiftsPresheaf`
  with condition (3) read on conormal *sheaves*, is
  `Stacks.Thickenings.exists_addAction_compatibleLifts`.
* The **transitivity** clause of [Stacks Project, Tag 04FJ], that over an open of `X'` carrying a
  lift this action is simply transitive, is
  `Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`. It is the general
  [Stacks Project, Tag 04FG], `Stacks.Thickenings.exists_isDerivationAction`, read for the
  restricted thickening `i ∣_ V` and transported to the conormal sheaves in which the sheaf of
  [Stacks Project, Tag 04FI] is stated. Here the clause is proved only for the global
  deformations over an affine `X'`, with condition (3) the equality of maps of conormal
  *modules* (`Stacks.Thickenings.existsUnique_act_eq`).

Affineness of `S` is used here only to recognise the constructed morphism as a morphism over `S`;
for sheaves that recognition is `Stacks.Thickenings.derivationActionSheaf_comp`, which needs no
affineness.

## References

* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 04FI](https://stacks.math.columbia.edu/tag/04FI)
* [Stacks Project, Tag 04FJ](https://stacks.math.columbia.edu/tag/04FJ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Thickenings

/-! ### A morphism into an affine scheme from a map of global sections -/

variable {S X X' Y Y' : Scheme.{u}}

/-- **The morphism into an affine scheme determined by a map of global sections.** For `T'`
affine, a map `φ : Γ(T', ⊤) ⟶ Γ(T, ⊤)` of global sections comes from a unique morphism
`T ⟶ T'`, namely this one; uniqueness is `AlgebraicGeometry.ext_of_isAffine`. -/
noncomputable def homOfAppTop {T T' : Scheme.{u}} [IsAffine T']
    (φ : Γ(T', (⊤ : T'.Opens)) ⟶ Γ(T, (⊤ : T.Opens))) : T ⟶ T' :=
  T.toSpecΓ ≫ Spec.map φ ≫ T'.isoSpec.inv

/-- `Stacks.Thickenings.homOfAppTop φ` acts on global sections as `φ`. -/
@[simp]
theorem homOfAppTop_appTop {T T' : Scheme.{u}} [IsAffine T']
    (φ : Γ(T', (⊤ : T'.Opens)) ⟶ Γ(T, (⊤ : T.Opens))) : (homOfAppTop φ).appTop = φ := by
  rw [homOfAppTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    Stacks.Modules.isoSpec_inv_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

/-! ### The modified comorphism -/

variable {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' : X' ⟶ Y'} {p : X' ⟶ S} {q : Y' ⟶ S}

/-- **The comorphism of the lift modified by a derivation.** Given a morphism of thickenings
`(a, a')` from `i : X ⟶ X'` to `j : Y ⟶ Y'` and a `Γ(Y, ⊤)`-linear map `θ` from the module of
relative differentials to the conormal module of `i`, this is the ring homomorphism
`x ↦ a'.appTop x + θ (d (j.appTop x))`, the comorphism `(a')^♯ + D` of the proof of
[Stacks Project, Tag 02H5] with `D = d_{Y/S} ∘ θ` as in Equation [Stacks Project, Tag 04BV]. -/
noncomputable def derivationActionAppTop [IsAffine X'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    (Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) →
      (Γ(Y', (⊤ : Y'.Opens)) →+* Γ(X', (⊤ : X'.Opens))) :=
  letI := appTopAlgebra (j ≫ q)
  letI := conormalModuleAlong hi a
  fun θ ↦
  { toFun := fun x ↦ a'.appTop.hom x +
      ((θ (KaehlerDifferential.D _ _ (j.appTop.hom x)) : RingHom.ker i.appTop.hom) :
        Γ(X', (⊤ : X'.Opens)))
    map_one' := by
      rw [map_one, map_one, Derivation.map_one_eq_zero, map_zero, ZeroMemClass.coe_zero, add_zero]
    map_zero' := by
      rw [map_zero, map_zero, map_zero, map_zero, ZeroMemClass.coe_zero, add_zero]
    map_add' := fun x y ↦ by
      rw [map_add, map_add, map_add, map_add, AddMemClass.coe_add]
      ring
    map_mul' := fun x y ↦ by
      have hz := mul_eq_zero_of_mem_ker_appTop hi
        (θ (KaehlerDifferential.D _ _ (j.appTop.hom x)))
        (θ (KaehlerDifferential.D _ _ (j.appTop.hom y)))
      rw [map_mul, map_mul, Derivation.leibniz, map_add, map_smul, map_smul, AddMemClass.coe_add,
        conormalModuleAlong_smul hi a (j.appTop.hom x) (x := a'.appTop.hom x)
          (appTop_comm_of_comm comm_a x),
        conormalModuleAlong_smul hi a (j.appTop.hom y) (x := a'.appTop.hom y)
          (appTop_comm_of_comm comm_a y),
        Submodule.coe_smul, Submodule.coe_smul, smul_eq_mul, smul_eq_mul]
      linear_combination -hz }

/-- The value of `Stacks.Thickenings.derivationActionAppTop`. -/
theorem derivationActionAppTop_apply [IsAffine X'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    ∀ (θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) (x : Γ(Y', (⊤ : Y'.Opens))),
      derivationActionAppTop hi comm_a q θ x = a'.appTop.hom x +
        ((θ (KaehlerDifferential.D _ _ (j.appTop.hom x)) : RingHom.ker i.appTop.hom) :
          Γ(X', (⊤ : X'.Opens))) :=
  fun _ _ ↦ rfl

/-! ### The modified lift -/

/-- **The lift modified by a derivation.** The morphism `b' : X' ⟶ Y'` of
[Stacks Project, Tag 02H5], whose comorphism is `Stacks.Thickenings.derivationActionAppTop`.
In the notation of [Stacks Project, Tag 0CK1] this is `θ ⬝ a'`. -/
noncomputable def derivationAction [IsAffine X'] [IsAffine Y'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    (Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) → (X' ⟶ Y') :=
  letI := appTopAlgebra (j ≫ q)
  letI := conormalModuleAlong hi a
  fun θ ↦ homOfAppTop (CommRingCat.ofHom (derivationActionAppTop hi comm_a q θ))

/-- The comorphism of `Stacks.Thickenings.derivationAction` is
`Stacks.Thickenings.derivationActionAppTop`. -/
theorem derivationAction_appTop [IsAffine X'] [IsAffine Y'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    ∀ (θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) (x : Γ(Y', (⊤ : Y'.Opens))),
      (derivationAction hi comm_a q θ).appTop.hom x = a'.appTop.hom x +
        ((θ (KaehlerDifferential.D _ _ (j.appTop.hom x)) : RingHom.ker i.appTop.hom) :
          Γ(X', (⊤ : X'.Opens))) := by
  intro θ x
  rw [derivationAction, homOfAppTop_appTop]
  rfl

/-! ### The modified lift is a lift over the base with the same conormal map -/

/-- Two morphisms into an affine scheme agreeing elementwise on global sections are equal. -/
private theorem ext_of_appTop_apply {T T' : Scheme.{u}} [IsAffine T'] {f g : T ⟶ T'}
    (h : ∀ x, f.appTop.hom x = g.appTop.hom x) : f = g :=
  AlgebraicGeometry.ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext h))

/-- **The modified lift is again a lift of `a`**, which is condition (1) of
[Stacks Project, Tag 04FG] for the pair `(a', b')`: it is a morphism of thickenings from
`i : X ⟶ X'` to `j : Y ⟶ Y'` whose restriction to the closed subschemes is the same `a`. The
perturbation `θ ∘ d` takes values in the defining ideal of `i`, so it disappears on `X`. -/
theorem derivationAction_comm [IsAffine X'] [IsAffine Y'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    ∀ θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom,
      i ≫ derivationAction hi comm_a q θ = a ≫ j := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  intro θ
  refine ext_of_appTop_apply fun x ↦ ?_
  have hker : i.appTop.hom
      ((θ (KaehlerDifferential.D _ _ (j.appTop.hom x)) : RingHom.ker i.appTop.hom) :
        Γ(X', (⊤ : X'.Opens))) = 0 :=
    RingHom.mem_ker.mp (θ (KaehlerDifferential.D _ _ (j.appTop.hom x))).2
  rw [← appTop_comp_apply, ← appTop_comp_apply, derivationAction_appTop, map_add, hker,
    appTop_comm_of_comm comm_a x, add_zero]

/-- **The modified lift is again a morphism over `S`.** The perturbation `θ ∘ d` kills the image
of `(j ≫ q).appTop`, which is the structure map of the `Γ(S, ⊤)`-algebra `Γ(Y, ⊤)`, because a
derivation kills the image of the algebra map. -/
theorem derivationAction_comp [IsAffine S] [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    ∀ θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom,
      derivationAction hi comm_a q θ ≫ q = p := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  intro θ
  refine ext_of_appTop_apply fun r ↦ ?_
  have halg : j.appTop.hom (q.appTop.hom r)
      = algebraMap Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) r := by
    rw [appTop_comp_apply, algebraMap_appTopAlgebra]
  have hd : KaehlerDifferential.D Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens))
      (j.appTop.hom (q.appTop.hom r)) = 0 := by
    rw [halg, Derivation.map_algebraMap]
  rw [← appTop_comp_apply, derivationAction_appTop, hd, map_zero, ZeroMemClass.coe_zero, add_zero,
    appTop_comp_apply, ha']

/-- **The modified lift has the same conormal map as the original**, which is condition (2) of
[Stacks Project, Tag 04FG] for the pair `(a', b')`. The perturbation `θ ∘ d ∘ j^♯` vanishes on
the defining ideal of `j`, which is the kernel of `j^♯`. -/
theorem derivationAction_conormalMap [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    ∀ θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom,
      conormalMap hi hj (derivationAction_comm hi comm_a q θ) = conormalMap hi hj comm_a := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  let := Smooth.thickeningKerModule hj
  intro θ
  refine LinearMap.ext fun z ↦ Subtype.ext ?_
  have hz : j.appTop.hom (z : Γ(Y', (⊤ : Y'.Opens))) = 0 := RingHom.mem_ker.mp z.2
  rw [conormalMap_apply, conormalMap_apply, derivationAction_appTop, hz, map_zero, map_zero,
    ZeroMemClass.coe_zero, add_zero]

/-! ### The difference derivation of the modified lift -/

/-- **Equation [Stacks Project, Tag 04BV] for the modified lift.** The difference derivation of
[Stacks Project, Tag 04FG] for the pair `(b', a')`, with `b'` the lift modified by `θ`, is
`d_{Y/S}` followed by `θ`. Equivalently, [Stacks Project, Tag 0CK1]: the comorphisms `(a')^♯` and
`(θ ⬝ a')^♯` differ by a derivation `D`, and `D` is related to `θ` by that equation.

This covers that tag only over affine `S`, `X'` and `Y'`, and with the datum `θ` read on global
sections as a map out of `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]`. The general statement, for arbitrary schemes and
with the datum of the source, is `Stacks.Thickenings.differenceDerivation_derivationActionSheaf`.
-/
theorem derivationAction_mapDifferenceDerivation [IsAffine S] [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    ∀ (θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) (f : Γ(Y, (⊤ : Y.Opens))),
      mapDifferenceDerivation hi hj (derivationAction_comm hi comm_a q θ) comm_a
          (derivationAction_comp hi comm_a ha' θ) ha'
          (derivationAction_conormalMap hi hj comm_a q θ) f
        = θ (KaehlerDifferential.D _ _ f) := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  let := conormalModuleAlong hi (i ≫ p)
  intro θ f
  obtain ⟨x, rfl⟩ := Smooth.surjective_appTop_of_isFirstOrderThickening hj f
  refine Subtype.ext ?_
  rw [mapDifferenceDerivation_appTop, derivationAction_appTop]
  ring

/-- **Uniqueness of the modified lift.** Any lift of `a` over `S` with the same conormal map as
`a'` whose difference derivation from `a'` is `d_{Y/S}` followed by `θ` is the lift constructed
by `Stacks.Thickenings.derivationAction`. -/
theorem eq_derivationAction [IsAffine S] [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    ∀ (θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) (c : X' ⟶ Y') (comm_c : i ≫ c = a ≫ j) (hc : c ≫ q = p)
      (hC : conormalMap hi hj comm_c = conormalMap hi hj comm_a),
      (∀ f : Γ(Y, (⊤ : Y.Opens)), mapDifferenceDerivation hi hj comm_c comm_a hc ha' hC f
          = θ (KaehlerDifferential.D _ _ f)) →
        c = derivationAction hi comm_a q θ := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  let := conormalModuleAlong hi (i ≫ p)
  intro θ c comm_c hc hC hD
  refine ext_of_appTop_apply fun x ↦ ?_
  have h := congrArg (fun z : RingHom.ker i.appTop.hom ↦ (z : Γ(X', (⊤ : X'.Opens))))
    (hD (j.appTop.hom x))
  rw [mapDifferenceDerivation_appTop] at h
  rw [derivationAction_appTop, ← h]
  ring

/-! ### The action of a derivation on a lift -/

/-- **A derivation acts in exactly one way on a lift of a map**, the affine case of
[Stacks Project, Tag 02H5]. Let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings with
`X'`, `Y'` and `S` affine, let `p : X' ⟶ S` and `q : Y' ⟶ S` make them thickenings over `S`, and
let `(a, a')` be a morphism of thickenings over `S`. Then for every `Γ(Y, ⊤)`-linear map
`θ : Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)] ⟶ 𝒞_{X/X'}` there is exactly one morphism `b' : X' ⟶ Y'` such that
`(a, b')` is a morphism of thickenings over `S` — so that conditions (1) and (2) of
[Stacks Project, Tag 04FG] hold for `(a', b')` — and the difference derivation `D` of
[Stacks Project, Tag 04FG] is related to `θ` by Equation [Stacks Project, Tag 04BV],
`D = d_{Y/S} ∘ θ`.

Condition (1) of the source, that the two reductions agree, is built into the statement by
writing both squares over the same `a`. -/
theorem existsUnique_derivationAction [IsAffine S] [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    ∀ θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom,
      ∃! b' : X' ⟶ Y', ∃ (comm_b : i ≫ b' = a ≫ j) (hb' : b' ≫ q = p)
        (hC : conormalMap hi hj comm_b = conormalMap hi hj comm_a),
        ∀ f : Γ(Y, (⊤ : Y.Opens)), mapDifferenceDerivation hi hj comm_b comm_a hb' ha' hC f
          = θ (KaehlerDifferential.D _ _ f) := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  let := conormalModuleAlong hi (i ≫ p)
  intro θ
  refine ⟨derivationAction hi comm_a q θ, ⟨derivationAction_comm hi comm_a q θ,
    derivationAction_comp hi comm_a ha' θ, derivationAction_conormalMap hi hj comm_a q θ,
    derivationAction_mapDifferenceDerivation hi hj comm_a ha' θ⟩, ?_⟩
  rintro c ⟨comm_c, hc, hC, hD⟩
  exact eq_derivationAction hi hj comm_a ha' θ c comm_c hc hC hD

/-! ### The action laws -/

/-- **The zero map acts trivially on a lift.** -/
theorem derivationAction_zero [IsAffine X'] [IsAffine Y'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    derivationAction hi comm_a q 0 = a' := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  refine ext_of_appTop_apply fun x ↦ ?_
  rw [derivationAction_appTop, LinearMap.zero_apply, ZeroMemClass.coe_zero, add_zero]

/-- **A sum acts as the composite of the two actions.** Moving a lift by `θ + η` is moving it by
`η` and then moving the result by `θ`. -/
theorem derivationAction_add [IsAffine X'] [IsAffine Y'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (q : Y' ⟶ S) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    ∀ θ η : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom,
      derivationAction hi comm_a q (θ + η)
        = derivationAction hi (derivationAction_comm hi comm_a q η) q θ := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  intro θ η
  refine ext_of_appTop_apply fun x ↦ ?_
  rw [derivationAction_appTop, derivationAction_appTop, derivationAction_appTop,
    LinearMap.add_apply, AddMemClass.coe_add]
  ring

/-! ### The deformations of a map and the action on them -/

/-- **The two module structures on the conormal module form a scalar tower.** The conormal module
of `i : X ⟶ X'` is a `Γ(Y, ⊤)`-module through `a` and a `Γ(S, ⊤)`-module through the structure
morphism `i ≫ p` of `X` over `S`; if `a ≫ j ≫ q = i ≫ p` the latter action is the former
restricted along the algebra map `(j ≫ q).appTop`. -/
theorem isScalarTower_conormalModuleAlong [IsAffine X'] (hi : IsFirstOrderThickening i)
    (a : X ⟶ Y) (p : X' ⟶ S) (q : Y' ⟶ S) (hpq : a ≫ j ≫ q = i ≫ p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    IsScalarTower Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) (RingHom.ker i.appTop.hom) := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  let := conormalModuleAlong hi (i ≫ p)
  refine IsScalarTower.of_algebraMap_smul fun r m ↦ ?_
  rw [algebraMap_appTopAlgebra,
    conormalModuleAlong_smul hi a ((j ≫ q).appTop.hom r) (x := p.appTop.hom r)
      (by rw [appTop_comp_apply, appTop_comp_apply, hpq]),
    conormalModuleAlong_smul hi (i ≫ p) r (x := p.appTop.hom r) (appTop_comp_apply i p r)]

/-! ### The datum of the source: a map out of the pulled-back sheaf of differentials -/

/-- **Sections over the two top opens.** The map `Scheme.Hom.appLE` of a morphism over the top
open of the target and the top open of the source is `Scheme.Hom.appTop`. -/
theorem appLE_top_top {A B : Scheme.{u}} (g : A ⟶ B)
    (h : (⊤ : A.Opens) ≤ g ⁻¹ᵁ (⊤ : B.Opens)) :
    g.appLE (⊤ : B.Opens) (⊤ : A.Opens) h = g.appTop :=
  Scheme.Hom.appLE_eq_app g (U := ⊤)

/-- **The universal differential of `Ω_{Y/S}`, pulled back along `g : X ⟶ Y`, on global
sections.** This is `Stacks.Smooth.pullbackD` over the two top opens, the map
`d : Γ(Y, ⊤) ⟶ Γ(g^*Ω_{Y/S}, ⊤)` through which Equation [Stacks Project, Tag 04BV] reads the
datum `θ` of [Stacks Project, Tag 02H5] as a derivation. -/
noncomputable abbrev pullbackDTop (f : Y ⟶ S) (g : X ⟶ Y) :
    Γ(Y, (⊤ : Y.Opens)) →+ Γ(Smooth.pullbackCotangentSheaf f g, (⊤ : X.Opens)) :=
  Smooth.pullbackD f g ⊤ le_top

/-- The Leibniz rule for `Stacks.Thickenings.pullbackDTop`, with the action of `Γ(Y, ⊤)` on the
sections of `g^*Ω_{Y/S}` written through `g.appTop`. -/
theorem pullbackDTop_mul (f : Y ⟶ S) (g : X ⟶ Y) (b₁ b₂ : Γ(Y, (⊤ : Y.Opens))) :
    pullbackDTop f g (b₁ * b₂)
      = g.appTop.hom b₁ • pullbackDTop f g b₂ + g.appTop.hom b₂ • pullbackDTop f g b₁ := by
  rw [← appLE_top_top g le_top]
  exact Smooth.pullbackD_mul' f g ⊤ le_top b₁ b₂

/-- `Stacks.Thickenings.pullbackDTop` kills the unit section. -/
theorem pullbackDTop_one (f : Y ⟶ S) (g : X ⟶ Y) : pullbackDTop f g 1 = 0 :=
  Smooth.pullbackD_one f g ⊤ le_top

/-- `Stacks.Thickenings.pullbackDTop` kills the sections coming from the base, which is the
`𝒪_S`-linearity of the universal derivation of `Ω_{Y/S}`. -/
theorem pullbackDTop_appTop (f : Y ⟶ S) (g : X ⟶ Y) (r : Γ(S, (⊤ : S.Opens))) :
    pullbackDTop f g (f.appTop.hom r) = 0 := by
  rw [← appLE_top_top f le_top]
  exact Smooth.pullbackD_appLE f g ⊤ le_top le_top r

/-- **The two actions on the conormal module agree through `f.appTop`.** The action of `Γ(T, ⊤)`
on the conormal module of `i : X ⟶ X'` given by `Stacks.Thickenings.conormalModuleAlong hi f` is
the action of `Γ(X, ⊤)` of `Stacks.Smooth.thickeningKerModule hi` on the image of the scalar
under `f.appTop`; that is what the first is a restriction of scalars of. -/
theorem conormalModuleAlong_smul_appTop [IsAffine X'] {i : X ⟶ X'}
    (hi : IsFirstOrderThickening i) (f : X ⟶ Y) (c : Γ(Y, (⊤ : Y.Opens)))
    (y : RingHom.ker i.appTop.hom) :
    letI := conormalModuleAlong hi f
    letI := Smooth.thickeningKerModule hi
    c • y = f.appTop.hom c • y := by
  let := conormalModuleAlong hi f
  let := Smooth.thickeningKerModule hi
  obtain ⟨x, hx⟩ := Smooth.surjective_appTop_of_isFirstOrderThickening hi (f.appTop.hom c)
  rw [conormalModuleAlong_smul hi f c hx, ← hx, Smooth.thickeningKerModule_smul hi]

/-- **The structure morphism of `X` over `S` read through the target.** For a morphism of
thickenings `(a, a')` over `S`, going from `X` to `S` through `Y` and `Y'` is the structure
morphism `i ≫ p`. -/
theorem comm_structureMorphism (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    a ≫ j ≫ q = i ≫ p := by
  rw [← Category.assoc, ← comm_a, Category.assoc, ha']

/-- **The derivation attached to the datum of the source.** An `𝒪_X`-linear map
`θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`, read on global sections over the affine `X'`, composed with the
pulled-back universal differential `Stacks.Thickenings.pullbackDTop`, is a `Γ(S, ⊤)`-derivation
of `Γ(Y, ⊤)` with values in the conormal module. This is the derivation `D = θ ∘ d_{Y/S}` of
Equation [Stacks Project, Tag 04BV].

The Leibniz rule and the `𝒪_S`-linearity are those of `Stacks.Thickenings.pullbackDTop`, carried
through the `Γ(X, ⊤)`-linearity of `θ` by
`Stacks.Thickenings.conormalModuleAlong_smul_appTop`. -/
noncomputable def cotangentSheafDerivation [IsAffine X'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    letI := Smooth.thickeningKerModule hi
    (Γ(Smooth.pullbackCotangentSheaf (j ≫ q) a, (⊤ : X.Opens)) →ₗ[Γ(X, (⊤ : X.Opens))]
        RingHom.ker i.appTop.hom) →
      Derivation Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) (RingHom.ker i.appTop.hom) :=
  letI := appTopAlgebra (j ≫ q)
  letI := conormalModuleAlong hi a
  letI := conormalModuleAlong hi (i ≫ p)
  letI := Smooth.thickeningKerModule hi
  fun θ ↦
  { toFun := fun f ↦ θ (pullbackDTop (j ≫ q) a f)
    map_add' := fun f g ↦ by rw [map_add, map_add]
    map_smul' := fun r f ↦ by
      have hr : r • f = (j ≫ q).appTop.hom r * f := by
        rw [Algebra.smul_def, algebraMap_appTopAlgebra]
      have hcoef : a.appTop.hom ((j ≫ q).appTop.hom r) = (i ≫ p).appTop.hom r := by
        rw [appTop_comp_apply, comm_structureMorphism comm_a ha']
      rw [RingHom.id_apply, hr, pullbackDTop_mul, map_add, map_smul, map_smul,
        pullbackDTop_appTop, map_zero, smul_zero, add_zero, hcoef,
        conormalModuleAlong_smul_appTop hi (i ≫ p) r]
    map_one_eq_zero' := by
      change θ (pullbackDTop (j ≫ q) a 1) = 0
      rw [pullbackDTop_one, map_zero]
    leibniz' := fun f g ↦ by
      change θ (pullbackDTop (j ≫ q) a (f * g)) = _
      rw [pullbackDTop_mul, map_add, map_smul, map_smul,
        conormalModuleAlong_smul_appTop hi a f, conormalModuleAlong_smul_appTop hi a g]
      rfl }

/-- The value of `Stacks.Thickenings.cotangentSheafDerivation` is `θ` applied to the pulled-back
universal differential. -/
theorem cotangentSheafDerivation_apply [IsAffine X'] (hi : IsFirstOrderThickening i)
    (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    letI := Smooth.thickeningKerModule hi
    ∀ (θ : Γ(Smooth.pullbackCotangentSheaf (j ≫ q) a, (⊤ : X.Opens)) →ₗ[Γ(X, (⊤ : X.Opens))]
        RingHom.ker i.appTop.hom) (f : Γ(Y, (⊤ : Y.Opens))),
      cotangentSheafDerivation hi comm_a ha' θ f = θ (pullbackDTop (j ≫ q) a f) :=
  fun _ _ ↦ rfl

/-- **A map out of the pulled-back sheaf of relative differentials acts in exactly one way on a
lift of a map**, the affine case of [Stacks Project, Tag 02H5] with the datum of the source. Let
`i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings with `X'`, `Y'` and `S` affine, let
`p : X' ⟶ S` and `q : Y' ⟶ S` make them thickenings over `S`, and let `(a, a')` be a morphism of
thickenings over `S`. Then for every `𝒪_X`-linear map `θ : a^*Ω_{Y/S} ⟶ 𝒞_{X/X'}`, read over the
affine `X'` as a `Γ(X, ⊤)`-linear map on global sections, there is exactly one morphism
`b' : X' ⟶ Y'` such that `(a, b')` is a morphism of thickenings over `S` — so that conditions (1)
and (2) of [Stacks Project, Tag 04FG] hold for `(a', b')` — and the difference derivation `D` of
[Stacks Project, Tag 04FG] is related to `θ` by Equation [Stacks Project, Tag 04BV],
`D = θ ∘ d_{Y/S}`.

This differs from `Stacks.Thickenings.existsUnique_derivationAction` in the datum only: there the
map is out of Mathlib's `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]`, here out of the global sections of the
**sheaf** `a^*Ω_{Y/S}` of the source, with `d_{Y/S}` the universal derivation of
`Stacks.Smooth.cotangentSheaf`. The two agree over an affine base, and the translation is the
universal property `Derivation.liftKaehlerDifferential` applied to
`Stacks.Thickenings.cotangentSheafDerivation`.

Here `X'`, `Y'` and `S` are affine; the general statement is
`Stacks.Thickenings.existsUnique_derivationActionGlobal`. -/
@[sga "3 XII 9.4" "Affine global case"]
theorem existsUnique_derivationAction_cotangentSheaf [IsAffine S] [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    letI := conormalModuleAlong hi (i ≫ p)
    letI := Smooth.thickeningKerModule hi
    ∀ θ : Γ(Smooth.pullbackCotangentSheaf (j ≫ q) a, (⊤ : X.Opens)) →ₗ[Γ(X, (⊤ : X.Opens))]
        RingHom.ker i.appTop.hom,
      ∃! b' : X' ⟶ Y', ∃ (comm_b : i ≫ b' = a ≫ j) (hb' : b' ≫ q = p)
        (hC : conormalMap hi hj comm_b = conormalMap hi hj comm_a),
        ∀ f : Γ(Y, (⊤ : Y.Opens)), mapDifferenceDerivation hi hj comm_b comm_a hb' ha' hC f
          = θ (pullbackDTop (j ≫ q) a f) := by
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  let := conormalModuleAlong hi (i ≫ p)
  let := Smooth.thickeningKerModule hi
  intro θ
  have := isScalarTower_conormalModuleAlong hi a p q (comm_structureMorphism comm_a ha')
  set δ := cotangentSheafDerivation hi comm_a ha' θ
  obtain ⟨b, ⟨c1, c2, c3, hD⟩, hu⟩ :=
    existsUnique_derivationAction hi hj comm_a ha' δ.liftKaehlerDifferential
  refine ⟨b, ⟨c1, c2, c3, fun f ↦ (hD f).trans
    (Derivation.liftKaehlerDifferential_comp_D δ f)⟩, ?_⟩
  rintro c ⟨d1, d2, d3, hDc⟩
  exact hu c ⟨d1, d2, d3, fun f ↦ (hDc f).trans
    (Derivation.liftKaehlerDifferential_comp_D δ f).symm⟩

/-- **A deformation of `a` with conormal map `A`.** For first-order thickenings `i : X ⟶ X'` and
`j : Y ⟶ Y'` of affine schemes over `S`, this is a morphism `X' ⟶ Y'` over `S` restricting to
`a` on the closed subschemes and inducing `A` on conormal modules — the three conditions of
[Stacks Project, Tag 04FI] over all of `X'`, in the affine form in which
[Stacks Project, Tag 04FG] and [Stacks Project, Tag 02H5] are available here. -/
structure Deformation [IsAffine X'] [IsAffine Y'] (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (p : X' ⟶ S) (q : Y' ⟶ S) (a : X ⟶ Y)
    (A : letI := Smooth.thickeningKerModule hj
      letI := conormalModuleAlong hi a
      RingHom.ker j.appTop.hom →ₗ[Γ(Y, (⊤ : Y.Opens))] RingHom.ker i.appTop.hom) where
  /-- The underlying morphism `X' ⟶ Y'`. -/
  hom : X' ⟶ Y'
  /-- Condition (2) of [Stacks Project, Tag 04FI]: the morphism restricts to `a` on `X`. -/
  comm : i ≫ hom = a ≫ j
  /-- Condition (1) of [Stacks Project, Tag 04FI]: the morphism is a morphism over `S`. -/
  over : hom ≫ q = p
  /-- Condition (3) of [Stacks Project, Tag 04FI]: the induced map of conormal modules is `A`. -/
  conormal : conormalMap hi hj comm = A

variable {hi : IsFirstOrderThickening i} {hj : IsFirstOrderThickening j}

/-- Two deformations with the same underlying morphism are equal: the remaining fields are
propositions. -/
theorem Deformation.ext [IsAffine X'] [IsAffine Y'] {p : X' ⟶ S} {q : Y' ⟶ S} {a : X ⟶ Y}
    {A : letI := Smooth.thickeningKerModule hj
      letI := conormalModuleAlong hi a
      RingHom.ker j.appTop.hom →ₗ[Γ(Y, (⊤ : Y.Opens))] RingHom.ker i.appTop.hom}
    {b c : Deformation hi hj p q a A} (h : b.hom = c.hom) : b = c := by
  revert h
  obtain ⟨hb, -, -, -⟩ := b
  obtain ⟨hc, -, -, -⟩ := c
  intro h
  cases show hb = hc from h
  rfl

/-- **A morphism of thickenings over `S` is a deformation of its reduction**, with conormal map
its own. So the deformations of `a` with a given conormal map are inhabited exactly when `a` has
a lift inducing that map. -/
def Deformation.of [IsAffine X'] [IsAffine Y'] (comm_a : i ≫ a' = a ≫ j) (ha' : a' ≫ q = p) :
    Deformation hi hj p q a (conormalMap hi hj comm_a) where
  hom := a'
  comm := comm_a
  over := ha'
  conormal := rfl

/-- **The action of a derivation on a deformation.** The lift moved by `θ`, that is
`Stacks.Thickenings.derivationAction`, is again a deformation with the same conormal map. In the
notation of [Stacks Project, Tag 0CK1] this is `θ ⬝ b`. -/
noncomputable def Deformation.act [IsAffine S] [IsAffine X'] [IsAffine Y'] {p : X' ⟶ S}
    {q : Y' ⟶ S} {a : X ⟶ Y}
    {A : letI := Smooth.thickeningKerModule hj
      letI := conormalModuleAlong hi a
      RingHom.ker j.appTop.hom →ₗ[Γ(Y, (⊤ : Y.Opens))] RingHom.ker i.appTop.hom}
    (b : Deformation hi hj p q a A) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    (Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) → Deformation hi hj p q a A :=
  letI := appTopAlgebra (j ≫ q)
  letI := conormalModuleAlong hi a
  fun θ ↦
  { hom := derivationAction hi b.comm q θ
    comm := derivationAction_comm hi b.comm q θ
    over := derivationAction_comp hi b.comm b.over θ
    conormal := (derivationAction_conormalMap hi hj b.comm q θ).trans b.conormal }

/-- **The action of [Stacks Project, Tag 04FJ], affine case.** The additive group of
`Γ(Y, ⊤)`-linear maps `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)] ⟶ 𝒞_{X/X'}` — the sections over the affine `X'` of
`SheafHom_{𝒪_X}(a^*Ω_{Y/S}, 𝒞_{X/X'})` — acts on the deformations of `a` with conormal map `A`,
by `Stacks.Thickenings.Deformation.act`. -/
@[instance_reducible,
  stacks 04FJ "the action on the deformations with a fixed conormal map, over affine schemes"]
noncomputable def deformationAddAction [IsAffine S] [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j) (p : X' ⟶ S) (q : Y' ⟶ S)
    (a : X ⟶ Y)
    (A : letI := Smooth.thickeningKerModule hj
      letI := conormalModuleAlong hi a
      RingHom.ker j.appTop.hom →ₗ[Γ(Y, (⊤ : Y.Opens))] RingHom.ker i.appTop.hom) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    AddAction (Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
        RingHom.ker i.appTop.hom) (Deformation hi hj p q a A) :=
  letI := appTopAlgebra (j ≫ q)
  letI := conormalModuleAlong hi a
  { vadd := fun θ b ↦ b.act θ
    zero_vadd := fun b ↦ Deformation.ext (derivationAction_zero hi b.comm q)
    add_vadd := fun θ η b ↦ Deformation.ext (derivationAction_add hi b.comm q θ η) }

/-- **Simple transitivity of the action of [Stacks Project, Tag 04FJ], affine case.** Over an
`X'` carrying at least one deformation `b` of `a` with conormal map `A` — the hypothesis of the
source that the sheaf of [Stacks Project, Tag 04FI] has a section there — every deformation `c`
of `a` with conormal map `A` is `θ ⬝ b` for exactly one `θ`.

Existence is the universal property of `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]` applied to the difference derivation
of [Stacks Project, Tag 04FG] for the pair `(c, b)`; uniqueness is the uniqueness in
[Stacks Project, Tag 02H5] together with that universal property.

This covers the transitivity clause of that tag only over affine `S`, `X'` and `Y'`, with the
open `V` of the source taken to be `X'` itself, the datum `θ` read on global sections as a map
out of `Ω[Γ(Y, ⊤)⁄Γ(S, ⊤)]`, and condition (3) the equality of maps of conormal *modules*. The
general statement, for arbitrary schemes, an arbitrary open and the datum of the source, is
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`. -/
theorem existsUnique_act_eq [IsAffine S] [IsAffine X'] [IsAffine Y']
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j) (p : X' ⟶ S) (q : Y' ⟶ S)
    (a : X ⟶ Y)
    (A : letI := Smooth.thickeningKerModule hj
      letI := conormalModuleAlong hi a
      RingHom.ker j.appTop.hom →ₗ[Γ(Y, (⊤ : Y.Opens))] RingHom.ker i.appTop.hom) :
    letI := appTopAlgebra (j ≫ q)
    letI := conormalModuleAlong hi a
    ∀ b c : Deformation hi hj p q a A,
      ∃! θ : Ω[Γ(Y, (⊤ : Y.Opens))⁄Γ(S, (⊤ : S.Opens))] →ₗ[Γ(Y, (⊤ : Y.Opens))]
          RingHom.ker i.appTop.hom, b.act θ = c := by
  let := Smooth.thickeningKerModule hj
  let := appTopAlgebra (j ≫ q)
  let := conormalModuleAlong hi a
  let := conormalModuleAlong hi (i ≫ p)
  intro b c
  have := isScalarTower_conormalModuleAlong hi a p q (comm_structureMorphism b.comm b.over)
  have hC : conormalMap hi hj c.comm = conormalMap hi hj b.comm :=
    c.conormal.trans b.conormal.symm
  refine ⟨(mapDifferenceDerivation hi hj c.comm b.comm c.over b.over hC).liftKaehlerDifferential,
    Deformation.ext ?_, ?_⟩
  · exact (eq_derivationAction hi hj b.comm b.over _ c.hom c.comm c.over hC
      fun f ↦ (Derivation.liftKaehlerDifferential_comp_D _ f).symm).symm
  · intro η hη
    have hη' : derivationAction hi b.comm q η = c.hom :=
      congrArg (fun d : Deformation hi hj p q a A ↦ d.hom) hη
    have key : ∀ x : Γ(Y', (⊤ : Y'.Opens)),
        η (KaehlerDifferential.D Γ(S, (⊤ : S.Opens)) Γ(Y, (⊤ : Y.Opens)) (j.appTop.hom x))
          = mapDifferenceDerivation hi hj c.comm b.comm c.over b.over hC (j.appTop.hom x) := by
      intro x
      have h1 := mapDifferenceDerivation_appTop hi hj c.comm b.comm c.over b.over hC x
      have h2 := derivationAction_appTop hi b.comm q η x
      rw [hη'] at h2
      refine Subtype.ext ?_
      rw [h1, h2]
      ring
    refine Derivation.liftKaehlerDifferential_unique η _ (Derivation.ext fun f ↦ ?_)
    obtain ⟨x, rfl⟩ := Smooth.surjective_appTop_of_isFirstOrderThickening hj f
    exact (key x).trans (Derivation.liftKaehlerDifferential_comp_D _ _).symm

end Stacks.Thickenings

end
