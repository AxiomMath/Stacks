module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Extension
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.RingTheory.Etale.Basic

/-!
# Étaleness extends over a thickening whose ideal sheaves are related by base change

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a commutative square of schemes in which `i` and `j` are closed immersions and the kernel
ideal sheaf of `j` has square zero. If the ideal sheaf of `X` in `X'` is the base change along
`f'` of the ideal sheaf of `Y` in `Y'`, and `f` is étale, then `f'` is étale.

On a pair of affine opens `V' ⊆ Y'` and `U' ⊆ X'` with `f'(U') ⊆ V'` this is exactly the
algebra statement [Stacks Project, Tag 05YT]: write `A' = Γ(Y', V')`, `B' = Γ(X', U')`,
`A = Γ(Y, j⁻¹V')`, `B = Γ(X, i⁻¹U')`; the two closed immersions make `A' → A` and `B' → B`
surjective, the square-zero condition makes `I = ker (A' → A)` an ideal of square zero, the
hypothesis makes `J = ker (B' → B)` the base change `I ⊗_{A'} B'`, and `A → B` is étale
because `j⁻¹V'` and `i⁻¹U'` are affine.

## Main definitions

* `Stacks.Thickenings.IsKerBaseChange`: the affine-local condition that the kernel ideal of the
  source closed immersion is the base change of the kernel ideal of the target closed immersion.

## Main results

* `Stacks.Thickenings.etale_of_isKerBaseChange`: the scheme-level form of
  [Stacks Project, Tag 05YT].
* `Stacks.Thickenings.CartesianFiniteTypeMorphism.etale_iff`: the same statement for a cartesian
  morphism of thickenings with locally finite type components, where the cartesian square also
  gives the converse implication by base change.

## Implementation notes

The base-change condition cannot be dropped, and Tag 0BPG, which lists the properties invariant
under a cartesian morphism of thickenings with locally finite type components, has no étale
clause. Take `Y' = Spec k[x]/(x²)`, `Y = X = X' = Spec k`, with `j`
the closed immersion, `i` the identity and `f` the identity: the square is cartesian, both
horizontal maps are locally of finite type, `f` is étale, and `f'` is the closed immersion
`Spec k ⟶ Spec k[x]/(x²)`, which is not flat and so not étale. What fails is precisely the
hypothesis below: `I = (x)` is one-dimensional over `k` while `J = 0`.

`Stacks.Thickenings.IsKerBaseChange` is phrased as a condition on every `A'`-linear map `I → J`
lifting the ring map `A' → B'`; such a map is unique. The ideals are written as kernels of the
maps on sections rather than as the sections of the ideal sheaves `Scheme.Hom.ker`; the two agree
by `AlgebraicGeometry.Scheme.Hom.ker_apply`, a closed immersion being quasi-compact.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 05YT](https://stacks.math.columbia.edu/tag/05YT)
* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

variable {X X' Y Y' : Scheme.{u}}

/-- The map on sections of a morphism of schemes depends only on the morphism, not on the proof
that the open set is carried into the other. -/
private theorem appLE_eq_appLE_of_eq {Z W : Scheme.{u}} {g₁ g₂ : Z ⟶ W} (h : g₁ = g₂)
    (U : W.Opens) (V : Z.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) (e₂ : V ≤ g₂ ⁻¹ᵁ U) :
    g₁.appLE U V e₁ = g₂.appLE U V e₂ := by
  subst h; rfl

/-- The ideal sheaf of `X` in `X'` is the base change of the ideal sheaf of `Y` in `Y'`: for a
commutative square with vertical closed immersions `i : X ⟶ X'`, `j : Y ⟶ Y'` and
horizontal map `f' : X' ⟶ Y'`, this says that on every pair of affine opens `V' ⊆ Y'` and
`U' ⊆ X'` with `f'(U') ⊆ V'` the ideal `J = ker (Γ(X', U') → Γ(X, i⁻¹U'))` is the base change
along `Γ(Y', V') → Γ(X', U')` of the ideal `I = ker (Γ(Y', V') → Γ(Y, j⁻¹V'))`. -/
def IsKerBaseChange (i : X ⟶ X') (f' : X' ⟶ Y') (j : Y ⟶ Y') : Prop :=
  ∀ (V' : Y'.Opens), IsAffineOpen V' → ∀ (U' : X'.Opens), IsAffineOpen U' →
    ∀ e : U' ≤ f' ⁻¹ᵁ V',
      letI : Algebra Γ(Y', V') Γ(X', U') := (f'.appLE V' U' e).hom.toAlgebra
      ∀ g : ↥(RingHom.ker (j.app V').hom) →ₗ[Γ(Y', V')] ↥(RingHom.ker (i.app U').hom),
        (∀ x, (g x : Γ(X', U')) = (f'.appLE V' U' e).hom (x : Γ(Y', V'))) →
          IsBaseChange Γ(X', U') g

/-- Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a commutative square of schemes with `i` and `j` closed immersions. If the kernel ideal
sheaf of `j` has square zero, the kernel ideal sheaf of `i` is the base change along `f'` of the
kernel ideal sheaf of `j`, and `f` is étale, then `f'` is étale. The two hypotheses on `j`
together say that `j` is a first-order thickening, `Stacks.Thickenings.IsFirstOrderThickening`;
nothing is assumed about the order of `i`, nor that either closed immersion is surjective on
points. -/
@[stacks 05YT "The scheme-level form: on a commutative square of schemes with closed immersions
`i : X ⟶ X'` and `j : Y ⟶ Y'`, square-zero kernel ideal sheaf for `j` and the kernel ideal of
`i` the base change along `f'` of that of `j`, étaleness of `f` gives étaleness of `f'`. The
affine-local content on each pair of affine opens is the lemma itself, which is already proved
for ring maps as `Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange`; what is proved here is the
reduction of the scheme statement to it."]
theorem etale_of_isKerBaseChange {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    [IsClosedImmersion i] [IsClosedImmersion j] (hcomm : i ≫ f' = f ≫ j) (hj : j.ker ^ 2 = ⊥)
    (hbc : IsKerBaseChange i f' j) [Etale f] : Etale f' := by
  constructor
  intro V' hV' U' hU' e
  have hbase (x : X) : f'.base (i.base x) = j.base (f.base x) := by
    simpa using congrArg (fun k : X ⟶ Y' => k.base x) hcomm
  have e₂ : i ⁻¹ᵁ U' ≤ f ⁻¹ᵁ (j ⁻¹ᵁ V') := fun x hx => by
    have h1 : f'.base (i.base x) ∈ V' := e hx
    rwa [hbase x] at h1
  have hsqcat : f'.appLE V' U' e ≫ i.app U' = j.app V' ≫ f.appLE (j ⁻¹ᵁ V') (i ⁻¹ᵁ U') e₂ := by
    rw [Scheme.Hom.app_eq_appLE (f := i) (U := U'),
      Scheme.Hom.app_eq_appLE (f := j) (U := V'),
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_appLE_of_eq hcomm _ _ _ _
  have hsq : (i.app U').hom.comp (f'.appLE V' U' e).hom =
      (f.appLE (j ⁻¹ᵁ V') (i ⁻¹ᵁ U') e₂).hom.comp (j.app V').hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hsqcat]
  let : Algebra Γ(Y', V') Γ(Y, j ⁻¹ᵁ V') := (j.app V').hom.toAlgebra
  let : Algebra Γ(Y', V') Γ(X', U') := (f'.appLE V' U' e).hom.toAlgebra
  let : Algebra Γ(X', U') Γ(X, i ⁻¹ᵁ U') := (i.app U').hom.toAlgebra
  let : Algebra Γ(Y, j ⁻¹ᵁ V') Γ(X, i ⁻¹ᵁ U') :=
    (f.appLE (j ⁻¹ᵁ V') (i ⁻¹ᵁ U') e₂).hom.toAlgebra
  let : Algebra Γ(Y', V') Γ(X, i ⁻¹ᵁ U') :=
    ((i.app U').hom.comp (f'.appLE V' U' e).hom).toAlgebra
  have : IsScalarTower Γ(Y', V') Γ(X', U') Γ(X, i ⁻¹ᵁ U') :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y', V') Γ(Y, j ⁻¹ᵁ V') Γ(X, i ⁻¹ᵁ U') :=
    IsScalarTower.of_algebraMap_eq' hsq
  have : Algebra.Etale Γ(Y, j ⁻¹ᵁ V') Γ(X, i ⁻¹ᵁ U') :=
    f.etale_appLE (hV'.preimage j) (hU'.preimage i) e₂
  have hA : Function.Surjective (algebraMap Γ(Y', V') Γ(Y, j ⁻¹ᵁ V')) :=
    j.app_surjective V' hV'
  have hB : Function.Surjective (algebraMap Γ(X', U') Γ(X, i ⁻¹ᵁ U')) :=
    i.app_surjective U' hU'
  have hI : RingHom.ker (algebraMap Γ(Y', V') Γ(Y, j ⁻¹ᵁ V')) ^ 2 = ⊥ := by
    change RingHom.ker (j.app V').hom ^ 2 = ⊥
    rw [← j.ker_apply ⟨V', hV'⟩]
    simpa using congrArg (fun K : Y'.IdealSheafData => K.ideal ⟨V', hV'⟩) hj
  let g : ↥(RingHom.ker (j.app V').hom) →ₗ[Γ(Y', V')] ↥(RingHom.ker (i.app U').hom) :=
    { toFun x := ⟨(f'.appLE V' U' e).hom (x : Γ(Y', V')), by
        rw [RingHom.mem_ker, ← RingHom.comp_apply, hsq, RingHom.comp_apply,
          RingHom.mem_ker.mp x.2, map_zero]⟩
      map_add' x y := by ext; simp
      map_smul' r x := Subtype.ext (map_mul (f'.appLE V' U' e).hom r (x : Γ(Y', V'))) }
  have hg : ∀ x, (g x : Γ(X', U')) = (f'.appLE V' U' e).hom (x : Γ(Y', V')) := fun _ => rfl
  exact Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange hA hB hI g hg
    (hbc V' hV' U' hU' e g hg)

/-- For a cartesian morphism of thickenings with locally finite type components, whose target
thickening is of first order and whose kernel ideal sheaves are related by base change along the
ambient morphism, `f` is étale exactly when `f'` is. -/
theorem CartesianFiniteTypeMorphism.etale_iff (S : CartesianFiniteTypeMorphism.{u})
    (hj : S.j.ker ^ 2 = ⊥) (hbc : IsKerBaseChange S.i S.f' S.j) : Etale S.f ↔ Etale S.f' := by
  have : IsClosedImmersion S.i := S.sourceThickening.1
  have : IsClosedImmersion S.j := S.targetThickening.1
  have hcomm : S.i ≫ S.f' = S.f ≫ S.j := S.morphism.w.symm
  exact ⟨fun _ => etale_of_isKerBaseChange hcomm hj hbc,
    MorphismProperty.of_isPullback S.cartesian.flip⟩

end Stacks.Thickenings

end
