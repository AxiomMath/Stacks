module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreservingNoetherian
public import StacksFrontier.Deformation.Artin.FormalObject
public import StacksFrontier.Deformation.Artin.FormalObject.BaseContains

/-!
# Effective formal objects of a set-valued functor on the locally Noetherian site

Let `S` be a locally Noetherian scheme and `F` a set-valued functor on the category of locally
Noetherian schemes over `S`. Artin's axiom `[4]` for such a functor asks that every formal object
of `F` be effective.

A formal object of the category fibred in sets attached to `F` is a Noetherian complete local
`S`-algebra `R` with residue field of finite type over `S`, together with elements
`ξ_n ∈ F(Spec(R/𝔪ⁿ⁺¹))` such that `ξ_{n+1}` restricts to `ξ_n`: in a category fibred in sets a
morphism over the closed immersion `Spec(R/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺²)` from `ξ_n` to `ξ_{n+1}` exists
exactly when the restriction of `ξ_{n+1}` is `ξ_n`, and it is then unique. It is effective when
there is an element `x ∈ F(Spec R)` restricting to every `ξ_n`.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver.truncationObj`,
  `AlgebraicGeometry.LocallyNoetherianOver.baseObj`: the thickenings `Spec(R/𝔪ⁿ⁺¹)` and the
  complete base `Spec R` of a formal base, as objects of the locally Noetherian site.
* `AlgebraicGeometry.LocallyNoetherianOver.truncationObjSucc`,
  `AlgebraicGeometry.LocallyNoetherianOver.truncationObjIncl`: the canonical closed immersions
  between them.
* `AlgebraicGeometry.LocallyNoetherianOver.HasEffectiveFormalObjects`: axiom `[4]`.

## References

* [Stacks Project, Tag 07X4](https://stacks.math.columbia.edu/tag/07X4)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Deformation.Artin

namespace AlgebraicGeometry.LocallyNoetherianOver

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `n`-th infinitesimal thickening `Spec(R/𝔪ⁿ⁺¹)` of a formal base whose thickenings lie in
the site, as an object of the locally Noetherian site of `S`. -/
def truncationObj (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    LocallyNoetherianOver B S hS :=
  ⟨truncationOver B S hS A hA n, by
    have := A.noetherian
    change IsLocallyNoetherian (Spec (.of (A.R ⧸ IsLocalRing.maximalIdeal A.R ^ (n + 1))))
    infer_instance⟩

/-- The complete base `Spec R` of a formal base whose thickenings lie in the site, as an object of
the locally Noetherian site of `S`. -/
def baseObj (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n)) :
    LocallyNoetherianOver B S hS :=
  ⟨baseOver B S hS A (A.contains_spec_of_contains_truncation hA), by
    have := A.noetherian
    change IsLocallyNoetherian (Spec (.of A.R))
    infer_instance⟩

/-- The closed immersion `Spec(R/𝔪ⁿ⁺¹) ⟶ Spec(R/𝔪ⁿ⁺²)` in the locally Noetherian site. -/
def truncationObjSucc (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    truncationObj B S hS A hA n ⟶ truncationObj B S hS A hA (n + 1) :=
  ObjectProperty.homMk (truncationOverSucc B S hS A hA n)

/-- The closed immersion `Spec(R/𝔪ⁿ⁺¹) ⟶ Spec R` in the locally Noetherian site. -/
def truncationObjIncl (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n)) (n : ℕ) :
    truncationObj B S hS A hA n ⟶ baseObj B S hS A hA :=
  ObjectProperty.homMk
    (restrictionToBase B S hS A (A.contains_spec_of_contains_truncation hA) hA n)

/-- The inclusions of the thickenings into `Spec R` are compatible with the transition maps. -/
@[reassoc (attr := simp)]
theorem truncationObjSucc_incl (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (n : ℕ) :
    truncationObjSucc B S hS A hA n ≫ truncationObjIncl B S hS A hA (n + 1) =
      truncationObjIncl B S hS A hA n :=
  ObjectProperty.hom_ext _ <| Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <|
    adicThickeningSucc_ι A.R (IsLocalRing.maximalIdeal A.R) n

/-- **Artin's axiom `[4]`** for a set-valued functor on the locally Noetherian site of `S`:
every formal object of `F` is effective. For every Noetherian complete local `S`-algebra `R` with
residue field of finite type over `S` whose thickenings `Spec(R/𝔪ⁿ⁺¹)` lie in the site, and
every family `ξ_n ∈ F(Spec(R/𝔪ⁿ⁺¹))` with `ξ_{n+1}` restricting to `ξ_n`, there is an element of
`F(Spec R)` restricting to every `ξ_n`. -/
def HasEffectiveFormalObjects (F : (LocallyNoetherianOver B S hS)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : FormalBase S) (hA : ∀ n, B.Contains (A.truncation n))
    (ξ : ∀ n, F.obj (op (truncationObj B S hS A hA n))),
    (∀ n, F.map (truncationObjSucc B S hS A hA n).op (ξ (n + 1)) = ξ n) →
      ∃ x : F.obj (op (baseObj B S hS A hA)),
        ∀ n, F.map (truncationObjIncl B S hS A hA n).op x = ξ n

end AlgebraicGeometry.LocallyNoetherianOver

end
