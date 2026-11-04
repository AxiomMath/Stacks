module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Composition

/-!
# The zero scheme of a pulled-back section is independent of the factorization

Let `L` be an invertible module on a scheme `T` with a global section `s`, and let a scheme `A`
lie over `T` through two factorizations `q₁ ≫ q₂` and `r₁ ≫ r₂` of *one* morphism `A ⟶ T`. The
zero scheme of the section pulled back to `A` is the same for both readings: by Stacks 0B6Y each
is the scheme-theoretic inverse image of `Z(s)` along `A ⟶ T`, which mentions no factorization.

The two *invertible modules* `q₁^* q₂^* L` and `r₁^* r₂^* L` are a different matter. They are
isomorphic — both are pullbacks of `L` along the same morphism, so
`AlgebraicGeometry.Scheme.Modules.pullbackComp` relates them — but they are not equal, and a
`Stacks.Chow.GysinSystem` assigns two isomorphic invertible modules *a priori* unrelated first
Chern class rules. So the agreement of the two Gysin maps is not a consequence of the agreement
of the two zero schemes; it is the iterated-pullback case of Stacks 02TA for the system,
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward`, which is a property of the
chosen datum and is discharged for the canonical system in
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem`.

## Main results

* `Stacks.Divisors.zeroScheme_pullback_comp_comp` — the equality of the two zero schemes, for an
  arbitrary pair of factorizations of one morphism. This is Stacks 0B6Y and carries no hypothesis.
* `Stacks.Chow.GysinSystem.onChow_pullbackComp_comp` — the two Gysin maps agree, under the
  transport along that equality, granted the iterated-pullback case of Stacks 02TA.
* `Stacks.Chow.chowPushforwardOfIso_eqToHom_trans_eq` — the bookkeeping behind it: two classes on
  two equal ideal sheaves that transport to one and the same class on a third transport to each
  other.

## Implementation notes

`Stacks.Chow.GysinSystem.onChow_pullbackComp` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting` compares an iterated pullback with
the *one-step* pullback along the composite. Two factorizations of one morphism are compared here
by routing both through that one-step reading, which is why no new property of the Gysin system
is needed: this file assumes exactly
`Stacks.Chow.GysinSystem.IsNaturalUnderPullbackCompPushforward` and nothing more.

Where this is needed: the Gysin condition of Stacks 0B76 for an operation built by base change
meets one scheme over the test scheme `T` through two different factorizations — through the
divisor and through the base change of `f` — and the condition being verified speaks about the
module pulled back along one of them while the condition supplying it speaks about the other.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

/-- **Stacks 0B6Y.** The zero scheme of a section pulled back to `A` depends only on the morphism
`A ⟶ T`, not on a factorization of it: two factorizations `q₁ ≫ q₂ = r₁ ≫ r₂` give equal zero
schemes, both being the inverse image of `Z(s)` along that morphism. -/
@[stacks 0B6Y "the zero scheme of a section pulled back along a composite does not depend on the \
factorization"]
theorem zeroScheme_pullback_comp_comp {A B B' T : Scheme.{u}} (q₁ : A ⟶ B) (q₂ : B ⟶ T)
    (r₁ : A ⟶ B') (r₂ : B' ⟶ T) (h : q₁ ≫ q₂ = r₁ ≫ r₂) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    zeroScheme A ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections q₂ L s)) =
      zeroScheme A ((Scheme.Modules.pullback r₁).obj ((Scheme.Modules.pullback r₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections r₁ ((Scheme.Modules.pullback r₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r₂ L s)) := by
  rw [zeroScheme_pullback_comp q₁ q₂ L s, zeroScheme_pullback_comp r₁ r₂ L s, h]

end Stacks.Divisors

namespace Stacks.Chow

/-- Two Chow classes on the subschemes of two ideal sheaves that both transport, along the
equalities of those ideal sheaves with a third, to one and the same class there, transport to each
other. -/
theorem chowPushforwardOfIso_eqToHom_trans_eq {C : ChowSituation.{u}} {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {D₀ D₁ D₂ : X.IdealSheafData} (h₁ : D₁ = D₀)
    (h₂ : D₂ = D₀) {x₀ : chowGroup C (D₀.subschemeι ≫ p) k}
    {x₁ : chowGroup C (D₁.subschemeι ≫ p) k} {x₂ : chowGroup C (D₂.subschemeι ≫ p) k}
    (e₁ : chowPushforwardOfIso C (D₁.subschemeι ≫ p) (D₀.subschemeι ≫ p)
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme h₁))
      (by rw [← Category.assoc, subschemeι_eqToHom h₁]) k x₁ = x₀)
    (e₂ : chowPushforwardOfIso C (D₂.subschemeι ≫ p) (D₀.subschemeι ≫ p)
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme h₂))
      (by rw [← Category.assoc, subschemeι_eqToHom h₂]) k x₂ = x₀) :
    chowPushforwardOfIso C (D₁.subschemeι ≫ p) (D₂.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme (h₁.trans h₂.symm)))
        (by rw [← Category.assoc, subschemeι_eqToHom (h₁.trans h₂.symm)]) k x₁ = x₂ := by
  cases h₁
  cases h₂
  have hb : eqToHom (congrArg Scheme.IdealSheafData.subscheme (rfl : D₀ = D₀)) ≫
      (D₀.subschemeι ≫ p) = D₀.subschemeι ≫ p := by
    rw [← Category.assoc, subschemeι_eqToHom (rfl : D₀ = D₀)]
  have key : ∀ x : chowGroup C (D₀.subschemeι ≫ p) k,
      chowPushforwardOfIso C (D₀.subschemeι ≫ p) (D₀.subschemeι ≫ p)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme (rfl : D₀ = D₀))) hb k x = x := by
    intro x
    rw [chowPushforwardOfIso_congr_apply C (D₀.subschemeι ≫ p) (D₀.subschemeι ≫ p)
      (eqToHom (congrArg Scheme.IdealSheafData.subscheme (rfl : D₀ = D₀))) (𝟙 D₀.subscheme)
      (by simp) hb (Category.id_comp _) k x]
    exact chowPushforwardOfIso_id C (D₀.subschemeι ≫ p) k x
  exact (key x₁).trans (((key x₁).symm.trans e₁).trans ((key x₂).symm.trans e₂).symm)

/-- **The iterated-pullback case of Stacks 02TA, for two factorizations.** A scheme `A` over `T`
through two factorizations of one morphism carries two readings of a section of an invertible
module on `T` pulled back to it; their zero schemes agree by
`Stacks.Divisors.zeroScheme_pullback_comp_comp`, and their Gysin maps agree under the transport
along that equality.

Both readings are compared with the one-step pullback along the common composite by
`Stacks.Chow.GysinSystem.onChow_pullbackComp`, so the only hypothesis is the one that lemma
carries. -/
theorem GysinSystem.onChow_pullbackComp_comp {C : ChowSituation.{u}} {G : GysinSystem C}
    (hG : G.IsNaturalUnderPullbackCompPushforward) {A B B' T : Scheme.{u}} (q₁ : A ⟶ B)
    (q₂ : B ⟶ T) (r₁ : A ⟶ B') (r₂ : B' ⟶ T) (h : q₁ ≫ q₂ = r₁ ≫ r₂) (pA : A ⟶ C.S)
    [LocallyOfFiniteType pA] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ) (α : chowGroup C pA (k + 1)) :
    chowPushforwardOfIso C
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback q₁).obj
          ((Scheme.Modules.pullback q₂).obj L))
          (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q₂ L s))).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback r₁).obj
          ((Scheme.Modules.pullback r₂).obj L))
          (AlgebraicGeometry.pullbackGlobalSections r₁ ((Scheme.Modules.pullback r₂).obj L)
            (AlgebraicGeometry.pullbackGlobalSections r₂ L s))).subschemeι ≫ pA)
        (eqToHom (congrArg Scheme.IdealSheafData.subscheme
          (Stacks.Divisors.zeroScheme_pullback_comp_comp q₁ q₂ r₁ r₂ h L s)))
        (by
          rw [← Category.assoc,
            subschemeι_eqToHom (Stacks.Divisors.zeroScheme_pullback_comp_comp q₁ q₂ r₁ r₂ h L s)])
        k
        (G.onChow pA ((Scheme.Modules.pullback q₁).obj ((Scheme.Modules.pullback q₂).obj L))
          (AlgebraicGeometry.pullbackGlobalSections q₁ ((Scheme.Modules.pullback q₂).obj L)
            (AlgebraicGeometry.pullbackGlobalSections q₂ L s)) k α) =
      G.onChow pA ((Scheme.Modules.pullback r₁).obj ((Scheme.Modules.pullback r₂).obj L))
        (AlgebraicGeometry.pullbackGlobalSections r₁ ((Scheme.Modules.pullback r₂).obj L)
          (AlgebraicGeometry.pullbackGlobalSections r₂ L s)) k α :=
  chowPushforwardOfIso_eqToHom_trans_eq pA k
    (Stacks.Divisors.zeroScheme_pullback_comp_eq q₁ q₂ (q₁ ≫ q₂) rfl L s)
    (Stacks.Divisors.zeroScheme_pullback_comp_eq r₁ r₂ (q₁ ≫ q₂) h.symm L s)
    (GysinSystem.onChow_pullbackComp hG q₁ q₂ (q₁ ≫ q₂) rfl pA L s k α)
    (GysinSystem.onChow_pullbackComp hG r₁ r₂ (q₁ ≫ q₂) h.symm pA L s k α)

end Stacks.Chow

end
