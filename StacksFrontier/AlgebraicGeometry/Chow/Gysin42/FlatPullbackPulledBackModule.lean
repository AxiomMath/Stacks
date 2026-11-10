module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible

/-!
# Stacks 0B71 for a module pulled back from a third scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `u : A ⟶ B` be a
flat morphism of relative dimension `r` of schemes locally of finite type over `S`, and let both
`A` and `B` map compatibly to a third scheme `P` carrying an invertible module `L` with a global
section `s`. Stacks 0B71 says that the Gysin map of the pulled-back section on `A` commutes with
flat pullback along `u`:

  `i_A^* u^* α = v^* i_B^* α`  in  `A_{k+r}(Z_A)`,

where `Z_A ⊆ A` and `Z_B ⊆ B` are the zero schemes of the two pullbacks of `s` and `v : Z_A ⟶ Z_B`
is the induced morphism.

`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_of_invertible` states 0B71 on cycles with
the module on `A` the pullback along `u` of the module on `B` and with the comparison morphism of
Remark 0B6Y. Here the module on `A` is the pullback along `A ⟶ P` and the morphism of zero schemes
is any one over `u`; the comparison is the one of
`Stacks.Chow.gysinSystemOfInvertible_properPushforward_pullbackModule`.

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_flatPullback` — **Stacks 0B71** on Chow groups, at the
  Gysin system of the first Chern class rule, for the comparison morphism of Remark 0B6Y.
* `Stacks.Chow.gysinSystemOfInvertible_flatPullback_pullbackModule` — **Stacks 0B71** for a module
  pulled back from a third scheme.

## References

* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Transport of a class of a cycle along an equality of degrees is the class of the transported
cycle. -/
theorem chowGroupDegreeEquiv_mk (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {k l : ℤ} (h : k = l) (c : CycleGroup C sX k) :
    chowGroupDegreeEquiv C sX h (QuotientAddGroup.mk' (rationalEquivalences C sX k) c) =
      QuotientAddGroup.mk' (rationalEquivalences C sX l) (h ▸ c) := by
  subst h
  rfl

/-- **Stacks 0B71 on Chow groups**, at the Gysin system of the first Chern class rule: for
`f : X' ⟶ X` flat of relative dimension `r`, the Gysin map of the pulled-back section commutes
with flat pullback, the morphism of zero schemes being the comparison morphism of Remark 0B6Y. -/
theorem gysinSystemOfInvertible_flatPullback (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (p' : X' ⟶ C.S) [LocallyOfFiniteType p']
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hp : f ≫ p = p')
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (x : chowGroup C p (k + 1)) :
    (gysinSystemOfInvertible C).onChow p' ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s) (k + (r : ℤ))
        (chowGroupDegreeEquiv C p' (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
          (flatPullbackChow C p' p f hp r hf (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _)
            x)) =
      flatPullbackChow C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackHom f L s)
        (zeroSchemePullbackHom_comp f L s C p p' hp) r
        (relativeDimension_zeroSchemePullbackHom f L s r hf) k
        (flatPullbackDescends C _ _ _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow p L s k x) := by
  subst hp
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    change (gysinSystemOfInvertible C).onChow (f ≫ p) ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s) (k + (r : ℤ))
        (chowGroupDegreeEquiv C (f ≫ p) _ (QuotientAddGroup.mk' _
          (flatPullback C (f ≫ p) p f rfl r hf (k + 1) a))) = _
    rw [chowGroupDegreeEquiv_mk]
    exact gysinHomomorphismOfInvertible_flatPullback_of_invertible C p f r hf k L s a

/-- A heterogeneous equality of two additive maps with heterogeneously equal targets, indexed by
an equality of closed subschemes, applied to one argument. -/
theorem heq_gysin_apply {C : ChowSituation.{u}} {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) {D₁ D₂ : X.IdealSheafData} (hD : D₁ = D₂)
    [LocallyOfFiniteType (D₁.subschemeι ≫ p)] [LocallyOfFiniteType (D₂.subschemeι ≫ p)]
    (F₁ : chowGroup C p (k + 1) →+ chowGroup C (D₁.subschemeι ≫ p) k)
    (F₂ : chowGroup C p (k + 1) →+ chowGroup C (D₂.subschemeι ≫ p) k) (hF : F₁ ≍ F₂)
    (x : chowGroup C p (k + 1)) : F₁ x ≍ F₂ x := by
  subst hD
  rw [eq_of_heq hF]

/-- **Stacks 0B71 for a module pulled back from a third scheme.** Let `u : A ⟶ B` be flat of
relative dimension `r` over the base and let `A` and `B` map compatibly to a scheme `P` carrying an
invertible module `L` with a global section `s`. Then the Gysin map of the pullback of `s` to `A`
commutes with flat pullback along `u`, the morphism `v` of the two zero schemes being any one over
`u`. -/
theorem gysinSystemOfInvertible_flatPullback_pullbackModule (C : ChowSituation.{u})
    {A B P : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (qA : A ⟶ P) (qB : B ⟶ P) (u : A ⟶ B) [LocallyOfFiniteType u]
    [Flat u] (hu : u ≫ pB = pA) (huq : u ≫ qB = qA) (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension u r) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.sheaf.obj A.ringCatSheaf.property
      ((Scheme.Modules.pullback qA).obj L)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property
      ((Scheme.Modules.pullback qB).obj L)] (k : ℤ)
    (v : (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qA L s)).subscheme ⟶
          (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
            (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme)
    [LocallyOfFiniteType v] [Flat v]
    (hvsq : v ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ u)
    (hv : v ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) =
        (Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
    (hvr : AlgebraicGeometry.RelativeDimension v r) (x : chowGroup C pB (k + 1)) :
    (gysinSystemOfInvertible C).onChow pA ((Scheme.Modules.pullback qA).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qA L s) (k + (r : ℤ))
        (chowGroupDegreeEquiv C pA (by ring : k + 1 + (r : ℤ) = k + (r : ℤ) + 1)
          (flatPullbackChow C pA pB u hu r hr (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _) x)) =
      flatPullbackChow C ((Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback qA).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qA L s)).subschemeι ≫ pA)
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) v hv r hvr k
        (flatPullbackDescends C _ _ _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s) k x) := by
  subst huq hu
  have := Stacks.ChernCap42.isInvertible_sheafObj_modulePullback
    ((Scheme.Modules.pullback qB).obj L) u
  have hZZ := zeroScheme_pullback_pullback u qB L s
  have h0B71 := gysinSystemOfInvertible_flatPullback C pB (u ≫ pB) u rfl r hr k
    ((Scheme.Modules.pullback qB).obj L) (AlgebraicGeometry.pullbackGlobalSections qB L s) x
  have hG := heq_gysinHomomorphismOnChowOfInvertible C (u ≫ pB) (k + (r : ℤ))
    ((Scheme.Modules.pullback (u ≫ qB)).obj L)
    ((Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback qB).obj L))
    (AlgebraicGeometry.pullbackGlobalSections (u ≫ qB) L s)
    (AlgebraicGeometry.pullbackGlobalSections u ((Scheme.Modules.pullback qB).obj L)
      (AlgebraicGeometry.pullbackGlobalSections qB L s))
    ((Scheme.Modules.pullbackComp u qB).app L).symm hZZ.symm
    (gysinOfInvertibleDescends C _ _ _ _) (gysinOfInvertibleDescends C _ _ _ _)
  have key : ∀ (Z : A.IdealSheafData)
      (hZ : Stacks.Divisors.zeroScheme A
        ((Scheme.Modules.pullback u).obj ((Scheme.Modules.pullback qB).obj L))
        (AlgebraicGeometry.pullbackGlobalSections u ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)) = Z)
      (v : Z.subscheme ⟶ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
        (AlgebraicGeometry.pullbackGlobalSections qB L s)).subscheme)
      [LocallyOfFiniteType v] [Flat v]
      (_hvsq : v ≫ (Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι = Z.subschemeι ≫ u)
      (hv : v ≫ ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) =
        Z.subschemeι ≫ (u ≫ pB))
      (hvr : AlgebraicGeometry.RelativeDimension v r),
      flatPullbackChow C ((pullbackZeroScheme u ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ (u ≫ pB))
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB)
        (zeroSchemePullbackHom u ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s))
        (zeroSchemePullbackHom_comp u _ _ C pB (u ≫ pB) rfl) r
        (relativeDimension_zeroSchemePullbackHom u _ _ r hr) k
        (flatPullbackDescends C _ _ _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s) k x) ≍
      flatPullbackChow C (Z.subschemeι ≫ (u ≫ pB))
        ((Stacks.Divisors.zeroScheme B ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s)).subschemeι ≫ pB) v hv r hvr k
        (flatPullbackDescends C _ _ _ _ _ _ _)
        ((gysinSystemOfInvertible C).onChow pB ((Scheme.Modules.pullback qB).obj L)
          (AlgebraicGeometry.pullbackGlobalSections qB L s) k x) := by
    intro Z hZ v _ _ hvsq _ _
    subst hZ
    obtain rfl := eq_zeroSchemePullbackHom u _ _ v hvsq
    rfl
  refine eq_of_heq ((heq_gysin_apply (u ≫ pB) (k + (r : ℤ)) hZZ.symm _ _ hG _).trans
    ((heq_of_eq h0B71).trans (key _ hZZ v hvsq hv hvr)))

end Stacks.Chow

end
