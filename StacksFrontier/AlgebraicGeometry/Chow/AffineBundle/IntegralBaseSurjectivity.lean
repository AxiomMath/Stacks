module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.DeltaDimensionInduction

/-!
# Surjectivity of flat pullback along an affine-space bundle over an integral base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be an
affine-space bundle of rank `r` over an integral base `Y` of finite delta-dimension. A
trivializing open neighbourhood `V` of the generic point of `Y` is dense, so its reduced closed
complement has strictly smaller delta-dimension. Over `V` the bundle is the trivial bundle, and
over the complement it is again an affine-space bundle of rank `r`; so if flat pullback is
surjective along every trivial bundle and along every affine-space bundle of rank `r` whose base
has smaller delta-dimension, then it is surjective along `f`.

This is the induction step of the second paragraph of the proof of Stacks 02TT, with the
localization step of `StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity`
as its engine.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle_of_isIntegral` — the induction
  step over an integral base.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-- **Surjectivity over a trivializing open subscheme.** If flat pullback along the projection
of affine `r`-space is surjective over every base, then it is surjective along the restriction of
an affine-space bundle to an open subscheme of its target over which the bundle is trivial.

Precomposing with the trivialization does not change surjectivity, by
`Stacks.Chow.flatPullbackChow_surjective_of_isIso_comp`. -/
theorem flatPullbackChow_surjective_morphismRestrict_of_trivialization (C : ChowSituation.{u})
    (htriv : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (r : ℕ) (j : ℤ),
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin r); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin r); B) ↘ B) rfl r
        (relativeDimension_affineSpaceOver B r) j))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (V : Y.Opens)
    (e : (f ⁻¹ᵁ V).toScheme ≅ 𝔸(ULift.{u} (Fin r); V.toScheme))
    (he : e.hom ≫ (𝔸(ULift.{u} (Fin r); V.toScheme) ↘ V.toScheme) = f ∣_ V) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (V.ι ≫ sY) (f ∣_ V)
      (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) r
      (relativeDimension_morphismRestrict' f V r hf) k) := by
  have _ : LocallyOfFiniteType (f ∣_ V) := inferInstance
  have _ : AlgebraicGeometry.Flat (f ∣_ V) := inferInstance
  have _ : IsIso e.hom := inferInstance
  exact flatPullbackChow_surjective_of_isIso_comp C ((f ⁻¹ᵁ V).ι ≫ f ≫ sY)
    ((𝔸(ULift.{u} (Fin r); V.toScheme) ↘ V.toScheme) ≫ (V.ι ≫ sY)) (V.ι ≫ sY) e.hom
    (𝔸(ULift.{u} (Fin r); V.toScheme) ↘ V.toScheme) (f ∣_ V) he
    (by rw [← Category.assoc, he, ← Category.assoc, morphismRestrict_ι, Category.assoc])
    rfl (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) r
    (relativeDimension_affineSpaceOver V.toScheme r)
    (relativeDimension_morphismRestrict' f V r hf) k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (htriv V.toScheme (V.ι ≫ sY) r k)

/-- **The induction step of Stacks 02TT over an integral base.** Let `f : X ⟶ Y` be an
affine-space bundle of rank `r` with `Y` integral, locally of finite type over the base of
chapter 42 and of finite delta-dimension. Assume

* flat pullback along the projection of affine `r`-space is surjective in degree `k` over every
  base, and
* flat pullback in degree `k` is surjective along every affine-space bundle of rank `r` whose
  base has strictly smaller delta-dimension than `Y`.

Then flat pullback along `f` is surjective in degree `k`.

A trivializing open neighbourhood `V` of the generic point of `Y` is dense, so the reduced
induced closed subscheme on its complement has strictly smaller delta-dimension by
`Stacks.Chow.schemeDeltaDimension_lt_of_range_eq_compl`. Over `V` the bundle is trivial, and the
restriction of `f` to the inverse image of the complement is an affine-space bundle of rank `r`
by `Stacks.Chow.isAffineSpaceBundle_comapRestrict`, so both hypotheses of
`Stacks.Chow.flatPullbackChow_surjective_of_opens_of_comap` are available. -/
theorem flatPullbackChow_surjective_of_isAffineSpaceBundle_of_isIntegral (C : ChowSituation.{u})
    (htriv : ∀ (B : Scheme.{u}) (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (r : ℕ) (j : ℤ),
      Function.Surjective (flatPullbackChowOfRelativeDimension C
        ((𝔸(ULift.{u} (Fin r); B) ↘ B) ≫ sB) sB (𝔸(ULift.{u} (Fin r); B) ↘ B) rfl r
        (relativeDimension_affineSpaceOver B r) j))
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (hbundle : IsAffineSpaceBundle f r) (k : ℤ)
    {n : ℤ} (hn : schemeDeltaDimension C sY = (n : EInt))
    (hsmaller : ∀ (Z W : Scheme.{u}) (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sW : W ⟶ C.S)
      [LocallyOfFiniteType sW] (g : W ⟶ Z) [LocallyOfFiniteType g] [AlgebraicGeometry.Flat g]
      (hgb : g ≫ sZ = sW) (hg : AlgebraicGeometry.RelativeDimension g r),
      IsAffineSpaceBundle g r → schemeDeltaDimension C sZ < schemeDeltaDimension C sY →
      Function.Surjective (flatPullbackChowOfRelativeDimension C sW sZ g hgb r hg k)) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) := by
  -- a trivializing open neighbourhood of the generic point
  obtain ⟨V, hgen, e, he⟩ := hbundle (genericPoint Y)
  have hVne : ((V : Set Y)).Nonempty := ⟨genericPoint Y, hgen⟩
  -- the reduced induced structure on its complement
  set Z : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨((V : Set Y))ᶜ, V.2.isClosed_compl⟩ with hZdef
  have hcomplement : Set.range Z.subschemeι.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, hZdef,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Scheme.Opens.range_ι]
    rfl
  have hlt : schemeDeltaDimension C (Z.subschemeι ≫ sY) < schemeDeltaDimension C sY :=
    schemeDeltaDimension_lt_of_range_eq_compl C sY Z.subschemeι V hcomplement hVne hn
  refine flatPullbackChow_surjective_of_opens_of_comap C sY f r hf k V Z hcomplement
    (flatPullbackChow_surjective_morphismRestrict_of_trivialization C htriv sY f r hf k V e he)
    ?_
  have _ := locallyOfFiniteType_comapRestrict Z f
  have _ := flat_comapRestrict Z f
  exact hsmaller Z.subscheme (Z.comap f).subscheme (Z.subschemeι ≫ sY)
    ((Z.comap f).subschemeι ≫ f ≫ sY) (comapRestrict Z f)
    (comapRestrict_comp_base C (f ≫ sY) sY f rfl Z)
    (relativeDimension_comapRestrict Z f hf)
    (isAffineSpaceBundle_comapRestrict f hbundle Z) hlt

end Stacks.Chow

end
