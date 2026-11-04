module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHomIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleKFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineChartwiseBaseChangeSheafHomPseudoCoherent

/-!
# Stacks 08JQ: formation of `Rf_*R𝓗om(E, 𝒢^•)` commutes with base change

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces, `E` an object
of `D(𝒪_X)` and `𝒢^•` a complex of quasi-coherent `𝒪_X`-modules. For every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

the base change map `Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` of
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHomBaseChangeMap` is an isomorphism if

1. `E` is perfect, `𝒢^•` is bounded above and each `𝒢^n` is flat over `Y`, or
2. `E` is pseudo-coherent, `𝒢^•` is bounded, each `𝒢^n` is flat over `Y`, **and `g` has finite
   Tor dimension**.

## Part (2) is false as written

Without the condition on `g`, part (2) fails. Let `k` be a separably closed field,
`A = k[x]/(x²)`, `X = Y = Spec A`, `f = id`, `E = k` (pseudo-coherent, `A` being Noetherian),
`𝒢^• = 𝒪_X` in degree `0` (bounded, flat over `Y`) and `g : Spec k ⟶ Spec A` the closed point.
As `A` is self-injective, `RHom_A(k, A) = k[0]`, so `Lg^*Rf_*R𝓗om(E, 𝒢^•)` corresponds to
`k ⊗ᴸ_A k`, whose cohomology is `k` in every degree `≤ 0`, while
`Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` corresponds to `RHom_k(k ⊗ᴸ_A k, k)`, which lives in degrees
`≥ 0`; in degree `-1` the base change map is `k ⟶ 0`. The source's proof passes through
Stacks 0DKI (3), which fails for the same reason; with `g` of finite Tor dimension both hold.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent`:
  part (2), with `g` of finite Tor dimension.
* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedSheafHomBaseChangeMap_tag`: both parts.

## References

* [Stacks Project, Tag 08JQ](https://stacks.math.columbia.edu/tag/08JQ)
* [Stacks Project, Tag 0DKI](https://stacks.math.columbia.edu/tag/0DKI)
* [Stacks Project, Tag 0DKH](https://stacks.math.columbia.edu/tag/0DKH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Formation of `Rf_*R𝓗om(E, 𝒢^•)` commutes with base change of finite Tor dimension, for
pseudo-coherent `E`.** For a cartesian square of algebraic spaces with `f` quasi-compact and
quasi-separated and `g` of finite Tor dimension, `E` pseudo-coherent and a bounded complex
`𝒢^•` of quasi-coherent `𝒪_X`-modules flat over `Y`, the base change map
`Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` is an isomorphism. This is
Stacks 08JQ (2) with the condition on `g` that makes it true. -/
theorem isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent
    (sq : IsPullback g' f' f g) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (hg : HasFiniteTorDimension g)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (G.X i))
    (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G) := by
  obtain ⟨a, b, hab⟩ := hGb
  have : G.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff G b).2 fun i hi => hab i (Or.inr hi)
  have : G.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff G a).2 fun i hi => hab i (Or.inl hi)
  have := pullbackModules_smallEtale_additive (B := B) (S := S) (hS := hS) g'
  let P := (AlgebraicGeometry.RingedToposHom.toModulesHom (X := smallEtaleRingedTopos B S hS X')
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS g')).pullbackModules
  let G' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')) ℤ :=
    (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  have : CochainComplex.IsStrictlyGE G' a := (CochainComplex.isStrictlyGE_iff G' a).2 fun i hi =>
    P.map_isZero (hab i (Or.inl hi))
  have hK := qcohDerived_Q_obj_of_isQuasicoherentOnSite G hq
  have hK' := qcohDerived_Q_obj_of_isQuasicoherentOnSite G'
    fun n => isQuasicoherentOnSite_pullbackModules B S hS g' (G.X n) (hq n)
  have hKp : DerivedCategoryB.derivedCategoryBPlus
      (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))
      (DerivedCategory.Q.obj G) :=
    ⟨⟨a, fun i hi => (DerivedCategory.Q.obj G).isZero_of_isGE a i hi⟩, hK⟩
  have hKp' : DerivedCategoryB.derivedCategoryBPlus
      (A := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)))
      (DerivedCategory.Q.obj G') :=
    ⟨⟨a, fun i hi => (DerivedCategory.Q.obj G').isZero_of_isGE a i hi⟩, hK'⟩
  have h2 :=
    affineChartwiseBaseChange_sheafHom_of_isPseudoCoherent g' f g f' sq hg E hE _ hKp _ hK' _
      (affineChartwiseBaseChange_pullbackQComparison B S hS sq G b hq hfl)
  have hiso := isIso_smallEtaleDerivedBaseChangeComp_of_affineChartwiseBaseChange B S hS sq hfqc
    hfqs _ (qcohDerived_smallEtaleDerivedSheafHom_of_isPseudoCoherent X _ _ hE hKp) _
    (qcohDerived_smallEtaleDerivedSheafHom_of_isPseudoCoherent X' _ _
      (isPseudoCoherent_smallEtaleDerivedModulePullback g' E hE) hKp') _ h2
  unfold smallEtaleDerivedSheafHomBaseChangeMap smallEtaleDerivedModulePullbackQComparison
  rw [Functor.map_comp, ← Category.assoc]
  exact isIso_smallEtaleDerivedBaseChangeComp_of_comp_inv B S hS f g f' g' sq.w _ _ _ hiso
    (@Functor.map_isIso _ _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _ (NatIso.hom_app_isIso _ _)))

/-- **Stacks 08JQ.** Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic
spaces, `E ∈ D(𝒪_X)` and `𝒢^•` a complex of quasi-coherent `𝒪_X`-modules. For every cartesian
square, the base change map `Lg^*Rf_*R𝓗om(E, 𝒢^•) ⟶ Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` is an
isomorphism if

1. `E` is perfect, `𝒢^•` is bounded above and each `𝒢^n` is flat over `Y`, or
2. `E` is pseudo-coherent, `𝒢^•` is bounded, each `𝒢^n` is flat over `Y`, **and `g` has finite
   Tor dimension**.

Part (1) is stated at the source's exact hypotheses. Only part (2) carries an extra hypothesis,
`HasFiniteTorDimension g`, which is not in the source. Without it, part (2) is false, by the
following counterexample.

* Let `k` be a field, `A = k[x]/(x²)`, `X = Y = Spec A`, `f = id`, `E = k` (pseudo-coherent, `A`
  being Noetherian), `𝒢^• = 𝒪_X` in degree `0` (bounded, flat over `Y`), and
  `g : Y' = Spec k ⟶ Spec A` the closed point, so that `X' = Spec k`, `f' = id`, `g' = g`.
* `A` is self-injective (a Frobenius algebra), so `RHom_A(k, A) = Hom_A(k, A)[0] = k[0]`, the
  socle `(x) ≅ k`. As `f = id`, `Rf_*R𝓗om(E, 𝒢^•)` corresponds to `k[0]`, and
  `Lg^*Rf_*R𝓗om(E, 𝒢^•)` corresponds to `k ⊗ᴸ_A k`. Its cohomology in degree `-i` is
  `Tor_i^A(k, k) = k` for every `i ≥ 0`, by the periodic resolution `⋯ → A →x A →x A → k`. In
  particular `H^{-1} = Tor_1^A(k, k) = k ≠ 0`.
* `Rf'_*R𝓗om(L(g')^*E, (g')^*𝒢^•)` corresponds to `RHom_k(k ⊗ᴸ_A k, k)`. This is the internal
  Hom out of an object of `D^{≤ 0}` into `k[0]`, so it lies in `D^{≥ 0}`, and its `H^{-1}` is `0`.
* So in degree `-1` the base change map is `k ⟶ 0`, which is not an isomorphism. No
  isomorphism between the two sides exists at all.

The source proves (2) by Stacks 0DKH and 0DKI (3). Stacks 0DKI (3) fails for the same reason, and
holds once `g` has finite Tor dimension; the proof here takes that route. With the condition,
the counterexample is excluded: `Spec k ⟶ Spec k[x]/(x²)` does not have finite Tor dimension,
`k` having infinite Tor dimension over `A`. -/
theorem isIso_smallEtaleDerivedSheafHomBaseChangeMap_tag
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    (RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E →
      (∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) →
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G)) ∧
    (RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS X.1 X.2) E →
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (G.X i)) →
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
        (sq : IsPullback g' f' f g), HasFiniteTorDimension g →
        IsIso (smallEtaleDerivedSheafHomBaseChangeMap f g f' g' sq.w E G)) :=
  ⟨fun hE hGb _ _ _ _ _ sq =>
      isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPerfect sq hfqc hfqs E hE G hGb hq hfl,
    fun hE hGb _ _ _ _ _ sq hg =>
      isIso_smallEtaleDerivedSheafHomBaseChangeMap_of_isPseudoCoherent sq hfqc hfqs hg E hE G hGb
        hq hfl⟩

end AlgebraicGeometry.Space

end
