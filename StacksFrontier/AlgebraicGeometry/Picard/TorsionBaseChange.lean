module

public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsionExponent
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.PicardGaloisInvariants
public import StacksFrontier.AlgebraicGeometry.Picard.PurelyInseparablePullback

/-!
# Torsion in the Picard group under a base change of fields

Let `X` be a quasi-compact and quasi-separated scheme over a field `k` with `H⁰(X, 𝒪_X) = k`,
and let `k'/k` be an extension of fields. For every integer `n`, pullback along `X_{k'} ⟶ X`
carries the `n`-torsion of `Pic(X)` into the `n`-torsion of `Pic(X_{k'})`, does so injectively,
and preserves the order of a class. If moreover `k` has characteristic `p > 0`, `n` is prime to
`p` and `k'/k` is purely inseparable, then it is bijective
([Stacks, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)).

## Main results

* `Stacks.Picard.mapsTo_schemePullbackClass_zsmulTorsion`: pullback along a morphism of schemes
  carries `n`-torsion Picard classes to `n`-torsion Picard classes.
* `Stacks.Picard.injOn_schemePullbackClass_zsmulTorsion`: the map `Pic(X)[n] → Pic(X_{k'})[n]`
  is injective, for every extension of fields and every `n`.
* `Stacks.Picard.addOrderOf_schemePullbackClass`: pullback along `X_{k'} ⟶ X` preserves the
  order of a Picard class.
* `Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_isPurelyInseparable`: **Tag 0CD5.**
  For `k` of characteristic `p > 0`, `n` prime to `p` and `k'/k` purely inseparable,
  `Pic(X)[n] → Pic(X_{k'})[n]` is bijective.

## Implementation notes

**Injectivity** of `Pic(X) → Pic(X_{k'})` for a quasi-compact, quasi-separated `X` with
`H⁰(X, 𝒪_X) = k` is [Stacks, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5), available
here as `Stacks.Picard.injective_schemePullbackClass_of_globalSectionsIso`; this is also the
source's first step.

**Surjectivity** is not proved by the source's route. The source descends an `n`-torsion
invertible module along the fpqc covering `{X_{k'} → X}`, building the cocycle from the
thickening `X_{k'} → X_{k' ⊗_k k'}`. Here it is proved in two steps instead.

* *A finite purely inseparable extension.* It has an exponent `e`, so the `p ^ e`-power map
  `k' → k` is a ring map and `X_{k'} → X` has a morphism back whose two composites with it are
  the `e`-fold absolute Frobenius of `X` and of `X_{k'}`. Pullback along the absolute Frobenius
  is multiplication by `p` on every Picard group
  (`Stacks.Picard.schemePullbackClass_absoluteFrobenius`), so both composites of the two
  pullback maps are multiplication by `p ^ e`, and for `n` prime to `p` that makes pullback a
  bijection on `n`-torsion. This is
  `Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_hasExponent`, and it needs none of the
  hypotheses on `X`.
* *An arbitrary purely inseparable extension.* `X_{k'}` is the limit of the `X_E` over the
  finite subextensions `E/k`, so every class of `Pic(X_{k'})` is pulled back from some `Pic(X_E)`
  ([Stacks, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W), as
  `Stacks.Picard.exists_finiteSubextension_schemePullbackClass_eq`). Pullback from `X_E` to
  `X_{k'}` is injective, by Tag 0CC5 at the stage `X_E`, whose global sections are `E`
  (`Stacks.Picard.injective_schemePullbackClass_stageProjection`); so a class pulled back to an
  `n`-torsion class is itself `n`-torsion, and the finite case applies at `E/k`. This is where
  quasi-compactness, quasi-separatedness and `H⁰(X, 𝒪_X) = k` are used.

**`H⁰(X, 𝒪_X) = k` is spelled** `IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)`, the
canonical map from `k = H⁰(Spec k, 𝒪)` induced by the structure morphism being an isomorphism,
and the `n`-torsion is `Stacks.Picard.zsmulTorsion`, the set of classes killed by `n`.
Quasi-compactness and quasi-separatedness are taken absolutely, as `CompactSpace X` and
`QuasiSeparatedSpace X`; over the affine base `Spec k` these are the relative conditions
`QuasiCompact f` and `QuasiSeparated f`. "`k` has characteristic `p > 0`" is `CharP k p` with
`0 < p`, and "`n` prime to `p`" is `n.natAbs.Coprime p`.

## References

* [Stacks Project, Tag 0CD5](https://stacks.math.columbia.edu/tag/0CD5)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 03SM](https://stacks.math.columbia.edu/tag/03SM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **Pullback carries `n`-torsion Picard classes to `n`-torsion Picard classes.** Pullback is a
homomorphism of abelian groups, and a homomorphism preserves the elements killed by `n`. -/
theorem mapsTo_schemePullbackClass_zsmulTorsion {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℤ) :
    Set.MapsTo (schemePullbackClass f) (zsmulTorsion (ofScheme Y) n)
      (zsmulTorsion (ofScheme X) n) :=
  mapsTo_zsmulTorsion (A := ofScheme Y) (B := ofScheme X) (schemePullbackClassHom f) n

variable {k k' : Type u} [Field k] [Field k'] (φ : k →+* k') {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]

/-- **Pullback to a base change of fields is injective on `n`-torsion.** Let `X` be a
quasi-compact, quasi-separated scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, let `k'/k` be an
extension of fields and let `n` be an integer. Then `Pic(X)[n] → Pic(X_{k'})[n]` is injective,
`Pic(X) → Pic(X_{k'})` being injective by Tag 0CC5. -/
theorem injOn_schemePullbackClass_zsmulTorsion (n : ℤ)
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) :
    Set.InjOn (schemePullbackClass (pullback.fst f (Spec.map (CommRingCat.ofHom φ))))
      (zsmulTorsion (ofScheme X) n) :=
  (injective_schemePullbackClass_of_globalSectionsIso φ f hΓ).injOn

/-- **Pullback along `X_{k'} ⟶ X` preserves the order of a Picard class**, under the hypotheses
of Tag 0CC5: it is then an injective homomorphism of abelian groups. In particular a class whose
pullback is `n`-torsion is itself `n`-torsion. -/
theorem addOrderOf_schemePullbackClass
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) (x : ofScheme X) :
    addOrderOf (schemePullbackClass (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) x) =
      addOrderOf x :=
  addOrderOf_injective (G := ofScheme X)
    (schemePullbackClassHom (pullback.fst f (Spec.map (CommRingCat.ofHom φ))))
    (injective_schemePullbackClass_of_globalSectionsIso φ f hΓ) x

/-- **Stacks Project, Tag 0CD5.** Let `k` be a field of characteristic `p > 0`, let `X` be a
quasi-compact and quasi-separated scheme over `k` with `H⁰(X, 𝒪_X) = k`, and let `n` be an
integer prime to `p`. Then for every purely inseparable extension `k'/k`, pullback along
`X_{k'} ⟶ X` is a bijection `Pic(X)[n] → Pic(X_{k'})[n]`.

Injectivity is Tag 0CC5. For surjectivity, a class of `Pic(X_{k'})[n]` is pulled back from a
class of `Pic(X_E)` for a finite subextension `E/k` (Tag 0B8W), which is again `n`-torsion
because pullback from `X_E` is injective (Tag 0CC5 at the stage), and the finite purely
inseparable case is
`Stacks.Picard.bijOn_schemePullbackClass_zsmulTorsion_of_hasExponent`, proved through the
absolute Frobenius. -/
@[stacks 0CD5]
theorem bijOn_schemePullbackClass_zsmulTorsion_of_isPurelyInseparable
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsPurelyInseparable k k']
    (p : ℕ) [CharP k p] (hp : 0 < p) {n : ℤ} (hn : n.natAbs.Coprime p)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]
    (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) :
    Set.BijOn
      (schemePullbackClass (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))))
      (zsmulTorsion (ofScheme X) n)
      (zsmulTorsion
        (ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) n) := by
  have : NeZero p := ⟨hp.ne'⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  refine ⟨mapsTo_schemePullbackClass_zsmulTorsion _ n,
    injOn_schemePullbackClass_zsmulTorsion (algebraMap k k') f n hΓ, fun y hy => ?_⟩
  have : Algebra.IsAlgebraic k k' := IsPurelyInseparable.isAlgebraic k k'
  let Xo : Over (Spec (.of k)) := Over.mk f
  have : CompactSpace Xo.left := ‹CompactSpace X›
  have : QuasiSeparatedSpace Xo.left := ‹QuasiSeparatedSpace X›
  obtain ⟨E, hE, q, z, hq₁, hq₂, hz⟩ := exists_finiteSubextension_schemePullbackClass_eq Xo y
  have hinj : Function.Injective (schemePullbackClass q) :=
    eq_stageProjection Xo E q hq₁ hq₂ ▸ injective_schemePullbackClass_stageProjection Xo hΓ E
  have hnz : n • z = 0 :=
    (map_eq_zero_iff (schemePullbackClassHom q) hinj).1 <| by
      rw [map_zsmul]
      exact (congrArg (n • ·) hz).trans hy
  obtain ⟨x, hx, hxz⟩ :=
    (bijOn_schemePullbackClass_zsmulTorsion_of_hasExponent k E p hn f).surjOn hnz
  refine ⟨x, hx, ?_⟩
  calc schemePullbackClass (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) x
      = schemePullbackClass (q ≫ pullback.fst f (spectrumMap k E)) x :=
        (congrArg (fun g => schemePullbackClass g x) hq₁).symm
    _ = schemePullbackClass q (schemePullbackClass (pullback.fst f (spectrumMap k E)) x) :=
        (schemePullbackClass_comp _ _ x).symm
    _ = y := by rw [hxz, hz]

end Stacks.Picard

end
