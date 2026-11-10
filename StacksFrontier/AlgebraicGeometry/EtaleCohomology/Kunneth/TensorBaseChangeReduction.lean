module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeUnbounded

/-!
# The canonical map of Tag 0F1J: reduction to single objects

Let `Λ` be a commutative ring and

```
X' <-h-- Y
|f'      |e
S' <-g-- T
```

a commutative square of schemes. The canonical map of [Stacks, Tag 0F1J] and [Stacks, Tag 0F1N]
on `D(-_étale, Λ)` is

`A ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L_Λ e⁻¹F)`

(`Stacks.EtaleCohomology.EtaleCoefficients.tensorBaseChangeMap`), and the source applies it at
`A = p⁻¹E` for a morphism `p : X' ⟶ X`. The first two paragraphs of the proof of Tag 0F1J reduce
its invertibility, for `E` of Tor amplitude in `[a, ∞]` and `F` bounded below, to the case where
`E` is a single flat sheaf of `Λ̲`-modules and `F` a single sheaf of `Λ̲`-modules. This file
proves that reduction, for an arbitrary ring `Λ` and an arbitrary commutative square, as
`isIso_tensorBaseChangeMap_of_isIso_single`. Nothing about fields, invertibility of `n` or
quasi-compactness of `g` enters: those are used only in the case of single objects.

## The proof

The source's, in the two variables in turn, through the reductions of
`StacksFrontier.Algebra.Homology.DerivedCategory.InvertibilityAtShiftsReductions`. Both sides of the
map are exact functors in each variable, and the map is natural in each variable
(`tensorBaseChangeNatTransLeft`, `tensorBaseChangeNatTransRight`); no compatibility of the map
with the shift is needed.

* **The variable `F`.** For `A` of Tor amplitude in `[k, ∞]` both sides carry `D^{≥m}` into
  `D^{≥m+k}`: the inverse images preserve `D^{≥m}` (they are exact,
  `Stacks.EtaleCohomology.EtaleCoefficients.isGE_pullback_obj`), so do the direct images, and
  tensoring with an object of Tor amplitude in `[k, ∞]` raises the lower bound by `k`. So the
  reduction along canonical truncations brings a bounded below `F` down to single sheaves.
* **The variable `E`.** Represent `E` by a K-flat complex `K` of flat sheaves vanishing below `a`
  (Stacks 0F1M). The stupid truncations `σ^{≥N}K` are again K-flat with flat terms, so `p⁻¹` of
  them has Tor amplitude in `[N, ∞]` (Stacks 08H5), and for `F ∈ D^{≥b}` both sides of the map at
  `σ^{≥N}K` lie in `D^{≥N+b}`. This is the source's "sitting in degrees `≥ N + b`", and the
  reduction along stupid truncations brings `E` down to the terms of `K`, single flat sheaves.

## Main results

* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_isIso_single` — **the
  reduction of Tag 0F1J to single objects.**
* `Stacks.EtaleCohomology.EtaleCoefficients.isIso_tensorBaseChangeMap_of_isIso_single_of_field` —
  Tag 0F1J in its own setting, given its case of a single flat sheaf and a single sheaf. Not
  registered: that case is the content of the last two paragraphs of the source's proof, which
  rest on Tags 0F1I, 0F0G and 09Z7 (see the implementation notes).

## Implementation notes

*What the conditional statement assumes.* `isIso_tensorBaseChangeMap_of_isIso_single_of_field`
takes as its one extra argument, `hsingle`, the invertibility of the canonical map at `p⁻¹` of a
flat sheaf of `ℤ/nℤ`-modules placed in a single degree and a sheaf of `ℤ/nℤ`-modules placed in a
single degree. The source proves this in its last two paragraphs: the reduction from `ℤ/nℤ` to
`𝔽_ℓ`, then, for sheaves of `𝔽_ℓ`-vector spaces, the reduction to `X` affine and to `E`
constructible (Tags 03SA and 09Z1), the embedding of a constructible sheaf into a finite sum of
`π_{i,*}𝔽_ℓ` (Tag 09Z7), and for `π_{i,*}𝔽_ℓ` the base change of Tag 0F1I along `X_i ⟶ Spec(K)`
together with Tag 0F0G for the finite morphisms `π_i`. Tags 0F0G and 09Z7 are not formalized
here, and Tag 0F1I is stated in this development for abelian sheaves on `X_étale` with the derived
base change map of `D^+` of those, not on `D(X_étale, Λ)`.

*Degrees.* "A single object" is an object placed in an arbitrary degree. Without a compatibility
of the canonical map with the shift the degree cannot be normalised to zero, and the source's
phrase "`E` is given by a single flat module" is read that way.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- AdjunctionForRingedTopoi.lean:394`)
-- is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

section Reduction

variable {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X')
  (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)

/-- Tensoring with `A` of Tor amplitude in `[k, ∞]` sends `(f')⁻¹Rg_*L`, `L ∈ D^{≥m}`, into
`D^{≥k+m}`. -/
private theorem isGE_tensor_pullback_pushforward_obj (A : DerivedModules Λ X') (k : ℤ)
    (hA : HasTorAmplitudeGE Λ A k) (L : DerivedModules Λ T) (m : ℤ) (hL : L.IsGE m) :
    (((tensor Λ X').obj A).obj ((pullback Λ f').obj ((pushforward Λ g).obj L))).IsGE (k + m) :=
  isGE_tensor_obj_of_hasTorAmplitudeGE Λ _ _ k m hA
    (isGE_pullback_obj Λ f' _ m (isGE_pushforward_obj Λ g L m hL))

/-- Tensoring with `A` of Tor amplitude in `[k, ∞]` sends `Rh_*(h⁻¹A ⊗ e⁻¹L)`, `L ∈ D^{≥m}`,
into `D^{≥k+m}`. -/
private theorem isGE_pushforward_tensor_pullback_obj (A : DerivedModules Λ X') (k : ℤ)
    (hA : HasTorAmplitudeGE Λ A k) (L : DerivedModules Λ T) (m : ℤ) (hL : L.IsGE m) :
    ((pushforward Λ h).obj (((tensor Λ Y).obj ((pullback Λ h).obj A)).obj
      ((pullback Λ e).obj L))).IsGE (k + m) :=
  isGE_pushforward_obj Λ h _ (k + m)
    (isGE_tensor_obj_of_hasTorAmplitudeGE Λ _ _ k m
      (hasTorAmplitudeGE_pullback_obj Λ h A k hA) (isGE_pullback_obj Λ e L m hL))

/-- **The reduction in the variable `F`.** Let `A ∈ D(X'_étale, Λ)` have Tor amplitude in
`[k, ∞]`. If the canonical map of Tag 0F1J at `A` is invertible at every sheaf of `Λ̲`-modules on
`T_étale` placed in any single degree, it is invertible at every bounded below `F`. -/
theorem isIso_tensorBaseChangeMap_of_isIso_singleFunctor_right (A : DerivedModules Λ X') (k : ℤ)
    (hA : HasTorAmplitudeGE Λ A k)
    (hsingle : ∀ (G : SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O)) (j : ℤ),
      IsIso (tensorBaseChangeMap Λ f' g h e w A ((DerivedCategory.singleFunctor _ j).obj G)))
    (F : DerivedModules Λ T) (b : ℤ) (hF : F.IsGE b) :
    IsIso (tensorBaseChangeMap Λ f' g h e w A F) :=
  CategoryTheory.NatTrans.isIso_app_of_isGE_of_isIso_app_singleFunctor
    (tensorBaseChangeNatTransRight Λ f' g h e w A) k
    (fun L m hL => by
      rw [add_comm]
      exact isGE_tensor_pullback_pushforward_obj Λ f' g A k hA L m hL)
    (fun L m hL => by
      rw [add_comm]
      exact isGE_pushforward_tensor_pullback_obj Λ h e A k hA L m hL)
    hsingle F b hF

open HomologicalComplex ComplexShape in
/-- **The reduction in the variable `E`, along stupid truncations.** Let `K` be a K-flat complex of
flat sheaves of `Λ̲`-modules on `X_étale` vanishing below `a`, and `F ∈ D^{≥b}`. If the canonical
map of Tag 0F1J at `(p⁻¹(-), F)` is invertible at every term of `K` placed in any single degree, it
is invertible at `p⁻¹K`. Both sides at `p⁻¹σ^{≥N}K` lie in `D^{≥N+b}`. -/
theorem isIso_tensorBaseChangeMap_pullback_Q_obj_of_isIso_singleFunctor_left
    (F : DerivedModules Λ T) (b : ℤ) (hF : F.IsGE b)
    (K : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) ℤ) (a : ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat (ringedTopos Λ X).O K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
      (O := (ringedTopos Λ X).O) (K.X i))
    (hzero : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hsingle : ∀ i k : ℤ, IsIso (tensorBaseChangeMap Λ f' g h e w
      ((pullback Λ p).obj ((DerivedCategory.singleFunctor _ k).obj (K.X i))) F)) :
    IsIso (tensorBaseChangeMap Λ f' g h e w ((pullback Λ p).obj (DerivedCategory.Q.obj K)) F) := by
  have : K.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]; exact hzero
  have hamp : ∀ N : ℤ, HasTorAmplitudeGE Λ
      ((pullback Λ p).obj (DerivedCategory.Q.obj (K.stupidTrunc (embeddingUpIntGE N)))) N :=
    fun N => hasTorAmplitudeGE_pullback_obj Λ p _ N
      (hasTorAmplitudeGE_Q_obj_stupidTruncGE Λ K hK hflat N)
  exact CategoryTheory.NatTrans.isIso_app_Q_obj_of_isIso_app_singleFunctor_X
    (Functor.whiskerLeft (pullback Λ p) (tensorBaseChangeNatTransLeft Λ f' g h e w F)) K a b
    hsingle
    (fun N => isGE_tensor_pullback_pushforward_obj Λ f' g _ N (hamp N) F b hF)
    (fun N => isGE_pushforward_tensor_pullback_obj Λ h e _ N (hamp N) F b hF)

/-- **The reduction of [Stacks, Tag 0F1J] to single objects.** Let `p : X' ⟶ X` and
`h ≫ f' = e ≫ g` be morphisms of schemes, `E ∈ D(X_étale, Λ)` of Tor amplitude in `[a, ∞]` and
`F ∈ D(T_étale, Λ)` bounded below. If the canonical map

`p⁻¹M ⊗^L_Λ (f')⁻¹Rg_*G ⟶ Rh_*(h⁻¹p⁻¹M ⊗^L_Λ e⁻¹G)`

is invertible for every flat sheaf of `Λ̲`-modules `M` on `X_étale` and every sheaf of
`Λ̲`-modules `G` on `T_étale`, each placed in any single degree, then the canonical map

`p⁻¹E ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_Λ e⁻¹F)`

is invertible. This is the first two paragraphs of the proof of Tag 0F1J, for an arbitrary
commutative ring `Λ` and an arbitrary commutative square. -/
theorem isIso_tensorBaseChangeMap_of_isIso_single
    (hsingle : ∀ (M : SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
        (O := (ringedTopos Λ X).O) M →
      ∀ (G : SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O)) (k j : ℤ),
      IsIso (tensorBaseChangeMap Λ f' g h e w
        ((pullback Λ p).obj ((DerivedCategory.singleFunctor _ k).obj M))
        ((DerivedCategory.singleFunctor _ j).obj G)))
    (E : DerivedModules Λ X) (a : ℤ) (hE : HasTorAmplitudeGE Λ E a)
    (F : DerivedModules Λ T) (b : ℤ) (hF : F.IsGE b) :
    IsIso (tensorBaseChangeMap Λ f' g h e w ((pullback Λ p).obj E) F) := by
  obtain ⟨K, hK, hflat, hzero, ⟨eK⟩⟩ :=
    (Stacks.SheafOfModules.hasTorAmplitudeGE_iff_exists_kFlatRepresentative
      (X := (ringedTopos Λ X).toRingedSite) E a).1 hE
  have hQ := isIso_tensorBaseChangeMap_pullback_Q_obj_of_isIso_singleFunctor_left Λ p f' g h e w
    F b hF K a hK hflat hzero (fun i k =>
      isIso_tensorBaseChangeMap_of_isIso_singleFunctor_right Λ f' g h e w _ k
        (hasTorAmplitudeGE_pullback_obj Λ p _ k
          (hasTorAmplitudeGE_singleFunctor_obj Λ (K.X i) (hflat i) k))
        (fun G j => hsingle (K.X i) (hflat i) G k j) F b hF)
  exact ((tensorBaseChangeNatTransLeft Λ f' g h e w F).isIso_app_iff_of_iso
    ((pullback Λ p).mapIso eK)).1 hQ

end Reduction

section Field

/-- **[Stacks, Tag 0F1J], given its case of single objects.** Let `K` be a field, `n ≥ 1`
invertible in `K`, and consider schemes `X ⟶ Spec(K)`, `S' ⟶ Spec(K)`, `X' = X ×_{Spec(K)} S'` with
projections `p : X' ⟶ X` and `f' : X' ⟶ S'`, a quasi-compact and quasi-separated `g : T ⟶ S'`, and
`Y = X' ×_{S'} T` with projections `h : Y ⟶ X'` and `e : Y ⟶ T`. For `E ∈ D^+(X_étale, ℤ/nℤ)` of
Tor amplitude in `[a, ∞]` and `F ∈ D^+(T_étale, ℤ/nℤ)` the canonical map

`p⁻¹E ⊗^L_{ℤ/nℤ} (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹p⁻¹E ⊗^L_{ℤ/nℤ} e⁻¹F)`

is an isomorphism, given the hypothesis `hsingle`: the same map is invertible when `E` is a flat
sheaf of `ℤ/nℤ`-modules and `F` a sheaf of `ℤ/nℤ`-modules, each placed in a single degree.

That case is the content of the last two paragraphs of the source's proof (Tags 0F1I, 0F0G,
09Z7, 03SA, 09Z1; see the implementation notes of the module); everything else is
`isIso_tensorBaseChangeMap_of_isIso_single`. The hypotheses on `K`, `n`, the two fibre squares
and `g` are those of the source and are what `hsingle` needs; the boundedness below of `E` is
implied by its Tor amplitude and is carried as the source states it. -/
theorem isIso_tensorBaseChangeMap_of_isIso_single_of_field (k : Type u) [Field k] (n : ℕ)
    [NeZero n] (_hn : IsUnit (n : k)) {X X' S' T Y : Scheme.{u}} (πX : X ⟶ Spec (.of k))
    (s : S' ⟶ Spec (.of k)) (p : X' ⟶ X) (f' : X' ⟶ S') (_hX' : IsPullback p f' πX s)
    (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T) (hY : IsPullback h e f' g) [QuasiCompact g]
    [QuasiSeparated g]
    (hsingle : ∀ (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod n)) X).O)),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u + 1, u + 1, u + 1, u + 1}
        (O := (ringedTopos (ULift.{u + 1} (ZMod n)) X).O) M →
      ∀ (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (ringedTopos (ULift.{u + 1} (ZMod n)) T).O)) (i j : ℤ),
      IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
        ((pullback (ULift.{u + 1} (ZMod n)) p).obj ((DerivedCategory.singleFunctor _ i).obj M))
        ((DerivedCategory.singleFunctor _ j).obj G)))
    (E : DerivedModules (ULift.{u + 1} (ZMod n)) X) (_hE : ∃ c : ℤ, E.IsGE c) (a : ℤ)
    (hEa : HasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) E a)
    (F : DerivedModules (ULift.{u + 1} (ZMod n)) T) (hF : ∃ b : ℤ, F.IsGE b) :
    IsIso (tensorBaseChangeMap (ULift.{u + 1} (ZMod n)) f' g h e hY.w
      ((pullback (ULift.{u + 1} (ZMod n)) p).obj E) F) := by
  obtain ⟨b, hb⟩ := hF
  exact isIso_tensorBaseChangeMap_of_isIso_single _ p f' g h e hY.w hsingle E a hEa F b hb

end Field

end Stacks.EtaleCohomology.EtaleCoefficients

end
