module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseRestrictionConverse
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.PseudoCoherentApproximation
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.SheafHomRestriction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.SheafHomTruncation
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.TorAmplitudeVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for `R𝓗om` out of a pseudo-coherent object, along `g` of finite Tor dimension

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `g` of finite Tor dimension, `K ∈ D(𝒪_X)` bounded below,
`K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` such that the map of Stacks 0DJ7 is an isomorphism at
every point of `X'` and in every degree, which is condition (1) of Stacks 0DJ8.  Then for every
pseudo-coherent `E ∈ D(𝒪_X)` the same holds for the comparison

`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`.

This is Stacks 0DJA (3) with the hypothesis "`g` has finite Tor dimension" added. As printed,
with no condition on `g`, part (3) is false:
`AlgebraicGeometry.not_pointwiseBaseChangeSheafHomOfPseudoCoherent` is a counterexample over
`ℤ/4`, with `g : Spec ℤ/2 ⟶ Spec ℤ/4`, which is not of finite Tor dimension.

## Finite Tor dimension

`g` has finite Tor dimension when `𝒪_{S'}` has Tor amplitude in some interval `[a, b]` as a
`g⁻¹𝒪_S`-module. Tor amplitude of a sheaf of modules is read at the stalks (Stacks 0DJJ), and the
stalk of `g⁻¹𝒪_S` at `s'` is `𝒪_{S, g s'}`; the hypothesis is stated in that form: there are
`a ≤ b`-bounds such that every local ring `𝒪_{S', s'}` has Tor amplitude in `[a, b]` over
`𝒪_{S, g s'}`.

## The proof

The source represents `E_x` by a bounded above complex of finite free modules and computes the
source and the target of the map of Stacks 0DJ7. The computation needs, in each degree, only
finitely many terms of that complex, and that is where finite Tor dimension enters: the derived
base change along `𝒪_{S, s} ⟶ 𝒪_{S', s'}` of an object bounded below by `c` is bounded below by
`c + a`. The proof here fixes a point `x'` and a degree `n` and makes that truncation precise:

* `K` is bounded below by some `a₁`, so `K'` is bounded below by `a₁ + a`
  (`AlgebraicGeometry.isGE_of_isIso_baseChangeCohomologyMap`);
* on an open `U ∋ g' x'` there is a distinguished triangle `P ⟶ E|_U ⟶ C ⟶ P[1]` with `P` perfect
  and `C` concentrated in degrees `≤ m`, for `m` far below `n`
  (`AlgebraicGeometry.exists_isPerfect_distTriang_derivedPullback_ι`);
* over the restricted cartesian square `g'⁻¹(U) ⟶ U`, the condition holds for `P` by Stacks
  0DJA (2), and passes to `E|_U` in degree `n` because the cones of `R𝓗om(E|_U, K) ⟶ R𝓗om(P, K)`
  and of its counterpart on `g'⁻¹(U)` are concentrated in high degrees
  (`isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_iff_of_distTriang`);
* restriction to the open `U` commutes with `R𝓗om` and with the comparison
  (`AlgebraicGeometry.isIso_baseChangeCohomologyMap_pullDatum_baseChangeSheafHomComparison_iff`),
  and the condition at a point of `g'⁻¹(U)` is the condition at its image in `X'`
  (`AlgebraicGeometry.isIso_baseChangeCohomologyMap_of_restrict`).

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_hasTorAmplitude`

## References

* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Stacks 0DJA (3), corrected: `g` of finite Tor dimension.** For a cartesian square of
schemes with `g` of finite Tor dimension (every `𝒪_{S', s'}` of Tor amplitude in a fixed
interval `[a, b]` over `𝒪_{S, g s'}`), if the map of Stacks 0DJ7 at `(K, K', φ)` is an
isomorphism at every point of `X'` and in every degree and `K` is bounded below, then so is the
one at the comparison `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, for every pseudo-coherent `E`
in `D(𝒪_X)`.

As printed, with no condition on `g`, part (3) is false:
`AlgebraicGeometry.not_pointwiseBaseChangeSheafHomOfPseudoCoherent` is a counterexample with
`g : Spec ℤ/2 ⟶ Spec ℤ/4`. -/
@[stacks 0DJA "(3), corrected: g of finite Tor dimension added (every local ring of S' of Tor \
amplitude in a fixed interval over the local ring of S below it); with no condition on g part \
(3) is false, see AlgebraicGeometry.not_pointwiseBaseChangeSheafHomOfPseudoCoherent"]
theorem isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_hasTorAmplitude
    (hpb : IsPullback g' f' f g)
    (hg : ∃ a b : ℤ, ∀ s' : S',
      letI := (g.stalkMap s').hom.toAlgebra
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical (S.presheaf.stalk (g s'))
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (ModuleCat.{u} (S.presheaf.stalk (g s'))) 0).obj
            (ModuleCat.of (S.presheaf.stalk (g s')) (S'.presheaf.stalk s')))) a b)
    (E K : DerivedCategory X.Modules)
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hK : DerivedCategoryB.IsBoundedBelow K)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ x' n))
    (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K)
      (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
        g'.toLRSHom.toShHom E K K' φ) x' n) := by
  obtain ⟨a₀, b₀, hg⟩ := hg
  obtain ⟨a, ha⟩ := hK
  have hKa : K.IsGE a := (DerivedCategory.isGE_iff K a).2 ha
  have hK'a : K'.IsGE (a + a₀) :=
    isGE_of_isIso_baseChangeCohomologyMap f g f' g' hpb.w a₀ b₀ hg K K' φ h a hKa
  obtain ⟨U, hU, T, hT, hP, hT₂, hC⟩ :=
    exists_isPerfect_distTriang_derivedPullback_ι E hE (g' x') (a + a₀ - n - 2)
  let y : (g' ⁻¹ᵁ U).toScheme := ⟨x', hU⟩
  have hpbU := (isPullback_morphismRestrict g' U).paste_vert hpb
  let φU := Stacks.Cohomology.BaseChangeCover.pullDatum (g' ∣_ U).toLRSHom.toShHom
    (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom U.ι.toLRSHom.toShHom g'.toLRSHom.toShHom
    (comp_toShHom_of_comm (morphismRestrict_ι g' U)) K K' φ
  have hU' : ∀ (z : (g' ⁻¹ᵁ U).toScheme) (j : ℤ), IsIso (baseChangeCohomologyMap (U.ι ≫ f) g
      ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U) hpbU.w ((derivedPullback U.ι.toLRSHom.toShHom).obj K)
      ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K') φU z j) := fun z j =>
    isIso_baseChangeCohomologyMap_pullDatum hpb hpbU U.ι (g' ⁻¹ᵁ U).ι (𝟙 S) (𝟙 S')
      (morphismRestrict_ι g' U) (Category.comp_id _) (Category.comp_id _)
      (by rw [Category.comp_id, Category.id_comp]) K K' φ z j (h _ j)
  have hKU : ((derivedPullback U.ι.toLRSHom.toShHom).obj K).IsGE a :=
    Stacks.Cohomology.DerivedInternalHomPullback.isGE_derivedPullback_obj_of_isFlat _
      (fun z => Flat.stalkMap U.ι z) K a hKa
  have hK'U : ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K').IsGE (a + a₀) :=
    isGE_of_isIso_baseChangeCohomologyMap (U.ι ≫ f) g ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U) hpbU.w
      a₀ b₀ hg _ _ φU hU' a hKU
  have hPy := isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect hpbU
    T.obj₁ ((derivedPullback U.ι.toLRSHom.toShHom).obj K) hP
    ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K') φU hU' y n
  have hEy := (isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_iff_of_distTriang
    (U.ι ≫ f) g ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U) hpbU.w T hT (a + a₀ - n - 2) hC
    ((derivedPullback U.ι.toLRSHom.toShHom).obj K) a hKU
    ((derivedPullback (g' ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj K') (a + a₀) hK'U φU y a₀
    (fun N c j hN hj => isZero_baseChangeCohomologyOverBase_of_isGE (U.ι ≫ f) g
      ((g' ⁻¹ᵁ U).ι ≫ f') (g' ∣_ U) hpbU.w a₀ b₀ hg y N c j hN hj)
    n (by omega) (by omega)).2 hPy
  rw [hT₂] at hEy
  exact isIso_baseChangeCohomologyMap_of_restrict hpb U _ _ _ y n
    ((isIso_baseChangeCohomologyMap_pullDatum_baseChangeSheafHomComparison_iff hpb U E K K' φ y
      n).2 hEy)

end AlgebraicGeometry
