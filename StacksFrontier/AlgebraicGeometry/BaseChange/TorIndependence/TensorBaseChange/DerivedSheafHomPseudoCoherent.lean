module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.FlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPerfectAndPseudoCoherent
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for a derived internal hom out of a pseudo-coherent object

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `g` flat, `K ∈ D(𝒪_X)` bounded below,
`K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'` such that the map of Stacks 0DJ7 is an isomorphism at
every point of `X'` and in every degree.  Then for every pseudo-coherent `E ∈ D(𝒪_X)` the same
holds for the comparison

`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`.

This is Stacks 0DJA (3) for a flat `g`.  Without flatness of `g` the statement fails:
`AlgebraicGeometry.not_pointwiseBaseChangeSheafHomOfPseudoCoherent` is a counterexample over
`ℤ/4`.

## Main results

* `isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPseudoCoherent`: for `g` flat,
  `K` bounded below and `E` pseudo-coherent, the map of Stacks 0DJ7 for `R𝓗om(E, K)` is an
  isomorphism at every point and in every degree whenever the one for `(K, K', φ)` is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedInternalHomPullback

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Stacks 0DJA (3), for a flat `g`.** For a cartesian square of schemes with `g` flat, if the
map of Stacks 0DJ7 at `(K, K', φ)` is an isomorphism at every point of `X'` and in every degree
and `K` is bounded below, then so is the one at the comparison
`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`, for every pseudo-coherent `E` in `D(𝒪_X)`. -/
@[stacks 0DJA "(3), for a flat morphism g : S' → S; without flatness of g part (3) fails, by \
the counterexample over ℤ/4 AlgebraicGeometry.not_pointwiseBaseChangeSheafHomOfPseudoCoherent"]
theorem isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPseudoCoherent
    (hpb : IsPullback g' f' f g) [Flat g] (E K : DerivedCategory X.Modules)
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
  have : Flat g' := MorphismProperty.of_isPullback hpb.flip ‹Flat g›
  have hg' : AlgebraicGeometry.IsFlat g'.toLRSHom.toShHom := fun x => Flat.stalkMap g' x
  have hKl : AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow X.toRingedSpace K := by
    obtain ⟨N, hN⟩ := hK
    exact fun x => ⟨⊤, trivial, N, fun i hi => Functor.map_isZero _ (hN i hi)⟩
  have hφ : IsIso φ := isIso_of_isIso_baseChangeCohomologyMap_of_flat hpb K K' φ h
  have hc : IsIso (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
      g'.toLRSHom.toShHom E K K' φ) :=
    IsIso.comp_isIso' (isIso_derivedPullbackSheafHomMap_of_isPseudoCoherent g'.toLRSHom.toShHom
      hg' E hE K hKl) (Functor.map_isIso _ _)
  have h1 := (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hpb.w _ _ _ (𝟙 _) _ hc
    x' n).2 (isIso_baseChangeCohomologyMap_id_of_flat hpb _ x' n)
  exact isIso_baseChangeCohomologyMap_of_eq hpb.w _ _ _ _ (Category.id_comp _).symm x' n h1

end AlgebraicGeometry
