module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.DerivedSheafHom
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapNaturality
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedPullbackAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude

/-!
# Base change for a derived internal hom out of an approximable object

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes, `K ∈ D(𝒪_X)` and `K' ∈ D(𝒪_{X'})` bounded below and
`φ : L(g')^*K ⟶ K'` such that the map of Stacks 0DJ7 is an isomorphism at every point of `X'` and
in every degree, which is condition (1) of Stacks 0DJ8. Fix a point `x'` of `X'` lying over
`s' ∈ S'` and `s ∈ S`, and suppose that `𝒪_{S', s'}` has Tor amplitude in `[-d, e]` over
`𝒪_{S, s}`. If `E ∈ D(𝒪_X)` receives a map `α : P ⟶ E` from a perfect `P` which is an isomorphism
on cohomology above a degree `m` and surjective in degree `m`, then the map of Stacks 0DJ7 for the
comparison

`L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')`

is an isomorphism at `x'` in every degree `n` small enough with respect to `m`.

This is the truncation step of the corrected Stacks 0DJA (3). The cone `Z` of `α` lies in
`D^{≤ m - 1}`, so `R𝓗om(Z, K)` lies in `D^{≥ a - m + 1}` and, after the derived base change of its
stalk along `𝒪_{S, s} ⟶ 𝒪_{S', s'}`, in `D^{≥ a - m + 1 - d}`: here the Tor amplitude of
`𝒪_{S', s'}` is used. On the other side `R𝓗om(L(g')^*Z, K')` lies in `D^{≥ a' - m + 1}`. So both
sides of the map of Stacks 0DJ7 for `E` agree in degree `n` with those for `P`, where the map is
an isomorphism by Stacks 0DJA (2).

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_approximation`

## References

* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open StacksDraft.TorAmplitude

universe u w

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedInternalHomPullback
open RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

private instance (h : X' ⟶ X) : (derivedPullback h.toLRSHom.toShHom).CommShift ℤ :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift h.toLRSHom.toShHom

private instance (h : X' ⟶ X) : (derivedPullback h.toLRSHom.toShHom).IsTriangulated :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated h.toLRSHom.toShHom

/-- **The comparison for a derived internal hom is natural in the source.** For `α : P ⟶ E`, the
comparison `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` followed by precomposition with
`L(g')^*α` is the derived pullback of precomposition with `α` followed by the comparison at
`P`. -/
theorem baseChangeSheafHomComparison_comp_map_op (h : X' ⟶ X)
    {P E : DerivedCategory X.Modules} (α : P ⟶ E) (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback h.toLRSHom.toShHom).obj K ⟶ K') :
    Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
        h.toLRSHom.toShHom E K K' φ ≫
      ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).map
        ((derivedPullback h.toLRSHom.toShHom).map α).op).app K' =
    (derivedPullback h.toLRSHom.toShHom).map
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map α.op).app K) ≫
      Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
        h.toLRSHom.toShHom P K K' φ := by
  have sq := Transpose.homComparison_naturality_source (derivedPullbackFunctor h.toLRSHom.toShHom)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X'.sheaf)
    (internalHomTensorUncurried X.toRingedSpace) (internalHomTensorUncurried X'.toRingedSpace)
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X.sheaf) A B C).toEquiv)
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X'.sheaf) A B C).toEquiv)
    (pullbackTensorIso h.toLRSHom.toShHom)
    (tensorHomEquivNaturalLeft_ringedSpace X.toRingedSpace)
    (tensorHomEquivDinatural_ringedSpace X.toRingedSpace)
    (tensorHomEquivNaturalLeft_ringedSpace X'.toRingedSpace)
    (tensorHomEquivDinatural_ringedSpace X'.toRingedSpace) α K
  have hφ := ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).map
    ((derivedPullback h.toLRSHom.toShHom).map α).op).naturality φ
  dsimp only [Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => _ ≫ t) hφ).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ _) sq.symm).trans ?_
  exact Category.assoc _ _ _

/-- Taking stalks commutes with cohomology: a morphism of `D(𝒪_Z)` invertible on cohomology in
degree `n` has invertible stalks on cohomology in degree `n`. -/
private theorem isIso_homologyMap_derivedStalkFunctor_map {Z : Scheme.{u}}
    [HasDerivedCategory.{w} Z.Modules] {z : Z}
    [HasDerivedCategory.{w} (ModuleCat.{u} (Z.presheaf.stalk z))]
    {A B : DerivedCategory Z.Modules} (v : A ⟶ B) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor Z.Modules n).map v)) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map ((derivedStalkFunctor z).map v)) :=
  (NatIso.isIso_map_iff (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z) n) v).2
    (Functor.map_isIso (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z) _)

/-- A morphism whose composite with an isomorphism is a composite of two isomorphisms is an
isomorphism. -/
private theorem isIso_of_comp_eq_comp {C : Type*} [Category C] {a b c d : C} (u : a ⟶ b)
    (v : b ⟶ d) (s : a ⟶ c) (t : c ⟶ d) (h : u ≫ v = s ≫ t) [IsIso v] [IsIso s] [IsIso t] :
    IsIso u := by
  have : IsIso (u ≫ v) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right u v

/-- **Stacks 0DJA (3) at an approximable object, in one degree.** Let the square be cartesian,
let `K` be bounded below by `a` and `K'` by `a'`, and let `φ : L(g')^*K ⟶ K'` satisfy condition (1)
of Stacks 0DJ8. Let `x'` be a point of `X'` at which the base stalk map
`𝒪_{S, s} ⟶ 𝒪_{S', s'}` makes `𝒪_{S', s'}` of Tor amplitude in `[-d, e]` over `𝒪_{S, s}`. If
`α : P ⟶ E` is a map from a perfect object which is invertible on cohomology above `m` and
surjective in degree `m`, with `n + 1 < a - (m - 1) - d` and `n + 1 < a' - (m - 1)`, then the map
of Stacks 0DJ7 for `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` is an isomorphism at `x'` in
degree `n`. -/
theorem isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_approximation
    (hpb : IsPullback g' f' f g) (E K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules) (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' hpb.w K K' φ x' n))
    (a a' : ℤ) (hK : K.IsGE a) (hK' : K'.IsGE a') (x' : X') (n d e m : ℤ)
    (hT : HasTorAmplitudeCanonical (S.presheaf.stalk (f (g' x')))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (S.presheaf.stalk (f (g' x')))) 0).obj
        ((ModuleCat.restrictScalars (baseStalkMap f g f' g' hpb.w x')).obj
          (ModuleCat.of (S'.presheaf.stalk (f' x')) (S'.presheaf.stalk (f' x'))))) (-d) e)
    (hm : n + 1 < a - (m - 1) - d) (hm' : n + 1 < a' - (m - 1))
    (P : DerivedCategory X.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P)
    (α : P ⟶ E) (hiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    IsIso (baseChangeCohomologyMap f g f' g' hpb.w
      (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K)
      (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
        (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj K')
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
        g'.toLRSHom.toShHom E K K' φ) x' n) := by
  obtain ⟨Z, β, δ, hT₀⟩ := Pretriangulated.distinguished_cocone_triangle α
  have hZ : Z.IsLE (m - 1) :=
    DerivedCategory.isLE_three_of_homologyMap_mor₁ (Triangle.mk α β δ) hT₀ m hiso hepi
  let H := Stacks.SheafOfModules.derivedSheafHom X.sheaf
  let H' := Stacks.SheafOfModules.derivedSheafHom X'.sheaf
  let L := derivedPullback g'.toLRSHom.toShHom
  let θ := (H.map α.op).app K
  let θ' := (H'.map (L.map α).op).app K'
  -- the two sides of the map of Stacks 0DJ7 agree in degree `n` for `E` and for `P`
  have hθ' : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((derivedStalkFunctor x').map θ')) := by
    have hX := AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHom_map_of_isLE₃
      (Stacks.SheafOfModules.ringedSite X'.sheaf) (L.mapTriangle.obj (Triangle.mk α β δ))
      (L.map_distinguished _ hT₀) (m - 1)
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj
        g'.toLRSHom.toShHom Z (m - 1) hZ) K' a' hK' n hm'
    exact isIso_homologyMap_derivedStalkFunctor_map (z := x') θ' n hX
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' hpb.w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' hpb.w x')
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')))
  let := Tg.commShift
  let := Tg.isTriangulated
  have hθ : IsIso ((DerivedCategory.homologyFunctor _ n).map (Tg.functor.map
      ((ModuleCat.restrictScalars (algebraMap (S.presheaf.stalk (f (g' x')))
        (X.presheaf.stalk (g' x')))).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g' x')).mapDerivedCategory.map
            θ)))) := by
    obtain ⟨δ', hδ'⟩ := AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom
      (Stacks.SheafOfModules.ringedSite X.sheaf) K _ hT₀
    have h₁ := AlgebraicGeometry.RingedSite.isGE_derivedSheafHom
      (Stacks.SheafOfModules.ringedSite X.sheaf) Z K (m - 1) a hZ hK
    have h₂ := DerivedPullbackAmplitude.isGE_derivedStalkFunctor _ _ h₁ (g' x')
    have h₃ := isGE_mapDerivedCategory_obj (ModuleCat.restrictScalars
      (algebraMap (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')))) _ _ h₂
    have h₄ := DerivedPullbackAmplitude.isGE_totalDerivedExtensionScalars
      (baseStalkMap f g f' g' hpb.w x') (-d) e hT _ _ h₃
    exact isIso_homologyMap_map_mor₂_of_isGE₁
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X (g' x')).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (algebraMap (S.presheaf.stalk (f (g' x')))
          (X.presheaf.stalk (g' x')))).mapDerivedCategory ⋙ Tg.functor)
      _ hδ' n (a - (m - 1) + -d) h₄ (by omega)
  have hsrc := isIso_baseChangeCohomologyMapHom_of_isIso (R := S.presheaf.stalk (f (g' x')))
    (R' := S'.presheaf.stalk (f' x')) ((derivedStalkFunctor (g' x')).map θ) n hθ
  have hP' := isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_of_isPerfect hpb P K hP
    K' φ h x' n
  have hsq := baseChangeSheafHomComparison_comp_map_op g' α K K' φ
  have key := (baseChangeCohomologyMap_comp f g f' g' hpb.w _ _ _
      (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
        g'.toLRSHom.toShHom E K K' φ) θ' x' n).symm.trans
    ((congrArg (fun t => baseChangeCohomologyMap f g f' g' hpb.w _ _ t x' n) hsq).trans
      (baseChangeCohomologyMap_map_comp f g f' g' hpb.w _ _ _ θ
        (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
          g'.toLRSHom.toShHom P K K' φ) x' n))
  refine @isIso_of_comp_eq_comp _ _ _ _ _ _ _ _ _ _ key ?_ ?_ hP'
  · exact hθ'
  · exact ((ModuleCat.extendScalars _).mapIso (@asIso _ _ _ _ _ hsrc)).isIso_hom

end AlgebraicGeometry

end
