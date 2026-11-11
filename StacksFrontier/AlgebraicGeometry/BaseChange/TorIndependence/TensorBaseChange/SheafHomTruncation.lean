module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeComparisonMaps
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedBoundedBelow
public import StacksFrontier.Homology.Tor.BaseChangeCohomologyDevissage

/-!
# Truncation for the pointwise base-change map of a derived internal hom

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes, `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and
`φ : L(g')^*K ⟶ K'`. For `E ∈ D(𝒪_X)` the comparison
`c_E : L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` is a datum for the pointwise base-change map of
Stacks 0DJ7. This module shows that a distinguished triangle `P ⟶ E ⟶ C ⟶ P[1]` with `C` bounded
above by `m` does not change whether that map is invertible in a fixed degree `n`, provided `K`
and `K'` are bounded below far enough beyond `m` and `n`, and the derived base change of stalks
along `𝒪_{S, s} ⟶ 𝒪_{S', s'}` lowers lower bounds by at most a fixed amount. This is the
truncation step in the proof of Stacks 0DJA (3) for a morphism `g` of finite Tor dimension.

The argument compares the two data through a morphism of data: the map
`R𝓗om(E, K) ⟶ R𝓗om(P, K)` and the map `R𝓗om(L(g')^*E, K') ⟶ R𝓗om(L(g')^*P, K')`, which commute
with the comparisons. The cone of each is `R𝓗om` out of `C` (respectively `L(g')^*C`), which
is bounded below by `a - m` (respectively `b - m`), so both maps are invertible on cohomology in
the degrees that matter.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_iff_of_comm`: a morphism of data which is
  invertible on the stalkwise cohomology of the target and on the cohomology of the derived base
  change of the stalk of the source, in degree `n`, identifies the two maps of Stacks 0DJ7 in
  degree `n` up to isomorphism.
* `AlgebraicGeometry.isIso_baseChangeCohomologyOverBaseMap_derivedStalkFunctor_map_mor₂`: the
  derived base change of a stalk of the second morphism of a distinguished triangle is
  invertible in degree `n` when that of the first vertex vanishes in degrees `n` and `n + 1`.
* `Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison_naturality_source`:
  the comparison `c_E` is natural in `E`.
* `AlgebraicGeometry.isIso_homologyMap_derivedStalkFunctor_map_derivedSheafHom_map_mor₁`: the
  stalk of `R𝓗om(T.mor₁, M)` is invertible on cohomology in low degrees.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_iff_of_distTriang`:
  the truncation step itself.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open RingTheory.TorIndependence

universe u

/-! ### Naturality of the comparison in the first variable -/

namespace Stacks.Cohomology.DerivedBaseChangeComparison

open Stacks.Cohomology.DerivedInternalHomPullback

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X' X : AlgebraicGeometry.RingedSpace.{u, u}} (h : X' ⟶ X)

/-- **The base-change comparison for a derived internal hom is natural in the first variable.**
For `α : P ⟶ E` in `D(𝒪_X)`, the comparisons
`Lh^*R𝓗om(E, K) ⟶ R𝓗om(Lh^*E, K')` and `Lh^*R𝓗om(P, K) ⟶ R𝓗om(Lh^*P, K')` built from the same
`φ : Lh^*K ⟶ K'` commute with `R𝓗om(α, K)` and `R𝓗om(Lh^*α, K')`. -/
theorem baseChangeSheafHomComparison_naturality_source
    {P E : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)}
    (α : P ⟶ E) (K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (K' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'))
    (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj K ⟶ K') :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).map
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map α.op).app K) ≫
      baseChangeSheafHomComparison h P K K' φ =
    baseChangeSheafHomComparison h E K K' φ ≫
      ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).map α).op).app
          K' := by
  have sq := Transpose.homComparison_naturality_source (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (Stacks.SheafOfModules.derivedSheafHom X'.sheaf)
    (internalHomTensorUncurried X) (internalHomTensorUncurried X')
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X.sheaf) A B C).toEquiv)
    (fun A B C => (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X'.sheaf) A B C).toEquiv)
    (pullbackTensorIso h)
    (tensorHomEquivNaturalLeft_ringedSpace X) (tensorHomEquivDinatural_ringedSpace X)
    (tensorHomEquivNaturalLeft_ringedSpace X') (tensorHomEquivDinatural_ringedSpace X') α K
  have nat := ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).map
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).map α).op).naturality φ
  unfold baseChangeSheafHomComparison
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sq).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) nat.symm).trans (Category.assoc _ _ _).symm)))

end Stacks.Cohomology.DerivedBaseChangeComparison

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedInternalHomPullback

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The derived stalk functor is triangulated -/

section Stalk

variable {Y : Scheme.{u}} (y : Y)

instance derivedStalkFunctor_commShift [HasDerivedCategory Y.Modules]
    [HasDerivedCategory (ModuleCat.{u} (Y.presheaf.stalk y))] :
    (derivedStalkFunctor y).CommShift ℤ :=
  inferInstanceAs
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).mapDerivedCategory.CommShift ℤ)

instance derivedStalkFunctor_isTriangulated [HasDerivedCategory Y.Modules]
    [HasDerivedCategory (ModuleCat.{u} (Y.presheaf.stalk y))] :
    (derivedStalkFunctor y).IsTriangulated :=
  inferInstanceAs
    ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).mapDerivedCategory.IsTriangulated)

/-- The derived stalk functor preserves lower bounds on cohomology. -/
theorem isGE_derivedStalkFunctor_obj [HasDerivedCategory Y.Modules]
    [HasDerivedCategory (ModuleCat.{u} (Y.presheaf.stalk y))] (N : DerivedCategory Y.Modules)
    (c : ℤ) (hN : N.IsGE c) :
    ((derivedStalkFunctor y).obj N).IsGE c :=
  isGE_mapDerivedCategory_obj (Stacks.ModuleSkyscraper.modulesStalkFunctor Y y) N c hN

/-- **The derived base change of a stalk of the second morphism of a distinguished triangle.**
Let `T` be a distinguished triangle of `D(𝒪_Y)` and `R ⟶ 𝒪_{Y, y}`, `R ⟶ R'` ring maps. If the
cohomology of `(T.obj₁)_y ⊗^L_R R'` vanishes in degrees `n` and `n + 1`, the map induced by
`T.mor₂` on the cohomology of the derived base change in degree `n` is invertible. -/
theorem isIso_baseChangeCohomologyOverBaseMap_derivedStalkFunctor_map_mor₂
    [HasDerivedCategory Y.Modules] [HasDerivedCategory (ModuleCat.{u} (Y.presheaf.stalk y))]
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R (Y.presheaf.stalk y)] [Algebra R R']
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} R')]
    (T : Triangle (DerivedCategory Y.Modules)) (hT : T ∈ distTriang _) (n : ℤ)
    (h₀ : IsZero (baseChangeCohomologyOverBase (R := R) (R' := R')
      ((derivedStalkFunctor y).obj T.obj₁) n))
    (h₁ : IsZero (baseChangeCohomologyOverBase (R := R) (R' := R')
      ((derivedStalkFunctor y).obj T.obj₁) (n + 1))) :
    IsIso (baseChangeCohomologyOverBaseMap (R := R) (R' := R') _ _
      ((derivedStalkFunctor y).map T.mor₂) n) := by
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R R')
  let _ := Tg.commShift
  let _ := Tg.isTriangulated
  let F := derivedStalkFunctor y ⋙
    (ModuleCat.restrictScalars.{u} (algebraMap R (Y.presheaf.stalk y))).mapDerivedCategory ⋙
      Tg.functor
  have hF := F.map_distinguished T hT
  have hepi : Epi ((DerivedCategory.homologyFunctor _ n).map (F.map T.mor₂)) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hF n (n + 1) rfl).2
      (h₁.eq_zero_of_tgt _)
  have hmono : Mono ((DerivedCategory.homologyFunctor _ n).map (F.map T.mor₂)) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hF n).2 (h₀.eq_zero_of_src _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor _ n).map (F.map T.mor₂))

/-- **The stalk of `R𝓗om(T.mor₁, M)` is invertible on cohomology in low degrees.** Let
`A ⟶ L ⟶ C ⟶ A[1]` be a distinguished triangle of `D(𝒪_Y)` with `C` bounded above by `m`, and
`M` bounded below by `b`. Then the stalk at `y` of `R𝓗om(L, M) ⟶ R𝓗om(A, M)` is invertible on
cohomology in every degree `j` with `j + 1 < b - m`. -/
theorem isIso_homologyMap_derivedStalkFunctor_map_derivedSheafHom_map_mor₁
    (T : Triangle (DerivedCategory Y.Modules)) (hT : T ∈ distTriang _) (m : ℤ)
    (hC : T.obj₃.IsLE m) (M : DerivedCategory Y.Modules) (b : ℤ) (hM : M.IsGE b) (j : ℤ)
    (hj : j + 1 < b - m) :
    IsIso ((DerivedCategory.homologyFunctor _ j).map ((derivedStalkFunctor y).map
      (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).map T.mor₁.op).app M))) := by
  obtain ⟨δ, hδ⟩ := Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first Y.sheaf M T hT
  exact isIso_homologyMap_map_mor₂_of_isGE₁ (derivedStalkFunctor y) _ hδ j (b - m)
    (isGE_derivedStalkFunctor_obj y _ (b - m)
      (Stacks.SheafOfModules.isGE_derivedSheafHom Y.sheaf T.obj₃ M m b hC hM)) hj

end Stalk

/-! ### Morphisms of data -/

section Square

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

attribute [local instance] hasDerivedCategory_ringedSpaceModules in
/-- **A morphism of data for the map of Stacks 0DJ7.** Let `(M₁, M₁', ψ₁)` and `(M₂, M₂', ψ₂)` be
two data and `u : M₁ ⟶ M₂`, `u' : M₁' ⟶ M₂'` with `ψ₁ ≫ u' = L(g')^*u ≫ ψ₂`. If `u'` is
invertible on the stalkwise cohomology at `x'` in degree `n`, and `u` is invertible on the
cohomology of the derived base change of the stalk at `g' x'` in degree `n`, then the map of
Stacks 0DJ7 at the first datum is invertible in degree `n` exactly when the one at the second
is. -/
theorem isIso_baseChangeCohomologyMap_iff_of_comm
    [HasDerivedCategory X.Modules] [HasDerivedCategory X'.Modules]
    {M₁ M₂ : DerivedCategory X.Modules} {M₁' M₂' : DerivedCategory X'.Modules}
    (ψ₁ : (derivedPullback g'.toLRSHom.toShHom).obj M₁ ⟶ M₁')
    (ψ₂ : (derivedPullback g'.toLRSHom.toShHom).obj M₂ ⟶ M₂')
    (u : M₁ ⟶ M₂) (u' : M₁' ⟶ M₂')
    (hcomm : ψ₁ ≫ u' = (derivedPullback g'.toLRSHom.toShHom).map u ≫ ψ₂) (x' : X')
    [HasDerivedCategory (ModuleCat.{u} (S.presheaf.stalk (f (g' x'))))]
    [HasDerivedCategory (ModuleCat.{u} (X.presheaf.stalk (g' x')))]
    [HasDerivedCategory (ModuleCat.{u} (S'.presheaf.stalk (f' x')))]
    [HasDerivedCategory (ModuleCat.{u} (X'.presheaf.stalk x'))] (n : ℤ)
    (hu' : IsIso ((DerivedCategory.homologyFunctor _ n).map ((derivedStalkFunctor x').map u')))
    (hu : letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
        ((f.stalkMap (g' x')).hom).toAlgebra
      letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
        (baseStalkMap f g f' g' w x').toAlgebra
      IsIso (baseChangeCohomologyOverBaseMap (R := S.presheaf.stalk (f (g' x')))
        (R' := S'.presheaf.stalk (f' x')) _ _ ((derivedStalkFunctor (g' x')).map u) n)) :
    IsIso (baseChangeCohomologyMap f g f' g' w M₁ M₁' ψ₁ x' n) ↔
      IsIso (baseChangeCohomologyMap f g f' g' w M₂ M₂' ψ₂ x' n) := by
  have h1 :=
    (congrArg (fun φ => baseChangeCohomologyMap f g f' g' w M₁ M₂' φ x' n) hcomm).symm.trans
      (baseChangeCohomologyMap_comp f g f' g' w M₁ M₁' M₂' ψ₁ u' x' n)
  have h2 := baseChangeCohomologyMap_comp_source f g f' g' w M₁ M₂ M₂' u ψ₂ x' n
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  have hinj := (ModuleCat.mono_iff_injective (baseChangeCohomologyOverBaseMap
    (R := S.presheaf.stalk (f (g' x'))) (R' := S'.presheaf.stalk (f' x')) _ _
    ((derivedStalkFunctor (g' x')).map u) n)).1 inferInstance
  have hsurj := (ModuleCat.epi_iff_surjective (baseChangeCohomologyOverBaseMap
    (R := S.presheaf.stalk (f (g' x'))) (R' := S'.presheaf.stalk (f' x')) _ _
    ((derivedStalkFunctor (g' x')).map u) n)).1 inferInstance
  have : Mono (baseChangeCohomologyMapHom (R := S.presheaf.stalk (f (g' x')))
      (R' := S'.presheaf.stalk (f' x')) _ _ ((derivedStalkFunctor (g' x')).map u) n) :=
    (ModuleCat.mono_iff_injective _).2 hinj
  have : Epi (baseChangeCohomologyMapHom (R := S.presheaf.stalk (f (g' x')))
      (R' := S'.presheaf.stalk (f' x')) _ _ ((derivedStalkFunctor (g' x')).map u) n) :=
    (ModuleCat.epi_iff_surjective _).2 hsurj
  have : IsIso (baseChangeCohomologyMapHom (R := S.presheaf.stalk (f (g' x')))
      (R' := S'.presheaf.stalk (f' x')) _ _ ((derivedStalkFunctor (g' x')).map u) n) :=
    isIso_of_mono_of_epi _
  exact (isIso_comp_right_iff _ _).symm.trans
    ((congrArg IsIso (h1.symm.trans h2)).to_iff.trans (isIso_comp_left_iff _ _))

/-- **The truncation step for the map of Stacks 0DJ7 at a derived internal hom.** Let
`P ⟶ E ⟶ C ⟶ P[1]` be a distinguished triangle of `D(𝒪_X)` with `C` bounded above by `m`, let
`K ∈ D(𝒪_X)` be bounded below by `a` and `K' ∈ D(𝒪_{X'})` bounded below by `b`, and suppose
the derived base change of stalks at `g' x'` along `𝒪_{S, f(g' x')} ⟶ 𝒪_{S', f' x'}` carries
objects bounded below by `c` to objects with cohomology vanishing below `c + a₀`. Then in every
degree `n` with `n + 1 < a - m + a₀` and `n + 1 < b - m`, the map of Stacks 0DJ7 at the
comparison `L(g')^*R𝓗om(E, K) ⟶ R𝓗om(L(g')^*E, K')` is invertible exactly when the one at
`L(g')^*R𝓗om(P, K) ⟶ R𝓗om(L(g')^*P, K')` is. -/
theorem isIso_baseChangeCohomologyMap_baseChangeSheafHomComparison_iff_of_distTriang
    (T : Triangle (DerivedCategory X.Modules)) (hT : T ∈ distTriang _) (m : ℤ)
    (hC : T.obj₃.IsLE m) (K : DerivedCategory X.Modules) (a : ℤ) (hK : K.IsGE a)
    (K' : DerivedCategory X'.Modules) (b : ℤ) (hK' : K'.IsGE b)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') (x' : X') (a₀ : ℤ)
    (hvan : letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
        ((f.stalkMap (g' x')).hom).toAlgebra
      letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
        (baseStalkMap f g f' g' w x').toAlgebra
      ∀ (N : DerivedCategory X.Modules) (c j : ℤ), N.IsGE c → j < c + a₀ →
        IsZero (baseChangeCohomologyOverBase (R := S.presheaf.stalk (f (g' x')))
          (R' := S'.presheaf.stalk (f' x')) ((derivedStalkFunctor (g' x')).obj N) j))
    (n : ℤ) (hna : n + 1 < a - m + a₀) (hnb : n + 1 < b - m) :
    IsIso (baseChangeCohomologyMap f g f' g' w
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op T.obj₂)).obj K)
        (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj T.obj₂))).obj K')
        (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
          g'.toLRSHom.toShHom T.obj₂ K K' φ) x' n) ↔
      IsIso (baseChangeCohomologyMap f g f' g' w
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op T.obj₁)).obj K)
        (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj T.obj₁))).obj K')
        (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison
          g'.toLRSHom.toShHom T.obj₁ K K' φ) x' n) := by
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  obtain ⟨δ, hδ⟩ := Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first X.sheaf K T hT
  have hGE := Stacks.SheafOfModules.isGE_derivedSheafHom X.sheaf T.obj₃ K m a hC hK
  refine isIso_baseChangeCohomologyMap_iff_of_comm f g f' g' w _ _
    (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).map T.mor₁.op).app K)
    (((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).map
      ((derivedPullback g'.toLRSHom.toShHom).map T.mor₁).op).app K')
    (Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison_naturality_source
      _ T.mor₁ K K' φ).symm x' n ?_ ?_
  · let T₀ : Triangle (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))) := T
    have hT₀ : T₀ ∈ distTriang _ := hT
    exact isIso_homologyMap_derivedStalkFunctor_map_derivedSheafHom_map_mor₁ x'
      ((derivedPullback g'.toLRSHom.toShHom).mapTriangle.obj T₀)
      ((derivedPullback g'.toLRSHom.toShHom).map_distinguished T₀ hT₀) m
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPullback_obj _ T.obj₃ m hC)
      K' b hK' n hnb
  · exact isIso_baseChangeCohomologyOverBaseMap_derivedStalkFunctor_map_mor₂ (g' x') _ hδ n
      (hvan _ (a - m) n hGE (by omega)) (hvan _ (a - m) (n + 1) hGE (by omega))

end Square

end AlgebraicGeometry

end
