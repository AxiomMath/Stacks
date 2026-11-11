module

public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.DerivedCategory.Monoidal.BoundedBelowSubcategory
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTorObj
public import StacksFrontier.Homology.Tor.DerivedFibreBoundedBelow
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedPullbackAmplitude

/-!
# Lower bounds for derived base change along a map with Tor amplitude bounded below

Let `R → R'` be a map of commutative rings such that `R'`, as an object of `D(R)`, has Tor
amplitude in `[a, b]`. Then derived extension of scalars `- ⊗ᴸ_R R'` carries `D^{≥ c}(R)` into
`D^{≥ c + a}(R')`. Represent `R'` by a bounded complex `F` of flat `R`-modules in degrees
`[a, b]` (Stacks 0654) and `M ∈ D^{≥ c}(R)` by a K-flat complex `P` (Stacks 06Y4). Then
`P ⊗ R'` is quasi-isomorphic to `P ⊗ F` because `P` is K-flat, and `P ⊗ F` to
`τ_{≥ c} P ⊗ F` because `F` is K-flat (Stacks 064K); the last complex vanishes below `c + a`.

For a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

in which every local ring `𝒪_{S', s'}` has Tor amplitude in `[a₀, b₀]` over `𝒪_{S, g s'}`, this
gives the vanishing of the source of the map of Stacks 0DJ7 at `(N, x')` in degrees below
`c + a₀` whenever `N ∈ D^{≥ c}(𝒪_X)`. Consequently, if that map is an isomorphism at every point
and in every degree for `(K, K', φ)` with `K ∈ D^{≥ a}(𝒪_X)`, then `K' ∈ D^{≥ a + a₀}(𝒪_{X'})`.

## Main results

* `StacksDraft.TorAmplitude.isGE_tensorObj_of_kFlat`: `P ⊗ F` lies in degrees `≥ c + a` when `P`
  has cohomology in degrees `≥ c` and `F` is K-flat and vanishes below `a`.
* `CochainComplex.DerivedExtensionScalars`, the theorem
  `isGE_totalDerivedExtensionScalars_obj_of_hasTorAmplitudeCanonical`: derived extension of
  scalars along `R → R'` with `R'` of Tor amplitude `[a, b]` carries `D^{≥ c}(R)` into
  `D^{≥ c + a}(R')`.
* `RingTheory.TorIndependence.isZero_baseChangeCohomologyOverBase_of_hasTorAmplitudeCanonical`:
  the ring-level vanishing of `H^j(N ⊗ᴸ_R R')` for `N ∈ D^{≥ c}(A)` and `j < c + a`.
* `AlgebraicGeometry.hasTorAmplitudeCanonical_baseStalkMap`: the Tor amplitude of
  `𝒪_{S', s'}` over `𝒪_{S, g s'}` read over `𝒪_{S, f (g' x')}` along `baseStalkMap`.
* `AlgebraicGeometry.isZero_baseChangeCohomologyOverBase_of_isGE`: the vanishing at a point.
* `AlgebraicGeometry.isGE_of_isIso_baseChangeCohomologyMap`: the lower bound for `K'`.

## References

* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.TorAmplitude

variable {R : Type u} [CommRing R]

/-- If `P` has cohomology in degrees `≥ c` and `F` is a K-flat complex vanishing below `a`, then
the total tensor product `P ⊗ F` has cohomology in degrees `≥ c + a`: tensoring the
quasi-isomorphism `P ⟶ τ_{≥ c} P` with the K-flat `F` is a quasi-isomorphism, and
`τ_{≥ c} P ⊗ F` vanishes below `c + a`. -/
theorem isGE_tensorObj_of_kFlat (P F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : F.KFlat)
    (c a : ℤ) [P.IsGE c] [F.IsStrictlyGE a] : (P ⊗ F).IsGE (c + a) := by
  have : QuasiIso ((tensorRight F).map (P.πTruncGE c)) := quasiIso_tensorRight_map hF _
  have h : (P.truncGE c ⊗ F).IsStrictlyGE (c + a) :=
    CochainComplex.KFlatMonoidal.isStrictlyGE_tensorObj _ _ _ c a
  have h' : (P.truncGE c ⊗ F).IsGE (c + a) := inferInstance
  rw [← DerivedCategory.isGE_Q_obj_iff] at h' ⊢
  have : (DerivedCategory.Q.obj ((tensorRight F).obj (P.truncGE c))).IsGE (c + a) := h'
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (asIso (DerivedCategory.Q.map ((tensorRight F).map (P.πTruncGE c)))).symm _

/-- If the `R`-module `N` has Tor amplitude in `[a, b]` and `P` is a K-flat complex with
cohomology in degrees `≥ c`, then termwise tensoring `P` by `N` has cohomology in degrees
`≥ c + a`. -/
theorem isGE_tensorModuleRight_of_hasTorAmplitudeCanonical (N : ModuleCat.{u} R) (a b : ℤ)
    (hN : HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)) a b)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (c : ℤ) [P.IsGE c] :
    CochainComplex.IsGE
      (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) (c + a) := by
  obtain ⟨F, hflat, hGE, hLE, ⟨e⟩⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R _ a b).1 hN
  have hF : F.KFlat := CochainComplex.KFlat.kFlat_of_flat F b
  have hinv : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).IsInvertedBy
      (tensorLeft P ⋙ DerivedCategory.Q) := by
    intro X Y f hf
    have : QuasiIso f := hf
    have : QuasiIso ((tensorLeft P).map f) := quasiIso_tensorLeft_map P hP f
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((tensorLeft P).map f)))
  let L := Localization.lift (tensorLeft P ⋙ DerivedCategory.Q) hinv DerivedCategory.Q
  let fac : DerivedCategory.Q ⋙ L ≅ tensorLeft P ⋙ DerivedCategory.Q :=
    Localization.fac _ hinv DerivedCategory.Q
  have h := isGE_tensorObj_of_kFlat P F hF c a
  rw [← DerivedCategory.isGE_Q_obj_iff] at h ⊢
  have : ((tensorLeft P ⋙ DerivedCategory.Q).obj F).IsGE (c + a) := h
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((fac.app F).symm ≪≫ L.mapIso e.symm ≪≫ fac.app _ ≪≫
      DerivedCategory.Q.mapIso ((termwiseTensorSingleIso N).app P).symm) _

end StacksDraft.TorAmplitude

namespace CochainComplex.DerivedExtensionScalars

open StacksDraft.TorAmplitude

/-- **Derived extension of scalars along a map with Tor amplitude bounded below.** If `R'` has
Tor amplitude in `[a, b]` as an object of `D(R)`, then `- ⊗ᴸ_R R'` carries `D^{≥ c}(R)` into
`D^{≥ c + a}(R')`. -/
theorem isGE_totalDerivedExtensionScalars_obj_of_hasTorAmplitudeCanonical
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R'] (a b : ℤ)
    (hR' : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R'))) a b)
    (M : DerivedCategory (ModuleCat.{u} R)) (c : ℤ) (hM : M.IsGE c) :
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj M).IsGE (c + a) := by
  let f := algebraMap R R'
  let T := totalDerivedExtensionScalars.{u, u, u} f
  obtain ⟨P, hP, ⟨eP⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative M
  have : P.IsGE c := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso eP.symm c
  let N₀ := RingTheory.TorIndependence.baseModule R R'
  have hR'' : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N₀)) a b := by
    rw [hasTorAmplitudeCanonical_iff_hasFlatRepresentative] at hR' ⊢
    exact hasFlatRepresentative_of_iso (DerivedCategory.Q.mapIso
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (RingTheory.TorIndependence.baseModuleIso (R := R) (R' := R')).symm)) hR'
  have h1 := isGE_tensorModuleRight_of_hasTorAmplitudeCanonical N₀ a b hR'' P hP c
  let E := ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let α : ModuleCat.extendScalars.{u, u, u} f ⋙ ModuleCat.restrictScalars.{u, u, u} f ≅
      tensorModuleRight N₀ :=
    RingTheory.TorIndependence.extendRestrictIsoTensorLeft ≪≫
      BraidedCategory.tensorLeftIsoTensorRight N₀ ≪≫
        NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  let iso : ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ≅
      ((tensorModuleRight N₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P :=
    (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)).app P
  rw [← DerivedCategory.isGE_Q_obj_iff] at h1
  have h3 : ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
      (DerivedCategory.Q.obj E)).IsGE (c + a) :=
    DerivedCategory.TStructure.t.isGE_of_iso (DerivedCategory.Q.mapIso iso.symm ≪≫
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.app E).symm) _
  have h4 : (DerivedCategory.Q.obj E).IsGE (c + a) :=
    (isGE_restrictScalars_mapDerivedCategory_obj_iff f _ _).1 h3
  have : IsIso (T.comparison.app P) := T.comparison_isIso_of_kFlat P hP
  have : ((extensionOfScalarsComplexGeneral.{u, u, u} f).obj P).IsGE (c + a) := h4
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((asIso (T.comparison.app P)).symm ≪≫ T.functor.mapIso eP) _

/-- The form of `isGE_totalDerivedExtensionScalars_obj_of_hasTorAmplitudeCanonical` used for
base change: for an `R`-algebra `A` and `N ∈ D^{≥ c}(A)`, the derived base change of `N`, read
over `R`, to `R'` lies in `D^{≥ c + a}(R')`. -/
theorem isGE_totalDerivedExtensionScalars_restrictScalars_of_hasTorAmplitudeCanonical
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    (a b : ℤ)
    (hR' : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R'))) a b)
    (N : DerivedCategory (ModuleCat.{u} A)) (c : ℤ) (hN : N.IsGE c) :
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N)).IsGE (c + a) :=
  isGE_totalDerivedExtensionScalars_obj_of_hasTorAmplitudeCanonical a b hR' _ c
    ((isGE_restrictScalars_mapDerivedCategory_obj_iff (algebraMap R A) N c).2 hN)

end CochainComplex.DerivedExtensionScalars

namespace RingTheory.TorIndependence

open StacksDraft.TorAmplitude CochainComplex.DerivedExtensionScalars

/-- If `R'` has Tor amplitude in `[a, b]` over `R` and `N ∈ D^{≥ c}(A)`, then the cohomology
`H^j(N ⊗ᴸ_R R')` vanishes for `j < c + a`. -/
theorem isZero_baseChangeCohomologyOverBase_of_hasTorAmplitudeCanonical
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    (a b : ℤ)
    (hR' : HasTorAmplitudeCanonical R (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R'))) a b)
    (N : DerivedCategory (ModuleCat.{u} A)) (c j : ℤ) (hN : N.IsGE c) (hj : j < c + a) :
    IsZero (baseChangeCohomologyOverBase (R := R) (R' := R') N j) :=
  (DerivedCategory.isGE_iff _ (c + a)).1
    (isGE_totalDerivedExtensionScalars_restrictScalars_of_hasTorAmplitudeCanonical
      a b hR' N c hN) j hj

end RingTheory.TorIndependence

namespace AlgebraicGeometry

open StacksDraft.TorAmplitude RingTheory.TorIndependence

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- Tor amplitude of `𝒪_{S', s'}` over `𝒪_{S, g s'}` transports to the stalk at any point equal
to `g s'`, along the specialization isomorphism of stalks. -/
private theorem hasTorAmplitudeCanonical_stalkCongr_comp (a b : ℤ) (s' : S')
    (hg : letI := (g.stalkMap s').hom.toAlgebra
      HasTorAmplitudeCanonical (S.presheaf.stalk (g s'))
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (ModuleCat.{u} (S.presheaf.stalk (g s'))) 0).obj
            (ModuleCat.of (S.presheaf.stalk (g s')) (S'.presheaf.stalk s')))) a b)
    (p : S) (h : p = g s') :
    letI := ((S.presheaf.stalkCongr (.of_eq h)).hom ≫ g.stalkMap s').hom.toAlgebra
    HasTorAmplitudeCanonical (S.presheaf.stalk p)
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (ModuleCat.{u} (S.presheaf.stalk p)) 0).obj
          (ModuleCat.of (S.presheaf.stalk p) (S'.presheaf.stalk s')))) a b := by
  subst h
  have e : (S.presheaf.stalkCongr (.of_eq (rfl : g s' = g s'))).hom ≫ g.stalkMap s' =
      g.stalkMap s' := by
    rw [show (S.presheaf.stalkCongr (.of_eq (rfl : g s' = g s'))).hom = 𝟙 _ from
      S.presheaf.stalkSpecializes_refl _, Category.id_comp]
  rw [e]
  exact hg

/-- If every local ring `𝒪_{S', s'}` has Tor amplitude in `[a, b]` over `𝒪_{S, g s'}`, then at
every point `x'` of `X'` the local ring `𝒪_{S', f' x'}` has Tor amplitude in `[a, b]` over
`𝒪_{S, f (g' x')}` along `baseStalkMap`. -/
theorem hasTorAmplitudeCanonical_baseStalkMap (a b : ℤ)
    (hg : ∀ s' : S',
      letI := (g.stalkMap s').hom.toAlgebra
      HasTorAmplitudeCanonical (S.presheaf.stalk (g s'))
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (ModuleCat.{u} (S.presheaf.stalk (g s'))) 0).obj
            (ModuleCat.of (S.presheaf.stalk (g s')) (S'.presheaf.stalk s')))) a b)
    (x' : X') :
    letI := (baseStalkMap f g f' g' w x').toAlgebra
    HasTorAmplitudeCanonical (S.presheaf.stalk (f (g' x')))
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
        (ModuleCat.{u} (S.presheaf.stalk (f (g' x')))) 0).obj
          (ModuleCat.of (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))))) a b :=
  hasTorAmplitudeCanonical_stalkCongr_comp g a b (f' x') (hg (f' x')) _
    (congrArg (fun h : X' ⟶ S ↦ h x') w)

/-- If every local ring `𝒪_{S', s'}` has Tor amplitude in `[a, b]` over `𝒪_{S, g s'}` and
`N ∈ D^{≥ c}(𝒪_X)`, then at every point `x'` of `X'` the cohomology
`H^j(N_{g' x'} ⊗ᴸ_{𝒪_{S, f (g' x')}} 𝒪_{S', f' x'})` vanishes for `j < c + a`. -/
theorem isZero_baseChangeCohomologyOverBase_of_isGE (a b : ℤ)
    (hg : ∀ s' : S',
      letI := (g.stalkMap s').hom.toAlgebra
      HasTorAmplitudeCanonical (S.presheaf.stalk (g s'))
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (ModuleCat.{u} (S.presheaf.stalk (g s'))) 0).obj
            (ModuleCat.of (S.presheaf.stalk (g s')) (S'.presheaf.stalk s')))) a b)
    (x' : X') (N : DerivedCategory X.Modules) (c j : ℤ) (hN : N.IsGE c) (hj : j < c + a) :
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
      ((f.stalkMap (g' x')).hom).toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      (baseStalkMap f g f' g' w x').toAlgebra
    IsZero (baseChangeCohomologyOverBase (R := S.presheaf.stalk (f (g' x')))
      (R' := S'.presheaf.stalk (f' x')) ((derivedStalkFunctor (g' x')).obj N) j) :=
  letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  isZero_baseChangeCohomologyOverBase_of_hasTorAmplitudeCanonical a b
    (hasTorAmplitudeCanonical_baseStalkMap f g f' g' w a b hg x') _ c j
    (DerivedPullbackAmplitude.isGE_derivedStalkFunctor N c hN (g' x')) hj

/-- **The lower bound of the target of a pointwise base-change isomorphism.** If every local
ring `𝒪_{S', s'}` has Tor amplitude in `[a₀, b₀]` over `𝒪_{S, g s'}`, `K ∈ D^{≥ a}(𝒪_X)`, and the
map of Stacks 0DJ7 at `(K, K', φ)` is an isomorphism at every point and in every degree, then
`K' ∈ D^{≥ a + a₀}(𝒪_{X'})`: in each degree below `a + a₀` the source of the map vanishes at
every point, so every derived stalk of `K'` does. -/
theorem isGE_of_isIso_baseChangeCohomologyMap (a₀ b₀ : ℤ)
    (hg : ∀ s' : S',
      letI := (g.stalkMap s').hom.toAlgebra
      HasTorAmplitudeCanonical (S.presheaf.stalk (g s'))
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (ModuleCat.{u} (S.presheaf.stalk (g s'))) 0).obj
            (ModuleCat.of (S.presheaf.stalk (g s')) (S'.presheaf.stalk s')))) a₀ b₀)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n))
    (a : ℤ) (hK : K.IsGE a) : K'.IsGE (a + a₀) := by
  refine DerivedPullbackAmplitude.isGE_of_forall_derivedStalkFunctor K' _ fun x' => ?_
  rw [DerivedCategory.isGE_iff]
  intro j hj
  refine IsZero.of_iso ?_ (asIso (baseChangeCohomologyMap f g f' g' w K K' φ x' j)).symm
  refine Functor.map_isZero _ ?_
  have h0 := isZero_baseChangeCohomologyOverBase_of_isGE f g f' g' w a₀ b₀ hg x' K a j hK hj
  rw [ModuleCat.isZero_iff_subsingleton] at h0 ⊢
  exact h0

end AlgebraicGeometry
