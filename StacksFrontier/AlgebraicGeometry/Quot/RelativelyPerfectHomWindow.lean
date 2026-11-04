module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseAcyclic
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorStalkwise
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StalkRelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.PseudoCoherentHomComparison
public import StacksFrontier.CategoryTheory.Sites.Point.StalkKFlatColimit
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent

/-!
# The window of the proof of Stacks 0DKY

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces with `Y`
quasi-compact, and let `E` be a `Y`-perfect object of `D(𝒪_X)`.  This file proves
`AlgebraicGeometry.Space.RelativelyPerfectHomWindow`: there is an integer `a` such that, for every
cartesian square `X' = X ×_Y Y'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`, and every
morphism `φ : A ⟶ A'` of perfect objects of `D(𝒪_X)` which is an isomorphism on cohomology in
degrees `≥ k`, the map
`Rf'_* R𝓗om(L(g')^*A', L(g')^*E) ⟶ Rf'_* R𝓗om(L(g')^*A, L(g')^*E)`
is an isomorphism on cohomology in degrees `≤ a - k`.

The proof is the source's.  `X` is quasi-compact, so `E` has Tor amplitude in one interval
`[a₀, b₀]` over `f⁻¹𝒪_Y` at all of its geometric stalks
(`AlgebraicGeometry.Space.exists_stalkBound_of_locallyHasFiniteTorDimension`).  Stacks 0DKD, read
at the stalks, carries that bound to `L(g')^*E` over `f'⁻¹𝒪_{Y'}` for every cartesian square, so
`L(g')^*E` has no cohomology below `a₀`, uniformly in the square.  The cone `C` of `φ` has no
cohomology in degrees `≥ k`; `L(g')^*` is right t-exact, `R𝓗om(D^{≤ k-1}, D^{≥ a₀})` lies in
`D^{≥ a₀-k+1}` and `Rf'_*` is left t-exact, so the long exact cohomology sequence of the image of
the triangle of `φ` gives the window with `a = a₀ - 1`.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_stalk_pullbackModules_of_cartesian`: Stacks 0DKD (1)
  at a geometric stalk, read as a lower bound on cohomology.
* `AlgebraicGeometry.Space.exists_isGE_pull_of_isPerfectRelativeToCanonical`: the uniform lower
  bound on the cohomology of `L(g')^*E`, Stacks 0DKD at the geometric stalks.
* `AlgebraicGeometry.Space.exists_distinguished_smallEtaleDerivedSheafHom`: Stacks 08JC in the
  contravariant variable on an algebraic space.
* `AlgebraicGeometry.Space.isGE_smallEtaleDerivedSheafHom_of_isLE_of_isGE`:
  `R𝓗om(D^{≤ m}, D^{≥ n}) ⊆ D^{≥ n - m}` on an algebraic space.
* `AlgebraicGeometry.Space.relativelyPerfectHomWindow`: the window, as stated in
  `AlgebraicGeometry.Space.RelativelyPerfectHomWindow`.

## Implementation notes

*The cartesian input of Stacks 0DKD.*  Read at the étale local rings, the cartesian input of
Stacks 0DKD is `AlgebraicGeometry.Space.IsEtaleStalkTensorFlat`, which holds at every geometric
point of every cartesian square (`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat`).
The argument below reads the stalks at the points of the small étale sites rather than at the
étale local rings, where the
same transfer is `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_structureStalk_of_cartesian`,
whose flatness input `AlgebraicGeometry.Space.cartesian_stalkRing_tensor_flat` is proved, so
nothing is carried.  The derived pullback along `g'` is computed on a K-flat representative of
`E` whose stalks are K-flat, as in
`AlgebraicGeometry.Space.ComplexesSituation.locallyHasFiniteTorDimension_pull`.

*The derived internal Hom.*  `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom` is the derived
internal Hom of the equi-universe model of the small étale site read through the derived
equivalence `AlgebraicGeometry.Space.smallEtaleModelDerivedEquivalence`, whose two functors are
`CategoryTheory.Functor.mapDerivedCategory` of an equivalence of abelian categories; both the
triangle and the bound are therefore those of the model, transported along exact functors.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open StacksDraft.TorAmplitude

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The derived internal Hom on an algebraic space -/

section SheafHom

-- The standard model is forced: `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom` is defined at
-- it, and at plain priority the derived category of the modules of the equi-universe model is
-- found at another model, so that the internal Hom of the model does not typecheck against it.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (X : AlgebraicSpaces B S hS)

/-- **Stacks 08JC in the contravariant variable, on an algebraic space.**  For a distinguished
triangle `T` of `D(𝒪_X)` and an object `E`, the two morphisms
`R𝓗om(T₃, E) ⟶ R𝓗om(T₂, E) ⟶ R𝓗om(T₁, E)` extend to a distinguished triangle.

This is `AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom` on the equi-universe
model, transported along the two exact functors of the derived equivalence with the model. -/
theorem exists_distinguished_smallEtaleDerivedSheafHom
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (T : Triangle (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))))
    (hT : T ∈ distTriang
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))) :
    ∃ δ : ((smallEtaleDerivedSheafHom B S hS X).flip.obj E).obj (op T.obj₁) ⟶
        (((smallEtaleDerivedSheafHom B S hS X).flip.obj E).obj (op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk (((smallEtaleDerivedSheafHom B S hS X).flip.obj E).map T.mor₂.op)
        (((smallEtaleDerivedSheafHom B S hS X).flip.obj E).map T.mor₁.op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) := by
  let F := (smallEtaleModelModulesEquivalence B S hS X).functor.mapDerivedCategory
  let G := (smallEtaleModelModulesEquivalence B S hS X).inverse.mapDerivedCategory
  obtain ⟨δ₀, h₀⟩ := RingedSite.exists_distinguished_derivedSheafHom
    (smallEtaleModelRingedSite B S hS X.1 X.2) (F.obj E) (F.mapTriangle.obj T)
    (F.map_distinguished T hT)
  exact ⟨G.map δ₀ ≫ (G.commShiftIso (1 : ℤ)).hom.app _, G.map_distinguished _ h₀⟩

/-- **The derived internal Hom of a bounded-above object into a bounded-below one, on an
algebraic space.**  If `P` has no cohomology above degree `m` and `Q` none below degree `n`, then
`R𝓗om(P, Q)` has none below degree `n - m`. -/
theorem isGE_smallEtaleDerivedSheafHom_of_isLE_of_isGE
    (P Q : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (m n : ℤ) (hP : P.IsLE m) (hQ : Q.IsGE n) :
    (((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj Q).IsGE (n - m) := by
  let Φ := smallEtaleModelModulesEquivalence B S hS X
  rw [smallEtaleDerivedSheafHom_obj_obj]
  exact Φ.inverse.isGE_mapDerivedCategory_obj _ (n - m)
    (RingedSite.isGE_derivedSheafHom (smallEtaleModelRingedSite B S hS X.1 X.2) _ _ m n
      (Φ.functor.isLE_mapDerivedCategory_obj P m hP)
      (Φ.functor.isGE_mapDerivedCategory_obj Q n hQ))

end SheafHom

/-! ### A uniform lower bound for the pullbacks of a relatively perfect object -/

section Pullback

-- The standard model is forced: `HasTorAmplitudeCanonical`,
-- `AlgebraicGeometry.Space.exists_stalkBound_of_locallyHasFiniteTorDimension` and
-- `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_scalarRestriction_stalk_iff` are stated only
-- for it, and at plain priority the derived categories of the stalk rings are found at another
-- model, so that the derived stalks of those statements do not match.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

/-- Tor amplitude in `[a, b]` at the canonical derived tensor product of a ring bounds the
cohomology of the object below by `a`: a flat representative concentrated in `[a, b]`
(Stacks 0654) has no terms below `a`. -/
theorem isGE_of_hasTorAmplitudeCanonical {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) (h : HasTorAmplitudeCanonical R K a b) :
    K.IsGE a := by
  obtain ⟨L, -, hGE, -, ⟨e⟩⟩ := (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).1 h
  have := hGE
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a

variable {X Y : AlgebraicSpaces B S hS}

/-- **The relative Tor amplitude of a stalk of a representative.**  If the geometric stalk of `E`
at `x̄`, read over the stalk of `f⁻¹𝒪_Y`, has Tor amplitude in `[a, b]`, then so has the stalk at
`x̄` of any complex `K` representing `E`, read over `𝒪_{Y, f(x̄)}` through the stalk map
`𝒪_{Y, f(x̄)} ⟶ 𝒪_{X, x̄}`.  This is the change of spelling between
`AlgebraicGeometry.Space.exists_stalkBound_of_locallyHasFiniteTorDimension` and
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_structureStalk_of_cartesian`. -/
theorem hasTorAmplitudeCanonical_structureStalk_of_stalkBound (f : X ⟶ Y)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (eK : DerivedCategory.Q.obj K ≅ E)
    (x : GeometricPoint B S hS X.1) (a b : ℤ)
    (h : HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj)
      ((ModuleCat.restrictScalars.{u} (inverseImageStalkRingHom B S hS f x)).mapDerivedCategory.obj
        ((geometricStalkFunctor B S hS x).mapDerivedCategory.obj E)) a b) :
    HasTorAmplitudeCanonical (structureStalkRing B S hS Y (geometricPointMap f.hom x))
      ((ModuleCat.restrictScalars.{u}
          (smallEtaleStalkPullbackRingMap B S hS f x)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))) a b := by
  have h₁ : HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
      a b :=
    AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (Iso.refl _ ≪≫ derivedScalarRestrictionStalkIso B S hS f x E).symm a b h
  let eS : (derivedScalarRestriction B S hS f).obj E ≅
      DerivedCategory.Q.obj
        (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    (derivedScalarRestriction B S hS f).mapIso eK.symm ≪≫
      (derivedScalarRestrictionFactors B S hS f).app K
  have h₂ := (hasTorAmplitudeCanonical_iff_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).mapIso eS ≪≫
      (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).mapDerivedCategoryFactors.app _) a b).1 h₁
  have h₃ := (hasTorAmplitudeCanonical_scalarRestriction_stalk_iff B S hS f x K a b).1 h₂
  exact (hasTorAmplitudeCanonical_iff_of_iso
    ((ModuleCat.restrictScalars.{u}
      (smallEtaleStalkPullbackRingMap B S hS f x)).mapDerivedCategoryFactors.app _) a b).2 h₃

/-- A complex represents an object that is `≥ a` iff its homology vanishes below degree `a`. -/
private theorem isGE_Q_obj_iff_isZero_homology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : CochainComplex C ℤ) (a : ℤ) :
    (DerivedCategory.Q.obj K).IsGE a ↔ ∀ i < a, IsZero (K.homology i) := by
  simp only [DerivedCategory.isGE_Q_obj_iff, CochainComplex.isGE_iff,
    HomologicalComplex.exactAt_iff_isZero_homology]

/-- **Stacks 0DKD (1) at a geometric stalk, read as a degree bound.**  In a cartesian square with
`f` flat, let `K` be a complex of `𝒪_X`-modules whose stalk at `g'(x̄')` is K-flat and has Tor
amplitude in `[a, b]` over `𝒪_{Y, f(g'(x̄'))}`.  Then the stalk at `x̄'` of the degreewise pullback
of `K` along `g'` has no cohomology below `a`. -/
theorem isZero_homology_stalk_pullbackModules_of_cartesian {X' Y' : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g)
    (hflat : IsFlat B S hS f.hom) (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (x' : GeometricPoint B S hS X'.1)
    (hK : CochainComplex.KFlat.{u, u}
      (((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (a b : ℤ)
    (hamp : HasTorAmplitudeCanonical
      (structureStalkRing B S hS Y (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ((ModuleCat.restrictScalars.{u} (smallEtaleStalkPullbackRingMap B S hS f
          (geometricPointMap g'.hom x'))).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          (((Stacks.sheafModuleFiberOfCommRing
            (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
            (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K))) a b)
    (i : ℤ) (hi : i < a) :
    IsZero ((((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X'.1 x' X'.2)
      (smallEtaleRingedTopos B S hS X').O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((((smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)).homology i) := by
  let C := ((ModuleCat.extendScalars
      (smallEtaleStalkPullbackRingMap B S hS g' x')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let ρ := ModuleCat.restrictScalars.{u} (smallEtaleStalkPullbackRingMap B S hS f' x')
  have hGE := isGE_of_hasTorAmplitudeCanonical _ a b
    (hasTorAmplitudeCanonical_structureStalk_of_cartesian B S hS g' f' f g hpb hflat x' _ hK a b
      hamp)
  have hρ : IsZero (((ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C).homology i) :=
    (isGE_Q_obj_iff_isZero_homology _ a).1 hGE i hi
  have hC : IsZero (C.homology i) := by
    have h' : IsZero (ρ.obj (C.homology i)) := hρ.of_iso ((C.sc i).mapHomologyIso ρ).symm
    rwa [ModuleCat.isZero_iff_subsingleton] at h' ⊢
  exact hC.of_iso (HomologicalComplex.homologyMapIso
    (pullbackModulesStalkComplexIso B S hS g' x' K) i)

/-- A complex of `𝒪_X`-modules on an algebraic space whose stalk complexes at all geometric points
have no cohomology in degree `i` has no cohomology in degree `i`: the geometric points are a
conservative family (Stacks 04K5) and the stalk functors are exact. -/
theorem isZero_homology_of_forall_isZero_homology_stalk
    (P : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (i : ℤ)
    (h : ∀ x : GeometricPoint B S hS X.1,
      IsZero ((((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          P).homology i)) :
    IsZero (P.homology i) := by
  have := smallEtaleRingedSite_hasSheafify_addCommGrpCat B S hS X
  have := smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat B S hS X
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  refine (Stacks.exactAt_iff_forall_exactAt_mapSheafModuleFiberOfCommRing
    (smallEtaleRingedTopos B S hS X).O P
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2) i).2 ?_
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (h x)

/-- **The pullbacks of a relatively perfect object are bounded below, uniformly in the square**
(Stacks 0DKD (1), read at the stalks).  Let `f : X ⟶ Y` be flat and locally of finite
presentation with `X` quasi-compact, and let `E` be `Y`-perfect.  Then there is an integer `a`
such that for every cartesian square `X' = X ×_Y Y'` with projection `g' : X' ⟶ X`, the derived
pullback `L(g')^*E` has no cohomology below degree `a`.

`E` has Tor amplitude in one interval `[a, b]` over `f⁻¹𝒪_Y` at all its geometric stalks
(`AlgebraicGeometry.Space.exists_stalkBound_of_locallyHasFiniteTorDimension`).  `E` is represented
by a K-flat complex `K` with K-flat stalks (Stacks 06YS), on which `L(g')^*` is the degreewise
pullback (Stacks 06YY); at a geometric point `x̄'` of `X'` the stalk of that pullback is the
extension of scalars of the stalk of `K` at `g'(x̄')` (Stacks 05V5), which has Tor amplitude in
`[a, b]` over `𝒪_{Y', f'(x̄')}`
(`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_structureStalk_of_cartesian`), hence no
cohomology below `a`. -/
theorem exists_isGE_pull_of_isPerfectRelativeToCanonical
    (f : X ⟶ Y) (hX : IsQuasiCompactSpace B S hS X.1) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hlfp E) :
    ∃ a : ℤ, ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
      IsPullback g' f' f g → ((smallEtaleDerivedModulePullback B S hS g').obj E).IsGE a := by
  obtain ⟨a, b, hab⟩ := exists_stalkBound_of_locallyHasFiniteTorDimension B S hS f hX
    (canonicalSliceDerivedTensorProduct B S hS f) E hE.2
  refine ⟨a, fun {X' Y'} g' f' g hpb => ?_⟩
  -- a K-flat representative of `E` which is a sequential colimit of bounded above flat complexes
  let K₀ : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ := DerivedCategory.Q.objPreimage E
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize
    (smallEtaleRingedTopos B S hS X).O
  obtain ⟨Dn, α, hLE, hflatD, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize
      (smallEtaleRingedTopos B S hS X).O K₀
  have hDn : HasColimit Dn := inferInstance
  let K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ := (Arrow.mk α).left
  let α' : K ⟶ K₀ := α
  have hQα : IsIso (DerivedCategory.Q.map α') := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  let eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map α') ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize
    (smallEtaleRingedTopos B S hS X).O
  have hKflat : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
      _ Dn hLE hflatD,
      Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize _ Dn hflatD⟩
  have hDn' : HasColimit (show ℕ ⥤ CochainComplex (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u}
        (smallEtaleRingedTopos B S hS X).O)) ℤ from Dn) := hDn
  have hstalk : ∀ x, CochainComplex.KFlat.{u, u}
      (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := fun x =>
    Stacks.kFlat_mapHomologicalComplex_sheafModuleFiber_colimit
      (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O _ hLE hflatD
  -- the pullback, computed on `K`, and the bound at its stalks
  let P : CochainComplex (Modules.{u, u} B S hS X'.1 X'.2) ℤ :=
    (((smallEtaleRingedToposHom B S hS g').toModulesHom.pullbackModules).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  let e₂ : (smallEtaleDerivedModulePullback B S hS g').obj E ≅ DerivedCategory.Q.obj P :=
    (smallEtaleDerivedModulePullback B S hS g').mapIso eK.symm ≪≫
      derivedPullbackObjIsoOfIsKFlat B S hS g' K hKflat
  have : (DerivedCategory.Q.obj P).IsGE a :=
    (isGE_Q_obj_iff_isZero_homology P a).2 fun i hi =>
      isZero_homology_of_forall_isZero_homology_stalk B S hS P i fun x' =>
        isZero_homology_stalk_pullbackModules_of_cartesian B S hS g' f' f g hpb hflat K x'
          (hstalk _) a b
          (hasTorAmplitudeCanonical_structureStalk_of_stalkBound B S hS f E K eK _ a b (hab _))
          i hi
  exact @Triangulated.TStructure.isGE_of_iso _ _ _ _ _ _ _ _ _ _ e₂.symm a this

end Pullback

/-! ### The window -/

section Window

-- The derived categories of the statement are all at the standard model; nothing else is pinned.
attribute [local instance] HasDerivedCategory.standard

/-- **The window of the proof of Stacks 0DKY** (step 3).  For a proper, flat, finitely presented
`f : X ⟶ Y` with `Y` quasi-compact and quasi-separated and a `Y`-perfect `E`, there is an integer
`a` such that after every cartesian base change `X' = X ×_Y Y'`, every morphism `φ : A ⟶ A'` of
perfect objects of `D(𝒪_X)` which is an isomorphism on cohomology in degrees `≥ k` induces a map
`Rf'_* R𝓗om(L(g')^*A', L(g')^*E) ⟶ Rf'_* R𝓗om(L(g')^*A, L(g')^*E)` which is an isomorphism on
cohomology in degrees `≤ a - k`.

`L(g')^*E` has no cohomology below some `a₀` independent of the square
(`AlgebraicGeometry.Space.exists_isGE_pull_of_isPerfectRelativeToCanonical`).  The cone `C` of
`φ` has no cohomology in degrees `≥ k`, nor has `L(g')^*C` (`L(g')^*` is right t-exact), so
`Rf'_* R𝓗om(L(g')^*C, L(g')^*E)` has none below `a₀ - k + 1`; it is the first vertex of the
image under `Rf'_* R𝓗om(-, L(g')^*E)` of the pulled back triangle of `φ`, whose second morphism
is the map of the statement.  The window is `a = a₀ - 1`. -/
theorem relativelyPerfectHomWindow : RelativelyPerfectHomWindow B S hS := by
  intro _ X Y f hYqc _ _ hflat hfp E hE
  obtain ⟨a₀, ha₀⟩ := exists_isGE_pull_of_isPerfectRelativeToCanonical B S hS f
    (isQuasiCompactSpace_of_isFinitePresentation B S hS f.hom Y.2 hYqc hfp) hflat hfp.1 E hE
  refine ⟨a₀ - 1, fun {X' Y'} g' f' g hpb {A A'} φ _ _ k hk i hi => ?_⟩
  obtain ⟨C, ψ, χ, hT⟩ := distinguished_cocone_triangle φ
  have hC : C.IsLE (k - 1) :=
    DerivedCategory.isLE_three_of_homologyMap_mor₁ (Triangle.mk φ ψ χ) hT k
      (fun i hi => hk i hi.le) (@IsIso.epi_of_iso _ _ _ _ _ (hk k le_rfl))
  let L := smallEtaleDerivedModulePullback B S hS g'
  have hLC : (L.obj C).IsLE (k - 1) := isLE_smallEtaleDerivedModulePullback_obj g' C (k - 1) hC
  obtain ⟨δ, hδ⟩ := exists_distinguished_smallEtaleDerivedSheafHom B S hS X' (L.obj E)
    (L.mapTriangle.obj (Triangle.mk φ ψ χ)) (L.map_distinguished _ hT)
  have hGE : ((spaceDerivedPushforward B S hS f').obj
      (((smallEtaleDerivedSheafHom B S hS X').obj (op (L.obj C))).obj (L.obj E))).IsGE
        (a₀ - (k - 1)) :=
    isGE_spaceDerivedPushforward_obj B S hS f' _ _
      (isGE_smallEtaleDerivedSheafHom_of_isLE_of_isGE B S hS X' (L.obj C) (L.obj E) (k - 1) a₀ hLC
        (ha₀ g' f' g hpb))
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isGE₁ _
    ((spaceDerivedPushforward B S hS f').map_distinguished _ hδ) i (a₀ - (k - 1)) hGE (by omega)

end Window

end AlgebraicGeometry.Space

end
