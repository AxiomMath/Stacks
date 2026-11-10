module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPushforwardTraceProper
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedPullbackBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceGeneral

/-!
# Stacks 0E5I: the base change map of the right adjoint of `Rf_*` over an affine base

For a cartesian square of quasi-compact and quasi-separated algebraic spaces

```
X' --g'--> X
|f'        |f
Y' --g---> Y
```

with `X` and `Y'` Tor independent over `Y` and `g` affine, the base change map
`α_K : L(g')^* a(K) ⟶ a'(Lg^* K)` of Stacks 0E5D is an isomorphism as soon as, for one perfect
generator `M` of `D_QCoh(𝒪_X)`, the trace maps of Stacks 0E57 at `(M, K)` and at
`(L(g')^*M, Lg^*K)` and the map `Lg^*R𝓗om(Rf_*M, K) ⟶ R𝓗om(Lg^*Rf_*M, Lg^*K)` of Stacks 08JF are
isomorphisms: then `Rf'_*R𝓗om(L(g')^*M, α_K)` is an isomorphism
(`AlgebraicGeometry.Space.smallEtalePushforwardTrace_baseChange`), so `α_K` induces bijections on
morphisms out of the shifts of the generator `L(g')^*M` of `D_QCoh(𝒪_{X'})` (Stacks 0E4R).

## Main results

* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isIso`:
  the reduction to a perfect generator.
* `isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isPerfect_pushforward`:
  the case where `Rf_*` preserves perfect objects.
* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isFlat`:
  case (1) of Stacks 0E5I, `f` proper and flat of finite presentation.
* `isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_hasFiniteTorDimensionRingHom`:
  case (3) of Stacks 0E5I, `K` bounded below, `g` of finite Tor dimension and `Y` Noetherian.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- `L(f')^*(𝒪_{Y'}[a]) ⊗^L G ≅ G[a]`: the pullback of a shift of the structure sheaf, tensored
with `G`. -/
def pullbackStructureShiftTensorIso {X' Y' : AlgebraicSpaces B S hS} (f' : X' ⟶ Y')
    (G : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))) (a : ℤ) :
    (smallEtaleDerivedModulePullback B S hS f' ⋙ (smallEtaleDerivedTensor B S hS X').flip.obj G).obj
        ((structureDerived Y')⟦a⟧) ≅ G⟦a⟧ :=
  letI : ((smallEtaleDerivedTensor B S hS X').flip.obj G).CommShift ℤ :=
    (smallEtaleDerivedTensorProduct B S hS X').commShift_left _
  ((smallEtaleDerivedTensor B S hS X').flip.obj G).mapIso
      (((smallEtaleDerivedModulePullback B S hS f').commShiftIso a).app (structureDerived Y') ≪≫
        (shiftFunctor _ a).mapIso (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S)
          (hS := hS) f')) ≪≫
    (((smallEtaleDerivedTensor B S hS X').flip.obj G).commShiftIso a).app (structureDerived X') ≪≫
    (shiftFunctor _ a).mapIso ((smallEtaleDerivedTensorLeftUnitor X').app G)

/-- If `a`, `b`, `c` and `d` are invertible and so is `a ≫ b ≫ x ≫ c ≫ d`, then `x` is. -/
theorem isIso_of_isIso_comp₅ {C : Type*} [Category C] {P Q R T V W : C} (a : P ⟶ Q) (b : Q ⟶ R)
    (x : R ⟶ T) (c : T ⟶ V) (d : V ⟶ W) (ha : IsIso a) (hb : IsIso b) (hc : IsIso c)
    (hd : IsIso d) (h : IsIso (a ≫ b ≫ x ≫ c ≫ d)) : IsIso x := by
  have := IsIso.of_isIso_comp_left a (b ≫ x ≫ c ≫ d)
  have := IsIso.of_isIso_comp_left b (x ≫ c ≫ d)
  exact IsIso.of_isIso_comp_right x (c ≫ d)

/-- `m ≫ x = e⁻¹ ≫ (e ≫ m) ≫ x`. -/
theorem comp_eq_inv_comp_hom_comp_comp {C : Type*} [Category C] {A B T T' : C} (e : A ≅ B)
    (m : B ⟶ T) (x : T ⟶ T') : m ≫ x = e.inv ≫ (e.hom ≫ m) ≫ x := by
  simp

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)

/-- **The base change map of Stacks 0E5D is an isomorphism once it is on a perfect generator**
(the argument of Stacks 0E5I). For `g` affine and `M` a perfect generator of `D_QCoh(𝒪_X)`, if
the trace maps of Stacks 0E57 at `(M, K)` and at `(L(g')^*M, Lg^*K)` and the map
`Lg^*R𝓗om(Rf_*M, K) ⟶ R𝓗om(Lg^*Rf_*M, Lg^*K)` of Stacks 08JF are isomorphisms, then so is
`L(g')^* a(K) ⟶ a'(Lg^*K)`. -/
theorem isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isIso
    (hg : IsAffineHom B S hS g.hom)
    (M : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2)
    (hM : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) M.obj)
    (hMgen : (ObjectProperty.singleton M).IsWeakTriangulatedGenerator)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2)
    (hTr : IsIso (smallEtalePushforwardTrace hZ f hXqc hXqs hYqs M K))
    (hTr' : IsIso (smallEtalePushforwardTrace hZ f'
      (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
      (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs
      ((quasicoherentDerivedModulePullback g').obj M)
      ((quasicoherentDerivedModulePullback g).obj K)))
    (hρ : IsIso (smallEtaleDerivedPullbackSheafHomMap g
      ((derivedModulePushforward B S hS f).obj M.obj) K.obj)) :
    IsIso ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
      hTor).app K) := by
  have hfqc := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom
  have hfqs := isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom
  have hg' : IsAffineHom B S hS g'.hom :=
    isAffineHom_of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq).flip hg
  have hg'qc := isQuasiCompact_of_isAffineHom_hom g' hg'
  have hg'qs := isQuasiSeparated_of_isAffineHom_hom g' hg'
  have hBCM : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w M.obj) :=
    isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f g f' g' sq hfqc hfqs hTor
      M.obj M.property
  have hBCH : IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w
      (((smallEtaleDerivedSheafHom B S hS X).obj (op M.obj)).obj
        ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj)) :=
    isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f g f' g' sq hfqc hfqs hTor _
      (qcohDerived_smallEtaleDerivedSheafHom X _ _
        (Or.inr ⟨hM, ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).property⟩))
  have hρ' := isIso_smallEtaleDerivedPullbackSheafHomMap_of_isAffineHom g' hg' M.obj
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj hM
    ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).property
  have hρA : IsIso (PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS Y)
      (smallEtaleDerivedTensor B S hS Y') (smallEtaleDerivedPullbackTensorIso g)
      (smallEtaleDerivedSheafHom B S hS Y) (smallEtaleDerivedSheafHom B S hS Y')
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y')
      ((derivedModulePushforward B S hS f).obj M.obj) K.obj) :=
    (smallEtaleDerivedPullbackSheafHomMap_eq g _ _) ▸ hρ
  have hρ'A : IsIso (PullbackInternalHom.pullbackHomMap (smallEtaleDerivedTensor B S hS X)
      (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedPullbackTensorIso g')
      (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X') M.obj
      ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K).obj) :=
    (smallEtaleDerivedPullbackSheafHomMap_eq g' _ _) ▸ hρ'
  have hTrA : IsIso (InternalHomTrace.pushforwardTrace (smallEtaleDerivedModuleAdjunction B S hS f)
      (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS Y)
      (smallEtaleDerivedPullbackTensorIso f).hom (smallEtaleDerivedSheafHom B S hS X)
      (smallEtaleDerivedSheafHom B S hS Y)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y) M.obj
      ((squareAdjF hZ hXqc hXqs hYqs).counit.app K).hom) := hTr
  have hTr'A : IsIso (InternalHomTrace.pushforwardTrace
      (smallEtaleDerivedModuleAdjunction B S hS f')
      (smallEtaleDerivedTensor B S hS X') (smallEtaleDerivedTensor B S hS Y')
      (smallEtaleDerivedPullbackTensorIso f').hom (smallEtaleDerivedSheafHom B S hS X')
      (smallEtaleDerivedSheafHom B S hS Y') (smallEtaleDerivedTensorSheafHomAdjunction B S hS X')
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS Y')
      ((smallEtaleDerivedModulePullback B S hS g').obj M.obj)
      (((squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs).counit.app
        ((quasicoherentDerivedModulePullback g).obj K)).hom :
          _ ⟶ (smallEtaleDerivedModulePullback B S hS g).obj K.obj)) := hTr'
  have h := smallEtalePushforwardTrace_baseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor M K
  have h₀ := (congrArg IsIso h).mpr
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ hTrA) hρA)
  have h₂ := isIso_of_isIso_comp₅ _ _ _ _ _ ?_ ?_ ?_ ?_ h₀
  rotate_left
  · exact hBCH
  · exact @Functor.map_isIso _ _ _ _ _ _ _ _ hρ'A
  · exact hTr'A
  · exact NatIso.hom_app_isIso _ _
  -- the generator `L(g')^*M` of `D_QCoh(𝒪_{X'})`
  let G := (quasicoherentDerivedModulePullback g').obj M
  have := (quasicoherentDerivedModuleAdjunction B S hS g' hg'qc hg'qs).left_adjoint_additive
  have hgen : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator :=
    ObjectProperty.isWeakTriangulatedGenerator_singleton_map_of_reflects_isZero
      (quasicoherentDerivedModuleAdjunction B S hS g' hg'qc hg'qs)
      (fun E hE => (isZero_quasicoherentDerivedPushforward_obj_iff_of_isAffineHom g' hg'qc hg'qs
        hg' E).1 hE) hMgen
  refine Pretriangulated.isIso_of_generator_hom_bijective G hgen _ fun P hP => ?_
  obtain ⟨Y₀, a, e, hY₀⟩ := hP
  rw [ObjectProperty.singleton_iff] at hY₀
  subst hY₀
  have hD := InternalHomTrace.bijective_comp_of_isIso_map
    ((smallEtaleDerivedModuleAdjunction B S hS f').comp
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X' G.obj)) _ h₂
    ((structureDerived Y')⟦a⟧)
  let eD := pullbackStructureShiftTensorIso f' G.obj a ≪≫
    (((QcohDerived B S hS X').ι.commShiftIso a).app G).symm ≪≫
      (QcohDerived B S hS X').ι.mapIso e.symm
  let α :=
    (quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor).app K
  let e (T : QuasicoherentDerivedCategory.{u, u} B S hS X'.1 X'.2) : (P ⟶ T) ≃ (_ ⟶ T.obj) :=
    { toFun := fun φ => eD.hom ≫ φ.hom
      invFun := fun u => ObjectProperty.homMk (eD.inv ≫ u)
      left_inv := fun φ => by ext; exact eD.inv_hom_id_assoc _
      right_inv := fun u => eD.hom_inv_id_assoc u }
  have key : (fun map : P ⟶ _ => map ≫ α) = (e _).symm ∘ (fun u => u ≫ α.hom) ∘ e _ := by
    funext map
    change map ≫ α = ObjectProperty.homMk (eD.inv ≫ ((eD.hom ≫ map.hom) ≫ α.hom))
    ext
    change map.hom ≫ α.hom = eD.inv ≫ (eD.hom ≫ map.hom) ≫ α.hom
    exact comp_eq_inv_comp_hom_comp_comp eD map.hom α.hom
  rw [key]
  exact (e _).symm.bijective.comp (hD.comp (e _).bijective)

end Square

/-- A quasi-compact quasi-separated algebraic space has a perfect weak generator of
`D_QCoh(𝒪_X)`. -/
private theorem exists_isPerfect_isWeakTriangulatedGenerator_of_qcqs
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ G : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) G.obj ∧
        (ObjectProperty.singleton G).IsWeakTriangulatedGenerator := by
  obtain ⟨G, hGc, hG⟩ := exists_isCompactObject_isWeakTriangulatedGenerator_of_qcqs B S hS hZ X
    hXqc hXqs
  exact ⟨G, (isCompactObject_iff_isPerfect X hXqc hXqs G).1 hGc, hG⟩

/-- **The base change map of Stacks 0E5D over affine bases, when `Rf_*` preserves perfect
objects** (the common argument of cases (1) and (2) of Stacks 0E5I). For a cartesian square of
algebraic spaces with `X` quasi-compact and quasi-separated, `Y`, `Y'` affine and `X`, `Y'` Tor
independent over `Y`, if `Rf_*E` is perfect for every perfect `E`, then
`L(g')^* a(K) ⟶ a'(Lg^*K)` is an isomorphism for every `K ∈ D_QCoh(𝒪_Y)`. In case (2) of
Stacks 0E5I (`f` proper and perfect, `Y` Noetherian) the input is Stacks 0E4U. -/
theorem isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isPerfect_pushforward
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (hY : IsAffineSpace B S hS Y.1)
    (hY' : IsAffineSpace B S hS Y'.1) (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (hperf : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E.obj →
        RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
          ((derivedModulePushforward B S hS f).obj E.obj))
    (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY'.isQuasiCompactSpace
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY') hTor).app K) := by
  have hYqs := isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY
  have hfqc := isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom
  have hfqs := isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom
  obtain ⟨G, hGp, hG⟩ := exists_isPerfect_isWeakTriangulatedGenerator_of_qcqs hZ X hXqc hXqs
  have hfG := hperf G hGp
  have hg := isAffineHom_of_isAffineSpace B S hS g.hom hY' hY
  have hBC := isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f g f' g' sq hfqc hfqs
    hTor G.obj G.property
  refine isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isIso hZ sq _ _ _ _ _ _ hg G hGp
    hG K ?_ ?_ ?_
  · exact isIso_smallEtalePushforwardTrace_of_isPerfect hZ f _ _ _ G K hY.isQuasiCompactSpace hGp
      hfG
  · exact isIso_smallEtalePushforwardTrace_of_isPerfect hZ f' _ _ _ _ _ hY'.isQuasiCompactSpace
      (isPerfect_smallEtaleDerivedModulePullback g' _ hGp)
      (isPerfect_of_iso (hE := isPerfect_smallEtaleDerivedModulePullback g _ hfG)
        (e := @asIso _ _ _ _ _ hBC))
  · exact isIso_smallEtaleDerivedPullbackSheafHomMap_of_isAffineHom g hg _ K.obj hfG K.property

/-- **The base change map of Stacks 0E5D over affine bases, for `f` proper and flat of finite
presentation** (case (1) of Stacks 0E5I). For a cartesian square with `Y`, `Y'` affine and `f`
proper, flat and of finite presentation, `L(g')^* a(K) ⟶ a'(Lg^*K)` is an isomorphism for every
`K ∈ D_QCoh(𝒪_Y)`: `Rf_*` preserves perfect objects (Stacks 0CTM). -/
theorem isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isFlat
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (hf : IsProper B S hS f.hom) (hfl : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (hY : IsAffineSpace B S hS Y.1)
    (hY' : IsAffineSpace B S hS Y'.1) (K : QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2) :
    IsIso ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq
      (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfp.2.1 hY)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfp.2.2 hY)
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY) hY'.isQuasiCompactSpace
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hY')
      (torIndependent_of_isFlat_left f g hfl)).app K) :=
  isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isPerfect_pushforward hZ
    sq _ _ hY hY' _ (fun E hE =>
      (isPerfect_derivedModulePushforward_and_isIso_baseChange_of_isFlat f hf hfl hfp E.obj hE).1) K

/-- **The base change map of Stacks 0E5D over affine bases, for `g` of finite Tor dimension and
`K` bounded below** (case (3) of Stacks 0E5I). Let `g : U' ⟶ U` be a morphism of affine objects
with rings `R ⟶ R'` of finite Tor dimension, `U` Noetherian, and consider a cartesian square with
`f : X ⟶ U` proper and `X`, `U'` Tor independent over `U`. Then
`L(g')^* a(K) ⟶ a'(Lg^*K)` is an isomorphism for every bounded below `K ∈ D_QCoh(𝒪_U)`: for a
perfect generator `M`, `Rf_*M` is pseudo-coherent (Stacks 08GK, 08IK) and Stacks 0GG4 (2),
Stacks 0E4Q (3) apply. -/
theorem isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_hasFiniteTorDimensionRingHom
    {U' U : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] (g₀ : U' ⟶ U)
    {X X' : AlgebraicSpaces B S hS} {f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩}
    {f' : X' ⟶ ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f (representedSpaceMap B S hS g₀)) (hf : IsProper B S hS f.hom)
    (hY : IsNoetherian B S hS hZ (yoneda.obj U))
    (hTor : TorIndependent X.2 (isAlgebraicSpace_yoneda B S hS U')
      (isAlgebraicSpace_yoneda B S hS U) f.hom (representedSpaceMap B S hS g₀).hom)
    (hR : HasFiniteTorDimensionRingHom (representedAffineCommRingCatHom B S hS g₀).hom)
    (K : QuasicoherentDerivedCategory.{u, u} B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq
      (isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hf.2.1.2
        (isAffineSpace_yoneda B S hS U inferInstance))
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f
        (isQuasiSeparated_of_isSeparated B S hS hf.1) (isAffineSpace_yoneda B S hS U inferInstance))
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS U inferInstance))
      (isAffineSpace_yoneda B S hS U' inferInstance).isQuasiCompactSpace
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS U' inferInstance)) hTor).app K) := by
  have hYa := isAffineSpace_yoneda B S hS U inferInstance
  have hY'a := isAffineSpace_yoneda B S hS U' inferInstance
  have hXqc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hf.2.1.2 hYa
  have hfqs := isQuasiSeparated_of_isSeparated B S hS hf.1
  have hXqs :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ f hfqs hYa
  have hXN : IsNoetherian B S hS hZ X.1 := ⟨hXqc, hXqs,
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (isAlgebraicSpace_yoneda B S hS U)
      f.hom hf.2.1.1 hY.2.2⟩
  have hfqc : IsQuasiCompact B S hS f.hom := hf.2.1.2
  obtain ⟨G, hGp, hG⟩ := exists_isPerfect_isWeakTriangulatedGenerator_of_qcqs hZ X hXqc hXqs
  have hGpc :=
    RingedSite.isPseudoCoherent_of_isPerfect_general (smallEtaleRingedSite B S hS X.1 X.2) hGp
  have hL := (isPseudoCoherent_iff_isCoherent_homology hZ X hXN G).1 hGpc
  have hfL := derivedCategoryBMinus_derivedModulePushforward hZ f hf hY G.obj ⟨hL.1, hL.2⟩
  have hfGpc : RingedSite.IsPseudoCoherent (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)) ((derivedModulePushforward B S hS f).obj G.obj) :=
    (isPseudoCoherent_iff_isCoherent_homology hZ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      hY ⟨_, fun i => (hfL.2 i).toIsQuasicoherentOnSite⟩).2 ⟨hfL.1, hfL.2⟩
  have hg := isAffineHom_of_isAffineSpace B S hS (representedSpaceMap B S hS g₀).hom hY'a hYa
  have hBC := isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f _ f' g' sq hfqc hfqs
    hTor G.obj G.property
  have hgK := isBoundedBelow_smallEtaleDerivedModulePullback_representedSpaceMap B S hS g₀ hR
    K.obj K.property hK
  have hfin := hasFiniteTorDimension_smallEtaleModelDerivedEquivalence_functor_obj B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ _
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleModelRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))) _
    (hasFiniteTorDimension_derivedPushforward_structureDerived_representedSpaceMap B S hS g₀ hR)
  refine isIso_quasicoherentDerivedRightAdjointBaseChangeMap_app_of_isIso hZ sq _ _ _ _ _ _ hg G hGp
    hG K ?_ ?_ ?_
  · exact isIso_smallEtalePushforwardTrace_of_isPseudoCoherent hZ f _ _ _ G K
      hYa.isQuasiCompactSpace hK hGpc hfGpc
  · refine isIso_smallEtalePushforwardTrace_of_isPseudoCoherent hZ f' _ _ _ _ _
      hY'a.isQuasiCompactSpace hgK (isPseudoCoherent_smallEtaleDerivedModulePullback g' _ hGpc) ?_
    obtain ⟨P, hP, ⟨e⟩⟩ := isPseudoCoherent_smallEtaleDerivedModulePullback
      (representedSpaceMap B S hS g₀) _ hfGpc
    exact ⟨P, hP, ⟨e ≪≫ @asIso _ _ _ _ _ hBC⟩⟩
  · exact isIso_smallEtaleDerivedPullbackSheafHomMap_of_isAffineHom_of_isPseudoCoherent _ hg _ K.obj
      hfGpc ⟨hK, K.property⟩ hgK hfin

end AlgebraicGeometry.Space

end
