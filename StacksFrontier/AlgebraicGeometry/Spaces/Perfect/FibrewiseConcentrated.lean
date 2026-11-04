module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeFibrewiseBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineSectionsFlat
public import StacksFrontier.Homology.RelativelyPerfect.FibreConcentrated
public import StacksFrontier.Homology.Tor.DerivedFibreHomology

/-!
# Pseudo-coherent objects whose derived fibres are concentrated in one degree

Let `f : X ⟶ T` be a flat morphism, locally of finite presentation, from an algebraic space to a
scheme, and let `E ∈ D(𝒪_X)` be pseudo-coherent. If for every point `s ∈ T` the derived pullback
of `E` to the fibre `X_s` has cohomology sheaves only in degree `n`, then so does `E`, and `H^n(E)`
is flat over `T`. Everything is local: on an affine étale chart `U` of `X` over an affine open
`O` of `T` the derived fibres of `RΓ(U, E)` over the primes of `Γ(O)` are read on the charts of
the fibres, and the algebra is
`PseudoCoherence.isZero_homology_and_flat_of_isZero_homology_derivedFibre`.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_residueFibreChart_iff` and
`OpenAffineChartSquare.isZero_homology_representedAffineDerivedExtension_residueFibreChartFst_iff`:
  the cohomology of the derived fibre on a chart, degree by degree, read on rings.
* `AlgebraicGeometry.Space.isFlatOverOnChartDiagram_of_flat_representedAffineSections`: flatness
  over the base read on the sections over an affine chart.
* `AlgebraicGeometry.Space.isZero_homology_and_isFlatOver_of_isZero_homology_residueFibre`: the
  statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T : BigFppfOver B S hS}
  {X : AlgebraicSpaces B S hS} (f : X ⟶ representedSpace T)
  (s : (BigFppfOver.toScheme B S hS).obj T)

/-- **Cohomology on the chart of the fibre, degree by degree.** For an étale chart `U` of `X`
with affine scheme, whose chart `U ×_X X_s` of the fibre is affine, and `E ∈ D_QCoh(𝒪_X)`, the
`i`-th cohomology sheaf of `E` pulled back to `U ×_X X_s` vanishes exactly when the `i`-th
cohomology of the base change `RΓ(U, E) ⊗^L_{Γ(U)} Γ(U ×_X X_s)` does. -/
theorem isZero_homology_residueFibreChart_iff (U : SmallEtale B S hS X.1)
    [hU : IsAffine (chartScheme U)] [hW : IsAffine (chartScheme (residueFibreChart f s U))]
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) (i : ℤ) :
    haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
    haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj (residueFibreChart f s U).1.left) := hW
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).1
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).2) i).obj
        ((smallEtaleDerivedModulePullback B S hS
          (chartToSpace B S hS (residueFibre f s) (residueFibreChart f s U))).obj
          ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E))) ↔
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s U)).functor.obj
        ((representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj
          ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E)))) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) := hU
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (residueFibreChart f s U).1.left) := hW
  let F := (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E
  have hF : QcohDerived B S hS (chartSpace B S hS X U) F :=
    derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X U) E hE
  have := isIso_representedAffineDerivedAdjunction_counit_app B S hS
    ((SmallEtale.toOver B S hS X.1).obj U) F hF
  let K := (representedAffineDerivedSections B S hS ((SmallEtale.toOver B S hS X.1).obj U)).obj F
  let e : (smallEtaleDerivedModulePullback B S hS
        (chartToSpace B S hS (residueFibre f s) (residueFibreChart f s U))).obj
        ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E) ≅
      (representedAffineDerivedAssociated B S hS (residueFibreChart f s U).1.left).obj
        ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s U)).functor.obj K) :=
    (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (chartToSpace_residueFibreChart_comp f s U)).app E ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app E).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS
        (representedSpaceMap B S hS (residueFibreChartFst f s U))).mapIso
        (asIso ((representedAffineDerivedAdjunction B S hS
          ((SmallEtale.toOver B S hS X.1).obj U)).counit.app F)).symm ≪≫
      (representedAffineDerivedBaseChangeIso B S hS (residueFibreChartFst f s U)).app K
  have e1 := (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).1
        (chartSpace B S hS (residueFibre f s) (residueFibreChart f s U)).2) i).mapIso e
  refine (Iso.isZero_iff e1).trans ?_
  have e2 := ((representedAffineAssociated B S hS
      (residueFibreChart f s U).1.left).mapDerivedCategoryHomologyIso i).app
    ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s U)).functor.obj K)
  exact (Iso.isZero_iff e2).trans (isZero_representedAffineAssociated_obj_iff B S hS _ _)

/-- **Flatness over the base, from the sections over an affine étale chart.** For a
quasi-coherent `𝒪_X`-module `𝒢`, étale `a : U ⟶ X`, `b : V ⟶ Y` with `U`, `V` affine and
`f₀ : U ⟶ V` over `f`, if the sections `Γ(U, a^*𝒢)` are a flat `Γ(V, 𝒪)`-module then `𝒢` is flat
over `Y` on the commuting square of étale charts cut out by `a`, `b` and `f₀`. This is the
converse of `AlgebraicGeometry.Space.flat_representedAffineSections_modulePullback_of_isFlatOver`
on that square. -/
theorem isFlatOverOnChartDiagram_of_flat_representedAffineSections
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (G : Modules.{u, u} B S hS X.1 X.2)
    (hGq : G.IsQuasicoherentOnSite)
    {U V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (a : (schemeSpace U : AlgebraicSpaces B S hS) ⟶ X)
    (ha : IsEtale B S hS a.hom)
    (b : (schemeSpace V : AlgebraicSpaces B S hS) ⟶ Y)
    (hb : IsEtale B S hS b.hom) (f₀ : U ⟶ V) (hf₀ : schemeSpaceMap f₀ ≫ b = a ≫ f)
    (hflat : Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        ((representedAffineSections B S hS U).obj ((modulePullback B S hS a).obj G)))) :
    IsFlatOverOnChartDiagram B S hS X.2 G
      { U := etaleChartOfIsEtale B S hS a.hom ha
        V := etaleChartOfIsEtale B S hS b.hom hb
        g := f₀
        comm := (congrArg (fun k => k.hom) hf₀).symm } := by
  let P := (modulePullback B S hS a).obj G
  have hP : P.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a G hGq
  have := isQuasicoherent_representedZariskiRestriction B S hS U P hP
  let : Module Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ(representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) P, ⊤) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map f₀).appTop.hom
  let i := restrictToChartSelfChartIsoRestrictModule B S hS U P
  let l :=
    (show ((ModuleCat.restrictScalars.{u} (representedAffineCommRingCatHom B S hS f₀).hom).obj
        ((representedAffineSections B S hS U).obj P) : Type u) ≃+
      Γ(representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) P, ⊤) from
      { toFun := fun x => (i.inv.val.app (op ⊤)).hom x
        invFun := fun y => (i.hom.val.app (op ⊤)).hom y
        left_inv := fun x => congrArg (fun φ => (φ.val.app (op ⊤)).hom x) i.inv_hom_id
        right_inv := fun y => congrArg (fun φ => (φ.val.app (op ⊤)).hom y) i.hom_inv_id
        map_add' := fun x y => map_add _ x y })
  have hl : ∀ (r : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) m, l (r • m) = r • l m := by
    intro r m
    have hx : ∀ t : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
        (((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.appTop).hom
          ((Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv.hom t) = t := fun t => by
      rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
      exact congrArg (fun φ => φ.hom t)
        (Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv_hom_id
    refine ((i.inv.val.app (op ⊤)).hom.map_smul
      (show ((etaleChartScheme B S hS (selfChart B S hS U)).ringCatSheaf.obj.obj (op ⊤) :
          Type u) from
        (((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.appTop).hom
          ((Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv.hom
            ((representedAffineCommRingCatHom B S hS f₀).hom r))) m).trans ?_
    exact congrArg (fun t : ((etaleChartScheme B S hS (selfChart B S hS U)).ringCatSheaf.obj.obj
      (op ⊤) : Type u) => t • (i.inv.val.app (op ⊤)).hom m) (hx _)
  have h3 : Module.Flat Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      Γ(representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) P, ⊤) :=
    Module.Flat.of_semilinearEquiv (RingEquiv.refl _) l.symm (fun r m => by
      apply l.injective
      rw [hl, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      rfl)
  have h2 := (AlgebraicGeometry.isFlatOver_iff_flat_sections
    ((BigFppfOver.toScheme B S hS).map f₀)
    (representedZariskiRestriction B S hS U (isAlgebraicSpace_yoneda B S hS U) P)).2 h3
  exact (AlgebraicGeometry.isFlatOver_iff_of_moduleIso _
    (restrictToChartIsoRepresentedZariskiRestrictionPullback B S hS a.hom ha G hGq)).2 h2

namespace OpenAffineChartSquare

variable {f} (c : OpenAffineChartSquare f)

/-- **Cohomology on the chart of the fibre, read on rings, degree by degree.** For an affine chart
`U` over an affine open `O ∋ s` and `K ∈ D(Γ(U))`, the `i`-th cohomology of the base change
`K ⊗^L_{Γ(U)} Γ(U ×_O Spec κ(s))` vanishes exactly when that of the derived fibre
`K ⊗^L_{Γ(O)} κ(p)` does, `p` the prime of `s`. -/
theorem isZero_homology_representedAffineDerivedExtension_residueFibreChartFst_iff
    (hfl : IsFlat B S hS f.hom) (hs : s ∈ c.O)
    (K : DerivedCategory (ModuleCat.{u} Γ(chartScheme c.toChartDiagram.U, ⊤))) (i : ℤ) :
    haveI := c.isAffine_residueFibreChart s hs
    haveI := (OpenAffineChartSquare.isField_siteObject (T := T) s).isDomain
    haveI := RingHom.ker_isPrime (c.residuePoint s hs).appTop.hom
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((representedAffineDerivedExtension B S hS (residueFibreChartFst f s c.U)).functor.obj
        K)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap Γ(chartScheme c.toChartDiagram.V, ⊤)
            (RingHom.ker (c.residuePoint s hs).appTop.hom).ResidueField)).functor.obj
        ((ModuleCat.restrictScalars.{u}
          ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom).mapDerivedCategory.obj
            K))) := by
  have := c.isAffine_residueFibreChart s hs
  have := (OpenAffineChartSquare.isField_siteObject (T := T) s).isDomain
  have := RingHom.ker_isPrime (c.residuePoint s hs).appTop.hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj c.U.obj.left) := c.isAffine_U
  have hsq := c.isPullback_residueFibreChart s hs
  let gR := ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom
  let ℓR := (c.residuePoint s hs).appTop.hom
  let qR := ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s c.U)).appTop.hom
  let rR := ((BigFppfOver.toScheme B S hS).map (residueFibreChartSnd f s c.U)).appTop.hom
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤) :=
    gR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤) :=
    ℓR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := qR.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := rR.toAlgebra
  let : Algebra Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) := (qR.comp gR).toAlgebra
  have hw : qR.comp gR = rR.comp ℓR := by
    have h1 : ((BigFppfOver.toScheme B S hS).map (residueFibreChartFst f s c.U) ≫
        (BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom = qR.comp gR := by
      rw [Scheme.Hom.comp_appTop]; rfl
    have h2 : ((BigFppfOver.toScheme B S hS).map (residueFibreChartSnd f s c.U) ≫
        c.residuePoint s hs).appTop.hom = rR.comp ℓR := by
      rw [Scheme.Hom.comp_appTop]; rfl
    rw [← h1, ← h2, hsq.w]
  have : IsScalarTower Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hw x)
  have : Algebra.IsPushout Γ(chartScheme c.toChartDiagram.V, ⊤)
      Γ(chartScheme c.toChartDiagram.U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤)
      Γ(chartScheme (residueFibreChart f s c.U), ⊤) :=
    (CommRingCat.isPushout_iff_isPushout).1 (isPushout_appTop_of_isPullback hsq)
  have : Module.Flat Γ(chartScheme c.toChartDiagram.V, ⊤) Γ(chartScheme c.toChartDiagram.U, ⊤) :=
    HasRingHomProperty.appTop (P := @Flat) _ (flat_chartDiagram_g f hfl c.toChartDiagram)
  open CochainComplex.DerivedExtensionScalars in
  have h1 := isZero_homology_totalDerivedExtensionScalars_iff_of_isPushout
    (R := Γ(chartScheme c.toChartDiagram.V, ⊤)) (A := Γ(chartScheme c.toChartDiagram.U, ⊤))
    (R' := Γ((BigFppfOver.toScheme B S hS).obj
        ((residueFieldValuedPoint B S hS T s).siteObject B S hS (yoneda.obj T)), ⊤))
    (A' := Γ(chartScheme (residueFibreChart f s c.U), ⊤)) K i
  open CochainComplex.DerivedExtensionScalars in
  have h2 := isZero_homology_totalDerivedExtensionScalars_iff_residueField
    (OpenAffineChartSquare.isField_siteObject (T := T) s) ℓR
    ((ModuleCat.restrictScalars.{u} gR).mapDerivedCategory.obj K) i
  exact h1.trans h2

end OpenAffineChartSquare


/-- The derived fibre at a prime only depends on the prime. -/
theorem isZero_homology_totalDerivedExtensionScalars_residueField_congr {R : Type u} [CommRing R]
    {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I = J) (M : DerivedCategory (ModuleCat.{u} R))
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R I.ResidueField)).functor.obj M)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R J.ResidueField)).functor.obj M)) := by
  subst h
  rfl

/-- **Pseudo-coherent objects whose derived fibres are concentrated in one degree.** Let
`f : X ⟶ T` be a flat morphism, locally of finite presentation, from an algebraic space to a
scheme, and let `E ∈ D(𝒪_X)` be pseudo-coherent. If for every point `s ∈ T` the derived pullback
`L(X_s ⟶ X)^*E` to the fibre has cohomology sheaves only in degree `n`, then `E` has cohomology
sheaves only in degree `n` and `H^n(E)` is flat over `T`. -/
theorem isZero_homology_and_isFlatOver_of_isZero_homology_residueFibre
    (hfl : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) (n : ℤ)
    (hfib : ∀ (s : (BigFppfOver.toScheme B S hS).obj T) (i : ℤ), i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E))) :
    (∀ i, i ≠ n → IsZero ((DerivedCategory.homologyFunctor _ i).obj E)) ∧
      IsFlatOver B S hS X.2 f.hom ((DerivedCategory.homologyFunctor _ n).obj E) := by
  have hEq : QcohDerived B S hS X E :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  have hEc : ∀ U : SmallEtale B S hS X.1,
      QcohDerived B S hS (chartSpace B S hS X U)
        ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X U)).obj E) :=
    fun U => derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ (chartToSpace B S hS X U)
      E hEq
  let K : ∀ c : OpenAffineChartSquare f,
      DerivedCategory (ModuleCat.{u} Γ(chartScheme c.toChartDiagram.U, ⊤)) := fun c =>
    (representedAffineDerivedSections B S hS
      ((SmallEtale.toOver B S hS X.1).obj c.toChartDiagram.U)).obj
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X c.toChartDiagram.U)).obj E)
  have hKpc : ∀ c : OpenAffineChartSquare f, StacksDraft.PseudoCoherence.IsPseudoCoherent (K c) :=
    fun c => (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).2 fun m =>
      (isPseudoCoherentFrom_iff_forall_isAffineChart X E hEq m).1
        ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ E).1 hE m)
          c.toChartDiagram.U c.isAffine_U
  have hfibc : ∀ (c : OpenAffineChartSquare f) (s : (BigFppfOver.toScheme B S hS).obj T)
      (hs : s ∈ c.O) (p : PrimeSpectrum Γ(chartScheme c.toChartDiagram.V, ⊤))
      (_ : RingHom.ker (c.residuePoint s hs).appTop.hom = p.asIdeal) (i : ℤ), i ≠ n →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap Γ(chartScheme c.toChartDiagram.V, ⊤) p.asIdeal.ResidueField)).functor.obj
        ((ModuleCat.restrictScalars.{u}
          ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom).mapDerivedCategory.obj
            (K c)))) := by
    intro c s hs p hker i hi
    obtain ⟨I, hI⟩ := p
    change RingHom.ker (c.residuePoint s hs).appTop.hom = I at hker
    subst hker
    have := (OpenAffineChartSquare.isField_siteObject (T := T) s).isDomain
    have := c.isAffine_U
    have := c.isAffine_residueFibreChart s hs
    have h0 : IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((smallEtaleDerivedModulePullback B S hS
          (chartToSpace B S hS (residueFibre f s) (residueFibreChart f s c.U))).obj
          ((smallEtaleDerivedModulePullback B S hS (residueFibreι f s)).obj E))) :=
      (isZero_over_homology_iff _ _ (residueFibreChart f s c.U) i).1
        (@Functor.map_isZero _ _ _ _ _ _ (SheafOfModules.overFunctor _ _)
          ⟨fun _ _ ↦ by rfl⟩ _ (hfib s i hi))
    have h1 := (isZero_homology_residueFibreChart_iff f s c.U E hEq i).1 h0
    exact (c.isZero_homology_representedAffineDerivedExtension_residueFibreChartFst_iff s hfl
      hs _ i).1 h1
  have hring : ∀ c : OpenAffineChartSquare f,
      (∀ i, i ≠ n → IsZero ((DerivedCategory.homologyFunctor _ i).obj (K c))) ∧
        Module.Flat Γ(chartScheme c.toChartDiagram.V, ⊤)
          ((ModuleCat.restrictScalars
            ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom).obj
            ((DerivedCategory.homologyFunctor _ n).obj (K c))) := by
    intro c
    refine PseudoCoherence.isZero_homology_and_flat_of_isZero_homology_derivedFibre
      (R := Γ(chartScheme c.toChartDiagram.V, ⊤)) (A := Γ(chartScheme c.toChartDiagram.U, ⊤))
      ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom
      (HasRingHomProperty.appTop (P := @Flat) _ (flat_chartDiagram_g f hfl c.toChartDiagram))
      (HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) _
        (locallyOfFinitePresentation_chartDiagram_g f hlfp c.toChartDiagram)) (K c) (hKpc c) n
      fun p i hi => ?_
    have key := c.exists_ker_residuePoint_eq p
    exact hfibc c key.choose key.choose_spec.choose p key.choose_spec.choose_spec i hi
  have hopen : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ O : ((BigFppfOver.toScheme B S hS).obj T).Opens, IsAffineOpen O ∧ t ∈ O := fun t => by
    obtain ⟨O, hO, htO, -⟩ := exists_isAffineOpen_mem_and_subset
      (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens)) (x := t) trivial
    exact ⟨O, hO, htO⟩
  have hover : ∀ (c : OpenAffineChartSquare f) (i : ℤ), i ≠ n →
      IsZero (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E).over
        (c.U : (smallEtaleRingedSite B S hS X.1 X.2).C)) := fun c i hi => by
    have := c.isAffine_U
    exact (isZero_over_homology_iff X E c.U i).2
      ((isZero_homology_iff_representedAffineDerivedSections
        ((SmallEtale.toOver B S hS X.1).obj c.toChartDiagram.U) _
        (hEc c.U) i).2 ((hring c).1 i hi))
  refine ⟨fun i hi => ?_, ?_⟩
  · refine isZero_of_supportOfSheaf_eq_empty B S hS X _ ?_
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨O, hO, hxO⟩ := hopen (pointsToScheme B S hS T (pointsMap B S hS _ f.hom x))
    obtain ⟨c, rfl, hxc⟩ := OpenAffineChartSquare.exists_of_mem x O hO hxO
    have := supportOfSheaf_inter_range_eq_empty_of_isZero_over B S hS X _ c.U (hover c i hi)
    exact (Set.eq_empty_iff_forall_notMem.mp this) x ⟨hx, hxc⟩
  · have hqc : ((DerivedCategory.homologyFunctor _ n).obj E).IsQuasicoherentOnSite := hEq n
    refine isFlatOver_of_forall_isFlatOverAtPoint B S hS f _ hqc fun x => ?_
    obtain ⟨O, hO, hxO⟩ := hopen (pointsToScheme B S hS T (pointsMap B S hS _ f.hom x))
    obtain ⟨c, rfl, y, hy⟩ := OpenAffineChartSquare.exists_of_mem x O hO hxO
    have := c.isAffine_U
    have : IsAffine (chartScheme c.toChartDiagram.V) := c.isAffineOpen_O
    let a := chartToSpace B S hS X c.U
    have ha : IsEtale B S hS a.hom := isEtale_chartToSpace B S hS X c.U
    let b := chartToSpace B S hS (representedSpace T) c.toChartDiagram.V
    have hb : IsEtale B S hS b.hom :=
      isEtale_chartToSpace B S hS (representedSpace T) c.toChartDiagram.V
    have hf₀ : representedSpaceMap B S hS c.toChartDiagram.g ≫ b = a ≫ f :=
      (chartToSpace_comp_eq f c.toChartDiagram).symm
    have := etaleModulePullback_additive B S hS a ha
    have := preservesFiniteLimits_etaleModulePullback B S hS a ha
    have := preservesFiniteColimits_etaleModulePullback B S hS a ha
    let eK : (DerivedCategory.homologyFunctor _ n).obj (K c) ≅
        (representedAffineSections B S hS ((SmallEtale.toOver B S hS X.1).obj c.U)).obj
          ((modulePullback B S hS a).obj ((DerivedCategory.homologyFunctor _ n).obj E)) :=
      representedAffineDerivedSectionsHomologyIso B S hS _ _ (hEc c.U) n ≪≫
        (representedAffineSections B S hS ((SmallEtale.toOver B S hS X.1).obj c.U)).mapIso
          ((DerivedCategory.homologyFunctor _ n).mapIso
              ((smallEtaleDerivedModulePullbackIsoEtale B S hS a ha).app E) ≪≫
            ((etaleModulePullback.{u, u} B S hS a ha).mapDerivedCategoryHomologyIso n).app E ≪≫
            ((modulePullbackIsoEtaleModulePullback B S hS a ha).app _).symm)
    have hflat := (Module.Flat.equiv_iff
      ((ModuleCat.restrictScalars
        ((BigFppfOver.toScheme B S hS).map c.toChartDiagram.g).appTop.hom).mapIso
          eK).toLinearEquiv).1 (hring c).2
    have hd := isFlatOverOnChartDiagram_of_flat_representedAffineSections f _ hqc a ha b hb
      c.toChartDiagram.g hf₀ hflat
    refine ⟨_, _, ?_, hd (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj c.U) y)⟩
    exact (congrArg (pointsMap B S hS _ a.hom) (Equiv.symm_apply_apply _ y)).trans hy

end AlgebraicGeometry.Space

end
