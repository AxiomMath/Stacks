module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeAffineReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineHomToStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChange

/-!
# Stacks 0A1P: perfectness of `Rf_*(E ⊗^L 𝒢^•)` for a morphism of finite presentation

Let `f : X ⟶ Y` be a morphism of finite presentation of algebraic spaces, `E` a perfect object of
`D(𝒪_X)` and `𝒢^•` a bounded complex of `𝒪_X`-modules of finite presentation, flat over `Y`,
with support proper over `Y`. Then `Rf_*(E ⊗^L 𝒢^•)` is perfect.

The proof is the source's. Perfectness is local on `Y`, so `Y` may be taken to be the spectrum of
a ring `A` of the site; viewing `X` over `Spec A`, a Noetherian approximation `Spec A ⟶ Y₀`
carries `(X, 𝒢^•)` as the base change of a model `(X₀, 𝒢₀^•)` over a Noetherian affine `Y₀`, and
`E` may be taken to be pulled back from a perfect object on `X₀` (Stacks 09IY, 09M8). On `Y₀`
the statement is the Noetherian case, and the base change result of Stacks 0A1K carries it to
`Y`.

## Main results

* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_smallEtaleDerivedModulePullback_of_iso`
* `AlgebraicGeometry.Space.derivedTensorPushforwardEtaleBaseChangeIso`
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor_of_relocalize`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

section Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Perfectness descends along the derived pullback by an isomorphism.** -/
theorem isPerfect_of_isPerfect_smallEtaleDerivedModulePullback_of_iso
    {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (h : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2)
      ((smallEtaleDerivedModulePullback B S hS e.hom).obj K)) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K :=
  isPerfect_of_iso B S hS (isPerfect_smallEtaleDerivedModulePullback e.inv _ h)
    ((smallEtaleDerivedModulePullbackCompIso B S hS e.inv e.hom).app K ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS e.inv_hom_id).app K ≪≫
      (smallEtaleDerivedModulePullbackIdentityIso B S hS Y).app K)

/-- **`Rf_*(E ⊗^L 𝒢^•)` under an étale base change.** For a cartesian square with `g` étale and
representable, `Lg^* Rf_*(E ⊗^L 𝒢^•) ≅ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)`. -/
def derivedTensorPushforwardEtaleBaseChangeIso {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) (hrep : yoneda.relativelyRepresentable g.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS g).obj
        ((derivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) ≅
      (derivedModulePushforward B S hS f').obj
        (((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).obj
          (DerivedCategory.Q.obj (((modulePullback B S hS g').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G))) :=
  haveI := isIso_smallEtaleDerivedBaseChangeMap_of_isEtale B S hS f g f' g' sq hg hrep
    (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))
  asIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w
      (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) ≪≫
    (derivedModulePushforward B S hS f').mapIso
      ((smallEtaleDerivedPullbackTensorIso g').app (E, DerivedCategory.Q.obj G) ≪≫
        ((smallEtaleDerivedTensor B S hS X').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E)).mapIso
          (smallEtaleDerivedModulePullbackObjQIsoOfIsEtale g'
            (isEtale_of_isPullback B S hS f' g' g f sq.flip hg) G))

end Transport

section Relocalize

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) {X Y : AlgebraicSpaces B T hT} (f : X ⟶ Y)

/-- **Perfectness of a derived direct image descends along the relocalization.** For a morphism
`f : X ⟶ Y` of algebraic spaces over `T` and its lower-shriek extension `Λ f` over `S`,
`Rf_*(E ⊗^L K)` is perfect as soon as `R(Λ f)_*(ρE ⊗^L ρK)` is. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_of_relocalize
    (E K : DerivedCategory (Modules.{u, u} B T hT X.1 X.2))
    (h : RingedSite.IsPerfect (smallEtaleRingedSite B S hS (relocalizeSpace B hT hS g Y).1
        (relocalizeSpace B hT hS g Y).2)
      ((derivedModulePushforward B S hS (relocalizeHom B hT hS g f)).obj
        (((smallEtaleDerivedTensor B S hS (relocalizeSpace B hT hS g X)).obj
          ((relocalizeDerivedFunctor B hT hS g X.1 X.2).obj E)).obj
          ((relocalizeDerivedFunctor B hT hS g X.1 X.2).obj K)))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B T hT Y.1 Y.2)
      ((derivedModulePushforward B T hT f).obj
        (((smallEtaleDerivedTensor B T hT X).obj E).obj K)) := by
  refine (isPerfect_relocalizeDerivedFunctor_obj_iff B hT hS g Y.1 Y.2 _).1 ?_
  refine isPerfect_of_iso B S hS h ?_
  exact ((derivedModulePushforward B S hS (relocalizeHom B hT hS g f)).mapIso
      (relocalizeDerivedTensorObjIso B hT hS g X.1 X.2 E K)).symm ≪≫
    (relocalizeDerivedPushforwardObjIso B hT hS g f _).symm

end Relocalize

/-- The base change statement of Stacks 0A1K, in the form of an isomorphism
`Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•) ≅ Lg^*Rf_*(E ⊗^L 𝒢^•)`, on every site of the big fppf site `B`. -/
structure BaseChangeIsoStatement (B : BigFppfSite.{u}) : Prop where
  /-- The isomorphism of Stacks 0A1K for a perfect `P₀`. -/
  iso : ∀ {S' : Scheme.{u}} (hS' : B.Contains S') {X₀ X₁ Y₀ Y₁ : AlgebraicSpaces B S' hS'}
    (f₀ : X₀ ⟶ Y₀) (y : Y₁ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (a : X₁ ⟶ X₀), IsPullback a f₁ f₀ y →
    IsQuasiCompact B S' hS' f₀.hom → IsQuasiSeparated B S' hS' f₀.hom →
    ∀ (P₀ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S' hS' X₀))),
    RingedSite.IsPerfect (smallEtaleRingedSite B S' hS' X₀.1 X₀.2) P₀ →
    ∀ (G₀ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S' hS' X₀)) ℤ),
    (∃ b : ℤ, ∀ i, b < i → IsZero (G₀.X i)) → (∀ n, (G₀.X n).IsQuasicoherentOnSite) →
    (∀ n, IsFlatOver B S' hS' X₀.2 f₀.hom (G₀.X n)) →
    Nonempty ((derivedModulePushforward B S' hS' f₁).obj
        (((smallEtaleDerivedTensor B S' hS' X₁).obj
          ((smallEtaleDerivedModulePullback B S' hS' a).obj P₀)).obj
          (DerivedCategory.Q.obj (((modulePullback B S' hS' a).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G₀))) ≅
      (smallEtaleDerivedModulePullback B S' hS' y).obj ((derivedModulePushforward B S' hS' f₀).obj
        (((smallEtaleDerivedTensor B S' hS' X₀).obj P₀).obj (DerivedCategory.Q.obj G₀))))

section NoetherianModel

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The Noetherian case carried along a base change.** Let `f₀ : X₀ ⟶ Y₀` be of finite
presentation with `Y₀` affine and Noetherian, `ℱ₀` an `𝒪_{X₀}`-module of finite presentation, flat
over `Y₀` with support proper over `Y₀`, and `X₁ = X₀ ×_{Y₀} Y₁` for an affine `Y₁`. If
`Rf₁_*(La^*P₀ ⊗^L a^*ℱ₀[n]) ≅ Ly^*Rf₀_*(P₀ ⊗^L ℱ₀[n])` for every perfect `P₀` (Stacks 0A1K), then
`Rf₁_*(E₁ ⊗^L a^*ℱ₀[n])` is perfect for every perfect `E₁` on `X₁`. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_single_of_noetherianModel
    (hZ : B.Contains (⊤_ Scheme.{u})) {X₀ X₁ Y₀ Y₁ : AlgebraicSpaces B S hS}
    (hY₀ : IsNoetherian B S hS hZ Y₀.1) (hY₀a : IsAffineSpace B S hS Y₀.1)
    (hY₁ : IsAffineSpace B S hS Y₁.1) (f₀ : X₀ ⟶ Y₀) (hf₀ : IsFinitePresentation B S hS f₀.hom)
    (F₀ : Modules.{u, u} B S hS X₀.1 X₀.2) (hF₀ : F₀.IsFinitePresentationOnSite)
    (hflat : IsFlatOver B S hS X₀.2 f₀.hom F₀)
    (hsupp : HasProperSupport B S hS X₀.2 Y₀.2 f₀.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf₀.1)
      ((SheafOfModules.toSheaf _).obj F₀))
    (y : Y₁ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (a : X₁ ⟶ X₀) (sq : IsPullback a f₁ f₀ y) (n : ℤ)
    (h0A1K : BaseChangeIsoStatement B)
    (E₁ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₁)))
    (hE₁ : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X₁.1 X₁.2) E₁) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y₁.1 Y₁.2)
      ((derivedModulePushforward B S hS f₁).obj
        (((smallEtaleDerivedTensor B S hS X₁).obj E₁).obj
          ((DerivedCategory.singleFunctor _ n).obj ((modulePullback B S hS a).obj F₀)))) := by
  have hft₀ := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf₀.1
  have hf₁ : IsFinitePresentation B S hS f₁.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hf₀
  have hX₀qc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f₀ hf₀.2.1 hY₀a
  have hX₀qs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS
    B.contains_terminal f₀ hf₀.2.2 hY₀a
  have hX₁qc := isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f₁ hf₁.2.1 hY₁
  have hX₁qs := isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS
    B.contains_terminal f₁ hf₁.2.2 hY₁
  have ha : IsAffineHom B S hS a.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq.flip)
      (isAffineHom_of_isAffineSpace B S hS y.hom hY₁ hY₀a)
  have := Fact.mk <| hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    X₀.2 Y₀.2 f₀.hom hft₀ hY₀.2.2
  let G₀ :=
    (HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀))
      (ComplexShape.up ℤ) n).obj F₀
  have hG0 : ∀ m, m ≠ n → IsZero (G₀.X m) := fun _ => HomologicalComplex.isZero_single_obj_X _ _ _ _
  have hG₀c : ∀ m, IsCoherent B S hS X₀.1 X₀.2 (G₀.X m) := fun m => by
    rcases eq_or_ne m n with rfl | hm
    · exact isCoherent_of_iso B S hS X₀.2
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) _ F₀).symm
        ((isCoherent_iff_isFinitePresentationOnSite B S hS X₀.1 X₀.2 F₀).2 hF₀)
    · exact IsCoherent.of_isZero B S hS X₀.1 X₀.2 (hG0 m hm)
  have hG₀f : ∀ m, IsFlatOver B S hS X₀.2 f₀.hom (G₀.X m) := fun m => by
    rcases eq_or_ne m n with rfl | hm
    · exact IsFlatOver.of_iso B S hS _
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) _ F₀).symm hflat
    · exact isFlatOver_of_isZero B S hS f₀ (hG0 m hm)
  refine isPerfect_derivedModulePushforward_derivedTensor_of_affineHom f₁ a ha hX₁qc hX₁qs hX₀qc
    hX₀qs _ (fun P₀ hP₀ => ?_) E₁ hE₁
  obtain ⟨e⟩ := h0A1K.iso hS f₀ y f₁ a sq hf₀.2.1 hf₀.2.2 P₀ hP₀ G₀
    ⟨n, fun i hi => hG0 i (ne_of_gt hi)⟩ (fun m => (hG₀c m).toIsQuasicoherentOnSite) hG₀f
  have := modulePullback_additive a
  refine isPerfect_of_iso B S hS (isPerfect_smallEtaleDerivedModulePullback y _ ?_)
    (e.symm ≪≫ (derivedModulePushforward B S hS f₁).mapIso
      (((smallEtaleDerivedTensor B S hS X₁).obj _).mapIso
        (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback B S hS a) (ComplexShape.up ℤ) n).app F₀) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ _ n).app _).symm)))
  refine isPerfect_derivedModulePushforward_tensor_of_isNoetherian hZ hY₀ f₀ hft₀ hf₀.2.1 hf₀.2.2
    P₀ hP₀ G₀ ((Set.finite_singleton n).subset fun i hi =>
      Classical.byContradiction fun h' => hi (hG0 i h')) hG₀c hG₀f (fun m => ?_)
  rcases eq_or_ne m n with rfl | hm
  · exact hasProperSupport_of_iso Y₀.2 _ _
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) _ F₀).symm hsupp
  · exact hasProperSupport_of_isZero B S hS _ _ _ _ (hG0 m hm)

end NoetherianModel

section SpecBase

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- **Stacks 0A1P over the spectrum of a ring, for a module in one degree.** Let `f : X ⟶ Spec A`
be of finite presentation, `E` perfect on `X` and `ℱ` an `𝒪_X`-module of finite presentation,
flat over `Spec A` with support proper over `Spec A`. Granting the base change result of Stacks
0A1K, `Rf_*(E ⊗^L ℱ[n])` is perfect. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_single_of_specBase
    (h0A1K : BaseChangeIsoStatement B) {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X ⟶ schemeSpace (Over.mk (𝟙 (B.obj hA))))
    (hf : IsFinitePresentation B (Spec (.of A)) hA f.hom)
    (E : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2) E)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver B (Spec (.of A)) hA X.2 f.hom F)
    (hsupp : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (Over.mk (𝟙 (B.obj hA)))).2
      f.hom (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hA hf.1)
      ((SheafOfModules.toSheaf _).obj F)) (n : ℤ) :
    RingedSite.IsPerfect (smallEtaleRingedSite B (Spec (.of A)) hA
        (schemeSpace (Over.mk (𝟙 (B.obj hA)))).1 (schemeSpace (Over.mk (𝟙 (B.obj hA)))).2)
      ((derivedModulePushforward B (Spec (.of A)) hA f).obj
        (((smallEtaleDerivedTensor B (Spec (.of A)) hA X).obj E).obj
          ((DerivedCategory.singleFunctor _ n).obj F))) := by
  obtain ⟨A₀, _, _, _, hA₀, g, hg, Y₀, y, X₀, f₀, hf₀, F₀, a, hY₀a, -, hY₀N, -, hF₀q, hF₀fp,
    hF₀flat, hF₀supp, hpb, ⟨eF⟩⟩ := exists_noetherianProductModel B X.2 f.hom hf F hF hflat hsupp
  refine isPerfect_derivedModulePushforward_derivedTensor_of_relocalize B hA hA₀ g f E
    ((DerivedCategory.singleFunctor _ n).obj F) ?_
  let bh := relocalizeBaseHom B hA hA₀ g
  let y₁ := bh ≫ schemeSpaceMap y
  have hst : relocalizeHom B hA hA₀ g f ≫ bh =
      ObjectProperty.homMk (OverShriek.viewStructureMap g X.1) :=
    ObjectProperty.hom_ext _ (relocalizeHom_comp_relocalizeBaseHom B hA hA₀ g X.2 f)
  have hsq₀ : IsPullback (𝟙 _) (relocalizeHom B hA hA₀ g f)
      (ObjectProperty.homMk (OverShriek.viewStructureMap g X.1)) bh :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hst]⟩
  have sq₁ : IsPullback a (relocalizeHom B hA hA₀ g f) f₀ y₁ := by
    simpa only [Category.id_comp] using hsq₀.paste_horiz hpb
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A₀)) hA₀).obj (Over.mk g)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have hY₁ : IsAffineSpace B (Spec (.of A₀)) hA₀
      (relocalizeSpace B hA hA₀ g (schemeSpace (Over.mk (𝟙 (B.obj hA))))).1 :=
    (isAffineSpace_yoneda B _ hA₀ (Over.mk g) inferInstance).of_iso
      ((ObjectProperty.ι _).mapIso (asIso bh).symm)
  have hY₀ : IsAffineSpace B (Spec (.of A₀)) hA₀ (schemeSpace Y₀).1 :=
    isAffineSpace_yoneda B _ hA₀ Y₀ hY₀a
  have hP := isPerfect_derivedModulePushforward_derivedTensor_single_of_noetherianModel
    B.contains_terminal hY₀N hY₀ hY₁ f₀ hf₀ F₀ hF₀fp hF₀flat hF₀supp y₁ (relocalizeHom B hA hA₀ g f)
    a sq₁ n h0A1K _ (isPerfect_relocalizeDerivedFunctor_obj B hA hA₀ g X.1 X.2 E hE)
  refine isPerfect_of_iso B _ hA₀ hP ((derivedModulePushforward B _ hA₀ _).mapIso
    (((smallEtaleDerivedTensor B _ hA₀ _).obj _).mapIso ?_))
  exact (DerivedCategory.singleFunctor _ n).mapIso eF.symm ≪≫
    ((relocalizeDerivedFunctorSingleIso B hA hA₀ g X.1 X.2 n).app F).symm

end SpecBase

section SchemeBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A : Type u} [CommRing A]
  {hA : B.Contains (Spec (.of A))}

/-- **Stacks 0A1P over the spectrum of a ring of the site, for a module in one degree.** Let
`f : X ⟶ h_{(Spec A, g)}` be of finite presentation, `E` perfect on `X` and `ℱ` an
`𝒪_X`-module of finite presentation, flat over `h_{(Spec A, g)}` with support proper over it.
Granting the base change result of Stacks 0A1K, `Rf_*(E ⊗^L ℱ[n])` is perfect. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_single_of_schemeBase
    (h0A1K : BaseChangeIsoStatement B) (g : B.obj hA ⟶ B.obj hS) {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace (Over.mk g)) (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver B S hS X.2 f.hom F)
    (hsupp : HasProperSupport B S hS X.2 (schemeSpace (Over.mk g)).2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj F)) (n : ℤ) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS (schemeSpace (Over.mk g)).1
        (schemeSpace (Over.mk g)).2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj
          ((DerivedCategory.singleFunctor _ n).obj F))) := by
  obtain ⟨XT, e, he⟩ := exists_relocalizeSpace_iso B hA hS g X f
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1
  have hfT := (isFinitePresentation_iff_of_relocalizeSpace_iso e he).1 hf
  obtain ⟨hFT, hFTflat, hFTsupp⟩ :=
    (coefficientConditions_iff_of_relocalizeSpace_iso e he hft F).1 ⟨hF, hflat, hsupp⟩
  let ρ := relocalizeDerivedEquivalence B hA hS g XT.1 XT.2
  let ET := ρ.inverse.obj ((smallEtaleDerivedModulePullback B S hS e.hom).obj E)
  have hET : RingedSite.IsPerfect (smallEtaleRingedSite B _ hA XT.1 XT.2) ET :=
    (isPerfect_relocalizeDerivedEquivalence_inverse_obj_iff B hA hS g XT.1 XT.2 _).2
      (isPerfect_smallEtaleDerivedModulePullback e.hom E hE)
  have hT := isPerfect_derivedModulePushforward_derivedTensor_single_of_specBase h0A1K
    (toFinalHom B hA XT) hfT ET hET (relocalizeSpaceModule e F) hFT hFTflat hFTsupp n
  have hρ := isPerfect_relocalizeDerivedFunctor_obj B hA hS g _ _ _ hT
  let bh := relocalizeBaseHom B hA hS g
  have : IsIso bh.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map bh))
  have sq : IsPullback e.hom (relocalizeHom B hA hS g (toFinalHom B hA XT)) f bh :=
    IsPullback.of_horiz_isIso ⟨he⟩
  refine isPerfect_of_iso B S hS (isPerfect_of_isPerfect_smallEtaleDerivedModulePullback_of_iso
    (asIso bh) _ (isPerfect_of_iso B S hS hρ ?_))
    ((derivedModulePushforward B S hS f).mapIso (((smallEtaleDerivedTensor B S hS X).obj E).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ n).app F).symm))
  have := modulePullback_additive e.hom
  refine relocalizeDerivedPushforwardObjIso B hA hS g (toFinalHom B hA XT) _ ≪≫
    (derivedModulePushforward B S hS _).mapIso
      (relocalizeDerivedTensorObjIso B hA hS g XT.1 XT.2 ET _ ≪≫
        ((smallEtaleDerivedTensor B S hS _).mapIso (ρ.counitIso.app _)).app _ ≪≫
        ((smallEtaleDerivedTensor B S hS _).obj _).mapIso
          ((relocalizeDerivedFunctorSingleIso B hA hS g XT.1 XT.2 n).app _ ≪≫
            (DerivedCategory.singleFunctor _ n).mapIso
              ((relocalizeModulesEquivalence B hA hS g XT.1 XT.2).counitIso.app _) ≪≫
            ((DerivedCategory.singleFunctorIsoCompQ _ n).app _) ≪≫
            DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
              (modulePullback B S hS e.hom) (ComplexShape.up ℤ) n).app F).symm)) ≪≫
    (derivedTensorPushforwardEtaleBaseChangeIso sq (isEtale_of_isIso B S hS bh.hom)
      (Functor.relativelyRepresentable.of_isIso yoneda bh.hom) E _).symm

end SchemeBase

section Main

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

variable (V : SmallEtale B S hS Y.1)
  [IsAffine ((SmallEtale.toOver B S hS Y.1).obj V).left.obj]

/-- The spectrum of the ring of global functions of an affine étale chart is in the site. -/
theorem contains_affineChartSpec :
    B.Contains (Spec (.of Γ(((SmallEtale.toOver B S hS Y.1).obj V).left.obj, ⊤))) :=
  lt_of_eq_of_lt (Scheme.size_congr ((SmallEtale.toOver B S hS Y.1).obj V).left.obj.isoSpec).symm
    ((SmallEtale.toOver B S hS Y.1).obj V).left.property

/-- The spectrum of the ring of global functions of an affine étale chart, over `S`. -/
noncomputable def affineChartSpecBase :
    B.obj (contains_affineChartSpec V) ⟶ B.obj hS :=
  (ObjectProperty.isoMk _ ((SmallEtale.toOver B S hS Y.1).obj V).left.obj.isoSpec.symm).hom ≫
    ((SmallEtale.toOver B S hS Y.1).obj V).hom

/-- **An affine étale chart, read over the spectrum of its ring of global functions**: the
algebraic space `h_{(Spec Γ(V), g)}` is isomorphic to the chart. -/
noncomputable def affineChartSpecIso :
    schemeSpace (Over.mk (affineChartSpecBase V)) ≅ chartSpace B S hS Y V :=
  (schemeSpaceFunctor B S hS).mapIso (Over.isoMk
    (ObjectProperty.isoMk _ ((SmallEtale.toOver B S hS Y.1).obj V).left.obj.isoSpec.symm) rfl)

omit [IsAffine ((SmallEtale.toOver B S hS Y.1).obj V).left.obj] in
/-- **Stacks 0A1P, the perfectness, granting the base change result of Stacks 0A1K.** For
`f : X ⟶ Y` of finite presentation, `E` perfect and `𝒢^•` a bounded complex of modules of finite
presentation, flat over `Y` with support proper over `Y`, `Rf_*(E ⊗^L 𝒢^•)` is perfect. -/
theorem isPerfect_derivedModulePushforward_derivedTensor_of_baseChangeIso
    (h0A1K : BaseChangeIsoStatement B) (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : {i : ℤ | ¬ IsZero (G.X i)}.Finite) (hGfp : ∀ n, (G.X n).IsFinitePresentation)
    (hGflat : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hGsupp : ∀ n, HasProperSupport B S hS X.2 Y.2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj (G.X n))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) := by
  have hft := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1
  refine isPerfect_derivedModulePushforward_derivedTensor_of_single f E G hGb fun n => ?_
  refine isPerfect_of_forall_isAffineChart_smallEtaleDerivedModulePullback _ fun V hV => ?_
  have : IsAffine ((SmallEtale.toOver B S hS Y.1).obj V).left.obj := hV
  let h := affineChartSpecIso V
  let j := h.hom ≫ chartToSpace B S hS Y V
  have hj : IsEtale B S hS j.hom :=
    isEtale_comp B S hS (isEtale_of_isIso B S hS h.hom.hom) (isEtale_chartToSpace B S hS Y V)
  have hjrep : yoneda.relativelyRepresentable j.hom :=
    MorphismProperty.comp_mem _ _ _ (Functor.relativelyRepresentable.of_isIso yoneda h.hom.hom)
      (relativelyRepresentable_chartToSpace B S hS Y V)
  refine isPerfect_of_isPerfect_smallEtaleDerivedModulePullback_of_iso h _ ?_
  have sq := IsPullback.of_hasPullback f j
  have hfp' : IsFinitePresentation B S hS (pullback.snd f j).hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hf
  obtain ⟨hF₁, hF₂, hF₃⟩ := modulePullback_coefficient_conditions sq hft (G.X n) (hGfp n)
    (hGflat n) (hGsupp n)
  have hP := isPerfect_derivedModulePushforward_derivedTensor_single_of_schemeBase h0A1K
    (affineChartSpecBase V) (pullback.snd f j) hfp'
    ((smallEtaleDerivedModulePullback B S hS (pullback.fst f j)).obj E)
    (isPerfect_smallEtaleDerivedModulePullback _ E hE) _ hF₁ hF₂ hF₃ n
  have := modulePullback_additive (pullback.fst f j)
  refine isPerfect_of_iso B S hS hP ?_
  exact (derivedModulePushforward B S hS _).mapIso
      (((smallEtaleDerivedTensor B S hS _).obj _).mapIso
      (((DerivedCategory.singleFunctorIsoCompQ _ n).app _) ≪≫
        DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback B S hS (pullback.fst f j)) (ComplexShape.up ℤ) n).app (G.X n)).symm)) ≪≫
    (derivedTensorPushforwardEtaleBaseChangeIso sq hj hjrep E _).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS j).mapIso ((derivedModulePushforward B S hS f).mapIso
      (((smallEtaleDerivedTensor B S hS X).obj E).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ _ n).app (G.X n)).symm)) ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS h.hom (chartToSpace B S hS Y V)).app _).symm

end Main

end AlgebraicGeometry.Space
