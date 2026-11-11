module
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftFunctorial
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunctionUnconditional
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafGenerationByQCQS
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantPresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerived
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.QuasiFiniteShriek
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.QuasiFiniteShriek

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftPushforward
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGenerationUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShriekGeneratorConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.FinitePushforwardConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceCompositionDerived
public import StacksFrontier.AlgebraicGeometry.FiniteFactorization.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image with compact support preserves constructibility

Let `Λ` be a Noetherian ring and let `f : X ⟶ Y` be a morphism of a big étale site which is
locally quasi-finite and of finite presentation. The direct image with compact support `f_!` with
coefficients in `Λ` (Stacks 0F5N) carries constructible sheaves of `Λ`-modules on `X_étale` to
constructible sheaves on `Y_étale`, and `D_c(X_étale, Λ)` into `D_c(Y_étale, Λ)` (Stacks 0GK3).

All names are in the namespace `Stacks.EtaleCohomology`.

## Main definitions

* `moduleFShriekDerivedCompHomologyFunctorIsoUniv`: degree-`i` cohomology commutes with the
  derived functor of a `Λ`-linear lift of `f_!`.
* `moduleExtensionByZeroIsoFShriekMod`: extension by zero along an étale morphism is the
  `Λ`-linear direct image with compact support.

## Main results

* `isConstructibleModuleSheaf_fShriekMod`: `f_!` of a constructible sheaf of `Λ`-modules is
  constructible.
* `isConstructible_moduleFShriekDerivedFunctor_general`: Stacks 0GK3, `f_!` sends
  `D_c(X_étale, Λ)` into `D_c(Y_étale, Λ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.SmallEtale

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

section

attribute [local instance] AlgebraicGeometry.SmallEtale.hasSheafify_moduleSheaf_over

variable {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]

/-- Degree-`i` cohomology commutes with the functor `f_!` of Stacks 0F5N: a `Λ`-linear lift of
the direct image with compact support is exact, so the induced functor on unbounded derived
categories is the termwise one and `Hⁱ(f_! K) ≅ f_!(Hⁱ K)`, naturally in `K`, as in the first
sentence of the proof of Stacks 0GK3. -/
public def moduleFShriekDerivedCompHomologyFunctorIsoUniv
    (fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ)
    (hlift : fShriekMod ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f) (i : ℤ) :
    moduleFShriekDerivedFunctor B Λ f fShriekMod hlift ⋙
        DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r} B Y Λ) i ≅
      DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r} B X Λ) i ⋙ fShriekMod :=
  let := additive_of_forgetModuleSheafIso B Λ f fShriekMod hlift
  let := preservesFiniteLimits_of_forgetModuleSheafIso B Λ f fShriekMod hlift
  let := isLeftAdjoint_of_forgetModuleSheafIso B Λ f fShriekMod hlift
  let : PreservesFiniteColimits fShriekMod := ⟨fun _ _ _ => inferInstance⟩
  fShriekMod.mapDerivedCategoryCompHomologyFunctorIso i

end

attribute [local instance 2000] smallEtaleHasSheafifyModuleMax Sheaf.instHasColimitsOfShape
  Sheaf.instHasFiniteCoproducts

section Sheaves

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- Extension by zero of sheaves of `Λ`-modules along an étale `j : U ⟶ X` (Stacks 03S3) is the
`Λ`-linear direct image with compact support along `j`: both are left adjoint to restriction
along `j`, the second because the abelian `j_!` of Stacks 0F6R is extension by zero (Stacks 0F6Q,
`AlgebraicGeometry.SmallEtale.fShriekAdjunctionRestriction`) and the lift of a left adjoint of
the abelian restriction is a left adjoint of the `Λ`-linear one. -/
public def moduleExtensionByZeroIsoFShriekMod (X : B.Scheme) (U : SmallEtale B X.obj X.property) :
    moduleExtensionByZero.{u, u + 1} B X.obj X.property U Λ ≅
      fShriekMod.{u, u, u + 1} B Λ U.obj.hom :=
  have := smallEtalePostcompose_isContinuous B X.obj X.property U
  Stacks.ModuleCatLift.leftAdjointIsoModuleLift.{u + 1} Λ
    (smallEtalePostcompose B X.obj X.property U) _ _
    (moduleExtensionByZeroAdjunction B X.obj X.property U Λ)
    (fShriekAdjunctionRestriction B X.obj X.property U)

/-- **The separated case over an affine base.** For a locally quasi-finite morphism of finite
presentation `h : U ⟶ V` between affine objects of a big étale site, `h_!` of the constant sheaf
with value `Λ` is constructible. Zariski's main theorem (Stacks 0F2N) factors `h` as an open
immersion `j : U ⟶ T` followed by a finite morphism of finite presentation `π : T ⟶ V`; then
`h_! = π_* ∘ j_!` (Stacks 0F52), `j_!Λ` is constructible by Stacks 03S8 and `π_*` preserves
constructibility by Stacks 095R. -/
private theorem isConstructibleModuleSheaf_fShriekMod_constant_of_isAffine {U V : B.Scheme}
    (h : U ⟶ V) [LocallyQuasiFinite (B.inclusion.map h)]
    [LocallyOfFinitePresentation (B.inclusion.map h)] [IsAffine U.obj] [IsAffine V.obj] :
    letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U Λ
    IsConstructibleModuleSheaf B V Λ ((fShriekMod.{u, u, u + 1} B Λ h).obj
      ((constantSheaf (SmallEtale.topology B U.obj U.property) (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (ULift.{u + 1} Λ)))) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U Λ
  have : IsAffine (B.inclusion.obj U) := ‹IsAffine U.obj›
  have : IsAffine (B.inclusion.obj V) := ‹IsAffine V.obj›
  have : IsSeparated (B.inclusion.map h) := IsSeparated.of_isAffineHom _
  obtain ⟨T, j, π, hj, hjqc, hπ, hπfp, hfac⟩ :=
    Stacks.FiniteFactorization.exists_isOpenImmersion_isFinite_finitePresentation_factorization
      (B.inclusion.map h)
  have : IsOpenImmersion j := hj
  have : IsFinite π := hπ
  have hT : B.Contains T :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact π V.property
  let Tb : B.Scheme := B.obj T hT
  let jb : U ⟶ Tb := ObjectProperty.homMk j
  let πb : Tb ⟶ V := ObjectProperty.homMk π
  have : IsOpenImmersion (B.inclusion.map jb) := ‹IsOpenImmersion j›
  have : IsFinite (B.inclusion.map πb) := ‹IsFinite π›
  have : IsAffine Tb.obj := isAffine_of_isAffineHom π
  have hhb : h = jb ≫ πb := ObjectProperty.hom_ext _ hfac
  subst hhb
  let W := SmallEtale.ofEtaleHom B jb
  have : IsOpenImmersion (B.inclusion.map W.obj.hom) := ‹IsOpenImmersion j›
  have := smallEtalePostcompose_isContinuous B Tb.obj Tb.property W
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B πb
  have := abelianExtensionByZero_additive B Tb.obj Tb.property W
  -- Stacks 0F52 for sheaves of `Λ`-modules
  let Φ : fShriekMod.{u, u, u + 1} B Λ (jb ≫ πb) ≅
      moduleExtensionByZero.{u, u + 1} B Tb.obj Tb.property W Λ ⋙
        B.smallPushforward πb (ModuleCat.{u + 1} Λ) :=
    Stacks.ModuleCatLift.moduleLiftNatIso.{u + 1} Λ _ _ _ _
        (fShriekFunctorIsoCompactification B πb W) ≪≫
      eqToIso (Stacks.ModuleCatLift.moduleLift_comp.{u + 1} Λ _ _ _ _ _) ≪≫
      Functor.isoWhiskerRight (Stacks.ModuleCatLift.leftAdjointIsoModuleLift.{u + 1} Λ
          (smallEtalePostcompose B Tb.obj Tb.property W) _ _
          (moduleExtensionByZeroAdjunction B Tb.obj Tb.property W Λ)
          (abelianExtensionByZeroAdjunction B Tb.obj Tb.property W)).symm _ ≪≫
      Functor.isoWhiskerLeft _
        (Stacks.ModuleCatLift.sheafPushforwardContinuousIsoModuleLift.{u + 1} Λ
          (AlgebraicGeometry.smallEtaleBaseChange B πb) _ _).symm
  have hU : CompactSpace W.obj.left.obj := inferInstanceAs (CompactSpace U.obj)
  have hU' : QuasiSeparatedSpace W.obj.left.obj := inferInstanceAs (QuasiSeparatedSpace U.obj)
  refine isConstructibleModuleSheaf_congr B Λ V (Φ.app _).symm ?_
  exact isConstructibleModuleSheaf_smallPushforward_of_isFinite B πb Λ hπfp _
    (isConstructibleModuleSheaf_moduleShriekConstant.{u, u + 1} B Tb Λ W)

/-- The generators `j_{U!}Λ` of Stacks 095N, at an affine étale object `U`, have constructible
image under `f_!` when the target of `f` is affine: `f_! j_{U!}Λ = (f ∘ j_U)_! Λ` by Stacks 0F6T,
and `f ∘ j_U` is a morphism between affine schemes. -/
private theorem isConstructibleModuleSheaf_fShriekMod_moduleShriekConstant {X Y : B.Scheme}
    (f : X ⟶ Y) [LocallyQuasiFinite (B.inclusion.map f)]
    [LocallyOfFinitePresentation (B.inclusion.map f)] [IsAffine Y.obj]
    (U : SmallEtale B X.1 X.property) (hU : SmallEtale.IsAffine B X.1 X.property U) :
    IsConstructibleModuleSheaf B Y Λ ((fShriekMod.{u, u, u + 1} B Λ f).obj
      (moduleShriekConstant.{u, u + 1, u + 1} B X Λ U)) := by
  have : IsAffine U.obj.left.obj := hU
  have : Etale (B.inclusion.map U.obj.hom) := U.property
  have : LocallyOfFinitePresentation (B.inclusion.map (U.obj.hom ≫ f)) := by
    rw [Functor.map_comp]; infer_instance
  have : LocallyQuasiFinite (B.inclusion.map (U.obj.hom ≫ f)) := by
    rw [Functor.map_comp]; infer_instance
  let := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B U.obj.left Λ
  let c := (constantSheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (ULift.{u + 1} Λ))
  have e : (fShriekMod.{u, u, u + 1} B Λ f).obj
      ((moduleExtensionByZero.{u, u + 1} B X.obj X.property U Λ).obj c) ≅
      (fShriekMod.{u, u, u + 1} B Λ (U.obj.hom ≫ f)).obj c :=
    (fShriekMod.{u, u, u + 1} B Λ f).mapIso
        ((moduleExtensionByZeroIsoFShriekMod B Λ X U).app c) ≪≫
      ((fShriekModCompIso.{u, u, u + 1} B Λ U.obj.hom f).app c).symm
  exact isConstructibleModuleSheaf_congr B Λ Y e.symm
    (isConstructibleModuleSheaf_fShriekMod_constant_of_isAffine B Λ (U.obj.hom ≫ f))

/-- **The case of an affine base.** Let `f : X ⟶ Y` be locally quasi-finite and of finite
presentation with `Y` affine, so that `X` is quasi-compact and quasi-separated. A constructible
`ℱ` on `X` is the cokernel of a map between finite direct sums of sheaves `j_{U!}Λ` with `U` affine
(Stacks 095N). Since `f_!` is right exact it is the cokernel of the images, and
`f_! j_{U!}Λ = (f ∘ j_U)_! Λ` (Stacks 0F6T) with `f ∘ j_U` a morphism between affine schemes; so
the separated case applies, and constructible sheaves form a weak Serre class (Stacks 03RZ). -/
private theorem isConstructibleModuleSheaf_fShriekMod_of_isAffine {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)] [IsAffine Y.obj]
    (G : ModuleSheaf.{u, u, u + 1} B X Λ) (hG : IsConstructibleModuleSheaf B X Λ G) :
    IsConstructibleModuleSheaf B Y Λ ((fShriekMod.{u, u, u + 1} B Λ f).obj G) := by
  have : IsAffine (B.inclusion.obj Y) := ‹IsAffine Y.obj›
  have : CompactSpace (B.inclusion.obj X) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map f)
  have : QuasiSeparatedSpace (B.inclusion.obj X) :=
    quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map f)
  have : CompactSpace X.1 := ‹CompactSpace (B.inclusion.obj X)›
  have : QuasiSeparatedSpace X.1 := ‹QuasiSeparatedSpace (B.inclusion.obj X)›
  let P : ObjectProperty (ModuleSheaf.{u, u, u + 1} B Y Λ) :=
    fun F => IsConstructibleModuleSheaf B Y Λ F
  have : P.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B Y Λ
  have := CategoryTheory.ObjectProperty.isClosedUnderFiniteProducts_of_isWeakSerreClass P
  have : HasFiniteBiproducts (ModuleSheaf.{u, u, u + 1} B Y Λ) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  let := isLeftAdjoint_of_forgetModuleSheafIso B Λ f (fShriekMod.{u, u, u + 1} B Λ f)
    (fShriekModForgetIso.{u, u, u + 1} B Λ f)
  obtain ⟨n, m, U, V, hU, hV, φ, ⟨e⟩⟩ :=
    (isConstructibleModuleSheaf_iff_hasFiniteAffineShriekPresentation B X Λ G).1 hG
  let eG : cokernel φ ≅ G :=
    (sheafToPresheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} Λ)).preimageIso
      (e ≪≫ Functor.isoWhiskerLeft G.obj (ModuleCat.uliftFunctorSelfIso.{u + 1, u + 1} Λ) ≪≫
        G.obj.rightUnitor)
  let F := fShriekMod.{u, u, u + 1} B Λ f
  have hcop : ∀ {n : ℕ} (W : Fin n → SmallEtale B X.1 X.property),
      (∀ i, SmallEtale.IsAffine B X.1 X.property (W i)) →
      P (F.obj (∐ fun i => moduleShriekConstant.{u, u + 1, u + 1} B X Λ (W i))) := fun W hW =>
    P.prop_of_iso (PreservesCoproduct.iso F _).symm <|
      P.prop_of_iso ((biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _) <|
        P.prop_product fun i =>
          isConstructibleModuleSheaf_fShriekMod_moduleShriekConstant B Λ f _ (hW i)
  exact P.prop_of_iso (F.mapIso eG) (P.prop_of_iso (PreservesCokernel.iso F φ).symm
    (P.prop_cokernel _ (hcop V hV) (hcop U hU)))

/-- **The sheaf-level form of Stacks 0GK3.** Let `Λ` be a Noetherian ring and let `f : X ⟶ Y` be a
morphism of a big étale site which is locally quasi-finite and of finite presentation. If `ℱ` is a
constructible sheaf of `Λ`-modules on `X_étale`, then `f_!ℱ` is a constructible sheaf of
`Λ`-modules on `Y_étale`, where `f_!` is `AlgebraicGeometry.SmallEtale.fShriekMod`.

The question is local on `Y` (Stacks 095F), and `f_!` commutes with restriction to an open of `Y`
(Stacks 0F5J); so `Y` may be taken affine, in which case
`isConstructibleModuleSheaf_fShriekMod_of_isAffine` applies. -/
public theorem isConstructibleModuleSheaf_fShriekMod {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
    [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)]
    (G : ModuleSheaf.{u, u, u + 1} B X Λ) (hG : IsConstructibleModuleSheaf B X Λ G) :
    IsConstructibleModuleSheaf B Y Λ ((fShriekMod.{u, u, u + 1} B Λ f).obj G) := by
  obtain ⟨I, W, j, hj, hWaff, hcover⟩ := exists_affine_openCover_of_bigEtaleSite B Y
  refine isConstructibleModuleSheaf_of_openCover B Λ Y _ W j hj hcover fun k => ?_
  have : IsAffine (W k).obj := hWaff k
  have : IsOpenImmersion (B.inclusion.map (j k)) := hj k
  let sq := IsPullback.of_hasPullback f (j k)
  have : LocallyQuasiFinite (B.inclusion.map (pullback.snd f (j k))) :=
    MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
  have : LocallyOfFinitePresentation (B.inclusion.map (pullback.snd f (j k))) :=
    MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
  have : QuasiCompact (B.inclusion.map (pullback.snd f (j k))) :=
    MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
  have : QuasiSeparated (B.inclusion.map (pullback.snd f (j k))) :=
    MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance
  let A := ModuleCat.{u + 1} Λ
  let pullIso : ∀ {S T : B.Scheme} (q : T ⟶ S),
      (AlgebraicGeometry.smallEtaleBaseChange B q).sheafPullback A
          (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property) ≅
        Stacks.ModuleCatLift.moduleLift.{u + 1} Λ (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property) (abPullback.{u, u + 1} B q) := fun q =>
    have := additive_abPullback.{u, u + 1} B q
    Stacks.ModuleCatLift.leftAdjointIsoModuleLift.{u + 1} Λ
      (AlgebraicGeometry.smallEtaleBaseChange B q) _ _
      ((AlgebraicGeometry.smallEtaleBaseChange B q).sheafAdjunctionContinuous A _ _)
      (abPullbackAdjunction.{u, u + 1} B q)
  -- Stacks 0F5J for sheaves of `Λ`-modules
  let bcF : fShriekMod.{u, u, u + 1} B Λ f ⋙
        (AlgebraicGeometry.smallEtaleBaseChange B (j k)).sheafPullback A
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B (W k).obj (W k).property) ≅
      (AlgebraicGeometry.smallEtaleBaseChange B (pullback.fst f (j k))).sheafPullback A
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (pullback f (j k)).obj (pullback f (j k)).property) ⋙
        fShriekMod.{u, u, u + 1} B Λ (pullback.snd f (j k)) :=
    Functor.isoWhiskerLeft _ (pullIso (j k)) ≪≫
      eqToIso (Stacks.ModuleCatLift.moduleLift_comp.{u + 1} Λ _ _ _
        (fShriekFunctor.{u, u + 1} B f) (abPullback.{u, u + 1} B (j k))).symm ≪≫
      Stacks.ModuleCatLift.moduleLiftNatIso.{u + 1} Λ _ _ _ _
        (fShriekBaseChangeNatIso.{u} B (pullback.fst f (j k)) (pullback.snd f (j k)) f (j k)
          sq) ≪≫
      eqToIso (Stacks.ModuleCatLift.moduleLift_comp.{u + 1} Λ _ _ _
        (abPullback.{u, u + 1} B (pullback.fst f (j k)))
        (fShriekFunctor.{u, u + 1} B (pullback.snd f (j k)))) ≪≫
      Functor.isoWhiskerRight (pullIso (pullback.fst f (j k))).symm _
  exact isConstructibleModuleSheaf_congr B Λ (W k) (bcF.app G).symm
    (isConstructibleModuleSheaf_fShriekMod_of_isAffine B Λ (pullback.snd f (j k)) _
      (isConstructibleModuleSheaf_pullback B Λ (pullback.fst f (j k)) G hG))

end Sheaves

section

variable {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyQuasiFinite (B.inclusion.map f)] [LocallyOfFinitePresentation (B.inclusion.map f)]
  [QuasiCompact (B.inclusion.map f)] [QuasiSeparated (B.inclusion.map f)]
  (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 0GK3.** Let `Λ` be a Noetherian ring and let `f : X ⟶ Y` be a morphism of schemes
which is locally quasi-finite and of finite presentation. The functor
`f_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of Stacks 0F5N, induced by the direct image with compact
support `AlgebraicGeometry.SmallEtale.fShriekMod` with coefficients in `Λ`, sends
`D_c(X_étale, Λ)` into `D_c(Y_étale, Λ)`. -/
@[stacks 0GK3 "for f locally quasi-finite and of finite presentation and Λ Noetherian, the \
  derived f_! of fShriekMod sends every K in D_c(X_étale, Λ) to D_c(Y_étale, Λ)",
  sga "4 XVII 5.3.6" "Quasi-finite case"]
public theorem isConstructible_moduleFShriekDerivedFunctor_general
    (K : DerivedCategory (ModuleSheaf.{u, u, u + 1} B X Λ)) (hK : IsConstructible B X Λ K) :
    IsConstructible B Y Λ ((moduleFShriekDerivedFunctor B Λ f (fShriekMod.{u, u, u + 1} B Λ f)
      (fShriekModForgetIso.{u, u, u + 1} B Λ f)).obj K) :=
  fun i => isConstructibleModuleSheaf_congr B Λ Y
    ((moduleFShriekDerivedCompHomologyFunctorIsoUniv B Λ f (fShriekMod.{u, u, u + 1} B Λ f)
      (fShriekModForgetIso.{u, u, u + 1} B Λ f) i).app K).symm
    (isConstructibleModuleSheaf_fShriekMod B Λ f _ (hK i))

end

end Stacks.EtaleCohomology

end
