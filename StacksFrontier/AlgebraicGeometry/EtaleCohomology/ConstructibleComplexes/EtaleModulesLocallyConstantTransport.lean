module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafCtf
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite

/-!
# Local constancy with finite projective values on the two small étale sites

A sheaf of modules on Mathlib's small étale site of `X` is locally constant with finite projective
values exactly when its transport `Stacks.EtaleCohomology.etaleModulesToSmallEtale` to the small
étale site of Stacks 021B is. Hence such a sheaf is constructible flat, and placed in one degree it
lies in `D_ctf(X_étale, Λ)`, for an arbitrary, possibly noncommutative, ring `Λ`.

## Main results

* `Stacks.ConstantSheaf.isConstantFiniteProjectiveOver_sheafPushforwardContinuous_iff` and
  `Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_iff_sheafPushforwardContinuous`: along a
  dense subsite inclusion `G : (C, J) ⥤ (D, K)`, restriction of sheaves of modules preserves and
  reflects constancy with finite projective value over an object, and local constancy with finite
  projective values.
* `Stacks.EtaleCohomology.isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_iff`: the case
  of the size-bounded small étale site of Stacks 021B inside Mathlib's small étale site.
* `Stacks.EtaleCohomology.isCtf_singlePlus_of_isFiniteProjectiveLocallyConstant`: such a sheaf in
  degree zero lies in `D_ctf(X_étale, Λ)`.

## Implementation notes

The proof is that of `Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_sheafPushforwardContinuous`
for sheaves of sets, with module coefficients. Over an object `Y` of `C` the localization
`Over.post G` is again a dense subsite inclusion (`Stacks.Sites.overPost_isDenseSubsite`), so
restriction along it is an equivalence of the sheaf categories of the two slices which commutes
with the constant sheaf functors (`CategoryTheory.equivCommuteConstant`), and the restriction of
the localized sheaf `F|_{G Y}` along `Over.post G` is the localization at `Y` of the restricted
sheaf, on the nose. The covering conditions are then transported through the trivializing sieves
`Stacks.ConstantSheaf.finProjTrivSieve`, by the cover-lifting property of `G` in one direction and
by cover density in the other.

No hypothesis on `X` is needed: neither quasi-compactness nor quasi-separatedness nor a Noetherian
condition enters, because the comparison is one of sites,
`AlgebraicGeometry.SmallEtale.toEtaleSite` being a dense subsite inclusion for every scheme of the
big étale site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w c r

namespace Stacks.ConstantSheaf

variable {C : Type c} [Category.{v} C] {D : Type c} [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsDenseSubsite J K] (R : Type r) [Ring R]
  [HasLimitsOfSize.{v, max c v} (ModuleCat.{w} R)]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
  [∀ V : D, HasWeakSheafify (K.over V) (ModuleCat.{w} R)]

/-- **Constancy with finite projective value over a slice is transported by restriction along a
dense subsite inclusion `G`.** The restriction of `F` is constant over `Y` exactly when `F` is
constant over `G Y`, with the same value. -/
public theorem isConstantFiniteProjectiveOver_sheafPushforwardContinuous_iff (Y : C)
    (F : Sheaf K (ModuleCat.{w} R)) :
    IsConstantFiniteProjectiveOver J R Y
        ((G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj F) ↔
      IsConstantFiniteProjectiveOver K R (G.obj Y) F := by
  have := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) G Y
  let e := Functor.IsDenseSubsite.sheafEquiv (J.over Y) (K.over (G.obj Y))
    (Over.post (X := Y) G) (ModuleCat.{w} R)
  have hc := equivCommuteConstant (J.over Y) (ModuleCat.{w} R) (K.over (G.obj Y))
    (Over.post (X := Y) G) (Over.mkIdTerminal (X := Y)) (overPostMkIdIsTerminal G Y)
  have hc' := equivCommuteConstant' (J.over Y) (ModuleCat.{w} R) (K.over (G.obj Y))
    (Over.post (X := Y) G) (Over.mkIdTerminal (X := Y)) (overPostMkIdIsTerminal G Y)
  let r : ((Over.post (X := Y) G).sheafPushforwardContinuous (ModuleCat.{w} R) (J.over Y)
        (K.over (G.obj Y))).obj ((K.overPullback (ModuleCat.{w} R) (G.obj Y)).obj F) ≅
      (J.overPullback (ModuleCat.{w} R) Y).obj
        ((G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj F) :=
    Iso.refl _
  constructor
  · rintro ⟨E, hfin, hproj, ⟨φ⟩⟩
    exact ⟨E, hfin, hproj,
      ⟨(hc.app E).symm ≪≫ e.functor.mapIso (φ ≪≫ r.symm) ≪≫ e.counitIso.app _⟩⟩
  · rintro ⟨E, hfin, hproj, ⟨φ⟩⟩
    exact ⟨E, hfin, hproj, ⟨hc'.app E ≪≫ e.inverse.mapIso φ ≪≫ r⟩⟩

/-- **Local constancy with finite projective values is detected on a dense subsite.** A sheaf of
modules on `(D, K)` is locally constant with finite projective values exactly when its restriction
along the dense subsite inclusion `G` is. -/
public theorem isFiniteProjectiveLocallyConstant_iff_sheafPushforwardContinuous
    (F : Sheaf K (ModuleCat.{w} R)) :
    IsFiniteProjectiveLocallyConstant R K F ↔
      IsFiniteProjectiveLocallyConstant R J
        ((G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj F) := by
  have : G.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K G
  have : ∀ (E : Type c) [Category.{v} E] (U V : E) (f : V ⟶ U) (P : (Over V)ᵒᵖ ⥤ ModuleCat.{w} R)
      (Y : (Over U)ᵒᵖ), HasLimit (StructuredArrow.proj Y (Over.map f).op ⋙ P) :=
    fun _ _ _ _ _ _ _ =>
      @HasLimitsOfShape.has_limit _ _ _ _ (HasLimitsOfSize.has_limits_of_shape _) _
  rw [isFiniteProjectiveLocallyConstant_iff_trivSieve_mem K R,
    isFiniteProjectiveLocallyConstant_iff_trivSieve_mem J R]
  constructor
  · intro hF U
    refine J.superset_covering ?_ (G.cover_lift J K (hF (G.obj U)))
    intro W g hg
    exact (isConstantFiniteProjectiveOver_sheafPushforwardContinuous_iff G R W F).2 hg
  · intro hF V
    have himage : ∀ W : C, finProjTrivSieve K R F (G.obj W) ∈ K (G.obj W) := by
      intro W
      refine K.superset_covering ?_ ((G.functorPushforward_mem_iff J K).2 (hF W))
      rintro Z h ⟨W', g, k, hg, rfl⟩
      exact ((isConstantFiniteProjectiveOver_sheafPushforwardContinuous_iff G R W' F).1
        hg).restrict K R k
    refine K.transitive (G.is_cover_of_isCoverDense K V) _ ?_
    rintro Z f ⟨⟨W, lift, -, -⟩⟩
    exact K.superset_covering (fun _ _ hh => hh) (K.pullback_stable lift (himage W))

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u})

/-- **Local constancy with finite projective values is the same on the two small étale sites.** A
sheaf of `Λ`-modules on Mathlib's small étale site of `X` is locally constant with finite
projective values exactly when its transport to the small étale site of Stacks 021B is. No
hypothesis on `X` is needed. -/
public theorem isFiniteProjectiveLocallyConstant_etaleModulesToSmallEtale_iff (X : B.Scheme)
    (Λ : Type r) [Ring Λ] (F : EtaleModules.{u, r} Λ X.obj) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B X.obj X.property) ((etaleModulesToSmallEtale B X Λ).obj F) ↔
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.obj.smallEtaleTopology F :=
  (Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_iff_sheafPushforwardContinuous
    (SmallEtale.toEtaleSite B X.obj X.property) Λ F).symm

/-- **A locally constant sheaf with finite projective values in degree zero lies in
`D_ctf(X_étale, Λ)`**, for an arbitrary, possibly noncommutative, ring `Λ`. -/
public theorem isCtf_singlePlus_of_isFiniteProjectiveLocallyConstant {Λ : Type r} [Ring Λ]
    (X : B.Scheme) (F : EtaleModules.{u, r} Λ X.obj)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.obj.smallEtaleTopology F) :
    IsCtf B X Λ (DerivedCategory.Q.obj
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F).obj) := by
  refine IsRepresentedByConstructibleFlatEtaleComplex.isCtf B Λ ?_
  let C := (HomologicalComplex.single (EtaleModules.{u, r} Λ X.obj) (ComplexShape.up ℤ) 0).obj F
  refine ⟨C, 0, 0, inferInstanceAs (CochainComplex.IsStrictlyGE C 0),
    inferInstanceAs (CochainComplex.IsStrictlyLE C 0), fun i => ?_, ⟨Iso.refl _⟩⟩
  by_cases hi : i = 0
  · subst hi
    exact IsConstructibleFlatEtaleModule.of_iso B X Λ
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm
      (isConstructibleFlatEtaleModule_of_isFiniteProjectiveLocallyConstant B X Λ F hF)
  · exact isConstructibleFlatEtaleModule_of_isZero B Λ X
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

end Stacks.EtaleCohomology

end
