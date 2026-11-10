module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Collapse
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ExactKernels
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.SourceChangeFunctor
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingLocal

/-!
# Acyclicity of an integral-transform kernel after a change of source

Let `R` be a commutative ring, let `X` and `Y` be schemes over `R` and let `K` be a
quasi-coherent kernel on `X ×_R Y` satisfying the two conditions of Tag 0FZH part (2): `K` is
flat over `X`, and the positive higher direct images `R^q pr_{2,*}(pr_1^*F ⊗ K)` vanish for
every quasi-coherent `F` on `X`.  This file proves that the second of those two conditions is
inherited by the inverse image of `K` along an **affine** change of source, and deduces Tag
0FZI.

## Main definitions

* `AlgebraicGeometry.baseChangeSourceOver` is `T ×_R X`, as a scheme over `R`, together with
  its two projections `AlgebraicGeometry.baseChangeSourceOverFst` to `T` and
  `AlgebraicGeometry.baseChangeSourceOverSnd` to `X`.
* `AlgebraicGeometry.baseChangeKernel` is `pr_{23}^*K`, the inverse image of `K` to
  `(T ×_R X) ×_R Y`, and `AlgebraicGeometry.baseChangeTargetMap` is `pr_{13}`.
* `AlgebraicGeometry.baseChangeOpenTargetMap`, `AlgebraicGeometry.baseChangeOpenSourceHom` and
  `AlgebraicGeometry.baseChangeOpenTripleMap` are the three open immersions
  `U ×_R Y ⟶ T ×_R Y`, `U ×_R X ⟶ T ×_R X` and `(U ×_R X) ×_R Y ⟶ (T ×_R X) ×_R Y` induced by
  an open subscheme `U` of `T`.
* `AlgebraicGeometry.PushforwardReflectsHigherDirectImageVanishingAlongAffine` is the statement
  that the vanishing of `R ⁿ (g ≫ c)_* M` implies that of `R ⁿ g_* M` for `c` affine and `M`
  quasi-coherent, and `AlgebraicGeometry.BaseChangeAcyclicityInput` is its conjunction with the
  locality on `T` of the vanishing of Tag 0FZI.

## Main results

* `AlgebraicGeometry.integralTransformIntegrandSourceChangeIso`: **affine base change (Tag
  02KG) and the projection formula (Tag 0FZE), combined on the integrand.**  For an affine
  `f : X' ⟶ X` over `R`, the integrand `pr_1^*(-) ⊗ K` evaluated at a direct image along `f`
  is the direct image along `f × id_Y` of the integrand of `(f × id_Y)^*K`.
* `AlgebraicGeometry.isZero_rightDerived_pushforward_sourceChangeKernel`: **condition (2)(b) of
  Tag 0FZH is inherited by an affine change of source.**
* `isZero_rightDerived_pushforward_baseChangeKernel_of_isAffineHom_of_quasiCompact`: **Tag 0FZI
  when `T` is affine over `R`.**
* `AlgebraicGeometry.isZero_rightDerived_pushforward_of_openCover`: **vanishing of a higher
  direct image is local on the middle scheme of a factorisation whose second leg becomes affine
  over a cover.**
* `AlgebraicGeometry.integrandBaseChangeOpenIso`: the inverse image of the integrand of
  `pr_{23}^*K` along `(U ×_R X) ×_R Y ⟶ (T ×_R X) ×_R Y` is the integrand over `U`.
* `AlgebraicGeometry.isZero_rightDerived_pushforward_baseChangeKernel`: **Tag 0FZI**: the positive
  higher direct images of `pr_{12}^*F ⊗ pr_{23}^*K` along `pr_{13}` vanish.

## Implementation notes

The triple product is associated to the left, and the tensor factors are reversed relative to
the display in the source, by the symmetry of the tensor product of sheaves of modules; this is
the convention of `AlgebraicGeometry.integralTransformIntegrand`, in which condition (2)(b) of
Tag 0FZH is already stated.  Degrees are the natural numbers indexing
`CategoryTheory.Functor.rightDerived`, again the spelling of condition (2)(b).

## References

* [Stacks Project, Tag 0FZI](https://stacks.math.columbia.edu/tag/0FZI)
* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The standard derived category of the module sheaves on a scheme. -/
local instance hasDerivedCategory_modules_sourceChange (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules :=
  HasDerivedCategory.standard _

/-! ### Preliminaries -/

/-- **The range of the base change of an open immersion.**  If the square
`a, b, i, f` is cartesian and `i` is an open immersion, then the range of `b` is the inverse
image along `f` of the range of `i`. -/
theorem opensRange_of_isPullback {P A B C : Scheme.{u}} {a : P ⟶ A} {b : P ⟶ B} {i : A ⟶ C}
    {f : B ⟶ C} (sq : IsPullback a b i f) [IsOpenImmersion i] [IsOpenImmersion b] :
    b.opensRange = f ⁻¹ᵁ i.opensRange := by
  have h : (sq.isoPullback.hom ≫ pullback.snd i f).opensRange = f ⁻¹ᵁ i.opensRange :=
    (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Scheme.Hom.opensRange_pullbackSnd i f)
  refine TopologicalSpace.Opens.ext ?_
  rw [← congrArg (fun U : B.Opens => (U : Set B)) h, Scheme.Hom.coe_opensRange,
    Scheme.Hom.coe_opensRange, sq.isoPullback_hom_snd]

/-- **Direct image along the inverse of an isomorphism is restriction along the
isomorphism.** -/
def pushforwardInvIsoRestrict {A B : Scheme.{u}} (e : A ≅ B) (M : B.Modules) :
    (Scheme.Modules.pushforward e.inv).obj M ≅ (Scheme.Modules.restrictFunctor e.hom).obj M :=
  ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app
      ((Scheme.Modules.pushforward e.inv).obj M)).symm ≪≫
    (Scheme.Modules.restrictFunctor e.hom).mapIso
      (((Scheme.Modules.pushforwardComp e.inv e.hom).app M).symm ≪≫
        (Scheme.Modules.pushforwardCongr e.inv_hom_id).app M ≪≫
        (Scheme.Modules.pushforwardId B).app M)

section TensorCongr

/-- **Isomorphic modules have isomorphic tensor functors.** -/
def tensorLeftFunctorSchemeIsoOfIso (P : Scheme.{u}) {K K' : P.Modules} (e : K ≅ K') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf)
          (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj (K)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨P.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (P.presheaf)
          (forget₂ CommRingCat RingCat) (P.ringCatSheaf.2)⟩).obj (K')) := by
  let : MonoidalCategory (PresheafOfModules.{u} P.ringCatSheaf.obj) := by
    change MonoidalCategory (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf P.presheaf))
    infer_instance
  exact Functor.isoWhiskerLeft (SheafOfModules.forget _)
    (Functor.isoWhiskerRight
      ((MonoidalCategory.curriedTensor _).mapIso ((SheafOfModules.forget _).mapIso e))
      (Stacks.SheafOfModules.TensorSheafification.sheafify P.presheaf P.ringCatSheaf.2))

end TensorCongr

/-! ### Affine base change and the projection formula, combined on the integrand -/

/-- **Affine base change and the projection formula on the integrand of an integral
transform.**  Let `f : X' ⟶ X` be an affine morphism of schemes over `R` and let `K` be a
quasi-coherent kernel on `X ×_R Y`.  Evaluating the integrand `pr_1^*(-) ⊗ K` of `K` at the
direct image of a quasi-coherent module along `f` is the same as evaluating the integrand of
`(f × id_Y)^*K` and taking the direct image along `f × id_Y` (Tags 02KG, 0FZE). -/
def integralTransformIntegrandSourceChangeIso (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    quasicoherentPushforward f.left ⋙ integralTransformIntegrand R X Y K ≅
      integralTransformIntegrand R X' Y (sourceChangeKernel R X X' Y f K) ⋙
        Scheme.Modules.pushforward (sourceChangeMap R X X' Y f) :=
  Functor.isoWhiskerRight
      (baseChangeIsoOfFunctor (isPullback_sourceChangeMap R X X' Y f)
        (SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι (fun M => M.property))
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        ⟨(pullback X.hom Y.hom).presheaf, Presheaf.isSheaf_of_isSheaf_comp _
          ((pullback X.hom Y.hom).presheaf) (forget₂ CommRingCat RingCat)
          ((pullback X.hom Y.hom).ringCatSheaf.2)⟩).obj (K.obj))) ≪≫
    Functor.isoWhiskerLeft
      ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X'.hom Y.hom) ⋙
          Scheme.Modules.pushforward (sourceChangeMap R X X' Y f))
      ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
        ((pullback X.hom Y.hom)).presheaf ((pullback X.hom Y.hom)).ringCatSheaf.2 (K.obj))) ≪≫
    projectionFormulaSourceIsoOfFunctor (sourceChangeMap R X X' Y f) K.obj K.property
      ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
        Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
      (isQuasicoherent_pullbackFst R X' Y) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((SheafOfModules.isQuasicoherent X'.left.ringCatSheaf).ι ⋙
          Scheme.Modules.pullback (pullback.fst X'.hom Y.hom))
        ((Stacks.SheafOfModules.TensorPower.tensorLeftIsoTensorRight
          ((pullback X'.hom Y.hom)).presheaf ((pullback X'.hom Y.hom)).ringCatSheaf.2
          (((Scheme.Modules.pullback (sourceChangeMap R X X' Y f)).obj K.obj)))).symm)
      (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f))

/-- The isomorphism of `AlgebraicGeometry.integralTransformIntegrandSourceChangeIso` at a
single quasi-coherent module. -/
def integralTransformIntegrandSourceChangeObjIso (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (F : Scheme.QuasicoherentModules X'.left) :
    (integralTransformIntegrand R X Y K).obj ((quasicoherentPushforward f.left).obj F) ≅
      (Scheme.Modules.pushforward (sourceChangeMap R X X' Y f)).obj
        ((integralTransformIntegrand R X' Y (sourceChangeKernel R X X' Y f K)).obj F) :=
  (integralTransformIntegrandSourceChangeIso R X X' Y f K).app F

/-! ### The collapse of the relative Leray spectral sequence at an affine first leg -/

/-- **The relative Leray spectral sequence collapses at an affine first leg.**  Let
`i : A ⟶ B` be an affine morphism of schemes, let `g : B ⟶ C` be arbitrary and let `p` be the
composite.  For a quasi-coherent module `M` on `A`, if `R ⁿ g_*(i_* M)` vanishes then so does
`R ⁿ p_* M` (Tags 01XC, 089W). -/
theorem isZero_rightDerived_pushforward_of_comp_eq {A B C : Scheme.{u}} (i : A ⟶ B)
    [IsAffineHom i] (g : B ⟶ C) (p : A ⟶ C) (hp : i ≫ g = p) (M : A.Modules)
    [M.IsQuasicoherent] (n : ℕ)
    (h : IsZero (((Scheme.Modules.pushforward g).rightDerived n).obj
      ((Scheme.Modules.pushforward i).obj M))) :
    IsZero (((Scheme.Modules.pushforward p).rightDerived n).obj M) := by
  subst hp
  exact IsZero.of_iso h (Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward i)
    (Scheme.Modules.pushforward g)
    (fun I hI =>
      Stacks.AlgebraicGeometry.RelativeCechAcyclic.rightAcyclic_pushforward_obj_injective i g I hI)
    (fun m hm => Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward i M m hm) n)

/-! ### Locality of the vanishing on the middle scheme -/

/-- **Vanishing of a higher direct image is local on the middle scheme of a factorisation whose
second leg becomes affine over a cover.**  Let `g : A ⟶ B` be quasi-compact and quasi-separated,
let `c : B ⟶ C` be arbitrary and let `M` be a quasi-coherent `𝒪_A`-module.  Suppose given open
immersions `j i : B' i ⟶ B` covering `B` with each `j i ≫ c` affine, and open immersions
`k i : A' i ⟶ A` whose ranges are the inverse images of the ranges of the `j i`.  If
`R ⁿ (k i ≫ g ≫ c)_*` of the restriction of `M` vanishes for every `i`, then `R ⁿ g_* M = 0`. -/
theorem isZero_rightDerived_pushforward_of_openCover {A B C : Scheme.{u}} (g : A ⟶ B)
    [QuasiCompact g] [QuasiSeparated g] (c : B ⟶ C) (M : A.Modules) [M.IsQuasicoherent] (n : ℕ)
    {ι : Type*} {A' B' : ι → Scheme.{u}} (j : ∀ i, B' i ⟶ B) (k : ∀ i, A' i ⟶ A)
    [∀ i, IsOpenImmersion (j i)] [∀ i, IsOpenImmersion (k i)]
    (hcover : ⨆ i, (j i).opensRange = ⊤) (haff : ∀ i, IsAffineHom (j i ≫ c))
    (hrange : ∀ i, (k i).opensRange = g ⁻¹ᵁ (j i).opensRange)
    (h : ∀ i, IsZero (((Scheme.Modules.pushforward (k i ≫ g ≫ c)).rightDerived n).obj
      ((Scheme.Modules.restrictFunctor (k i)).obj M))) :
    IsZero (((Scheme.Modules.pushforward g).rightDerived n).obj M) := by
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover
    (fun i => (j i).opensRange) hcover _ fun i => ?_
  refine IsZero.of_iso ?_
    ((Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso g
      (j i).opensRange n).app M).symm
  have hc : IsAffineHom ((j i).opensRange.ι ≫ c) := by
    have := haff i
    rw [← Scheme.Hom.isoOpensRange_inv_comp (j i), Category.assoc]
    infer_instance
  refine Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward_of_comp_eq_of_isAffineHom
    (g ∣_ (j i).opensRange) ((j i).opensRange.ι ≫ c)
    ((g ⁻¹ᵁ (j i).opensRange).ι ≫ g ≫ c)
    (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) _ n ?_
  have hr : Set.range (k i).base = Set.range (g ⁻¹ᵁ (j i).opensRange).ι.base := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, hrange i,
      Scheme.Opens.opensRange_ι]
  set e := IsOpenImmersion.isoOfRangeEq (k i) (g ⁻¹ᵁ (j i).opensRange).ι hr with he
  have hfac : e.hom ≫ (g ⁻¹ᵁ (j i).opensRange).ι = k i :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  refine isZero_rightDerived_pushforward_of_comp_eq e.inv (k i ≫ g ≫ c)
    ((g ⁻¹ᵁ (j i).opensRange).ι ≫ g ≫ c) (by simp [← hfac]) _ n ?_
  exact IsZero.of_iso (h i) (((Scheme.Modules.pushforward (k i ≫ g ≫ c)).rightDerived n).mapIso
    (pushforwardInvIsoRestrict e _ ≪≫
      ((Scheme.Modules.restrictFunctorComp e.hom (g ⁻¹ᵁ (j i).opensRange).ι).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hfac).app M))

/-! ### Condition (2)(b) of Tag 0FZH under an affine change of source -/

/-- **Condition (2)(b) of Tag 0FZH is inherited by an affine change of source.**  Let `K` be a
quasi-coherent kernel on `X ×_R Y` whose integrand has no positive higher direct images along
the second projection, and let `f : X' ⟶ X` be an affine morphism of schemes over `R`.  Then
the integrand of `(f × id_Y)^*K` has no positive higher direct images along the second
projection of `X' ×_R Y` either. -/
theorem isZero_rightDerived_pushforward_sourceChangeKernel (R : Type u) [CommRing R]
    (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X) [IsAffineHom f.left]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K)
    (F : Scheme.QuasicoherentModules X'.left) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (pullback.snd X'.hom Y.hom)).rightDerived q).obj
      ((integralTransformIntegrand R X' Y (sourceChangeKernel R X X' Y f K)).obj F)) := by
  have hG : ((integralTransformIntegrand R X' Y
      (sourceChangeKernel R X X' Y f K)).obj F).IsQuasicoherent :=
    isQuasicoherent_tensorLeftFunctor_pullback R X' Y (sourceChangeKernel R X X' Y f K) F
  refine isZero_rightDerived_pushforward_of_comp_eq (sourceChangeMap R X X' Y f)
    (pullback.snd X.hom Y.hom) (pullback.snd X'.hom Y.hom)
    (sourceChangeMap_comp_snd R X X' Y f) _ q ?_
  exact IsZero.of_iso (hK.2 ((quasicoherentPushforward f.left).obj F) q hq)
    (((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).rightDerived q).mapIso
      (integralTransformIntegrandSourceChangeObjIso R X X' Y f K F).symm)

/-! ### The triple product `T ×_R X ×_R Y` and its projections -/

variable (R : Type u) [CommRing R]

/-- **`T ×_R X`, as a scheme over `R`.**  Its structure morphism is the first projection
followed by the structure morphism of `T`. -/
abbrev baseChangeSourceOver (T X : Over (Spec (.of R))) : Over (Spec (.of R)) :=
  Over.mk (pullback.fst T.hom X.hom ≫ T.hom)

/-- The projection `T ×_R X ⟶ T`, as a morphism of schemes over `R`. -/
abbrev baseChangeSourceOverFst (T X : Over (Spec (.of R))) :
    baseChangeSourceOver R T X ⟶ T :=
  Over.homMk (pullback.fst T.hom X.hom) rfl

/-- The projection `T ×_R X ⟶ X`, as a morphism of schemes over `R`. -/
abbrev baseChangeSourceOverSnd (T X : Over (Spec (.of R))) :
    baseChangeSourceOver R T X ⟶ X :=
  Over.homMk (pullback.snd T.hom X.hom) pullback.condition.symm

/-- **The projection `pr_{13} : (T ×_R X) ×_R Y ⟶ T ×_R Y`**, as the change of source of
`T ×_R Y` along the projection `T ×_R X ⟶ T`. -/
abbrev baseChangeTargetMap (T X Y : Over (Spec (.of R))) :
    pullback (baseChangeSourceOver R T X).hom Y.hom ⟶ pullback T.hom Y.hom :=
  sourceChangeMap R T (baseChangeSourceOver R T X) Y (baseChangeSourceOverFst R T X)

/-- **The kernel `pr_{23}^*K` on `(T ×_R X) ×_R Y`**, the inverse image of a quasi-coherent
kernel on `X ×_R Y` along the change of source given by the projection `T ×_R X ⟶ X`. -/
abbrev baseChangeKernel (T X Y : Over (Spec (.of R)))
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom)) :
    Scheme.QuasicoherentModules (pullback (baseChangeSourceOver R T X).hom Y.hom) :=
  sourceChangeKernel R X (baseChangeSourceOver R T X) Y (baseChangeSourceOverSnd R T X) K

/-- An open subscheme of `T`, as a scheme over `R` through the structure morphism of `T`. -/
abbrev openSubOver (T : Over (Spec (.of R))) (U : T.left.Opens) : Over (Spec (.of R)) :=
  Over.mk (U.ι ≫ T.hom)

/-- The inclusion of an open subscheme of `T`, as a morphism of schemes over `R`. -/
abbrev openSubOverHom (T : Over (Spec (.of R))) (U : T.left.Opens) : openSubOver R T U ⟶ T :=
  Over.homMk U.ι rfl

/-- The inverse image of a quasi-coherent module on `T ×_R X` to `U ×_R X`, for `U` an open
subscheme of `T`. -/
def baseChangeOpenRestrict (T X : Over (Spec (.of R))) (U : T.left.Opens)
    (F : Scheme.QuasicoherentModules (baseChangeSourceOver R T X).left) :
    Scheme.QuasicoherentModules (baseChangeSourceOver R (openSubOver R T U) X).left :=
  ⟨(Scheme.Modules.pullback
      (sourceChangeMap R T (openSubOver R T U) X (openSubOverHom R T U))).obj F.obj,
    have : F.obj.IsQuasicoherent := F.property
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (sourceChangeMap R T (openSubOver R T U) X (openSubOverHom R T U)).toLRSHom.toShHom F.obj
      (by assumption)⟩

/-! ### The three open immersions attached to an open subscheme of `T` -/

/-- The change of source `X' ×_R Y ⟶ X ×_R Y` along an open immersion `X' ⟶ X` is an open
immersion. -/
instance isOpenImmersion_sourceChangeMap (X X' Y : Over (Spec (.of R))) (f : X' ⟶ X)
    [IsOpenImmersion f.left] : IsOpenImmersion (sourceChangeMap R X X' Y f) := by
  rw [sourceChangeMap]; infer_instance

/-- The inclusion of an open subscheme of `T`, as a morphism over `R`, is an open immersion. -/
instance isOpenImmersion_openSubOverHom (T : Over (Spec (.of R))) (U : T.left.Opens) :
    IsOpenImmersion (openSubOverHom R T U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- **The open immersion `U ×_R X ⟶ T ×_R X`**, as a morphism of schemes over `R`, for `U` an
open subscheme of `T`.  Inverse image along it is `AlgebraicGeometry.baseChangeOpenRestrict`. -/
abbrev baseChangeOpenSourceHom (T X : Over (Spec (.of R))) (U : T.left.Opens) :
    baseChangeSourceOver R (openSubOver R T U) X ⟶ baseChangeSourceOver R T X :=
  Over.homMk (sourceChangeMap R T (openSubOver R T U) X (openSubOverHom R T U))
    (by
      change sourceChangeMap R T (openSubOver R T U) X (openSubOverHom R T U) ≫
          pullback.fst T.hom X.hom ≫ T.hom =
        pullback.fst (openSubOver R T U).hom X.hom ≫ (openSubOver R T U).hom
      rw [← Category.assoc, sourceChangeMap_comp_fst, Category.assoc]
      rfl)

/-- The morphism `U ×_R X ⟶ T ×_R X` induced by an open subscheme `U` of `T` is an open
immersion. -/
instance isOpenImmersion_baseChangeOpenSourceHom (T X : Over (Spec (.of R)))
    (U : T.left.Opens) : IsOpenImmersion (baseChangeOpenSourceHom R T X U).left :=
  inferInstanceAs
    (IsOpenImmersion (sourceChangeMap R T (openSubOver R T U) X (openSubOverHom R T U)))

/-- **The open immersion `(U ×_R X) ×_R Y ⟶ (T ×_R X) ×_R Y`** induced by an open subscheme `U`
of `T`. -/
abbrev baseChangeOpenTripleMap (T X Y : Over (Spec (.of R))) (U : T.left.Opens) :
    pullback (baseChangeSourceOver R (openSubOver R T U) X).hom Y.hom ⟶
      pullback (baseChangeSourceOver R T X).hom Y.hom :=
  sourceChangeMap R (baseChangeSourceOver R T X)
    (baseChangeSourceOver R (openSubOver R T U) X) Y (baseChangeOpenSourceHom R T X U)

/-- **The open immersion `U ×_R Y ⟶ T ×_R Y`** induced by an open subscheme `U` of `T`. -/
abbrev baseChangeOpenTargetMap (T Y : Over (Spec (.of R))) (U : T.left.Opens) :
    pullback (openSubOver R T U).hom Y.hom ⟶ pullback T.hom Y.hom :=
  sourceChangeMap R T (openSubOver R T U) Y (openSubOverHom R T U)

/-- The projection `U ×_R X ⟶ X` is the projection `T ×_R X ⟶ X` restricted to `U ×_R X`. -/
theorem baseChangeOpenSourceHom_comp_snd (T X : Over (Spec (.of R))) (U : T.left.Opens) :
    baseChangeOpenSourceHom R T X U ≫ baseChangeSourceOverSnd R T X =
      baseChangeSourceOverSnd R (openSubOver R T U) X :=
  Over.OverMorphism.ext
    (sourceChangeMap_comp_snd R T (openSubOver R T U) X (openSubOverHom R T U))

/-- `U ×_R Y` is the open subscheme `pr_1^{-1}(U)` of `T ×_R Y`. -/
theorem opensRange_baseChangeOpenTargetMap (T Y : Over (Spec (.of R))) (U : T.left.Opens) :
    (baseChangeOpenTargetMap R T Y U).opensRange = pullback.fst T.hom Y.hom ⁻¹ᵁ U := by
  rw [opensRange_of_isPullback
    (isPullback_sourceChangeMap R T (openSubOver R T U) Y (openSubOverHom R T U))]
  change pullback.fst T.hom Y.hom ⁻¹ᵁ U.ι.opensRange = _
  rw [Scheme.Opens.opensRange_ι]

/-- `(U ×_R X) ×_R Y` is the open subscheme `pr_{13}^{-1}(U ×_R Y)` of `(T ×_R X) ×_R Y`. -/
theorem opensRange_baseChangeOpenTripleMap (T X Y : Over (Spec (.of R))) (U : T.left.Opens) :
    (baseChangeOpenTripleMap R T X Y U).opensRange =
      baseChangeTargetMap R T X Y ⁻¹ᵁ (baseChangeOpenTargetMap R T Y U).opensRange := by
  rw [opensRange_of_isPullback (isPullback_sourceChangeMap R (baseChangeSourceOver R T X)
      (baseChangeSourceOver R (openSubOver R T U) X) Y (baseChangeOpenSourceHom R T X U)),
    opensRange_baseChangeOpenTargetMap]
  change pullback.fst (baseChangeSourceOver R T X).hom Y.hom ⁻¹ᵁ
      (sourceChangeMap R T (openSubOver R T U) X (openSubOverHom R T U)).opensRange = _
  rw [opensRange_of_isPullback
    (isPullback_sourceChangeMap R T (openSubOver R T U) X (openSubOverHom R T U))]
  change pullback.fst (baseChangeSourceOver R T X).hom Y.hom ⁻¹ᵁ
      (pullback.fst T.hom X.hom ⁻¹ᵁ U.ι.opensRange) = _
  rw [Scheme.Opens.opensRange_ι, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    sourceChangeMap_comp_fst R T (baseChangeSourceOver R T X) Y (baseChangeSourceOverFst R T X)]
  rfl

/-- The open subschemes `U ×_R Y` of `T ×_R Y`, for `U` an affine open subscheme of `T`, cover
`T ×_R Y`. -/
theorem iSup_opensRange_baseChangeOpenTargetMap (T Y : Over (Spec (.of R))) :
    ⨆ U : T.left.affineOpens, (baseChangeOpenTargetMap R T Y (U : T.left.Opens)).opensRange =
      ⊤ := by
  rw [funext fun U : T.left.affineOpens =>
    opensRange_baseChangeOpenTargetMap R T Y (U : T.left.Opens),
    ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]
  simp

/-- **The integrand of `pr_{23}^*K` restricts to the integrand over an open subscheme of `T`.**
Inverse image along `(U ×_R X) ×_R Y ⟶ (T ×_R X) ×_R Y` commutes with the tensor product
(Tag 01CD), carries `pr_{23}^*K` to the corresponding kernel over `U` and carries `pr_{12}^*F`
to `pr_{12}^*` of the restriction of `F`. -/
def integrandBaseChangeOpenIso (T X Y : Over (Spec (.of R))) (U : T.left.Opens)
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (F : Scheme.QuasicoherentModules (baseChangeSourceOver R T X).left) :
    (Scheme.Modules.pullback (baseChangeOpenTripleMap R T X Y U)).obj
        ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
          (baseChangeKernel R T X Y K)).obj F) ≅
      (integralTransformIntegrand R (baseChangeSourceOver R (openSubOver R T U) X) Y
        (baseChangeKernel R (openSubOver R T U) X Y K)).obj
          (baseChangeOpenRestrict R T X U F) :=
  have hsig : baseChangeOpenTripleMap R T X Y U ≫
      sourceChangeMap R X (baseChangeSourceOver R T X) Y (baseChangeSourceOverSnd R T X) =
    sourceChangeMap R X (baseChangeSourceOver R (openSubOver R T U) X) Y
      (baseChangeSourceOverSnd R (openSubOver R T U) X) := by
    rw [sourceChangeMap_comp, baseChangeOpenSourceHom_comp_snd]
  have hfst : baseChangeOpenTripleMap R T X Y U ≫
      pullback.fst (baseChangeSourceOver R T X).hom Y.hom =
    pullback.fst (baseChangeSourceOver R (openSubOver R T U) X).hom Y.hom ≫
      (baseChangeOpenSourceHom R T X U).left := sourceChangeMap_comp_fst ..
  (pullbackTensorLeftIso (baseChangeOpenTripleMap R T X Y U)
      (baseChangeKernel R T X Y K).obj).app
    ((Scheme.Modules.pullback
      (pullback.fst (baseChangeSourceOver R T X).hom Y.hom)).obj F.obj) ≪≫
  (tensorLeftFunctorSchemeIsoOfIso _
      ((Scheme.Modules.pullbackComp (baseChangeOpenTripleMap R T X Y U)
          (sourceChangeMap R X (baseChangeSourceOver R T X) Y
            (baseChangeSourceOverSnd R T X))).app K.obj ≪≫
        (Scheme.Modules.pullbackCongr hsig).app K.obj)).app _ ≪≫
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(pullback (baseChangeSourceOver R (openSubOver R T U) X).hom Y.hom).presheaf,
      (pullback (baseChangeSourceOver R (openSubOver R T U) X).hom
        Y.hom).toRingedSpace.IsSheaf⟩).obj
        (baseChangeKernel R (openSubOver R T U) X Y K).obj).mapIso
    ((Scheme.Modules.pullbackComp (baseChangeOpenTripleMap R T X Y U)
        (pullback.fst (baseChangeSourceOver R T X).hom Y.hom)).app F.obj ≪≫
      (Scheme.Modules.pullbackCongr hfst).app F.obj ≪≫
      ((Scheme.Modules.pullbackComp
          (pullback.fst (baseChangeSourceOver R (openSubOver R T U) X).hom Y.hom)
          (baseChangeOpenSourceHom R T X U).left).app F.obj).symm)

/-! ### Tag 0FZI for a source affine over `R` -/

/-- The projection `pr_{13} : (T ×_R X) ×_R Y ⟶ T ×_R Y` is quasi-compact and quasi-separated
when `X` is. -/
private theorem quasiCompact_and_quasiSeparated_baseChangeTargetMap
    (T X Y : Over (Spec (.of R))) [QuasiCompact X.hom] [QuasiSeparated X.hom] :
    QuasiCompact (baseChangeTargetMap R T X Y) ∧ QuasiSeparated (baseChangeTargetMap R T X Y) :=
  have hsq := isPullback_sourceChangeMap R T (baseChangeSourceOver R T X) Y
    (baseChangeSourceOverFst R T X)
  have hfst := (IsPullback.of_hasPullback T.hom X.hom).flip
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hfst
        (inferInstance : QuasiCompact X.hom)),
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hfst
        (inferInstance : QuasiSeparated X.hom))⟩

/-- **Tag 0FZI over an affine `T`, from a reflection of the vanishing along the second
projection.**  If the vanishing of `R ^q pr_{2,*}` on `(T ×_R X) ×_R Y` implies that of
`R ^q pr_{13,*}` for quasi-coherent modules, then Tag 0FZI holds. -/
private theorem isZero_rightDerived_pushforward_baseChangeKernel_of_reflects
    (T X Y : Over (Spec (.of R))) [IsAffineHom T.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K)
    (F : Scheme.QuasicoherentModules (baseChangeSourceOver R T X).left) (q : ℕ) (hq : 0 < q)
    (h : ∀ (M : (pullback (baseChangeSourceOver R T X).hom Y.hom).Modules) [M.IsQuasicoherent],
      IsZero (((Scheme.Modules.pushforward
          (pullback.snd (baseChangeSourceOver R T X).hom Y.hom)).rightDerived q).obj M) →
        IsZero (((Scheme.Modules.pushforward (baseChangeTargetMap R T X Y)).rightDerived q).obj
          M)) :
    IsZero (((Scheme.Modules.pushforward (baseChangeTargetMap R T X Y)).rightDerived q).obj
      ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
        (baseChangeKernel R T X Y K)).obj F)) :=
  have : IsAffineHom (baseChangeSourceOverSnd R T X).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback T.hom X.hom) inferInstance
  have : ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
      (baseChangeKernel R T X Y K)).obj F).IsQuasicoherent :=
    isQuasicoherent_tensorLeftFunctor_pullback R (baseChangeSourceOver R T X) Y
      (baseChangeKernel R T X Y K) F
  h _ (isZero_rightDerived_pushforward_sourceChangeKernel R X (baseChangeSourceOver R T X) Y
    (baseChangeSourceOverSnd R T X) K hK F q hq)

/-- **Tag 0FZI when `T` is affine over `R`, for `X` quasi-compact and quasi-separated over
`R`.**  Let `K` be a quasi-coherent kernel on `X ×_R Y` satisfying the two conditions of Tag 0FZH
part (2).  Then `R ^q pr_{13,*}(pr_{12}^*F ⊗ pr_{23}^*K) = 0` for every quasi-coherent `F` on
`T ×_R X` and every `q > 0`. -/
theorem isZero_rightDerived_pushforward_baseChangeKernel_of_isAffineHom_of_quasiCompact
    (T X Y : Over (Spec (.of R))) [IsAffineHom T.hom]
    [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K)
    (F : Scheme.QuasicoherentModules (baseChangeSourceOver R T X).left) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (baseChangeTargetMap R T X Y)).rightDerived q).obj
      ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
        (baseChangeKernel R T X Y K)).obj F)) := by
  obtain ⟨hgqc, hgqs⟩ := quasiCompact_and_quasiSeparated_baseChangeTargetMap R T X Y
  have hc : IsAffineHom (pullback.snd T.hom Y.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback T.hom Y.hom) inferInstance
  exact isZero_rightDerived_pushforward_baseChangeKernel_of_reflects R T X Y K hK F q hq
    fun M _ =>
      Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward_of_comp_eq_of_isAffineHom
        (baseChangeTargetMap R T X Y) (pullback.snd T.hom Y.hom)
        (pullback.snd (baseChangeSourceOver R T X).hom Y.hom)
        (sourceChangeMap_comp_snd R T (baseChangeSourceOver R T X) Y
          (baseChangeSourceOverFst R T X)) M q

/-! ### Tag 0FZI -/

/-- **Higher direct images of an integral-transform kernel after base change.**  Let `R` be a
ring, let `X` and `Y` be schemes over `R` with the structure morphism of `X` quasi-compact and
quasi-separated, and let `K` be a quasi-coherent kernel on `X ×_R Y` satisfying the two
conditions of Tag 0FZH part (2).  Then for every scheme `T` over `R`,
`R ^q pr_{13,*}(pr_{12}^*F ⊗ pr_{23}^*K) = 0` for every quasi-coherent `F` on `T ×_R X` and
every `q > 0`. -/
@[stacks 0FZI "the positive higher direct images of pr_12^*F ⊗ pr_23^*K along pr_13 vanish"]
theorem isZero_rightDerived_pushforward_baseChangeKernel (T X Y : Over (Spec (.of R)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom]
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K)
    (F : Scheme.QuasicoherentModules (baseChangeSourceOver R T X).left) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (baseChangeTargetMap R T X Y)).rightDerived q).obj
      ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
        (baseChangeKernel R T X Y K)).obj F)) := by
  obtain ⟨hgqc, hgqs⟩ := quasiCompact_and_quasiSeparated_baseChangeTargetMap R T X Y
  have hG : ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
      (baseChangeKernel R T X Y K)).obj F).IsQuasicoherent :=
    isQuasicoherent_tensorLeftFunctor_pullback R (baseChangeSourceOver R T X) Y
      (baseChangeKernel R T X Y K) F
  refine isZero_rightDerived_pushforward_of_openCover (baseChangeTargetMap R T X Y)
    (pullback.snd T.hom Y.hom) _ q
    (fun U : T.left.affineOpens => baseChangeOpenTargetMap R T Y (U : T.left.Opens))
    (fun U : T.left.affineOpens => baseChangeOpenTripleMap R T X Y (U : T.left.Opens))
    (iSup_opensRange_baseChangeOpenTargetMap R T Y) (fun U => ?_)
    (fun U => opensRange_baseChangeOpenTripleMap R T X Y (U : T.left.Opens)) fun U => ?_
  · have hU : IsAffine (openSubOver R T (U : T.left.Opens)).left := U.property
    rw [sourceChangeMap_comp_snd]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (openSubOver R T (U : T.left.Opens)).hom Y.hom) inferInstance
  · have hU : IsAffine (openSubOver R T (U : T.left.Opens)).left := U.property
    have hsnd : IsAffineHom
        (baseChangeSourceOverSnd R (openSubOver R T (U : T.left.Opens)) X).left :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback (openSubOver R T (U : T.left.Opens)).hom X.hom) inferInstance
    have hcomp : baseChangeOpenTripleMap R T X Y (U : T.left.Opens) ≫
        baseChangeTargetMap R T X Y ≫ pullback.snd T.hom Y.hom =
      pullback.snd
        (baseChangeSourceOver R (openSubOver R T (U : T.left.Opens)) X).hom Y.hom := by
      simp only [sourceChangeMap_comp_snd]
    rw [hcomp]
    exact IsZero.of_iso (isZero_rightDerived_pushforward_sourceChangeKernel R X
        (baseChangeSourceOver R (openSubOver R T (U : T.left.Opens)) X) Y
        (baseChangeSourceOverSnd R (openSubOver R T (U : T.left.Opens)) X) K hK
        (baseChangeOpenRestrict R T X (U : T.left.Opens) F) q hq)
      (((Scheme.Modules.pushforward (pullback.snd
          (baseChangeSourceOver R (openSubOver R T (U : T.left.Opens)) X).hom
            Y.hom)).rightDerived q).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback
            (baseChangeOpenTripleMap R T X Y (U : T.left.Opens))).app _ ≪≫
          integrandBaseChangeOpenIso R T X Y (U : T.left.Opens) K F))

/-! ### The homological inputs of Tag 0FZI, as statements -/

/-- **The collapse of the relative Leray spectral sequence along an affine second leg**, as a
statement: for every `g : A ⟶ B`, every affine `c : B ⟶ C` and every quasi-coherent module `M` on
`A`, the vanishing of `R ⁿ (g ≫ c)_* M` implies the vanishing of `R ⁿ g_* M`. -/
def PushforwardReflectsHigherDirectImageVanishingAlongAffine : Prop :=
  ∀ {A B C : Scheme.{u}} (g : A ⟶ B) (c : B ⟶ C) (p : A ⟶ C), IsAffineHom c → g ≫ c = p →
    ∀ M : A.Modules, M.IsQuasicoherent → ∀ n : ℕ,
      IsZero (((Scheme.Modules.pushforward p).rightDerived n).obj M) →
        IsZero (((Scheme.Modules.pushforward g).rightDerived n).obj M)

/-- **Tag 0FZI when `T` is affine over `R`, assuming
`AlgebraicGeometry.PushforwardReflectsHigherDirectImageVanishingAlongAffine`.**  Let `K` be a
quasi-coherent kernel on `X ×_R Y` satisfying the two conditions of Tag 0FZH part (2).  Then
`R ^q pr_{13,*}(pr_{12}^*F ⊗ pr_{23}^*K) = 0` for every quasi-coherent `F` on `T ×_R X` and every
`q > 0`. -/
theorem isZero_rightDerived_pushforward_baseChangeKernel_of_isAffineHom
    (T X Y : Over (Spec (.of R))) [IsAffineHom T.hom]
    (hrefl : PushforwardReflectsHigherDirectImageVanishingAlongAffine.{u})
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (hK : integralTransformExactKernel R X Y K)
    (F : Scheme.QuasicoherentModules (baseChangeSourceOver R T X).left) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward (baseChangeTargetMap R T X Y)).rightDerived q).obj
      ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
        (baseChangeKernel R T X Y K)).obj F)) := by
  have hc : IsAffineHom (pullback.snd T.hom Y.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback T.hom Y.hom) inferInstance
  exact isZero_rightDerived_pushforward_baseChangeKernel_of_reflects R T X Y K hK F q hq
    fun M hM => hrefl (baseChangeTargetMap R T X Y) (pullback.snd T.hom Y.hom)
      (pullback.snd (baseChangeSourceOver R T X).hom Y.hom) hc
      (sourceChangeMap_comp_snd R T (baseChangeSourceOver R T X) Y
        (baseChangeSourceOverFst R T X)) M hM q

/-- **Two homological inputs of Tag 0FZI.**  The first field is the collapse of the relative Leray
spectral sequence along an affine second leg.  The second is the locality of the vanishing of
Tag 0FZI on `T`, for an arbitrary quasi-coherent kernel and an arbitrary quasi-coherent module:
the vanishing over every affine open subscheme `U` of `T`, after restricting the module, implies
the vanishing over `T`. -/
structure BaseChangeAcyclicityInput (T X Y : Over (Spec (.of R))) : Prop where
  /-- The collapse of the relative Leray spectral sequence along an affine second leg. -/
  pushforwardReflectsVanishing : PushforwardReflectsHigherDirectImageVanishingAlongAffine.{u}
  /-- The question of Tag 0FZI is local on `T`: it suffices to answer it over each affine open
  subscheme of `T`, after restricting the module there. -/
  vanishingLocalOnFirstFactor :
    ∀ (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
      (F : Scheme.QuasicoherentModules (baseChangeSourceOver R T X).left) (q : ℕ),
      (∀ U : T.left.affineOpens,
          IsZero (((Scheme.Modules.pushforward (baseChangeTargetMap R
              (openSubOver R T (U : T.left.Opens)) X Y)).rightDerived q).obj
            ((integralTransformIntegrand R
                (baseChangeSourceOver R (openSubOver R T (U : T.left.Opens)) X) Y
                (baseChangeKernel R (openSubOver R T (U : T.left.Opens)) X Y K)).obj
              (baseChangeOpenRestrict R T X (U : T.left.Opens) F)))) →
        IsZero (((Scheme.Modules.pushforward (baseChangeTargetMap R T X Y)).rightDerived q).obj
          ((integralTransformIntegrand R (baseChangeSourceOver R T X) Y
            (baseChangeKernel R T X Y K)).obj F))

end AlgebraicGeometry

end
