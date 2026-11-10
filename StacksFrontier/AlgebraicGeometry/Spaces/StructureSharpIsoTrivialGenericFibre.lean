module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsFlatBaseChangeOverObject
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsTorsionFree
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpChartwiseIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsMeromorphicChartFraction
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.RingTheory.IntegrallyClosed.GenericFibreTrivial

/-!
# `f_*𝒪_X = 𝒪_Y` for a proper morphism onto a normal integral space with trivial generic fibre

This file proves conclusion (1) of Stacks 0AYI: for a proper morphism `f : X ⟶ Y` of algebraic
spaces with `Y` integral and normal with generic point `ξ`, `X` reduced, every generic point of
an irreducible component of `|X|` lying over `ξ`, and `H⁰(X_ξ, 𝒪) = κ(ξ)`, the structure map
`𝒪_Y ⟶ f_*𝒪_X` is an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_fSharp_of_isProper_of_trivialGenericFibre`: conclusion (1) of
  Stacks 0AYI.
* `AlgebraicGeometry.Space.bijective_of_isNormalIntegralAffineChart`: its case of a normal
  integral affine étale chart `V`, `Γ(V) = Γ(X ×_Y V)`.
* `AlgebraicGeometry.Space.injective_globalFunctionsMap_of_isFractionRing` and
  `AlgebraicGeometry.Space.bijective_pullbackToGlobalFunctions_of_isPullback`: two consequences of
  flat base change of global functions along a morphism of affine objects of the site.
* `AlgebraicGeometry.Space.exists_totalFractionObject_comp_fieldMorphism`: the spectrum of the
  fraction field of an integral affine chart maps to `Y` through the residue field of `ξ`.
* `AlgebraicGeometry.Space.eq_pullbackToGlobalFunctions`: a ring map restricting on every étale
  chart to pullback of functions along a morphism to an object of the site is that pullback.

## Implementation notes

The proof does not go through the Stein factorization of Stacks 0A1C used in the Stacks
project.  Over a normal integral affine chart `V = Spec A` with fraction field `K`, the ring
`A' = Γ(X ×_Y V)` is integral over `A` (`f` is universally closed), embeds into the functions of
the generic fibre `X_K` (torsion freeness and flat base change), and those functions are `K`
(`Spec K ⟶ Y` factors through `Spec κ(ξ)` by Stacks 0H1T, and flat base change carries
hypothesis (6) to `X_K`).  So `A'` lies in `K` and is integral over `A`, hence equal to `A`.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Pullback of functions from an object of the site -/

/-- Pullback of functions from an object of the site restricts, on every étale scheme chart, to
pullback along the induced morphism of schemes. -/
theorem globalFunctionsChartRestriction_comp_pullbackToGlobalFunctions (X : AlgebraicSpaces B S hS)
    (T : BigFppfOver B S hS) (h : X ⟶ schemeSpace T) (c : SmallEtale B S hS X.1) :
    (globalFunctionsChartRestriction B S hS X c).comp (pullbackToGlobalFunctions B S hS X T h) =
      ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS h.hom c)).appTop.hom :=
  rfl

/-- A ring map into the global functions which restricts on every étale scheme chart to
pullback of functions along a morphism `h` to an object of the site is pullback along `h`. -/
theorem eq_pullbackToGlobalFunctions (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)
    (h : X ⟶ schemeSpace T)
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* globalFunctions B S hS X.1)
    (hψ : ∀ c : SmallEtale B S hS X.1, (globalFunctionsChartRestriction B S hS X c).comp ψ =
      ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS h.hom c)).appTop.hom) :
    ψ = pullbackToGlobalFunctions B S hS X T h :=
  RingHom.ext fun x => Subtype.ext (funext fun c => RingHom.congr_fun (hψ c.unop) x)

/-- If `R ⟶ G` is bijective then so is `T ⟶ T ⊗_R G`, for every `R`-algebra `T`. -/
theorem bijective_includeLeft_of_bijective_algebraMap {R T G : Type*} [CommRing R] [CommRing T]
    [CommRing G] [Algebra R T] [Algebra R G] (h : Function.Bijective (algebraMap R G)) :
    Function.Bijective (Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] G) := by
  let e : R ≃ₐ[R] G := AlgEquiv.ofBijective (Algebra.ofId R G) h
  let c : T ≃ₐ[R] T ⊗[R] G :=
    (Algebra.TensorProduct.rid R R T).symm.trans (Algebra.TensorProduct.congr AlgEquiv.refl e)
  have : ⇑(Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] G) = ⇑c :=
    funext fun t => by simp [c, e]
  rw [this]
  exact c.bijective

/-! ### The spectrum of the fraction field of a normal integral affine chart -/

/-- On an integral affine scheme `T`, the morphism `Spec Frac Γ(T) ⟶ T` sends the point of its
source to the generic point of `T`: the zero ideal of the fraction field pulls back to the zero
ideal of the domain `Γ(T)`. -/
theorem _root_.AlgebraicGeometry.Scheme.fromSpecTotalFractionRing_apply_eq_genericPoint
    (T : Scheme.{u}) [IsAffine T] [IsIntegral T]
    (z : Spec (CommRingCat.of (FractionRing Γ(T, ⊤)))) :
    T.fromSpecTotalFractionRing z = genericPoint T := by
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)))) z =
      genericPoint (Spec Γ(T, ⊤)) := by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)))
      (z : PrimeSpectrum (FractionRing Γ(T, ⊤))).asIdeal = ⊥
    rw [@Ideal.eq_bot_of_prime _ _ _ (z : PrimeSpectrum (FractionRing Γ(T, ⊤))).isPrime,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)]
  rw [Scheme.fromSpecTotalFractionRing, Scheme.Hom.comp_apply, h1]
  exact genericPoint_eq_of_isOpenImmersion T.isoSpec.inv

attribute [local instance] pointTopology

variable {X Y : AlgebraicSpaces B S hS}

/-- On a decent space `Y` with generic point `ξ`, the generic point of an irreducible étale
scheme chart maps to `ξ`: its image has a local ring of dimension zero (Stacks 0BAQ), hence
admits no proper generization, and `ξ` generizes it. -/
theorem pointsMap_eq_of_pointsToScheme_eq_genericPoint (hYdec : IsDecentSpace B S hS Y.1)
    {ξ : points B S hS Y.1} (hξ : IsGenericPoint ξ Set.univ) (V : SmallEtale B S hS Y.1)
    [IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj V.obj.left)]
    (w : points B S hS (yoneda.obj V.obj.left))
    (hw : pointsToScheme B S hS V.obj.left w =
      genericPoint ((BigFppfOver.toScheme B S hS).obj V.obj.left)) :
    pointsMap B S hS _ V.obj.hom w = ξ := by
  have hgen : genericPoint ((BigFppfOver.toScheme B S hS).obj V.obj.left) ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj V.obj.left) := by
    change closure {_} ∈ irreducibleComponents _
    rw [irreducibleComponents_eq_singleton, (genericPoint_spec _).def]
    rfl
  have hdim : localRingDimension B S hS (pointsMap B S hS _ V.obj.hom w) = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS Y.2 _).2
      ⟨V.obj.left, V.obj.hom, _, (isEtale_iff_presheaf_of_yoneda B S hS _).2 V.property,
        chartPoint_pointsToScheme B S hS V.obj.left V.obj.hom w, by rwa [hw]⟩
  refine (eq_of_specializes_of_localRingDimension_eq_zero B S hS Y.2 hYdec hdim ξ ?_).symm
  rw [specializes_iff_mem_closure, hξ.def]
  trivial

/-- **Stacks 0AYI, the generic fibre of a chart lies over the residue field of `ξ`.**  Let `Y`
be integral with generic point `ξ`, represented by a quasi-compact monomorphism
`Spec κ ⟶ Y`, and let `V` be an affine integral étale scheme chart of `Y`.  Then
`Spec Frac Γ(V) ⟶ V ⟶ Y` factors through `Spec κ ⟶ Y`: its image is `{ξ}`, and its source is
reduced, so Stacks 0H1T applies. -/
theorem exists_totalFractionObject_comp_fieldMorphism (hYint : IsIntegralSpace B S hS Y.1)
    {ξ : points B S hS Y.1} (hξ : IsGenericPoint ξ Set.univ) (V : SmallEtale B S hS Y.1)
    [IsAffine V.obj.left.left.1] [IsIntegral ((BigFppfOver.toScheme B S hS).obj V.obj.left)]
    (r : FieldValuedPoint B S hS Y.1) (hr : r.class B S hS Y.1 = ξ)
    (hmono : Mono (fieldMorphism B S hS Y.1 r))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y.1 r)) :
    ∃ g : totalFractionObject B S hS V.obj.left ⟶ r.siteObject B S hS Y.1,
      yoneda.map g ≫ fieldMorphism B S hS Y.1 r =
        yoneda.map (totalFractionObjectMap B S hS V.obj.left) ≫ V.obj.hom := by
  have hYdec := IsIntegralSpace.isDecentSpace B S hS Y.1 hYint
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) := ‹IsAffine V.obj.left.left.1›
  have : IsIntegral V.obj.left.left.1 :=
    ‹IsIntegral ((BigFppfOver.toScheme B S hS).obj V.obj.left)›
  have hrange : Set.range (pointsMap B S hS _
      (yoneda.map (totalFractionObjectMap B S hS V.obj.left) ≫ V.obj.hom)) ⊆ {ξ} := by
    rintro _ ⟨w, rfl⟩
    rw [Set.mem_singleton_iff, pointsMap_comp_apply]
    refine pointsMap_eq_of_pointsToScheme_eq_genericPoint hYdec hξ V _ ?_
    rw [pointsToScheme_pointsMap_yoneda, toScheme_map_totalFractionObjectMap]
    exact Scheme.fromSpecTotalFractionRing_apply_eq_genericPoint _ _
  have hred : HasEtaleLocalProperty B S hS (yoneda.obj (totalFractionObject B S hS V.obj.left))
      (fun W : Scheme.{u} => IsReduced W) := by
    refine hasEtaleLocalProperty_of_representable B S hS _
      (fun W : Scheme.{u} => IsReduced W) _ (Iso.refl _) ?_
    change IsReduced (Spec (CommRingCat.of (FractionRing Γ(V.obj.left.left.1, ⊤))))
    have : IsDomain (FractionRing Γ(V.obj.left.left.1, ⊤)) := inferInstance
    infer_instance
  obtain ⟨g', hg'⟩ := exists_comp_fieldMorphism_eq_of_range_pointsMap_subset_singleton B S hS
    Y.2 (isAlgebraicSpace_yoneda B S hS _) _ ξ hrange hred r hr hmono hqc
  exact ⟨yoneda.preimage g', by rwa [Functor.map_preimage]⟩

/-- Pullback of functions along `Spec Frac Γ(T) ⟶ T` makes `Γ(Spec Frac Γ(T))` a fraction ring
of `Γ(T)`, for an affine scheme `T`. -/
theorem _root_.AlgebraicGeometry.Scheme.isFractionRing_fromSpecTotalFractionRing_appTop
    (T : Scheme.{u}) [IsAffine T] :
    letI := T.fromSpecTotalFractionRing.appTop.hom.toAlgebra
    IsFractionRing Γ(T, ⊤) Γ(Spec (CommRingCat.of (FractionRing Γ(T, ⊤))), ⊤) := by
  let := T.fromSpecTotalFractionRing.appTop.hom.toAlgebra
  let e : FractionRing Γ(T, ⊤) ≃ₐ[Γ(T, ⊤)] Γ(Spec (CommRingCat.of (FractionRing Γ(T, ⊤))), ⊤) :=
    AlgEquiv.ofRingEquiv
      (f := (Scheme.ΓSpecIso
        (CommRingCat.of (FractionRing Γ(T, ⊤)))).symm.commRingCatIsoToRingEquiv)
      (fun a => by
        change (Scheme.ΓSpecIso _).inv _ = T.fromSpecTotalFractionRing.appTop a
        rw [← ΓSpecIso_hom_fromSpecTotalFractionRing_appTop]
        exact (Scheme.ΓSpecIso _).hom_inv_id_apply _)
  exact IsLocalization.isLocalization_of_algEquiv _ e

/-- Pullback of functions along `Spec Frac Γ(T) ⟶ T` is the structure map of the fraction ring,
read through `Γ(Spec Frac Γ(T)) = Frac Γ(T)`. -/
theorem _root_.AlgebraicGeometry.Scheme.fromSpecTotalFractionRing_appTop_eq (T : Scheme.{u})
    [IsAffine T] :
    T.fromSpecTotalFractionRing.appTop.hom =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(T, ⊤)))).inv.hom.comp
        (algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤))) := by
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply, ← ΓSpecIso_hom_fromSpecTotalFractionRing_appTop]
  exact ((Scheme.ΓSpecIso _).hom_inv_id_apply _).symm

/-- The morphism `Spec Frac Γ(U) ⟶ U` is flat: it is the spectrum of a localization. -/
instance flat_toScheme_map_totalFractionObjectMap (U : BigFppfOver B S hS) [IsAffine U.left.1] :
    Flat ((BigFppfOver.toScheme B S hS).map (totalFractionObjectMap B S hS U)) := by
  rw [toScheme_map_totalFractionObjectMap, Scheme.fromSpecTotalFractionRing]
  have : Flat (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(U.left.1, ⊤) (FractionRing Γ(U.left.1, ⊤))))) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]
    infer_instance
  exact @Flat.comp _ _ _ _ _ this inferInstance

/-! ### Flat base change of global functions along a morphism to an object of the site -/

/-- Pullback of functions along a commutative square whose right side is a morphism of the site
`g : Z' ⟶ Z`: pulling back from `Z` to `W` and then along `q : W' ⟶ W` is pulling back along `g`
and then from `Z'` to `W'`. -/
theorem globalFunctionsMap_comp_pullbackToGlobalFunctions {W W' : AlgebraicSpaces B S hS}
    {Z Z' : BigFppfOver B S hS} (q : W' ⟶ W) (p : W ⟶ schemeSpace Z) (r : W' ⟶ schemeSpace Z')
    (g : Z' ⟶ Z) (h : q ≫ p = r ≫ schemeSpaceMap g) :
    (globalFunctionsMap B S hS q).comp (pullbackToGlobalFunctions B S hS W Z p) =
      (pullbackToGlobalFunctions B S hS W' Z' r).comp
        ((BigFppfOver.toScheme B S hS).map g).appTop.hom := by
  rw [← pullbackToGlobalFunctions_comp_left, h]
  exact RingHom.ext fun x => pullbackToGlobalFunctions_comp_schemeSpaceMap B S hS W' r g x

/-- Flat base change of global functions, as a ring isomorphism: for a flat morphism `g : Z' ⟶ Z`
of affine objects of the site and a quasi-compact separated `W` over `Z`, there is a bijective
ring map `Γ(Z') ⊗_{Γ(Z)} Γ(W) ⟶ Γ(W')` sending `t ⊗ 1` to the pullback of `t` and `1 ⊗ s` to
the image of `s`, where `W' = W ×_Z Z'`. -/
private theorem exists_bijective_tensor_globalFunctions (hZ : B.Contains (⊤_ Scheme.{u}))
    {Z Z' : BigFppfOver B S hS} (g : Z' ⟶ Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [Flat ((BigFppfOver.toScheme B S hS).map g)]
    {W W' : AlgebraicSpaces B S hS} (p : W ⟶ schemeSpace Z) (q : W' ⟶ W)
    (r : W' ⟶ schemeSpace Z') (hsq : IsPullback q.hom r.hom p.hom (yoneda.map g))
    (hqc : IsQuasiCompactSpace B S hS W.obj) (hsep : IsAbsolutelySeparated B S hS hZ W.obj)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)]
    (hT : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom)
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) (globalFunctions B S hS W.obj)]
    (hG : algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) (globalFunctions B S hS W.obj) =
      pullbackToGlobalFunctions B S hS W Z p) :
    ∃ Φ : Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) ⊗[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
        globalFunctions B S hS W.obj →+* globalFunctions B S hS W'.obj,
      Function.Bijective Φ ∧
        (∀ t, Φ (t ⊗ₜ 1) = pullbackToGlobalFunctions B S hS W' Z' r t) ∧
        ∀ s, Φ (1 ⊗ₜ s) = globalFunctionsMap B S hS q s := by
  classical
  let ψ' := pullbackToGlobalFunctions B S hS W' Z' r
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) (globalFunctions B S hS W'.obj) :=
    (ψ'.comp (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤))).toAlgebra
  have hcomm := globalFunctionsMap_comp_pullbackToGlobalFunctions q p r g
    (ObjectProperty.hom_ext _ hsq.w)
  let Φ := Algebra.TensorProduct.lift
    (⟨ψ', fun _ => rfl⟩ : Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)
      →ₐ[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)] globalFunctions B S hS W'.obj)
    (⟨globalFunctionsMap B S hS q, fun a => by
        rw [hG]
        exact (RingHom.congr_fun hcomm a).trans (congrArg ψ' (RingHom.congr_fun hT a).symm)⟩ :
      globalFunctions B S hS W.obj
        →ₐ[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)] globalFunctions B S hS W'.obj)
    (fun _ _ => Commute.all _ _)
  refine ⟨Φ.toRingHom, bijective_globalFunctions_baseChange_of_flat hZ g p.hom q r.hom hsq hqc hsep
    hT (fun _ => by rw [hG]; rfl) ψ' (fun _ => rfl) Φ.toRingHom
    (fun t s => Algebra.TensorProduct.lift_tmul _ _ _ t s), fun t => ?_, fun s => ?_⟩
  · change ψ' t * globalFunctionsMap B S hS q 1 = ψ' t
    rw [map_one, mul_one]
  · change ψ' 1 * globalFunctionsMap B S hS q s = _
    rw [map_one, one_mul]

/-- **Injectivity of pullback of functions to a generic fibre.**  Let `g : Z' ⟶ Z` be a flat
morphism of affine objects of the site making `Γ(Z')` a fraction ring of the domain `Γ(Z)`, let
`W` be a quasi-compact separated algebraic space over `Z` whose global functions are torsion free
over `Γ(Z)`, and let `W' = W ×_Z Z'`.  Then pullback of global functions `Γ(W) ⟶ Γ(W')` is
injective: by flat base change
(`AlgebraicGeometry.Space.bijective_globalFunctions_baseChange_of_flat`) it is
`Γ(W) ⟶ Γ(Z') ⊗_{Γ(Z)} Γ(W)`, which is injective by torsion freeness. -/
theorem injective_globalFunctionsMap_of_isFractionRing (hZ : B.Contains (⊤_ Scheme.{u}))
    {Z Z' : BigFppfOver B S hS} (g : Z' ⟶ Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [Flat ((BigFppfOver.toScheme B S hS).map g)]
    [IsDomain Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
    (hfrac : letI := ((BigFppfOver.toScheme B S hS).map g).appTop.hom.toAlgebra
      IsFractionRing Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤))
    {W W' : AlgebraicSpaces B S hS} (p : W ⟶ schemeSpace Z) (q : W' ⟶ W)
    (r : W' ⟶ schemeSpace Z') (hsq : IsPullback q.hom r.hom p.hom (yoneda.map g))
    (hqc : IsQuasiCompactSpace B S hS W.obj) (hsep : IsAbsolutelySeparated B S hS hZ W.obj)
    (htor : ∀ a : Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤), a ≠ 0 →
      ∀ s : globalFunctions B S hS W.obj, pullbackToGlobalFunctions B S hS W Z p a * s = 0 →
        s = 0) :
    Function.Injective (globalFunctionsMap B S hS q) := by
  classical
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) :=
    ((BigFppfOver.toScheme B S hS).map g).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) (globalFunctions B S hS W.obj) :=
    (pullbackToGlobalFunctions B S hS W Z p).toAlgebra
  have := hfrac
  obtain ⟨Φ, hΦ, -, hΦ2⟩ := exists_bijective_tensor_globalFunctions hZ g p q r hsq hqc hsep rfl rfl
  have hinj := injective_includeRight_of_forall_mul_eq_zero
    Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) (globalFunctions B S hS W.obj) htor
  intro s t hst
  refine hinj (hΦ.1 ?_)
  change Φ (1 ⊗ₜ s) = Φ (1 ⊗ₜ t)
  rw [hΦ2, hΦ2]
  exact hst

/-- **Flat base change of the condition `Γ(W) = Γ(Z)`.**  Let `g : Z' ⟶ Z` be a flat morphism of
affine objects of the site, let `W` be a quasi-compact separated algebraic space over `Z` such
that pullback of functions `Γ(Z) ⟶ Γ(W)` is bijective, and let `W' = W ×_Z Z'`.  Then pullback
of functions `Γ(Z') ⟶ Γ(W')` is bijective: by flat base change
(`AlgebraicGeometry.Space.bijective_globalFunctions_baseChange_of_flat`) it is
`Γ(Z') ⟶ Γ(Z') ⊗_{Γ(Z)} Γ(W) = Γ(Z') ⊗_{Γ(Z)} Γ(Z)`. -/
theorem bijective_pullbackToGlobalFunctions_of_isPullback (hZ : B.Contains (⊤_ Scheme.{u}))
    {Z Z' : BigFppfOver B S hS} (g : Z' ⟶ Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z')]
    [Flat ((BigFppfOver.toScheme B S hS).map g)]
    {W W' : AlgebraicSpaces B S hS} (p : W ⟶ schemeSpace Z) (q : W' ⟶ W)
    (r : W' ⟶ schemeSpace Z') (hsq : IsPullback q.hom r.hom p.hom (yoneda.map g))
    (hqc : IsQuasiCompactSpace B S hS W.obj) (hsep : IsAbsolutelySeparated B S hS hZ W.obj)
    (hbij : Function.Bijective (pullbackToGlobalFunctions B S hS W Z p)) :
    Function.Bijective (pullbackToGlobalFunctions B S hS W' Z' r) := by
  classical
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) :=
    ((BigFppfOver.toScheme B S hS).map g).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) (globalFunctions B S hS W.obj) :=
    (pullbackToGlobalFunctions B S hS W Z p).toAlgebra
  obtain ⟨Φ, hΦ, hΦ1, -⟩ := exists_bijective_tensor_globalFunctions hZ g p q r hsq hqc hsep rfl rfl
  have hi := bijective_includeLeft_of_bijective_algebraMap
    (T := Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤)) hbij
  have : ⇑(pullbackToGlobalFunctions B S hS W' Z' r) = ⇑Φ ∘ ⇑(Algebra.TensorProduct.includeLeft :
      Γ((BigFppfOver.toScheme B S hS).obj Z', ⊤) →ₐ[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)]
        _ ⊗[Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)] globalFunctions B S hS W.obj) :=
    funext fun t => (hΦ1 t).symm
  rw [this]
  exact hΦ.comp hi

/-! ### The fibre over the residue field of the generic point -/

/-- The fibre `X_k = X ×_Y Spec k` of a morphism of algebraic spaces over a field-valued point
`r : Spec k ⟶ Y`, as an algebraic space. -/
noncomputable abbrev fieldFibreSpace (f : X ⟶ Y) (r : FieldValuedPoint B S hS Y.1) :
    AlgebraicSpaces B S hS :=
  ⟨fieldFibre B S hS f.hom r, isAlgebraicSpace_fieldFibre X.2 Y.2 f.hom r⟩

/-- The projection `X_k ⟶ Spec k` of the fibre over a field-valued point. -/
noncomputable abbrev fieldFibreProjection (f : X ⟶ Y) (r : FieldValuedPoint B S hS Y.1) :
    fieldFibreSpace f r ⟶ schemeSpace (r.siteObject B S hS Y.1) :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- **Pasting the generic fibre of a chart onto the fibre over `Spec k`.**  If
`W' = W ×_V K` for the base change `W = X ×_Y V` of `f` along a chart `V ⟶ Y`, and
`K ⟶ V ⟶ Y` factors through `Spec k ⟶ Y`, then `W' = X_k ×_{Spec k} K`. -/
theorem isPullback_fieldFibre_lift {F G T W W' K V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {e : T ⟶ G} {pv : W ⟶ V} {iv : W ⟶ F} {c : V ⟶ G}
    (hsq : IsPullback pv iv c f) {q : W' ⟶ W} {rK : W' ⟶ K} {g : K ⟶ V}
    (hsqK : IsPullback q rK pv g) {g' : K ⟶ T} (hg' : g' ≫ e = g ≫ c) :
    IsPullback (pullback.lift (q ≫ iv) (rK ≫ g') (by
        rw [Category.assoc, ← hsq.w, ← Category.assoc, hsqK.w, Category.assoc, Category.assoc,
          hg'])) rK (pullback.snd f e) g' := by
  have hout := hsqK.paste_horiz hsq.flip
  rw [← hg'] at hout
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f e)
  rw [pullback.lift_fst]
  exact hout

/-- The generic fibre `(X ×_Y V) ×_V Spec Frac Γ(V)` of the base change of `f : X ⟶ Y` to an
affine étale chart `V` of `Y`, as an algebraic space. -/
noncomputable abbrev chartBaseChangeGenericFibre (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    [IsAffine V.obj.left.left.1] : AlgebraicSpaces B S hS :=
  ⟨pullback (chartBaseChangeProjection B S hS f V).hom
      (yoneda.map (totalFractionObjectMap B S hS V.obj.left)),
    isAlgebraicSpace_pullback B S hS _ _ (chartBaseChangeSpace B S hS f V).2
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)⟩

/-- The inclusion of the generic fibre of a chart into the base change of `f` to the chart. -/
noncomputable abbrev chartGenericFibreInclusion (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    [IsAffine V.obj.left.left.1] :
    chartBaseChangeGenericFibre f V ⟶ chartBaseChangeSpace B S hS f V :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The projection of the generic fibre of a chart to `Spec Frac Γ(V)`. -/
noncomputable abbrev chartGenericFibreProjection (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    [IsAffine V.obj.left.left.1] :
    chartBaseChangeGenericFibre f V ⟶ schemeSpace (totalFractionObject B S hS V.obj.left) :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- **Stacks 0AYI, the generic fibre of a chart sees all functions.**  Under hypotheses (1)-(5) of
Stacks 0AYI, for an affine integral étale chart `V` of `Y`, pullback of global functions from
`X ×_Y V` to its generic fibre `(X ×_Y V) ×_V Spec Frac Γ(V)` is injective: `Γ(X ×_Y V)` is
torsion free over `Γ(V)` and flat base change identifies the generic fibre's functions with
`Frac Γ(V) ⊗_{Γ(V)} Γ(X ×_Y V)`. -/
theorem injective_globalFunctionsMap_chartGenericFibreInclusion (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hYint : IsIntegralSpace B S hS Y.1) {ξ : points B S hS Y.1}
    (hξ : IsGenericPoint ξ Set.univ)
    (hXred : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T))
    (h5 : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (V : SmallEtale B S hS Y.1) [IsAffine V.obj.left.left.1]
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))] :
    Function.Injective (globalFunctionsMap B S hS (chartGenericFibreInclusion f V)) := by
  have hZ := BigFppfSite.contains_terminal B
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) := ‹IsAffine V.obj.left.left.1›
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (totalFractionObject B S hS V.obj.left)) := by
    change IsAffine (Spec _)
    infer_instance
  have : IsIntegral V.obj.left.left.1 :=
    ‹IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))›
  have : IsDomain Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤) :=
    (inferInstance : IsDomain Γ(V.obj.left.left.1, ⊤))
  have hXdec : IsDecentSpace B S hS X.1 :=
    isDecentSpace_source_of_isQuasiSeparated B S hS X.2 Y.2 f.hom
      (isQuasiSeparated_of_isSeparated B S hS hf.1) (IsIntegralSpace.isDecentSpace B S hS Y.1 hYint)
  refine injective_globalFunctionsMap_of_isFractionRing hZ
    (totalFractionObjectMap B S hS V.obj.left)
    (Scheme.isFractionRing_fromSpecTotalFractionRing_appTop _)
    (ObjectProperty.homMk (chartBaseChangeProjection B S hS f V).hom) _ _
    (IsPullback.of_hasPullback _ _) ?_ ?_ fun a ha s hs => ?_
  · exact isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS _
      ⟨V.obj.left, inferInstance, ⟨Iso.refl _⟩⟩
      (isQuasiCompact_chartBaseChangeProjection B S hS f V hf.2.1.2)
  · exact isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ V.obj.left inferInstance _
      (isSeparated_of_isPullback B S hS (isPullback_chartBaseChangeProjection B S hS f V).flip hf.1)
  · exact eq_zero_of_mul_eq_zero_chartBaseChange B S hS f hXdec hXred hYint hξ h5 V _
      (globalFunctionsChartRestriction_comp_pullbackToGlobalFunctions _ _ _) ha hs

/-- **Stacks 0AYI, the generic fibre of a chart has functions `Frac Γ(V)`.**  Let `f : X ⟶ Y` be
proper with `Y` integral with generic point `ξ`, represented by a quasi-compact monomorphism
`r : Spec κ ⟶ Y`, such that pullback of functions `κ ⟶ Γ(X_ξ)` is bijective (hypothesis (6) of
Stacks 0AYI).  Then for an affine integral étale chart `V` of `Y`, pullback of functions
`Frac Γ(V) ⟶ Γ((X ×_Y V) ×_V Spec Frac Γ(V))` is bijective.

`Spec Frac Γ(V) ⟶ Y` factors through `r` (Stacks 0H1T), so the generic fibre of the chart is
`X_ξ ×_{Spec κ} Spec Frac Γ(V)`, and flat base change along `Spec Frac Γ(V) ⟶ Spec κ` carries
hypothesis (6) over. -/
theorem bijective_pullbackToGlobalFunctions_chartGenericFibreProjection (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hYint : IsIntegralSpace B S hS Y.1) {ξ : points B S hS Y.1}
    (hξ : IsGenericPoint ξ Set.univ) (r : FieldValuedPoint B S hS Y.1)
    (hr : r.class B S hS Y.1 = ξ) (hmono : Mono (fieldMorphism B S hS Y.1 r))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y.1 r))
    (h6 : Function.Bijective (pullbackToGlobalFunctions B S hS (fieldFibreSpace f r)
      (r.siteObject B S hS Y.1) (fieldFibreProjection f r)))
    (V : SmallEtale B S hS Y.1) [IsAffine V.obj.left.left.1]
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj V.obj.left)] :
    Function.Bijective (pullbackToGlobalFunctions B S hS (chartBaseChangeGenericFibre f V) _
      (chartGenericFibreProjection f V)) := by
  have hZ := BigFppfSite.contains_terminal B
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (totalFractionObject B S hS V.obj.left)) := by
    change IsAffine (Spec _)
    infer_instance
  have haffκ : IsAffine ((BigFppfOver.toScheme B S hS).obj (r.siteObject B S hS Y.1)) := by
    change IsAffine (Spec _)
    infer_instance
  have := subsingleton_toScheme_siteObject B S hS Y.1 r
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj (r.siteObject B S hS Y.1)) := by
    change IsIntegral (Spec _)
    infer_instance
  obtain ⟨gK', hgK'⟩ := exists_totalFractionObject_comp_fieldMorphism hYint hξ V r hr hmono hqc
  have hsq := isPullback_fieldFibre_lift (isPullback_chartBaseChangeProjection B S hS f V)
    (IsPullback.of_hasPullback _ _) (e := fieldMorphism B S hS Y.1 r) hgK'
  refine bijective_pullbackToGlobalFunctions_of_isPullback hZ gK' (fieldFibreProjection f r)
    (ObjectProperty.homMk _) (chartGenericFibreProjection f V) hsq ?_ ?_ h6
  · exact isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS _
      ⟨r.siteObject B S hS Y.1, haffκ, ⟨Iso.refl _⟩⟩
      (isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f.hom _) hf.2.1.2)
  · exact isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ _ haffκ _
      (isSeparated_of_isPullback B S hS (IsPullback.of_hasPullback f.hom _) hf.1)

/-- On the generic fibre of a chart, pulling back functions from `V` through `X ×_Y V` is pulling
them back to `Frac Γ(V)` and then to the generic fibre. -/
theorem globalFunctionsMap_chartGenericFibreInclusion_comp (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    [IsAffine V.obj.left.left.1] :
    (globalFunctionsMap B S hS (chartGenericFibreInclusion f V)).comp
        (pullbackToGlobalFunctions B S hS (chartBaseChangeSpace B S hS f V) V.obj.left
          (ObjectProperty.homMk (chartBaseChangeProjection B S hS f V).hom)) =
      ((pullbackToGlobalFunctions B S hS (chartBaseChangeGenericFibre f V) _
          (chartGenericFibreProjection f V)).comp
        (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(V.obj.left.left.1, ⊤)))).inv.hom).comp
        (algebraMap Γ(V.obj.left.left.1, ⊤) (FractionRing Γ(V.obj.left.left.1, ⊤))) := by
  refine (globalFunctionsMap_comp_pullbackToGlobalFunctions _ _ _
    (totalFractionObjectMap B S hS V.obj.left)
    (ObjectProperty.hom_ext _ (IsPullback.of_hasPullback _ _).w)).trans ?_
  exact congrArg (RingHom.comp (pullbackToGlobalFunctions B S hS (chartBaseChangeGenericFibre f V) _
    (chartGenericFibreProjection f V))) (Scheme.fromSpecTotalFractionRing_appTop_eq _)

/-- **Stacks 0AYI, conclusion (1), over a normal integral affine chart.**  Under the hypotheses of
Stacks 0AYI, for a normal integral affine étale chart `V = Spec A` of `Y`, pullback of functions
`A ⟶ Γ(X ×_Y V, 𝒪)` is bijective.

With `K` the fraction field of `A` and `X_K = (X ×_Y V) ×_V Spec K`: pullback `A ⟶ Γ(X ×_Y V)` is
integral (`f` is universally closed), `Γ(X ×_Y V) ⟶ Γ(X_K)` is injective
(`AlgebraicGeometry.Space.injective_globalFunctionsMap_chartGenericFibreInclusion`), and
`K ⟶ Γ(X_K)` is bijective
(`AlgebraicGeometry.Space.bijective_pullbackToGlobalFunctions_chartGenericFibreProjection`).
An element of `Γ(X ×_Y V)` is then an element of `K` integral over the normal domain `A`. -/
theorem bijective_of_isNormalIntegralAffineChart (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hYint : IsIntegralSpace B S hS Y.1) {ξ : points B S hS Y.1} (hξ : IsGenericPoint ξ Set.univ)
    (hXred : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T))
    (h5 : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (r : FieldValuedPoint B S hS Y.1) (hr : r.class B S hS Y.1 = ξ)
    (hmono : Mono (fieldMorphism B S hS Y.1 r))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y.1 r))
    (h6 : Function.Bijective (pullbackToGlobalFunctions B S hS (fieldFibreSpace f r)
      (r.siteObject B S hS Y.1) (fieldFibreProjection f r)))
    (V : SmallEtale B S hS Y.1) (hV : IsNormalIntegralAffineChart B S hS Y.1 V)
    (ψ : Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤) →+*
      globalFunctions B S hS (chartBaseChangeSpace B S hS f V).obj)
    (hψ : ∀ c : SmallEtale B S hS (chartBaseChangeSpace B S hS f V).obj,
      (globalFunctionsChartRestriction B S hS _ c).comp ψ =
        ((BigFppfOver.toScheme B S hS).map (smallEtaleChartMapToBase B S hS
          (chartBaseChangeProjection B S hS f V).hom c)).appTop.hom) :
    Function.Bijective ψ := by
  obtain ⟨haff, hnorm, hint⟩ := hV
  have : IsAffine V.obj.left.left.1 := haff
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V)) :=
    hint
  have : IsIntegral ((BigFppfOver.toScheme B S hS).obj V.obj.left) := hint
  have : IsIntegral V.obj.left.left.1 := hint
  have : IsNormal V.obj.left.left.1 := hnorm
  have : Nonempty (⊤ : V.obj.left.left.1.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  have : IsDomain Γ(V.obj.left.left.1, ⊤) := inferInstance
  have : IsIntegrallyClosed Γ(V.obj.left.left.1, ⊤) :=
    (isNormal_iff_forall_affineOpen_normal _).mp inferInstance ⟨⊤, isAffineOpen_top _⟩
      inferInstance
  have : IsDomain Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤) :=
    ‹IsDomain Γ(V.obj.left.left.1, ⊤)›
  have : IsIntegrallyClosed
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤) :=
    ‹IsIntegrallyClosed Γ(V.obj.left.left.1, ⊤)›
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
      (FractionRing Γ(V.obj.left.left.1, ⊤)) :=
    (inferInstance : Algebra Γ(V.obj.left.left.1, ⊤) (FractionRing Γ(V.obj.left.left.1, ⊤)))
  have : IsFractionRing
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V), ⊤)
      (FractionRing Γ(V.obj.left.left.1, ⊤)) :=
    (inferInstance : IsFractionRing Γ(V.obj.left.left.1, ⊤) (FractionRing Γ(V.obj.left.left.1, ⊤)))
  have hψint : ψ.IsIntegral := isIntegral_globalFunctions_of_universallyClosed B S hS haff _
    (universallyClosed_chartBaseChangeProjection B S hS f V hf.2.2) ψ hψ
  refine RingHom.bijective_of_isIntegral_of_injective_comp_eq ψ hψint
    (globalFunctionsMap B S hS (chartGenericFibreInclusion f V))
    (injective_globalFunctionsMap_chartGenericFibreInclusion f hf hYint hξ hXred h5 V)
    ((pullbackToGlobalFunctions B S hS (chartBaseChangeGenericFibre f V) _
        (chartGenericFibreProjection f V)).comp
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(V.obj.left.left.1, ⊤)))).inv.hom)
    ((bijective_pullbackToGlobalFunctions_chartGenericFibreProjection f hf hYint hξ r hr hmono
      hqc h6 V).comp (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.bijective) ?_
  rw [eq_pullbackToGlobalFunctions _ _
    (ObjectProperty.homMk (chartBaseChangeProjection B S hS f V).hom) ψ hψ]
  exact globalFunctionsMap_chartGenericFibreInclusion_comp f V

/-- **Stacks 0AYI, conclusion (1): `f_*𝒪_X = 𝒪_Y`.**  Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` such that
1. `f` is proper,
2. `Y` is integral with generic point `ξ`,
3. `Y` is normal,
4. `X` is reduced,
5. every generic point of an irreducible component of `|X|` maps to `ξ`,
6. `H⁰(X_ξ, 𝒪) = κ(ξ)`: for the residue field `Spec κ(ξ) ⟶ Y` at `ξ` (a quasi-compact
   monomorphism from the spectrum of a field representing `ξ`, which exists as `Y` is decent),
   pullback of functions `κ(ξ) ⟶ Γ(X_ξ, 𝒪)` to the fibre `X_ξ = X ×_Y Spec κ(ξ)` is bijective.

Then the structure map `𝒪_Y ⟶ f_*𝒪_X` of the morphism of small étale ringed topoi is an
isomorphism.  This is conclusion (1) of Stacks 0AYI; conclusion (2), geometric connectedness of
the fibres, is not part of this statement.

The normal integral affine étale charts of `Y` have enough objects
(`AlgebraicGeometry.Space.hasEnoughObjects_isNormalIntegralAffineChart`), so it suffices that
`Γ(V) ⟶ Γ(X ×_Y V)` is bijective for each of them
(`AlgebraicGeometry.Space.isIso_fSharp_of_forall_bijective_globalFunctions`), which is
`AlgebraicGeometry.Space.bijective_of_isNormalIntegralAffineChart`.  Unlike the proof in the
Stacks project this route needs no Stein factorization (Stacks 0A1C): the chart case is an
integral extension of the normal domain `Γ(V)` embedded in its fraction field. -/
theorem isIso_fSharp_of_isProper_of_trivialGenericFibre (f : X ⟶ Y)
    (hf : IsProper B S hS f.hom) (hYint : IsIntegralSpace B S hS Y.1) {ξ : points B S hS Y.1}
    (hξ : IsGenericPoint ξ Set.univ)
    (hYnorm : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsNormal T))
    (hXred : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T))
    (h5 : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (r : FieldValuedPoint B S hS Y.1) (hr : r.class B S hS Y.1 = ξ)
    (hmono : Mono (fieldMorphism B S hS Y.1 r))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS Y.1 r))
    (h6 : Function.Bijective (pullbackToGlobalFunctions B S hS (fieldFibreSpace f r)
      (r.siteObject B S hS Y.1) (fieldFibreProjection f r))) :
    IsIso (smallEtaleRingedToposHom B S hS f).fSharp :=
  isIso_fSharp_of_forall_bijective_globalFunctions B S hS f
    (hasEnoughObjects_isNormalIntegralAffineChart B S hS Y hYnorm hYint)
    (bijective_of_isNormalIntegralAffineChart f hf hYint hξ hXred h5 r hr hmono hqc h6)

end AlgebraicGeometry.Space

end
