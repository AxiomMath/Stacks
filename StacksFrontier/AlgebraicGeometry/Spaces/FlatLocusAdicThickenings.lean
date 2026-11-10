module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFieldSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAdicThickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTower
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChangeAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.RingTheory.Flat.AdicThickeningWeaklyEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite

/-!
# Stacks 08VP: flatness above `V(I)` from flatness of the infinitesimal thickenings

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `X` an algebraic space locally of finite
presentation over `S = Spec A`.  For `n ≥ 0` let `Xₙ = Spec(A/Iⁿ⁺¹) ×_S X` be the adic fibres of
`X` (`AlgebraicGeometry.Space.adicFibre`).  **Stacks 08VP** says that if `F` is a coherent
`𝒪_X`-module whose pullback `Fₙ` to every `Xₙ` is flat over `Spec(A/Iⁿ⁺¹)`, then the (open)
locus of `|X|` where `F` is flat over `S` contains the inverse image of `V(I)`.

## Main results

* `AlgebraicGeometry.Space.isOpen_flatLocus_and_preimage_subset_flatLocus`: **Stacks 08VP.**
* `AlgebraicGeometry.Space.flat_quotient_tensor_geometricModuleStalk`: the step at one adic
  fibre — flatness of `Fₙ` at a geometric point `z̄` of `Xₙ` gives flatness of
  `(A/Iⁿ⁺¹) ⊗_A F_{x̄}` over `A/Iⁿ⁺¹`, where `x̄` is the image of `z̄`.
* `AlgebraicGeometry.Space.weaklyEtale_etaleLocalRingGerm`: the étale local ring of an algebraic
  space at a geometric point is weakly étale over the ring of an affine pointed étale chart.
* `AlgebraicGeometry.Space.exists_geometricPoint_adicFibre`: a geometric point above
  `Spec(A/Iⁿ⁺¹)` lifts to the adic fibre `Xₙ`.

## Implementation notes

The source proves the lemma on an affine étale chart, by Algebra, Lemma 0523.  Here it is
proved at the geometric points, which is how the flat locus of Stacks 05VV (1) is read by
`AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint`.  The rings involved are
étale local rings; the étale local rings of `Spec A` and of `Spec(A/Iⁿ⁺¹)` are weakly étale over
`A` and `A/Iⁿ⁺¹` (Stacks 04KF and 0993), and the étale local ring of `Xₙ` is weakly étale over
the tensor product of the neighbouring ones
(`AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_weaklyEtale`).  These two facts reduce the
hypothesis on `Fₙ` to flatness of `(A/Iⁿ⁺¹) ⊗_A F_{x̄}`, without any identification of the étale
local ring of a thickening with a quotient of the étale local ring of `Spec A`; see
`StacksFrontier/RingTheory/Flat/AdicThickeningWeaklyEtale.lean`.

The thickenings are indexed from `0`, the `n`-th being `Spec(A/Iⁿ⁺¹)`; the source's `Sₙ` for
`n ≥ 1` is the `(n - 1)`-st.  The site's base scheme is `Spec A`, the convention of the
Grothendieck existence theorem of Stacks 08B7.

## References

* [Stacks Project, Tag 08VP](https://stacks.math.columbia.edu/tag/08VP)
* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 0993](https://stacks.math.columbia.edu/tag/0993)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The étale local ring is weakly étale over the ring of an affine chart.**  For a small
étale neighbourhood `V` of a geometric point `x̄` of an algebraic space whose chart is affine, the
germ map `Γ(V, 𝒪_V) → 𝒪_{F, x̄}` is weakly étale: by Stacks 04KF it is the canonical map to the
strict henselization of the chart at the chosen point, whose spectrum is weakly étale over the
chart by Stacks 0993. -/
theorem weaklyEtale_etaleLocalRingGerm (hF : IsAlgebraicSpace B S hS F)
    {x : GeometricPoint B S hS F} (V : SmallEtaleNeighborhood x)
    [IsAffine (neighborhoodChartScheme V)] :
    @Algebra.WeaklyEtale Γ(neighborhoodChartScheme V, ⊤) (etaleLocalRing B S hS F x) _ _
      (etaleLocalRingGerm B S hS F x (Opposite.op V)).toAlgebra := by
  let E := bigEtaleSiteOfFppfSite B
  have cV : E.Contains (neighborhoodChartScheme V) := V.chart.obj.left.left.property
  let X := neighborhoodChartScheme V
  let eV := (etaleLocalRingEquivChart hF V E cV)
  let sa := strictHenselizationToBase E X cV (chartGeometricPoint V)
  have wa : WeaklyEtale sa := weaklyEtale_strictHenselizationToBase E _ cV _
  have htf := weaklyEtale_tfae sa
  dsimp only at htf
  have h12 := htf.out 1 2
  have h1 := h12.mp wa ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) le_top
  -- the ring map on global sections, followed by `ΓSpecIso`, is the germ map of the scheme
  have happ := strictHenselizationToBase_appTop E X cV (chartGeometricPoint V)
  let R := ↥(_root_.AlgebraicGeometry.etaleLocalRing E X cV (chartGeometricPoint V))
  let g : Γ(X, ⊤) →+* R := ((X.presheaf.germ ⊤
      ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)) trivial) ≫
      CommRingCat.ofHom (structureSheafStalkFromLocalRing E X cV (chartGeometricPoint V))).hom
  have hg : @Algebra.WeaklyEtale Γ(X, ⊤) R _ _ g.toAlgebra := by
    let eR : Γ(Spec (.of R), ⊤) ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
    have hgeq : g = eR.toRingHom.comp (sa.appLE ⊤ ⊤ le_top).hom := by
      have h := congrArg (fun k => k.hom) happ
      simp only [CommRingCat.hom_comp] at h
      exact h.symm.trans rfl
    rw [hgeq]
    apply weaklyEtale_of_comp_ringEquiv _ (RingEquiv.refl _) eR.symm
    have hc : (eR.symm.toRingHom.comp (eR.toRingHom.comp (sa.appLE ⊤ ⊤ le_top).hom)).comp
        (RingEquiv.refl Γ(X, ⊤)).toRingHom = (sa.appLE ⊤ ⊤ le_top).hom := by
      ext a
      simp
    rwa [hc]
  apply weaklyEtale_of_comp_ringEquiv _ (RingEquiv.refl _) eV.1
  have hc : (eV.1.toRingHom.comp (etaleLocalRingGerm B S hS F x (Opposite.op V))).comp
      (RingEquiv.refl Γ(neighborhoodChartScheme V, ⊤)).toRingHom = g := by
    ext a
    exact eV.2.1 a
  have key : ∀ φ : Γ(neighborhoodChartScheme V, ⊤) →+* R, φ = g →
      @Algebra.WeaklyEtale _ _ _ _ φ.toAlgebra := by
    rintro φ rfl
    exact hg
  exact key _ hc

/-- **The canonical map of étale local rings of representables reads off the chart germs.** For a
morphism `h : U ⟶ V` of the big fppf site and a geometric point `ȳ` of `yoneda.obj U`, the
homomorphism of étale local rings induced by `yoneda.map h` precomposed with the germ map of the
identity chart of `yoneda.obj V` is the germ map of the identity chart of `yoneda.obj U` after
pulling back along `h`. -/
theorem etaleLocalRingMap_yoneda_comp_germ {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (y : GeometricPoint B S hS (yoneda.obj U)) :
    (etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U) (yoneda.map h) y).comp
        (etaleLocalRingGerm B S hS (yoneda.obj V) (geometricPointMap (yoneda.map h) y)
          (Opposite.op (yonedaIdentityNeighborhood V (geometricPointMap (yoneda.map h) y)))) =
      (etaleLocalRingGerm B S hS (yoneda.obj U) y
          (Opposite.op (yonedaIdentityNeighborhood U y))).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map h).op).hom :=
  (etaleLocalRingMap_isEtaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U) (yoneda.map h) y
    (yonedaIdentityNeighborhood U y)
    (yonedaIdentityNeighborhood V (geometricPointMap (yoneda.map h) y)) h
    (by simp) rfl).symm

/-- **The étale local ring of a represented affine scheme is weakly étale over its ring of
functions.** -/
theorem weaklyEtale_etaleLocalRingGerm_yoneda (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (y : GeometricPoint B S hS (yoneda.obj U)) :
    @Algebra.WeaklyEtale Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      (etaleLocalRing B S hS (yoneda.obj U) y) _ _
      (etaleLocalRingGerm B S hS (yoneda.obj U) y
        (Opposite.op (yonedaIdentityNeighborhood U y))).toAlgebra :=
  have : IsAffine (neighborhoodChartScheme (yonedaIdentityNeighborhood U y)) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  weaklyEtale_etaleLocalRingGerm (isAlgebraicSpace_yoneda B S hS U)
    (yonedaIdentityNeighborhood U y)

/-! ### The adic fibres of an algebraic space over an affine base -/

section AdicFibre

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))

/-- The `n`-th adic fibre `Spec(A/Iⁿ⁺¹) ×_{Spec A} X` of an algebraic space over `Spec A`, as an
algebraic space over `Spec A`. -/
abbrev adicFibreSpaceOf (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (n : ℕ) : AlgebraicSpaces B (Spec (.of A)) hA :=
  ⟨adicFibre A I B hA (contains_adicThickening A I B hA) f.hom n,
    isAlgebraicSpace_adicFibre A I B hA (contains_adicThickening A I B hA) X.2 f.hom n⟩

/-- The inclusion `Xₙ ⟶ X` of the `n`-th adic fibre. -/
abbrev adicFibreInclusion (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (n : ℕ) : adicFibreSpaceOf A I B hA X f n ⟶ X :=
  ObjectProperty.homMk (pullback.fst _ _)

/-- The projection `Xₙ ⟶ Spec(A/Iⁿ⁺¹)` of the `n`-th adic fibre. -/
abbrev adicFibreProjection (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (n : ℕ) :
    adicFibreSpaceOf A I B hA X f n ⟶
      schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n) :=
  ObjectProperty.homMk (pullback.snd _ _)

/-- The adic fibre is the fibre product of algebraic spaces. -/
theorem isPullback_adicFibre (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (n : ℕ) :
    IsPullback (adicFibreInclusion A I B hA X f n) (adicFibreProjection A I B hA X f n) f
      (schemeSpaceMap (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n)) :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B (Spec (.of A)) hA F)) (IsPullback.of_hasPullback _ _)

/-- The thickening `Spec(A/Iⁿ⁺¹) ⟶ Spec A` is a closed immersion of algebraic spaces. -/
theorem isClosedImmersion_adicThickeningMap (n : ℕ) :
    IsClosedImmersion B (Spec (.of A)) hA
      (schemeSpaceMap (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n)).hom :=
  (presheaf_yoneda_map_iff B (Spec (.of A)) hA inferInstance _).2
    (IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective)

/-- The coordinate map `A → 𝒪_{Spec A, ȳ}` to the étale local ring of the base at a geometric
point: the germ map of the identity chart read through `Γ(Spec A, 𝒪) = A`. -/
def baseGerm (y : GeometricPoint B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA))) :
    A →+* etaleLocalRing B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA)) y :=
  (etaleLocalRingGerm B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA)) y
    (Opposite.op (yonedaIdentityNeighborhood (baseObject A B hA) y))).comp
      (Scheme.ΓSpecIso (.of A)).inv.hom

/-- The coordinate map `A/Iⁿ⁺¹ → 𝒪_{Spec(A/Iⁿ⁺¹), ȳ}` to the étale local ring of a thickening. -/
def thickeningGerm (n : ℕ) (y : GeometricPoint B (Spec (.of A)) hA
    (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n))) :
    A ⧸ I ^ (n + 1) →+* etaleLocalRing B (Spec (.of A)) hA
      (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n)) y :=
  (etaleLocalRingGerm B (Spec (.of A)) hA _ y
    (Opposite.op (yonedaIdentityNeighborhood _ y))).comp
      (Scheme.ΓSpecIso (.of (A ⧸ I ^ (n + 1)))).inv.hom

/-- A ring map out of `C ≃ Γ(U, 𝒪)` that is the germ map of the identity chart of an affine
represented `U` transported along the isomorphism is weakly étale. -/
private theorem weaklyEtale_of_eq_germ_comp_symm (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)]
    (y : GeometricPoint B (Spec (.of A)) hA (yoneda.obj U)) {C : Type u} [CommRing C]
    (e : Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) ≃+* C)
    (φ : C →+* etaleLocalRing B (Spec (.of A)) hA (yoneda.obj U) y)
    (hφ : φ = (etaleLocalRingGerm B (Spec (.of A)) hA (yoneda.obj U) y
      (Opposite.op (yonedaIdentityNeighborhood U y))).comp e.symm.toRingHom) :
    @Algebra.WeaklyEtale C _ _ _ φ.toAlgebra := by
  refine weaklyEtale_of_comp_ringEquiv _ e (RingEquiv.refl _) ?_
  have hc : ((RingEquiv.refl _).toRingHom.comp φ).comp e.toRingHom =
      etaleLocalRingGerm B (Spec (.of A)) hA (yoneda.obj U) y
        (Opposite.op (yonedaIdentityNeighborhood U y)) := by
    subst hφ
    ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_refl,
      RingHom.id_apply, RingEquiv.coe_toRingHom]
    exact (RingHom.comp_apply _ _ _).trans (RingHom.congr_arg _ (e.symm_apply_apply a))
  rw [hc]
  exact weaklyEtale_etaleLocalRingGerm_yoneda U y

/-- The coordinate map of the base is weakly étale. -/
theorem weaklyEtale_baseGerm
    (y : GeometricPoint B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA))) :
    @Algebra.WeaklyEtale A _ _ _ (baseGerm A B hA y).toAlgebra := by
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  exact weaklyEtale_of_eq_germ_comp_symm A B hA _ y
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv _ rfl

/-- The coordinate map of a thickening is weakly étale. -/
theorem weaklyEtale_thickeningGerm (n : ℕ) (y : GeometricPoint B (Spec (.of A)) hA
    (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n))) :
    @Algebra.WeaklyEtale (A ⧸ I ^ (n + 1)) _ _ _ (thickeningGerm A I B hA n y).toAlgebra := by
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n)) :=
    inferInstanceAs (IsAffine (Spec (.of (A ⧸ I ^ (n + 1)))))
  exact weaklyEtale_of_eq_germ_comp_symm A B hA _ y
    (Scheme.ΓSpecIso (.of (A ⧸ I ^ (n + 1)))).commRingCatIsoToRingEquiv _ rfl

/-- **The coordinate maps are compatible with the thickening.**  For a geometric point `ȳₙ` of
`Spec(A/Iⁿ⁺¹)` and a geometric point `ȳ` of `Spec A` equal to its image, the composite
`A → 𝒪_{Spec A, ȳ} → 𝒪_{Spec(A/Iⁿ⁺¹), ȳₙ}` is `A → A/Iⁿ⁺¹ → 𝒪_{Spec(A/Iⁿ⁺¹), ȳₙ}`. -/
theorem etaleLocalRingMap_comp_baseGerm (n : ℕ) (yn : GeometricPoint B (Spec (.of A)) hA
    (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n)))
    (y : GeometricPoint B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA)))
    (hy : y = geometricPointMap
      (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n)) yn) :
    ((eqToHom (congrArg (etaleLocalRing B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA))) hy) ≫
        CommRingCat.ofHom (etaleLocalRingMap (isAlgebraicSpace_yoneda B (Spec (.of A)) hA _)
          (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n))
            yn)).hom).comp
        (baseGerm A B hA y) =
      (thickeningGerm A I B hA n yn).comp (Ideal.Quotient.mk (I ^ (n + 1))) := by
  subst hy
  simp only [eqToHom_refl, Category.id_comp, CommRingCat.hom_ofHom]
  ext a
  have h := RingHom.congr_fun (etaleLocalRingMap_yoneda_comp_germ
    (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n) yn)
    ((Scheme.ΓSpecIso (.of A)).inv a)
  have hΓ := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) a
  simp only [RingHom.comp_apply, baseGerm, thickeningGerm]
  refine h.trans ?_
  exact congrArg (fun t => etaleLocalRingGerm B (Spec (.of A)) hA _ yn
    (Opposite.op (yonedaIdentityNeighborhood _ yn)) t) hΓ.symm

/-! ### Geometric points above `V(I)` -/

/-- Morphisms into the terminal object `Spec A` of the big fppf category over `Spec A` agree. -/
theorem hom_baseObject_ext {U : BigFppfOver B (Spec (.of A)) hA} (a b : U ⟶ baseObject A B hA) :
    a = b := by
  apply Over.OverMorphism.ext
  exact (Category.comp_id _).symm.trans (((Over.w a).trans (Over.w b).symm).trans
    (Category.comp_id _))

/-- Morphisms of presheaves into the representable presheaf of `Spec A` over `Spec A` agree. -/
theorem hom_yoneda_baseObject_ext {P : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (a b : P ⟶ yoneda.obj (baseObject A B hA)) : a = b := by
  ext U t
  exact hom_baseObject_ext A B hA _ _

omit hA in
/-- A morphism from the spectrum of a field to `Spec A` factors through `Spec(A/J)` as soon as its
composite with a morphism from the spectrum of a field extension does. -/
theorem exists_factor_quotient_of_field_extension
    {K L : Type u} [Field K] [Field L] (J : Ideal A) (g₀ : Spec (.of K) ⟶ Spec (.of A))
    (g : Spec (.of L) ⟶ Spec (.of K)) (h : Spec (.of L) ⟶ Spec (.of (A ⧸ J)))
    (comm : g ≫ g₀ = h ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :
    ∃ q : Spec (.of K) ⟶ Spec (.of (A ⧸ J)),
      q ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = g₀ := by
  let φ := (Spec.preimage g₀).hom
  have hker : J ≤ RingHom.ker φ := by
    intro a ha
    apply (Spec.preimage g).hom.injective
    change ((Spec.preimage g₀) ≫ (Spec.preimage g)) a = (Spec.preimage g).hom 0
    rw [← Spec.preimage_comp, comm, Spec.preimage_comp]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift J φ hker)), ?_⟩
  apply Spec.homEquiv.injective
  simp only [Spec.homEquiv_apply, Spec.preimage_comp, Spec.preimage_map]
  ext a
  exact Ideal.Quotient.lift_mk J φ hker

omit hA in
/-- A morphism from the spectrum of a field to `Spec A` factoring through `Spec(A/J)` factors
through `Spec(A/J')` for every ideal `J' ≤ J`. -/
theorem exists_factor_quotient_of_le {K : Type u} [Field K] {J J' : Ideal A} (hJ : J' ≤ J)
    (g₀ : Spec (.of K) ⟶ Spec (.of A))
    (h : ∃ q : Spec (.of K) ⟶ Spec (.of (A ⧸ J)),
      q ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = g₀) :
    ∃ q : Spec (.of K) ⟶ Spec (.of (A ⧸ J')),
      q ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) = g₀ := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨q ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp]
  rfl

/-- **A geometric point above `V(I)` lifts to every adic fibre.**  If the structure morphism
`Spec k ⟶ Spec A` of a geometric point of `X` factors through `Spec(A/Iⁿ⁺¹)`, the point lifts to
a geometric point of the adic fibre `Xₙ`. -/
theorem exists_geometricPoint_adicFibre (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (n : ℕ)
    (x : GeometricPoint B (Spec (.of A)) hA X.1)
    (h : ∃ q : Spec (.of x.val.carrier) ⟶ adicThickening A I n,
      q ≫ adicThickeningι A I n = x.val.toBase) :
    ∃ z : GeometricPoint B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1,
      geometricPointMap (adicFibreInclusion A I B hA X f n).hom z = x := by
  obtain ⟨g, hg⟩ := h
  let Q := adicThickeningObject A I B hA (contains_adicThickening A I B hA) n
  let a : x.val.siteObject ⟶ Q := Over.homMk (ObjectProperty.homMk g)
    (by apply ObjectProperty.hom_ext; exact hg)
  let t : yoneda.obj x.val.siteObject ⟶ X.1 := yonedaEquiv.symm x.val.value
  have comm : t ≫ f.hom = yoneda.map a ≫
      yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n) :=
    hom_yoneda_baseObject_ext A B hA _ _
  let v := yonedaEquiv (pullback.lift t (yoneda.map a) comm)
  refine ⟨⟨{ x.val with value := v }, x.property⟩, ?_⟩
  apply Subtype.ext
  have hv : yonedaEquiv (pullback.lift t (yoneda.map a) comm ≫ pullback.fst _ _) =
      x.val.value :=
    (congrArg yonedaEquiv (pullback.lift_fst t (yoneda.map a) comm)).trans
      (yonedaEquiv.apply_symm_apply _)
  rw [yonedaEquiv_comp] at hv
  obtain ⟨⟨c, hc, tb, val⟩, hx⟩ := x
  simp only [geometricPointMap, FieldValuedPoint.map]
  congr 1

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **A point of `X` above `V(I)` is represented by field points over `Spec(A/I)`.**  If the
image of the class of a field point `p` of `X` lies in the image of `|Spec(A/I)| ⟶ |Spec A|`,
the structure morphism of `p` factors through `Spec(A/I)`. -/
theorem exists_factor_of_pointsMap_mem_range (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (p : FieldValuedPoint B (Spec (.of A)) hA X.1)
    (hp : pointsMap B (Spec (.of A)) hA X.1 f.hom (p.class B (Spec (.of A)) hA X.1) ∈
      Set.range (pointsMap B (Spec (.of A)) hA
        (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0))
        (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) 0)))) :
    ∃ q : Spec (.of p.carrier) ⟶ adicThickening A I 0, q ≫ adicThickeningι A I 0 = p.toBase := by
  obtain ⟨y, hy⟩ := hp
  induction y using Quot.inductionOn with | h y =>
  obtain ⟨r, ⟨a, _⟩, ⟨b, _⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA))
      _ _).mp hy
  have hb : b.left.hom ≫ p.toBase = r.toBase := congrArg (fun z => z.hom) b.w
  have ha : a.left.hom ≫ y.toBase = r.toBase := congrArg (fun z => z.hom) a.w
  have hyq : y.value.left.hom ≫ adicThickeningι A I 0 = y.toBase :=
    congrArg (fun z => z.hom) y.value.w
  have hcomm : b.left.hom ≫ p.toBase = (a.left.hom ≫ y.value.left.hom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) :=
    calc b.left.hom ≫ p.toBase
        = r.toBase := hb
      _ = a.left.hom ≫ y.toBase := ha.symm
      _ = a.left.hom ≫ (y.value.left.hom ≫ adicThickeningι A I 0) :=
        (congrArg (fun k => a.left.hom ≫ k) hyq).symm
      _ = _ := (Category.assoc _ _ _).symm
  exact exists_factor_quotient_of_field_extension A (I ^ (0 + 1)) p.toBase b.left.hom
    (a.left.hom ≫ y.value.left.hom) hcomm

/-! ### The local algebra at a geometric point of an adic fibre -/

/-- Transporting a ring homomorphism along an equality of geometric points preserves locality
and surjectivity. -/
theorem isLocalHom_and_surjective_eqToHom_comp
    {P : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} {y y' : GeometricPoint B (Spec (.of A)) hA P}
    (e : y = y') {Rn : Type (u + 1)} [CommRing Rn]
    (ψ : etaleLocalRing B (Spec (.of A)) hA P y' →+* Rn) [IsLocalHom ψ]
    (hψ : Function.Surjective ψ) :
    IsLocalHom ((eqToHom (congrArg (etaleLocalRing B (Spec (.of A)) hA P) e) ≫
        CommRingCat.ofHom ψ).hom) ∧
      Function.Surjective ((eqToHom (congrArg (etaleLocalRing B (Spec (.of A)) hA P) e) ≫
        CommRingCat.ofHom ψ).hom) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, CommRingCat.hom_ofHom]
  exact ⟨inferInstance, hψ⟩

/-- A geometric point of an adic fibre has the same image in `Spec A` through either side of
the pullback square. -/
private theorem geometricPointMap_adicFibre_comm (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (n : ℕ)
    (z : GeometricPoint B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1) :
    geometricPointMap f.hom (geometricPointMap (adicFibreInclusion A I B hA X f n).hom z) =
      geometricPointMap
        (schemeSpaceMap (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n)).hom
        (geometricPointMap (adicFibreProjection A I B hA X f n).hom z) :=
  congrArg (fun k : _ ⟶ schemeSpace (baseObject A B hA) => geometricPointMap k.hom z)
    (isPullback_adicFibre A I B hA X f n).w

/-- **Stacks 08VP at one adic fibre.**  Let `z̄` be a geometric point of the adic fibre `Xₙ` with
image `x̄` in `X`.  If the pullback `Fₙ` of `F` to `Xₙ` is flat over `Spec(A/Iⁿ⁺¹)` at `z̄`, then
`(A/Iⁿ⁺¹) ⊗_A F_{x̄}` is flat over `A/Iⁿ⁺¹`, where `A` acts on the geometric stalk `F_{x̄}` through
the étale local ring of `Spec A`.

The étale local ring of `Xₙ` at `z̄` is weakly étale over `𝒪_{X, x̄} ⊗_R Rₙ`, where `R` and `Rₙ`
are the étale local rings of `Spec A` and `Spec(A/Iⁿ⁺¹)` (Stacks 05VQ, 0993), and the stalk of
`Fₙ` is `𝒪_{Xₙ, z̄} ⊗_{𝒪_{X, x̄}} F_{x̄}`; the commutative algebra of
`StacksFrontier/RingTheory/Flat/AdicThickeningWeaklyEtale.lean` concludes. -/
theorem flat_quotient_tensor_geometricModuleStalk (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (n : ℕ) (z : GeometricPoint B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1)
    (hflat : IsFlatOverAtGeometricPoint B (Spec (.of A)) hA (adicFibreProjection A I B hA X f n)
      ((modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).obj F) z) :
    letI : Module A (geometricModuleStalk B (Spec (.of A)) hA X
        (geometricPointMap (adicFibreInclusion A I B hA X f n).hom z) F) :=
      Module.compHom _ ((etaleLocalRingMap X.2 f.hom
        (geometricPointMap (adicFibreInclusion A I B hA X f n).hom z)).comp
        (baseGerm A B hA (geometricPointMap f.hom
          (geometricPointMap (adicFibreInclusion A I B hA X f n).hom z))))
    Module.Flat (A ⧸ I ^ (n + 1)) ((A ⧸ I ^ (n + 1)) ⊗[A] geometricModuleStalk B (Spec (.of A))
      hA X (geometricPointMap (adicFibreInclusion A I B hA X f n).hom z) F) := by
  let g' := adicFibreInclusion A I B hA X f n
  let f' := adicFibreProjection A I B hA X f n
  let g := schemeSpaceMap (adicThickeningMap A I B hA (contains_adicThickening A I B hA) n)
  have hpb : IsPullback g' f' f g := isPullback_adicFibre A I B hA X f n
  have h := geometricPointMap_adicFibre_comm A I B hA X f n z
  obtain ⟨φ, hl, hr, hw⟩ := cartesian_etaleStalk_tensor_weaklyEtale B (Spec (.of A)) hA g' f' f g
    hpb z
  let x := geometricPointMap g'.hom z
  let R := etaleLocalRing B (Spec (.of A)) hA (schemeSpace (baseObject A B hA)).1
    (geometricPointMap f.hom x)
  let T := etaleLocalRing B (Spec (.of A)) hA X.1 x
  let Rn := etaleLocalRing B (Spec (.of A)) hA
    (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n)).1
    (geometricPointMap f'.hom z)
  let D := etaleLocalRing B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1 z
  let M := geometricModuleStalk B (Spec (.of A)) hA X x F
  let ψ := etaleLocalRingMap
    (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n)).2 g.hom
    (geometricPointMap f'.hom z)
  let ρ : R →+* Rn :=
    (eqToHom (congrArg (etaleLocalRing B (Spec (.of A)) hA
      (schemeSpace (baseObject A B hA)).1) h) ≫ CommRingCat.ofHom ψ).hom
  let : Algebra R T := (etaleLocalRingMap X.2 f.hom x).toAlgebra
  let : Algebra R Rn := ρ.toAlgebra
  let : Algebra T D := (etaleLocalRingMap (adicFibreSpaceOf A I B hA X f n).2 g'.hom z).toAlgebra
  let : Algebra Rn D := (etaleLocalRingMap (adicFibreSpaceOf A I B hA X f n).2 f'.hom z).toAlgebra
  let : Module R M := Module.compHom _ (etaleLocalRingMap X.2 f.hom x)
  have : IsScalarTower R T M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hDM : Module.Flat Rn (D ⊗[T] M) :=
    (ModuleCat.flat_extendScalars_obj_iff _ _ _).mp
      ((ModuleCat.flat_iff_of_iso (etaleLocalRingMap _ f'.hom z)
        (geometricModuleStalkPullbackIso B (Spec (.of A)) hA g' z F)).mp hflat)
  have : IsLocalRing T := isLocalRing_etaleLocalRing B (Spec (.of A)) hA X.1 X.2 x
  have : IsLocalRing D :=
    isLocalRing_etaleLocalRing B (Spec (.of A)) hA _ (adicFibreSpaceOf A I B hA X f n).2 z
  have : IsLocalRing R := isLocalRing_etaleLocalRing B (Spec (.of A)) hA _
    (schemeSpace (baseObject A B hA)).2 _
  have : IsLocalRing Rn := isLocalRing_etaleLocalRing B (Spec (.of A)) hA _
    (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n)).2 _
  have : IsLocalHom (algebraMap T D) := isLocalHom_etaleLocalRingMap B (Spec (.of A)) hA
    (adicFibreSpaceOf A I B hA X f n).2 X.2 g'.hom z
  have : IsLocalHom ψ := isLocalHom_etaleLocalRingMap B (Spec (.of A)) hA _
    (schemeSpace (baseObject A B hA)).2 g.hom _
  obtain ⟨hρloc, hρsurj⟩ := isLocalHom_and_surjective_eqToHom_comp A B hA h ψ
    (surjective_etaleLocalRingMap_of_isClosedImmersion B (Spec (.of A)) hA g
      (isClosedImmersion_adicThickeningMap A I B hA n) _)
  have h1 : Module.Flat Rn (Rn ⊗[R] M) :=
    Module.Flat.tensor_of_flat_tensor_weaklyEtale hρsurj φ hl hr hw
  let : Algebra A R := (baseGerm A B hA (geometricPointMap f.hom x)).toAlgebra
  let : Algebra (A ⧸ I ^ (n + 1)) Rn :=
    (thickeningGerm A I B hA n (geometricPointMap f'.hom z)).toAlgebra
  let : Algebra A Rn :=
    ((thickeningGerm A I B hA n (geometricPointMap f'.hom z)).comp
      (Ideal.Quotient.mk (I ^ (n + 1)))).toAlgebra
  have : IsScalarTower A (A ⧸ I ^ (n + 1)) Rn := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A R Rn := IsScalarTower.of_algebraMap_eq fun a =>
    (RingHom.congr_fun (etaleLocalRingMap_comp_baseGerm A I B hA n
      (geometricPointMap f'.hom z) (geometricPointMap f.hom x) h) a).symm
  have : Algebra.WeaklyEtale A R := weaklyEtale_baseGerm A B hA (geometricPointMap f.hom x)
  have : Algebra.WeaklyEtale (A ⧸ I ^ (n + 1)) Rn :=
    weaklyEtale_thickeningGerm A I B hA n (geometricPointMap f'.hom z)
  have : IsLocalHom (algebraMap R Rn) := hρloc
  let : Module A M := Module.compHom _ ((etaleLocalRingMap X.2 f.hom x).comp
    (baseGerm A B hA (geometricPointMap f.hom x)))
  have : IsScalarTower A R M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.quotient_tensor_of_flat_tensor_weaklyEtale (R := R) (Rn := Rn)
    Ideal.Quotient.mk_surjective

/-- **A geometric point lifting to the first thickening lies over `V(I)`.**  If a geometric point
`x̄` of `X` is the image of a geometric point of the adic fibre `X₀ = Spec(A/I) ×_{Spec A} X`,
then no element of `I` becomes a unit in the étale local ring of `Spec A` at the image of `x̄`. -/
theorem not_isUnit_baseGerm (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA))
    (z : GeometricPoint B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f 0).1)
    (a : A) (ha : a ∈ I) :
    ¬ IsUnit (baseGerm A B hA (geometricPointMap f.hom
      (geometricPointMap (adicFibreInclusion A I B hA X f 0).hom z)) a) := by
  let g' := adicFibreInclusion A I B hA X f 0
  let f' := adicFibreProjection A I B hA X f 0
  let g := schemeSpaceMap (adicThickeningMap A I B hA (contains_adicThickening A I B hA) 0)
  have h := geometricPointMap_adicFibre_comm A I B hA X f 0 z
  let ψ := etaleLocalRingMap
    (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0)).2 g.hom
    (geometricPointMap f'.hom z)
  let ρ := (eqToHom (congrArg (etaleLocalRing B (Spec (.of A)) hA
      (schemeSpace (baseObject A B hA)).1) h) ≫ CommRingCat.ofHom ψ).hom
  have : IsLocalRing (etaleLocalRing B (Spec (.of A)) hA
      (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0)).1
      (geometricPointMap f'.hom z)) :=
    isLocalRing_etaleLocalRing B (Spec (.of A)) hA _
      (schemeSpace (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0)).2 _
  have hcomp := etaleLocalRingMap_comp_baseGerm A I B hA 0 (geometricPointMap f'.hom z)
    (geometricPointMap f.hom (geometricPointMap g'.hom z)) h
  intro hu
  have hz : ρ (baseGerm A B hA _ a) = 0 := by
    refine (RingHom.congr_fun hcomp a).trans ?_
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using ha)]
    exact map_zero _
  exact not_isUnit_zero (hz ▸ hu.map ρ)

/-- **Stacks 08VP.**  Let `A` be a Noetherian ring, `I ⊆ A` an ideal, and `X` an algebraic space
locally of finite presentation over `S = Spec A`.  For `n ≥ 0` let `Xₙ = Spec(A/Iⁿ⁺¹) ×_S X` be
the adic fibres, and let `F` be a coherent `𝒪_X`-module whose pullback `Fₙ` to every `Xₙ` is flat
over `Spec(A/Iⁿ⁺¹)`.  Then the locus of points of `|X|` where `F` is flat over `S` is open, and it
contains the inverse image of `V(I) = |Spec(A/I)|` under `|X| ⟶ |S|`.

The source's thickenings are indexed by `n ≥ 1` and are `Spec(A/Iⁿ)`; here they are indexed by
`n ≥ 0` and are `Spec(A/Iⁿ⁺¹)`, the convention of `AlgebraicGeometry.Space.adicFibre`.  The
flatness of `Fₙ` is Stacks 05VV for the projection `Xₙ ⟶ Spec(A/Iⁿ⁺¹)`, and the flat locus is
`AlgebraicGeometry.Space.flatLocus` of Stacks 05VV (1).  Openness is Stacks 05WV.

At a geometric point `x̄` above `V(I)` the proof follows the source's reduction to Stacks 0523,
carried out on étale local rings rather than on an affine étale chart: `x̄` lifts to every `Xₙ`,
flatness of the stalks of `Fₙ` gives flatness of `(A/Iⁿ⁺¹) ⊗_A F_{x̄}` over `A/Iⁿ⁺¹`
(`AlgebraicGeometry.Space.flat_quotient_tensor_geometricModuleStalk`), and Stacks 0523 over the
Noetherian ring `A`, applied to the finite module `F_{x̄}` over the Noetherian local ring
`𝒪_{X, x̄}`, gives flatness over `A`, hence over the weakly étale `A`-algebra `𝒪_{S, ȳ}`. -/
@[stacks 08VP]
theorem isOpen_flatLocus_and_preimage_subset_flatLocus [IsNoetherianRing A]
    (X : AlgebraicSpaces B (Spec (.of A)) hA) (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFinitePresentation B (Spec (.of A)) hA f.hom)
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) [IsCoherent B (Spec (.of A)) hA X.1 X.2 F]
    (hflat : ∀ n : ℕ, IsFlatOver B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).2
      (adicFibreProjection A I B hA X f n).hom
      ((modulePullback B (Spec (.of A)) hA (adicFibreInclusion A I B hA X f n)).obj F)) :
    IsOpen (flatLocus B (Spec (.of A)) hA X.2 f.hom F) ∧
      pointsMap B (Spec (.of A)) hA X.1 f.hom ⁻¹'
          Set.range (pointsMap B (Spec (.of A)) hA
            (yoneda.obj (adicThickeningObject A I B hA (contains_adicThickening A I B hA) 0))
            (yoneda.map (adicThickeningMap A I B hA (contains_adicThickening A I B hA) 0))) ⊆
        flatLocus B (Spec (.of A)) hA X.2 f.hom F := by
  have hqc : F.IsQuasicoherentOnSite := IsCoherent.toIsQuasicoherentOnSite
  have hft : SheafOfModules.IsFiniteTypeOnSite F :=
    isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of A)) hA X F
  refine ⟨?_, ?_⟩
  · have hfp := isFinitePresentationOnCharts_of_isFinitePresentationOnSite B (Spec (.of A)) hA X F
      hqc (SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite F inferInstance)
    exact isOpen_flatLocus_of_isFinitePresentationOnCharts B (Spec (.of A)) hA X.2 f.hom F hf
      (fun U => isQuasicoherent_restrictToChart B (Spec (.of A)) hA X F hqc U) hfp
  intro x hx
  obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B (Spec (.of A)) hA X.1 x
  refine (mem_flatLocus_iff_isFlatOverAtGeometricPoint B (Spec (.of A)) hA f F xbar).mpr ?_
  -- the geometric point lifts to every adic fibre
  have hfac0 := exists_factor_of_pointsMap_mem_range A I B hA X f xbar.val hx
  have hlift : ∀ n, ∃ z : GeometricPoint B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1,
      geometricPointMap (adicFibreInclusion A I B hA X f n).hom z = xbar := fun n =>
    exists_geometricPoint_adicFibre A I B hA X f n xbar
      (exists_factor_quotient_of_le A (Ideal.pow_le_pow_right (by omega)) _ hfac0)
  -- the local rings and their Noetherianity
  let y : GeometricPoint B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA)) :=
    geometricPointMap f.hom xbar
  let R := etaleLocalRing B (Spec (.of A)) hA (yoneda.obj (baseObject A B hA)) y
  let T := etaleLocalRing B (Spec (.of A)) hA X.1 xbar
  let M := geometricModuleStalk B (Spec (.of A)) hA X xbar F
  have hN : HasEtaleLocalProperty B (Spec (.of A)) hA X.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of A)) hA X.2
      (schemeSpace (baseObject A B hA)).2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (Spec (.of A)) hA hf)
      (hasEtaleLocalProperty_isLocallyNoetherian_baseObject A B hA)
  have : IsNoetherianRing T :=
    isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B (Spec (.of A)) hA X.1 X.2 hN xbar
  have : IsLocalRing T := isLocalRing_etaleLocalRing B (Spec (.of A)) hA X.1 X.2 xbar
  have : IsLocalRing R := isLocalRing_etaleLocalRing B (Spec (.of A)) hA _
    (schemeSpace (baseObject A B hA)).2 y
  have : Module.Finite T M :=
    module_finite_geometricModuleStalk B (Spec (.of A)) hA X F hqc hft xbar
  -- the algebra structures
  let : Algebra A R := (baseGerm A B hA y).toAlgebra
  let : Algebra R T := (etaleLocalRingMap X.2 f.hom xbar).toAlgebra
  let : Algebra A T := ((etaleLocalRingMap X.2 f.hom xbar).comp (baseGerm A B hA y)).toAlgebra
  have : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.WeaklyEtale A R := weaklyEtale_baseGerm A B hA y
  let : Module R M := Module.compHom _ (etaleLocalRingMap X.2 f.hom xbar)
  let : Module A M := Module.compHom _ ((etaleLocalRingMap X.2 f.hom xbar).comp
    (baseGerm A B hA y))
  have : IsScalarTower A R M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R T M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A T M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hloc : IsLocalHom (etaleLocalRingMap X.2 f.hom xbar) := isLocalHom_etaleLocalRingMap B
    (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom xbar
  -- `I` maps into the maximal ideal of `𝒪_{X, x̄}`
  have hI : I.map (algebraMap A T) ≤ maximalIdeal T := by
    obtain ⟨z₀, hz₀⟩ := hlift 0
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    have hb := not_isUnit_baseGerm A I B hA X f z₀ a ha
    rw [hz₀] at hb
    change etaleLocalRingMap X.2 f.hom xbar (baseGerm A B hA y a) ∈ maximalIdeal T
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => hb (hloc.map_nonunit _ hu)
  -- flatness of the base changes to the thickenings
  have hn : ∀ n : ℕ, Module.Flat (A ⧸ I ^ (n + 1)) ((A ⧸ I ^ (n + 1)) ⊗[A] M) := by
    intro n
    have key : ∀ (x' : GeometricPoint B (Spec (.of A)) hA X.1)
        (_ : ∃ z : GeometricPoint B (Spec (.of A)) hA (adicFibreSpaceOf A I B hA X f n).1,
          geometricPointMap (adicFibreInclusion A I B hA X f n).hom z = x'),
        let : Module A (geometricModuleStalk B (Spec (.of A)) hA X x' F) :=
          Module.compHom _ ((etaleLocalRingMap X.2 f.hom x').comp
            (baseGerm A B hA (geometricPointMap f.hom x')))
        Module.Flat (A ⧸ I ^ (n + 1))
          ((A ⧸ I ^ (n + 1)) ⊗[A] geometricModuleStalk B (Spec (.of A)) hA X x' F) := by
      rintro _ ⟨z, rfl⟩
      have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B (Spec (.of A)) hA
        (adicFibreInclusion A I B hA X f n) F hqc
      exact flat_quotient_tensor_geometricModuleStalk A I B hA X f F n z
        ((isFlatOver_iff_forall_isFlatOverAtGeometricPoint B (Spec (.of A)) hA _ _).mp
          (hflat n) z)
    exact key xbar (hlift n)
  exact Module.Flat.of_flat_quotient_tensor_pow_of_weaklyEtale (R := R) (T := T) (M := M) I hI hn

end AdicFibre

end AlgebraicGeometry.Space

end
