module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Limits.AffineSiteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Quasi-compactness of `Isom_U(Y, X)`: reduction to affine bases

Let `Y ⟶ U` and `X ⟶ U` be families of curves over a common base `U`. The last two paragraphs of
the proof of Stacks 0DSQ show that `Isom_U(Y, X) ⟶ U` is quasi-compact. This file carries out the
first, formal, reduction of that argument: quasi-compactness of a morphism of algebraic spaces is
tested on affine schemes over the target (Stacks 03KG), and the base change of `Isom_U(Y, X)`
along an affine `T ⟶ U` is `Isom_T(Y_T, X_T)` (Stacks 05Y4), so it suffices that
`Isom_T(Y, X)` is a quasi-compact algebraic space for all families of curves `Y` and `X` over an
affine base `T`.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_hom_baseMap_eq`: a family of curves can be base changed
  along any morphism into its base (Stacks 0D51).
* `AlgebraicGeometry.CurveFamily.isQuasiCompact_isomFunctorProjection_of_affine`: the reduction.

## References

* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
* [Stacks Project, Tag 05Y4](https://stacks.math.columbia.edu/tag/05Y4)
* [Stacks Project, Tag 0D51](https://stacks.math.columbia.edu/tag/0D51)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **Base change of a family of curves.** For a family of curves `F` over `U` and a morphism
`g : T ⟶ U`, there is a morphism of families of curves `F' ⟶ F` (hence a cartesian square) whose
base map is `g`, up to the identification of the base of `F'` with `T`. -/
theorem exists_hom_baseMap_eq (F : CurveFamily B hZ) {T : BigFppfOver B integerBase hZ}
    (g : T ⟶ F.base) :
    ∃ (F' : CurveFamily B hZ) (φ : F' ⟶ F) (h : F'.base = T), φ.baseMap = eqToHom h ≫ g := by
  obtain ⟨F', φ, hφ⟩ :=
    (CurveDeformation.curvesProjectionOver_isFiberedInGroupoids (B := B) (hZ := hZ)).exists_lift
      g F rfl
  refine ⟨F', φ, IsHomLift.domain_eq (curvesProjectionOver B hZ) g φ, ?_⟩
  refine (IsHomLift.fac' (curvesProjectionOver B hZ) g φ).trans ?_
  congr 1

/-- **Fill-in through a morphism of families of curves.** Given morphisms `α : F₁ ⟶ F₂` and
`δ : F ⟶ F₂` of families of curves and a morphism `f` of bases with `f ≫ α.baseMap = δ.baseMap`,
there is a morphism `F ⟶ F₁` with base map `f` (Stacks 0D51, 003S (b)). -/
theorem exists_hom_baseMap_eq_of_comp {F F₁ F₂ : CurveFamily B hZ} (α : F₁ ⟶ F₂) (δ : F ⟶ F₂)
    (f : F.base ⟶ F₁.base) (hf : f ≫ α.baseMap = δ.baseMap) :
    ∃ χ : F ⟶ F₁, χ.baseMap = f := by
  obtain ⟨χ, ⟨hχ, -⟩, -⟩ :=
    (CurveDeformation.curvesProjectionOver_isFiberedInGroupoids (B := B) (hZ := hZ)).unique_lift
      α δ f hf
  exact ⟨χ, hχ⟩

/-- **Stacks 0DSQ, the quasi-compactness of `Isom_U(Y, X)`, reduced to affine bases.** Let `F`
and `G` be families of curves over a common base `U` with `Isom_U(F, G)` an algebraic space. If
`Isom_T(F', G')` is a quasi-compact algebraic space for all families of curves `F'` and `G'` over
a common affine base `T`, then `Isom_U(F, G) ⟶ U` is quasi-compact: by Stacks 03KG it suffices to
check that its base change along every morphism from an affine scheme `T` is quasi-compact, and
that base change is `Isom_T(F_T, G_T)` by Stacks 05Y4. -/
theorem isQuasiCompact_isomFunctorProjection_of_affine (F G : CurveFamily B hZ)
    (hb : G.base = F.base)
    (halg : IsAlgebraicSpace B integerBase hZ
      (isomFunctor F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))).toFunctor)
    (hT : ∀ (F' G' : CurveFamily B hZ) (hb' : G'.base = F'.base),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) →
        Space.IsQuasiCompactSpace B integerBase hZ
          (isomFunctor F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb'))).toFunctor) :
    Space.IsQuasiCompact B integerBase hZ
      (isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))) := by
  refine Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine' B integerBase hZ _ halg
    (isAlgebraicSpace_yoneda B integerBase hZ F.base) fun Z g hZaff => ?_
  obtain ⟨g₀, rfl⟩ : ∃ g₀ : Z ⟶ F.base, yoneda.map g₀ = g :=
    ⟨_, Yoneda.fullyFaithful.map_preimage g⟩
  obtain ⟨F', φ, h, hφ⟩ := exists_hom_baseMap_eq F g₀
  obtain ⟨G', ψ, h', hψ⟩ := exists_hom_baseMap_eq G (g₀ ≫ eqToHom hb.symm)
  have hb' : G'.base = F'.base := h'.trans h.symm
  have hφψ : ψ.baseMap ≫ eqToHom hb = eqToHom hb' ≫ φ.baseMap := by
    rw [hφ, hψ]
    simp
  obtain ⟨g', hpb⟩ := exists_isPullback_isomFunctorProjection_eqToHom φ ψ hb hb' hφψ
  have hpb' : IsPullback g'
      (isomFunctorProjection F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb')) ≫
        yoneda.map (eqToHom h))
      (isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))) (yoneda.map g₀) :=
    hpb.of_iso (Iso.refl _) (Iso.refl _) (yoneda.mapIso (eqToIso h)) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [hφ]; rfl)
  have haff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) := by
    rw [h]
    exact hZaff
  exact Space.isQuasiCompactSpace_of_iso B integerBase hZ hpb'.isoPullback (hT F' G' hb' haff)

/-- The base map of a morphism of families of curves lying over a morphism `f` of bases is `f`,
up to the identifications of the bases. -/
theorem baseMap_eq_of_isHomLift {F' F : CurveFamily B hZ} (φ : F' ⟶ F)
    {T V : BigFppfOver B integerBase hZ} (f : T ⟶ V)
    (hφ : (curvesProjectionOver B hZ).IsHomLift f φ) :
    ∃ (h₁ : F'.base = T) (h₂ : F.base = V), φ.baseMap = eqToHom h₁ ≫ f ≫ eqToHom h₂.symm :=
  ⟨IsHomLift.domain_eq (curvesProjectionOver B hZ) f φ,
    IsHomLift.codomain_eq (curvesProjectionOver B hZ) f φ,
    IsHomLift.fac' (curvesProjectionOver B hZ) f φ⟩

/-- Bookkeeping of identifications for the base maps of descended families. -/
private theorem eqToHom_comp_comp_eqToHom_aux {C : Type*} [Category C] {A A' K K' I I' : C}
    (hA : A' = A) (πk : A ⟶ K) (Ms : K ⟶ I) (πi : A ⟶ I) (hw : πk ≫ Ms = πi) (hK : K' = K)
    (hI : I' = I) :
    (eqToHom hA ≫ πk ≫ eqToHom hK.symm) ≫ eqToHom hK ≫ Ms ≫ eqToHom hI.symm =
      eqToHom hA ≫ πi ≫ eqToHom hI.symm := by
  subst_vars
  simp

/-- Bookkeeping of identifications for the base maps of two descended families. -/
private theorem eqToHom_comp_eqToHom_aux {C : Type*} [Category C] {G₀ F₀ A K Y X : C}
    (h₀' : G₀ = A) (h₀ : F₀ = A) (hb : G₀ = F₀) (πk : A ⟶ K) (hyk : Y = K) (hxk : X = K)
    (hbk : Y = X) :
    (eqToHom h₀' ≫ πk ≫ eqToHom hyk.symm) ≫ eqToHom hbk =
      eqToHom hb ≫ eqToHom h₀ ≫ πk ≫ eqToHom hxk.symm := by
  subst_vars
  simp

/-- **Stacks 0DSQ, the quasi-compactness of `Isom_T(Y, X)` over an affine base, reduced to
Noetherian bases.** Suppose the stack of curves is limit preserving (`hlim`, Stacks 0D55) and
that `Isom_V(Y', X') ⟶ V` is quasi-compact for all families of curves `Y'` and `X'` over a common
affine Noetherian base `V`. Then `Isom_T(Y, X)` is a quasi-compact algebraic space for all
families of curves `Y` and `X` over a common affine base `T`: writing `T` as the limit of the
spectra of the finitely generated subalgebras of `Γ(T, 𝒪_T)`
(`AlgebraicGeometry.affineSiteStageCone`), both families descend to a common stage `V` by
`hlim`, and `Isom_T(Y, X) = T ×_V Isom_V(Y', X')` (Stacks 05Y4) is quasi-compact over the
quasi-compact `T`. -/
theorem isQuasiCompactSpace_isomFunctor_of_isLimitPreserving
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hN : ∀ (F' G' : CurveFamily B hZ) (hb' : G'.base = F'.base),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj F'.base) →
        Space.IsQuasiCompact B integerBase hZ
          (isomFunctorProjection F' G' (G'.toBase.hom ≫ yoneda.map (eqToHom hb'))))
    (F G : CurveFamily B hZ) (hb : G.base = F.base)
    (haff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj F.base)) :
    Space.IsQuasiCompactSpace B integerBase hZ
      (isomFunctor F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))).toFunctor := by
  classical
  let D := affineSiteStageDiagram B hZ F.base
  let c := affineSiteStageCone B hZ F.base
  let D' := D ⋙ BigAffineFppf.inclusion B integerBase hZ
  let c' := (BigAffineFppf.inclusion B integerBase hZ).mapCone c
  let p := (curvesFiberedCategory B hZ).val.p
  let : p.IsFibered := (curvesFiberedCategory B hZ).2.isFibered
  have hEq := hlim _ D c (isLimit_affineSiteStageCone B hZ F.base)
  have hdesc := Deformation.Artin.descentObj_of_essSurj p D' c'
  obtain ⟨i, xi, δ, hδ⟩ := hdesc ⟨F, rfl⟩
  obtain ⟨j, yj, ε, hε⟩ := hdesc ⟨G, hb⟩
  let k := IsCofiltered.min i j
  have hp := CurveDeformation.curvesProjectionOver_isFiberedInGroupoids (B := B) (hZ := hZ)
  obtain ⟨xk, α, hα⟩ := hp.exists_lift (D'.map (IsCofiltered.minToLeft i j)) xi.1 xi.2
  obtain ⟨yk, β, hβ⟩ := hp.exists_lift (D'.map (IsCofiltered.minToRight i j)) yj.1 yj.2
  obtain ⟨hxk, hxi, hα'⟩ := baseMap_eq_of_isHomLift α _ hα
  obtain ⟨hyk, hyj, hβ'⟩ := baseMap_eq_of_isHomLift β _ hβ
  obtain ⟨h₀, hxi', hδ'⟩ := baseMap_eq_of_isHomLift δ _ hδ
  obtain ⟨h₀', hyj', hε'⟩ := baseMap_eq_of_isHomLift ε _ hε
  have hw : c'.π.app k ≫ D'.map (IsCofiltered.minToLeft i j) = c'.π.app i := c'.w _
  have hw' : c'.π.app k ≫ D'.map (IsCofiltered.minToRight i j) = c'.π.app j := c'.w _
  obtain ⟨χ, hχ⟩ := exists_hom_baseMap_eq_of_comp α δ
    (eqToHom h₀ ≫ c'.π.app k ≫ eqToHom hxk.symm) (by
      rw [hα', hδ']
      exact eqToHom_comp_comp_eqToHom_aux h₀ _ _ _ hw hxk hxi')
  obtain ⟨χ', hχ'⟩ := exists_hom_baseMap_eq_of_comp β ε
    (eqToHom h₀' ≫ c'.π.app k ≫ eqToHom hyk.symm) (by
      rw [hβ', hε']
      exact eqToHom_comp_comp_eqToHom_aux h₀' _ _ _ hw' hyk hyj')
  have hbk : yk.base = xk.base := hyk.trans hxk.symm
  have hφψ : χ'.baseMap ≫ eqToHom hbk = eqToHom hb ≫ χ.baseMap := by
    rw [hχ, hχ']
    exact eqToHom_comp_eqToHom_aux h₀' h₀ hb _ hyk hxk hbk
  obtain ⟨g, hpb⟩ := exists_isPullback_isomFunctorProjection_eqToHom χ χ' hbk hb hφψ
  have hkaff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj xk.base) := by
    rw [hxk]
    exact (D.obj k).property
  have hknoeth : IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj xk.base) := by
    rw [hxk]
    exact isNoetherian_affineSiteStageDiagram_obj B hZ F.base k
  have hqc := hN xk yk hbk hkaff hknoeth (yoneda.obj F.base)
    (isAlgebraicSpace_yoneda B integerBase hZ F.base)
    (Space.isQuasiCompact_yoneda_of_compact B integerBase hZ F.base inferInstance)
    (yoneda.map χ.baseMap)
  exact Space.isQuasiCompactSpace_of_iso B integerBase hZ hpb.flip.isoPullback.symm hqc

end CurveFamily

end AlgebraicGeometry

end
