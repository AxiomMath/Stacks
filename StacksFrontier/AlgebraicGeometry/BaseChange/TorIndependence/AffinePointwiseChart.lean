module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseSpec
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineBaseInduction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard

/-!
# Stacks 0DJ9 over a pushout square of rings, at a datum with quasi-coherent cohomology

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a pushout square of rings, `E ∈ D(𝒪_{Spec A})` and
`E' ∈ D(𝒪_{Spec A'})` with quasi-coherent cohomology, and `ψ : L(Spec c)^*E ⟶ E'`.  If the map of
Stacks 0DJ7 of the square of spectra at `ψ` is invertible at every point and in every degree, the
composition `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E ⟶ Rf'_*E'` is an isomorphism.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_comp_specMap_of_isQuasicoherent`: the composition
  `Lg^*Rf_*E ⟶ Rf'_*E'` is an isomorphism when the maps of Stacks 0DJ7 are invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {R A R' A' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'}

/-- If `t = 𝟙`, `q ≫ qθ = h ≫ q'` and `q' ≫ q'inv = 𝟙`, then
`a ≫ b ≫ h = ((a ≫ b ≫ t ≫ q) ≫ qθ) ≫ q'inv`. -/
theorem datum_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ : C} (a : P₀ ⟶ P₁)
    (b : P₁ ⟶ P₂) (t : P₂ ⟶ P₂) (h : P₂ ⟶ P₃) (q : P₂ ⟶ P₄) (qθ : P₄ ⟶ P₅) (q' : P₃ ⟶ P₅)
    (q'inv : P₅ ⟶ P₃) (ht : t = 𝟙 _) (hn : q ≫ qθ = h ≫ q') (hinv : q' ≫ q'inv = 𝟙 _) :
    a ≫ b ≫ h = ((a ≫ b ≫ t ≫ q) ≫ qθ) ≫ q'inv := by
  subst ht
  simp only [Category.assoc, Category.id_comp, reassoc_of% hn, hinv, Category.comp_id]

/-- If `qq = t ≫ gg`, `gg ≫ si = ti ≫ pinv ≫ φ ≫ vi`, and `t ≫ ti`, `p ≫ pinv` and `vi ≫ vh`
are identities, then `(p ≫ qq) ≫ si ≫ vh = φ`. -/
theorem model_chase {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C} (p : X₀ ⟶ X₁)
    (t : X₁ ⟶ X₂) (gg : X₂ ⟶ X₃) (si : X₃ ⟶ X₄) (vh : X₄ ⟶ X₅) (qq : X₁ ⟶ X₃) (ti : X₂ ⟶ X₁)
    (pinv : X₁ ⟶ X₀) (φ : X₀ ⟶ X₅) (vi : X₅ ⟶ X₄) (hqq : qq = t ≫ gg)
    (hk : gg ≫ si = ti ≫ pinv ≫ φ ≫ vi) (h1 : t ≫ ti = 𝟙 _) (h2 : p ≫ pinv = 𝟙 _)
    (h3 : vi ≫ vh = 𝟙 _) : (p ≫ qq) ≫ si ≫ vh = φ := by
  subst hqq
  simp only [Category.assoc]
  rw [reassoc_of% hk, reassoc_of% h1, reassoc_of% h2, h3, Category.comp_id]

/-- If `Lu = lh ≫ uh`, `li ≫ spd = D ≫ qci`, `D ≫ vh = uh ≫ χ`, and `lh ≫ li` and `qci ≫ qch`
are identities, then `Lu ≫ χ = spd ≫ qch ≫ vh`. -/
theorem transport_chase {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ : C} (lh : X₀ ⟶ X₁)
    (li : X₁ ⟶ X₀) (uh : X₁ ⟶ X₂) (χ : X₂ ⟶ X₃) (spd : X₀ ⟶ X₄) (D : X₁ ⟶ X₅) (qci : X₅ ⟶ X₄)
    (qch : X₄ ⟶ X₅) (vh : X₅ ⟶ X₃) (Lu : X₀ ⟶ X₂) (hLu : Lu = lh ≫ uh)
    (hs : li ≫ spd = D ≫ qci) (h1 : lh ≫ li = 𝟙 _) (h2 : qci ≫ qch = 𝟙 _)
    (hk : D ≫ vh = uh ≫ χ) : Lu ≫ χ = spd ≫ qch ≫ vh := by
  subst hLu
  rw [show spd = lh ≫ D ≫ qci by rw [← hs, reassoc_of% h1]]
  simp only [Category.assoc]
  rw [reassoc_of% h2, hk]

/-- The datum of a map of complexes `ψ₀ : A' ⊗_A M ⟶ N`, read through the two presentations of
the derived category. -/
theorem specPullbackDatum_eq (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (N : CochainComplex (ModuleCat.{u} A') ℤ)
    (ψ₀ : ((ModuleCat.extendScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ N) :
    (derivedPullback (Spec.map c).toLRSHom.toShHom).map
        ((DerivedCategory.quotientCompQhIso (Spec A).Modules).inv.app
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      specPullbackDatum c M N ψ₀ =
    (pullbackComparisonOnComplex (Spec.map c)
        (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app
        M ≫ ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀)) ≫
      (DerivedCategory.quotientCompQhIso (Spec A').Modules).inv.app
        (((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).obj N) := by
  unfold pullbackComparisonOnComplex specPullbackDatum
  exact datum_chase _ _ (DerivedCategory.Qh.map
      (((modulePullback (Spec.map c).toLRSHom.toShHom).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).hom.app (((tilde.functor A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M))) _ _ _ _ _
    ((congrArg DerivedCategory.Qh.map (Quotient.lift.isLift_hom _ _ _ _)).trans
      (CategoryTheory.Functor.map_id _ _))
    ((DerivedCategory.quotientCompQhIso (Spec A').Modules).hom.naturality
      ((AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app M ≫
        ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map ψ₀)).symm
    (Iso.hom_inv_id_app _ _)

/-- **Stacks 0DJ9 over a pushout square of rings, for a datum with quasi-coherent cohomology.**
For `E ∈ D_QCoh(𝒪_{Spec A})`, `E' ∈ D_QCoh(𝒪_{Spec A'})` and `χ : L(Spec c)^*E ⟶ E'` whose maps of
Stacks 0DJ7 are invertible at every point and in every degree, the composition
`L(Spec b)^*R(Spec a)_*E ⟶ R(Spec d)_*L(Spec c)^*E ⟶ R(Spec d)_*E'` is an isomorphism. -/
theorem isIso_comp_specMap_of_isQuasicoherent (h : IsPushout a b c d)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec A).toSheafedSpace)))
    (E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing (Spec A').toSheafedSpace)))
    (χ : (derivedPullback (Spec.map c).toLRSHom.toShHom).obj E ⟶ E')
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec A).toSheafedSpace)) n).obj E).IsQuasicoherent)
    (hE' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing (Spec A').toSheafedSpace)) n).obj E').IsQuasicoherent)
    (hp : ∀ (x' : Spec A') (n : ℤ), IsIso (baseChangeCohomologyMap (Spec.map a) (Spec.map b)
      (Spec.map d) (Spec.map c) (isPullback_specMap h).w E E' χ x' n)) :
    IsIso (derivedBaseChangeMap (Spec.map c).toLRSHom.toShHom (Spec.map d).toLRSHom.toShHom
        (Spec.map a).toLRSHom.toShHom (Spec.map b).toLRSHom.toShHom
        (comp_toShHom_of_comm (isPullback_specMap h).w) E ≫
      (derivedPushforward (Spec.map d).toLRSHom.toShHom).map χ) := by
  obtain ⟨M₀, ⟨e₁⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory A E hE
  obtain ⟨M, π, hM, -, hπ, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    (DerivedCategory.Q.objPreimage M₀)
  let T := tilde.functor A
  let T' := tilde.functor A'
  let u₀ : DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≅ E :=
    (T.mapDerivedCategoryFactors.app M).symm ≪≫ T.mapDerivedCategory.mapIso
      (asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso M₀) ≪≫ e₁
  obtain ⟨M₀', ⟨e₁'⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory A' E' hE'
  let N₁ := DerivedCategory.Q.objPreimage M₀'
  let v₀ : DerivedCategory.Q.obj ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N₁) ≅ E' :=
    (T'.mapDerivedCategoryFactors.app N₁).symm ≪≫ T'.mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso M₀') ≪≫ e₁'
  let L := derivedPullback (Spec.map c).toLRSHom.toShHom
  let φQ := L.map u₀.hom ≫ χ
  let P := pullbackComparisonOnComplex (Spec.map c)
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)
  have : IsIso P := isIso_pullbackComparisonOnComplex_of_kFlat _ _
    (Stacks.TildeStalk.kFlatComplex_tilde A M hM)
  let θ₀ := (AlgebraicGeometry.tildePullbackComplexIso A A' c).hom.app M
  let φ₃ : DerivedCategory.Q.obj ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars c.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ⟶
      DerivedCategory.Q.obj ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N₁) :=
    inv (DerivedCategory.Q.map θ₀) ≫ (asIso P).inv ≫ φQ ≫ v₀.inv
  let β := (AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful A').preimage
    (T'.mapDerivedCategoryFactors.hom.app _ ≫ φ₃ ≫ T'.mapDerivedCategoryFactors.inv.app N₁)
  obtain ⟨N, g, s, hs, hβ⟩ := DerivedCategory.left_fac β
  let F := T'.mapDerivedCategory
  let fac := T'.mapDerivedCategoryFactors
  have n_s := T'.mapDerivedCategoryFactors_hom_naturality s
  have hβ' := (AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful A').map_preimage
    (fac.hom.app _ ≫ φ₃ ≫ fac.inv.app N₁)
  have hTs :
      IsIso (DerivedCategory.Q.map ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) := by
    have : IsIso (fac.hom.app N₁ ≫
        DerivedCategory.Q.map ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) := by
      rw [← n_s]
      infer_instance
    exact IsIso.of_isIso_comp_left (fac.hom.app N₁) _
  have hinvs : fac.hom.app N ≫ inv (DerivedCategory.Q.map
      ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ≫ fac.inv.app N₁ =
      inv (F.map (DerivedCategory.Q.map s)) := by
    rw [← cancel_epi (F.map (DerivedCategory.Q.map s)), IsIso.hom_inv_id, reassoc_of% n_s,
      IsIso.hom_inv_id_assoc, Iso.hom_inv_id_app]
    rfl
  have hkey : DerivedCategory.Q.map ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
      inv (DerivedCategory.Q.map ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) = φ₃ := by
    have e : fac.hom.app _ ≫ (DerivedCategory.Q.map ((T'.mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) ≫ inv (DerivedCategory.Q.map ((T'.mapHomologicalComplex
          (ComplexShape.up ℤ)).map s))) ≫ fac.inv.app N₁ = fac.hom.app _ ≫ φ₃ ≫ fac.inv.app N₁ := by
      rw [← hβ']
      change _ = F.map β
      rw [hβ, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv, ← hinvs]
      simp only [Category.assoc]
      rw [reassoc_of% (T'.mapDerivedCategoryFactors_hom_naturality g)]
    rwa [cancel_epi, cancel_mono] at e
  let θ := θ₀ ≫ (T'.mapHomologicalComplex (ComplexShape.up ℤ)).map g
  let v' := (asIso (DerivedCategory.Q.map
    ((T'.mapHomologicalComplex (ComplexShape.up ℤ)).map s))).symm ≪≫ v₀
  have key2 : (P ≫ DerivedCategory.Q.map θ) ≫ v'.hom = φQ :=
    model_chase _ _ _ _ _ _ _ _ _ _ (DerivedCategory.Q.map_comp _ _) hkey
      (IsIso.hom_inv_id (DerivedCategory.Q.map θ₀)) (asIso P).hom_inv_id v₀.inv_hom_id
  have hw := (isPullback_specMap h).w
  let uu := (DerivedCategory.quotientCompQhIso (Spec A).Modules).app _ ≪≫ u₀
  let vv := (DerivedCategory.quotientCompQhIso (Spec A').Modules).app _ ≪≫ v'
  refine (@Stacks.Cohomology.BaseChangeCover.isIso_bc_iff_of_iso _ _ _ _ _ _ _ _ _ _ _ _ _
    (specPullbackDatum c M N g) χ uu.hom vv.hom (Iso.isIso_hom uu) (Iso.isIso_hom vv)
    (transport_chase _ _ _ χ _ _ _ _ v'.hom _ (L.map_comp _ _) (specPullbackDatum_eq M N g)
      ((L.map_comp _ _).symm.trans ((congrArg L.map (Iso.hom_inv_id_app _ _)).trans (L.map_id _)))
      (Iso.inv_hom_id_app _ _) key2)).1
    (isIso_comp_specMap_of_pointwise h M hM N g fun x' n => ?_)
  exact (isIso_baseChangeCohomologyMap_iff_of_isIso_target _ _ _ _ hw _ _ E' _ v'.hom
      (Iso.isIso_hom v') x' n).1 ((congrArg (fun t => IsIso (baseChangeCohomologyMap (Spec.map a)
        (Spec.map b) (Spec.map d) (Spec.map c) hw _ E' t x' n)) key2).mpr
        ((isIso_baseChangeCohomologyMap_iff_of_isIso_source _ _ _ _ hw _ E E' u₀.hom
          (Iso.isIso_hom u₀) χ x' n).2 (hp x' n)))

end Stacks.Cohomology.DerivedBaseChange
