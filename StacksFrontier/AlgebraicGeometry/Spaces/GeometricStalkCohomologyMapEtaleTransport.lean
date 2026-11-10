module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuadrupleEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackGeometricStalkComp
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointwiseAffineChartwise
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffineFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompCondition

/-!
# The map of Equation 0DKF along an affine étale quadruple

For a cartesian square of algebraic spaces and a cartesian square of affine schemes mapping to it
by étale morphisms `a, b, c, a'`, the map of Equation 0DKF of the first square at `a'(x̄)` is
invertible exactly when the one of the second square at `x̄`, for `La^*K`, `La'^*K'` and the
morphism induced by `φ`, is. Hence conditions (1) and (2) of Stacks 0DKG, the latter read on
affine étale quadruples, are equivalent. The ring-level half identifies the stalk squares through
the bijective homomorphisms of geometric stalk rings of the étale maps; the derived pullback-stalk
comparisons along `a` and `a'` identify the data, compatibly by their composition law.

## Main results

* `AlgebraicGeometry.Space.isIso_geometricStalkBaseChangeCohomologyMap_iff_affineQuadruple`
* `AlgebraicGeometry.Space.geometricPointwiseBaseChange_iff_affineChartwiseBaseChange`
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingTheory.TorIndependence

universe u v₁ v₂ v₃ u₁ u₂ u₃

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Transport of a derived extension of scalars along an equality of points. -/
theorem dext_obj_eqToHom_comp {ι : Type*} (R : ι → CommRingCat.{u})
    (F : ∀ i, DerivedCategory (ModuleCat.{u} (R i))) {i j : ι} (h : j = i) {T : CommRingCat.{u}}
    (σ : R i ⟶ T) :
    (dext (eqToHom (congrArg R h) ≫ σ).hom).obj (F j) = (dext σ.hom).obj (F i) := by
  subst h
  rfl

/-- Transport of a derived extension of scalars along a composite, along an equality of points. -/
theorem dext_comp_obj_eqToHom_comp {ι : Type*} (R : ι → CommRingCat.{u})
    (F : ∀ i, DerivedCategory (ModuleCat.{u} (R i))) {i j : ι} (h : j = i) {T T' : CommRingCat.{u}}
    (σ : R i ⟶ T) (β : T →+* T') :
    (dext (β.comp (eqToHom (congrArg R h) ≫ σ).hom)).obj (F j) =
      (dext (β.comp σ.hom)).obj (F i) := by
  subst h
  rfl

/-- The composition isomorphism of derived extension of scalars commutes with the transport along
an equality of points. -/
theorem totalDerivedExtensionScalarsComp_hom_app_eqToHom_comp {ι : Type*}
    (R : ι → CommRingCat.{u})
    (F : ∀ i, DerivedCategory (ModuleCat.{u} (R i))) {i j : ι} (h : j = i) {T T' : CommRingCat.{u}}
    (σ : R i ⟶ T) (β : T →+* T') :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        (eqToHom (congrArg R h) ≫ σ).hom β).hom.app (F j) ≫
        eqToHom (dext_comp_obj_eqToHom_comp R F h σ β) =
      (dext β).map (eqToHom (dext_obj_eqToHom_comp R F h σ)) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          σ.hom β).hom.app (F i) := by
  subst h
  change (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        σ.hom β).hom.app (F _) ≫ 𝟙 _ = (dext β).map (𝟙 _) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        σ.hom β).hom.app (F _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

variable {B S hS} in
/-- The derived pullback-stalk comparison along equal morphisms, read through the identification
of the two derived pullbacks. -/
theorem derivedPullbackGeometricStalkMap_app_comp_map_congr {X₁ X : AlgebraicSpaces B S hS}
    {m₁ m₂ : X₁ ⟶ X} (h : m₁ = m₂) (x : GeometricPoint B S hS X₁.1)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (derivedPullbackGeometricStalkMap m₁ x).app K ≫ (geometricDerivedStalk B S hS x).map
        ((smallEtaleDerivedModulePullbackCongr B S hS h).hom.app K) =
      eqToHom (congrArg (fun m : X₁ ⟶ X => (dext (stalkStructureMap B S hS m x).hom).obj
          ((geometricDerivedStalk B S hS (geometricPointMap m.hom x)).obj K)) h) ≫
        (derivedPullbackGeometricStalkMap m₂ x).app K := by
  subst h
  simp only [smallEtaleDerivedModulePullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    eqToHom_refl, Category.id_comp]
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- A diagram chase in three categories: a composite `c₁ ≫ eqToHom ≫ c₂ ≫ m ≫ d₁` agrees with
`G(t ≫ d_a) ≫ d_g ≫ Γ(k₁ ≫ c_g ≫ k₂ ≫ l_φ)` given the composition laws `hCL₁`, `hCL₂`, the
naturality `hnat`, the congruence `hcong` and the transport `hTR`. -/
theorem etaleTransport_chase {C : Type u₁} [Category.{v₁} C] {D₁ : Type u₂} [Category.{v₂} D₁]
    {E : Type u₃} [Category.{v₃} E] (G : D₁ ⥤ C) (Γ : E ⥤ C)
    {Q₀ Q₁ Q₂ : D₁} {E₀ E₁ E₂ E₃ E₄ : E} {O₂ O₃ O₄ O₅ O₆ O₂' P₁ P₂ : C}
    {t : Q₀ ⟶ Q₁} {da : Q₁ ⟶ Q₂} {k₁ : E₀ ⟶ E₁} {k₁i : E₁ ⟶ E₀} {cg : E₁ ⟶ E₂} {k₂ : E₂ ⟶ E₃}
    {lφ : E₃ ⟶ E₄} {c₁ : G.obj Q₀ ⟶ O₂} {p₁ : O₂ = O₃} {c₂ : O₃ ⟶ O₄} {m : O₄ ⟶ O₆}
    {m₁ : O₄ ⟶ O₅} {m₂ : O₅ ⟶ O₆} {d₁ : O₆ ⟶ Γ.obj E₄} {d₂ : O₅ ⟶ Γ.obj E₃}
    {dg : G.obj Q₂ ⟶ Γ.obj E₀} {D₁₂ : P₁ ⟶ Γ.obj E₁} {D₂₁ : P₂ ⟶ Γ.obj E₂}
    {c₃ : G.obj Q₁ ⟶ O₂'} {c₃i : O₂' ⟶ G.obj Q₁} {p₂ : P₂ = O₃} {p₃ : O₂ = O₂'} {p₄ : P₁ = O₂'}
    {p₅ : P₁ = P₂}
    (hm : m = m₁ ≫ m₂)
    (hnat : m₂ ≫ d₁ = d₂ ≫ Γ.map lφ)
    (hCL₂ : D₂₁ ≫ Γ.map k₂ = eqToHom p₂ ≫ c₂ ≫ m₁ ≫ d₂)
    (hCL₁ : D₁₂ ≫ Γ.map k₁i = eqToHom p₄ ≫ c₃i ≫ G.map da ≫ dg)
    (hcong : D₁₂ ≫ Γ.map cg = eqToHom p₅ ≫ D₂₁)
    (hTR : c₁ ≫ eqToHom p₃ = G.map t ≫ c₃)
    (hc₃ : c₃ ≫ c₃i = 𝟙 _) (hk : k₁i ≫ k₁ = 𝟙 _) :
    (c₁ ≫ eqToHom p₁ ≫ c₂ ≫ m) ≫ d₁ = G.map (t ≫ da) ≫ dg ≫ Γ.map (k₁ ≫ cg ≫ k₂ ≫ lφ) := by
  subst hm
  have hCL₁' : G.map da ≫ dg ≫ Γ.map k₁ = c₃ ≫ eqToHom p₄.symm ≫ D₁₂ := by
    have := congrArg (fun z => eqToHom p₄.symm ≫ z ≫ Γ.map k₁) hCL₁
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Γ.map_comp, hk, Γ.map_id, Category.comp_id] at this
    rw [this, reassoc_of% hc₃]
  have hCL₂' : c₂ ≫ m₁ ≫ d₂ = eqToHom p₂.symm ≫ D₂₁ ≫ Γ.map k₂ := by
    rw [hCL₂, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [G.map_comp, Γ.map_comp, Γ.map_comp, Γ.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hCL₁', reassoc_of% hcong, hnat, reassoc_of% hCL₂', ← reassoc_of% hTR]
  simp only [eqToHom_trans_assoc]

/-- An equivalence with the invertibility of a base-change map transfers along isomorphisms of
the data. -/
theorem iff_isIso_ringBaseChangeCohomologyMap_of_iso {R A R' A' : Type u} {_ : CommRing R}
    {_ : CommRing A} {_ : CommRing R'} {_ : CommRing A'} {_ : Algebra R A} {_ : Algebra R R'}
    {_ : Algebra R A'} {_ : Algebra A A'} {_ : Algebra R' A'} {_ : IsScalarTower R A A'}
    {_ : IsScalarTower R R' A'} {P : Prop} {n : ℤ}
    {K K₁ : DerivedCategory (ModuleCat.{u} A)} {K' K₁' : DerivedCategory (ModuleCat.{u} A')}
    {φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K'}
    {φ₁ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K₁ ⟶ K₁'}
    (H : P ↔ IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n))
    (e : K ≅ K₁) (e' : K' ≅ K₁')
    (h : φ ≫ e'.hom = (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.map e.hom ≫ φ₁) :
    P ↔ IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K₁ K₁' φ₁ n) :=
  H.trans (isIso_ringBaseChangeCohomologyMap_iff_of_iso e e' φ φ₁ h.symm n)

variable {B S hS} in
/-- **The map of Equation 0DKF along an affine étale quadruple.** For a cartesian square of
algebraic spaces and a cartesian square of affine schemes mapping to it by étale morphisms, the
map of Equation 0DKF of the first square at `a'(x̄)` is invertible exactly when the one of the
second square at `x̄`, for the pullbacks of `K`, `K'` and the induced morphism, is. -/
theorem isIso_geometricStalkBaseChangeCohomologyMap_iff_affineQuadruple
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    ∀ (U V V' U' : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
      [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
      (a : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (b : (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS) ⟶ Y)
      (c : (⟨yoneda.obj V', isAlgebraicSpace_yoneda B S hS V'⟩ : AlgebraicSpaces B S hS) ⟶ Y')
      (a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ : AlgebraicSpaces B S hS) ⟶ X')
      (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀),
      IsEtale B S hS a.hom → IsEtale B S hS b.hom → IsEtale B S hS c.hom →
      IsPullback g₀' f₀' f₀ g₀ →
      representedSpaceMap B S hS f₀ ≫ b = a ≫ f →
      representedSpaceMap B S hS g₀ ≫ b = c ≫ g →
      representedSpaceMap B S hS f₀' ≫ c = a' ≫ f' →
      ∀ (ha' : representedSpaceMap B S hS g₀' ≫ a = a' ≫ g')
      (x₁' : GeometricPoint B S hS (yoneda.obj U')) (n : ℤ),
      IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS f g f' g' sq.w
        (geometricPointMap a'.hom x₁') K K' φ n) ↔
      IsIso (canonicalGeometricStalkBaseChangeCohomologyMap B S hS (representedSpaceMap B S hS f₀)
        (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
        (representedSpaceMap B S hS g₀') (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) x₁'
        ((smallEtaleDerivedModulePullback B S hS a).obj K)
        ((smallEtaleDerivedModulePullback B S hS a').obj K')
        ((smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₀')
            a).hom.app K ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS a').map φ) n) := by
  intro U V V' U' _ _ _ _ a b c a' f₀ g₀ f₀' g₀' w₀ ha hb hc hpb hfa hgb hfc ha' x n
  have ha'e : IsEtale B S hS a'.hom :=
    isEtale_of_isPullback_of_etaleQuadruple B S hS sq ha hb hc
      (isPullback_representedSpaceMap B S hS hpb) hfa hgb hfc ha'
  have H := isIso_geometricStalkBaseChangeCohomologyMap_iff_of_isEtale_square B S hS sq.w
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀) hfa hgb hfc ha' ha hb hc ha'e x K K' φ n
  have hpt := (congrArg (fun m : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ :
    AlgebraicSpaces B S hS) ⟶ X => geometricPointMap m.hom x) ha').symm
  refine iff_isIso_ringBaseChangeCohomologyMap_of_iso H
    (eqToIso (dext_obj_eqToHom_comp
        (i := geometricPointMap a.hom (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
        (j := geometricPointMap g'.hom (geometricPointMap a'.hom x))
        (fun z => geometricStalkRing B S hS (X := X) z)
        (fun z => (geometricDerivedStalk B S hS z).obj K)
        hpt
        (stalkStructureMap B S hS a (geometricPointMap (representedSpaceMap B S hS g₀').hom x))) ≪≫
      (@asIso _ _ _ _ (derivedPullbackGeometricStalkMap a
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
        (isIso_derivedPullbackGeometricStalkMap a
          (geometricPointMap (representedSpaceMap B S hS g₀').hom x))).app K)
    ((@asIso _ _ _ _ (derivedPullbackGeometricStalkMap a' x)
      (isIso_derivedPullbackGeometricStalkMap a' x)).app K') ?_
  exact etaleTransport_chase
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (stalkStructureMap B S hS (representedSpaceMap B S hS g₀') x).hom).functor
    (geometricDerivedStalk B S hS (X := (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ :
      AlgebraicSpaces B S hS)) x) (Functor.map_comp _ _ _)
    ((derivedPullbackGeometricStalkMap a' x).naturality φ)
    (derivedPullbackGeometricStalkMap_comp B S hS a' g' x K)
    (derivedPullbackGeometricStalkMap_comp B S hS (representedSpaceMap B S hS g₀') a x K)
    (derivedPullbackGeometricStalkMap_app_comp_map_congr ha' x K)
    (totalDerivedExtensionScalarsComp_hom_app_eqToHom_comp
      (fun z => geometricStalkRing B S hS (X := X) z)
      (fun z => (geometricDerivedStalk B S hS z).obj K)
      hpt
      (stalkStructureMap B S hS a (geometricPointMap (representedSpaceMap B S hS g₀').hom x))
      (stalkStructureMap B S hS (representedSpaceMap B S hS g₀') x).hom)
    (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _)

variable {B S hS} in
/-- **Conditions (1) and (2) of Stacks 0DKG are equivalent**, condition (2) read on affine étale
quadruples: for a cartesian square of algebraic spaces and `K`, `K'` with quasi-coherent
cohomology, the map of Equation 0DKF attached to `φ : L(g')^*K ⟶ K'` is invertible at every
geometric point exactly when the composite of Stacks 065Z with the map induced by `φ` is
invertible at every affine étale quadruple. -/
theorem geometricPointwiseBaseChange_iff_affineChartwiseBaseChange
    {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hK : QcohDerived B S hS X K)
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (hK' : QcohDerived B S hS X' K')
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    GeometricPointwiseBaseChange B S hS f g f' g' sq.w K K' φ ↔
      AffineChartwiseBaseChange B S hS f g f' g' sq.w K K' φ :=
  geometricPointwiseBaseChange_iff_affineChartwiseBaseChange_of sq K hK K' hK' φ
    (isIso_geometricStalkBaseChangeCohomologyMap_iff_affineQuadruple sq K K' φ)
    (forall_isIso_geometricStalkBaseChangeCohomologyMap_iff_isIso_affineSectionsBaseChangeComp
      B S hS)

end AlgebraicGeometry.Space

end
