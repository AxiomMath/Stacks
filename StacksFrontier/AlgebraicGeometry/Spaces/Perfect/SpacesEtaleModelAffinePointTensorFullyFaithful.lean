module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SpacesEtaleModelAffinePointTensor

/-!
# Maps between the complexes `𝒪_X ⊗_A C` on an affine algebraic space

Let `X ≅ h_{Spec A}` be an affine algebraic space and let `T_ψ = 𝒪_X ⊗_A -` be the functor from
`A`-modules to modules on the model of the spaces-étale site, for the ring isomorphism
`ψ : A ≅ Γ(X, 𝒪_X)`. For complexes `C` and `C'` of `A`-modules, the morphisms
`T_ψ(C) ⟶ T_ψ(C')` in `D(𝒪_X)` are the morphisms `C ⟶ C'` in `D(A)`: the functor
`D(A) ⥤ D(𝒪_X)` is the derived functor of `M ↦ ε^*(M̃)` (fully faithful by Stacks 06Z0 and
071Q) followed by equivalences.

For `C` K-projective (for instance a bounded complex of finite projective modules), every
morphism `T_ψ(C) ⟶ T_ψ(C')` in `D(𝒪_X)` is therefore induced by a map of complexes `C ⟶ C'`,
and two maps of complexes induce the same morphism exactly when they are homotopic. This is the
form in which the proof of Stacks 09RI reduces morphisms between perfect objects on an affine
stage to the ring-level statement of Stacks 09RE.

## Main results

* `AlgebraicGeometry.Space.representedTildeMapDerivedCategoryFullyFaithful`: the derived functor
  of `M ↦ ε^*(M̃)` is fully faithful on all of `D(A)`.
* `AlgebraicGeometry.Space.pointTensorQCompIso`: `T_ψ` followed by the derived equivalence of the
  model is the derived functor of `M ↦ g^*ε^*(M̃)`, on complexes.
* `AlgebraicGeometry.Space.exists_pointTensor_Q_map_eq`: morphisms out of `T_ψ(C)` in `D(𝒪_X)`
  for `C` K-projective are maps of complexes.
* `AlgebraicGeometry.Space.pointTensor_Q_map_eq_iff`: two maps of complexes agree in `D(𝒪_X)`
  after `T_ψ` exactly when they agree in `D(A)`.

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable {𝒞 𝒟 𝒟' 𝒜 : Type*} [Category 𝒞] [Category 𝒟] [Category 𝒟'] [Category 𝒜]
  {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒟'} {Q : 𝒞 ⥤ 𝒜} {Φ : 𝒜 ⥤ 𝒟'}

/-- **Two maps agree after `F` exactly when they agree after `Q`**, when `F ⋙ G ≅ Q ⋙ Φ` with
`G` faithful and `Φ` faithful. -/
theorem map_eq_iff_of_isoComp (e : F ⋙ G ≅ Q ⋙ Φ) [G.Faithful] [Φ.Faithful] {X Y : 𝒞}
    (u u' : X ⟶ Y) : F.map u = F.map u' ↔ Q.map u = Q.map u' := by
  have key : ∀ v : X ⟶ Y, G.map (F.map v) = e.hom.app X ≫ Φ.map (Q.map v) ≫ e.inv.app Y :=
    fun v => (NatIso.naturality_2 e v).symm
  refine ⟨fun h => Φ.map_injective ?_, fun h => G.map_injective (by rw [key, key, h])⟩
  have h' := congrArg G.map h
  rwa [key, key, cancel_epi, cancel_mono] at h'

/-- **Every map `F X ⟶ F Y` is `F.map u`** when every map `Q X ⟶ Q Y` is `Q.map u`, for
`F ⋙ G ≅ Q ⋙ Φ` with `G` full and faithful and `Φ` full. -/
theorem exists_map_eq_of_isoComp (e : F ⋙ G ≅ Q ⋙ Φ) [G.Full] [G.Faithful] [Φ.Full] {X Y : 𝒞}
    (hQ : ∀ ψ : Q.obj X ⟶ Q.obj Y, ∃ u : X ⟶ Y, Q.map u = ψ) (φ : F.obj X ⟶ F.obj Y) :
    ∃ u : X ⟶ Y, F.map u = φ := by
  obtain ⟨ψ, hψ⟩ := Φ.map_surjective (e.inv.app X ≫ G.map φ ≫ e.hom.app Y)
  obtain ⟨u, rfl⟩ := hQ ψ
  refine ⟨u, G.map_injective ?_⟩
  have h := NatIso.naturality_2 e u
  dsimp at h hψ
  rw [hψ] at h
  simpa using h.symm

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance high] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S)

/-- **The derived functor of `M ↦ ε^*(M̃)` is fully faithful on `D(A)`**: it is the derived
functor of `~`, fully faithful into `D_QCoh(𝒪_{Spec A})` (Stacks 06Z0), followed by `ε^*`,
fully faithful on `D_QCoh(𝒪_{Spec A})` (Stacks 071Q). -/
def representedTildeMapDerivedCategoryFullyFaithful :
    (representedTilde B S hS hA p).mapDerivedCategory.FullyFaithful := by
  let T := BigFppfOver.mk B S hS hA p
  haveI : (tilde.functor (CommRingCat.of A)).Additive := ⟨tilde.map_add _ _⟩
  haveI : PreservesFiniteColimits (tilde.functor (CommRingCat.of A)) :=
    Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of A)
  haveI : PreservesFiniteLimits (tilde.functor (CommRingCat.of A)) :=
    AlgebraicGeometry.tilde.preservesFiniteLimits _
  let Fd := (tilde.functor (CommRingCat.of A)).mapDerivedCategory
  let L : DerivedCategory (ModuleCat.{u} A) ⥤
      (representedSchemeDerivedQcoh B S hS T).FullSubcategory :=
    ObjectProperty.lift _ Fd fun M => representedSchemeDerivedQcoh_tilde B S hS hA p M
  have hF : Fd.FullyFaithful :=
    AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful (CommRingCat.of A)
  have hL : L.FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := (representedSchemeDerivedQcoh B S hS T).ι)
      (hF.ofIso (ObjectProperty.liftCompιIso _ _ _).symm)
  exact (hL.comp (representedDerivedAssociatedModuleFullyFaithful B S hS T)).ofIso
    ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫
    representedTildeMapDerivedCategoryIso B S hS hA p)

variable {X : AlgebraicSpaces B S hS}
  (g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩)

section Exactness

variable (X) in
/-- The exactness of the equivalence of modules on the model with `𝒪_X`-modules. -/
theorem spacesEtaleModelModulesEquiv_exact :
    (spacesEtaleModelModulesEquiv B S hS X).functor.Additive ∧
      PreservesFiniteLimits (spacesEtaleModelModulesEquiv B S hS X).functor ∧
      PreservesFiniteColimits (spacesEtaleModelModulesEquiv B S hS X).functor := by
  let e := spacesEtaleModelModulesEquiv B S hS X
  have : PreservesFiniteLimits e.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ e.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits e.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      e.toAdjunction.leftAdjoint_preservesColimits
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- The exactness of the étale restriction along an isomorphism. -/
theorem etaleModulePullbackEquivalenceOfIsoSameUniverse_exact :
    (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor.Additive ∧
      PreservesFiniteLimits (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor ∧
      PreservesFiniteColimits
        (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor := by
  let e := etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g
  have : PreservesFiniteLimits e.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ e.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteColimits e.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      e.toAdjunction.leftAdjoint_preservesColimits
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

end Exactness

/-- **`T_ψ` followed by the derived equivalence of the model is the derived functor of
`M ↦ g^*ε^*(M̃)`**, on complexes of `A`-modules: for the ring isomorphism `ψ` of
`AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom`,
`e_X(T_ψ(C)) ≅ g^*ε^*(C̃)` naturally in the complex `C`. -/
def pointTensorQCompIso :
    letI := (spacesEtaleModelModulesEquiv_exact B S hS X).1
    letI := (spacesEtaleModelModulesEquiv_exact B S hS X).2.1
    letI := (spacesEtaleModelModulesEquiv_exact B S hS X).2.2
    letI := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).1
    letI := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.1
    letI := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.2
    ((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        (spacesEtaleModelModulesEquiv B S hS X).functor.mapDerivedCategory ≅
      DerivedCategory.Q ⋙ (representedTilde B S hS hA p).mapDerivedCategory ⋙
        (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor.mapDerivedCategory :=
  letI := (spacesEtaleModelModulesEquiv_exact B S hS X).1
  letI := (spacesEtaleModelModulesEquiv_exact B S hS X).2.1
  letI := (spacesEtaleModelModulesEquiv_exact B S hS X).2.2
  letI := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).1
  letI := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.1
  letI := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.2
  let T := spacesEtaleModelPointTensor B S hS (representedTildeOfIsoPointRingHom B S hS hA p g)
  let e := (spacesEtaleModelModulesEquiv B S hS X).functor
  let R := representedTilde B S hS hA p
  let Eq := (etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g).functor
  let m₁ : T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      e.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (T ⋙ e).mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ e)) (ComplexShape.up ℤ)
  let m₂ : (T ⋙ e).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (representedTildeOfIso B S hS hA p g).mapHomologicalComplex (ComplexShape.up ℤ) :=
    NatIso.mapHomologicalComplex (pointTensorIsoRepresentedTildeOfIso B S hS hA p g)
      (ComplexShape.up ℤ)
  let m₃ : (representedTildeOfIso B S hS hA p g).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Eq.mapHomologicalComplex (ComplexShape.up ℤ) :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (R ⋙ Eq)) (ComplexShape.up ℤ)).symm
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (T.mapHomologicalComplex (ComplexShape.up ℤ))
      e.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (m₁ ≪≫ m₂ ≪≫ m₃) DerivedCategory.Q ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
      Eq.mapDerivedCategoryFactors.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight R.mapDerivedCategoryFactors.symm _ ≪≫
    Functor.associator _ _ _

/-- **Two maps of complexes of `A`-modules agree after `T_ψ` in `D(𝒪_X)` exactly when they agree
in `D(A)`**, for `X ≅ h_{Spec A}` and the ring isomorphism `ψ` of
`AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom`. -/
theorem pointTensor_Q_map_eq_iff {C C' : CochainComplex (ModuleCat.{u} A) ℤ} (u u' : C ⟶ C') :
    DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map u) =
      DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map u') ↔
      DerivedCategory.Q.map u = DerivedCategory.Q.map u' := by
  let := (spacesEtaleModelModulesEquiv_exact B S hS X).1
  let := (spacesEtaleModelModulesEquiv_exact B S hS X).2.1
  let := (spacesEtaleModelModulesEquiv_exact B S hS X).2.2
  let := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).1
  let := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.1
  let := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.2
  have := (spacesEtaleModelDerivedEquiv B S hS X).faithful_functor
  have : (representedTilde B S hS hA p).mapDerivedCategory.Faithful :=
    (representedTildeMapDerivedCategoryFullyFaithful B S hS hA p).faithful
  let eg := etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g
  let DE := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence eg.functor eg.inverse eg.unitIso
    eg.counitIso
  have : eg.functor.mapDerivedCategory.Faithful := DE.faithful_functor
  have : ((representedTilde B S hS hA p).mapDerivedCategory ⋙
      eg.functor.mapDerivedCategory).Faithful := Functor.Faithful.comp _ _
  exact Functor.map_eq_iff_of_isoComp (pointTensorQCompIso B S hS hA p g) u u'

/-- **Every morphism `T_ψ(C) ⟶ T_ψ(C')` in `D(𝒪_X)` is induced by a map of complexes**, for
`X ≅ h_{Spec A}`, the ring isomorphism `ψ` of
`AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom` and `C` K-projective. -/
theorem exists_pointTensor_Q_map_eq {C C' : CochainComplex (ModuleCat.{u} A) ℤ} [C.IsKProjective]
    (φ : DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) ⟶
      DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C')) :
    ∃ u : C ⟶ C', DerivedCategory.Q.map (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map u) = φ := by
  let := (spacesEtaleModelModulesEquiv_exact B S hS X).1
  let := (spacesEtaleModelModulesEquiv_exact B S hS X).2.1
  let := (spacesEtaleModelModulesEquiv_exact B S hS X).2.2
  let := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).1
  let := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.1
  let := (etaleModulePullbackEquivalenceOfIsoSameUniverse_exact B S hS hA p g).2.2
  have := (spacesEtaleModelDerivedEquiv B S hS X).faithful_functor
  have := (spacesEtaleModelDerivedEquiv B S hS X).full_functor
  have : (representedTilde B S hS hA p).mapDerivedCategory.Full :=
    (representedTildeMapDerivedCategoryFullyFaithful B S hS hA p).full
  let eg := etaleModulePullbackEquivalenceOfIso.{u, u} B S hS g
  let DE := Stacks.DerivedGlueing.mapDerivedCategoryEquivalence eg.functor eg.inverse eg.unitIso
    eg.counitIso
  have : eg.functor.mapDerivedCategory.Full := DE.full_functor
  have : ((representedTilde B S hS hA p).mapDerivedCategory ⋙
      eg.functor.mapDerivedCategory).Full := Functor.Full.comp _ _
  refine Functor.exists_map_eq_of_isoComp (pointTensorQCompIso B S hS hA p g) (fun ψ => ?_) φ
  let ι := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  obtain ⟨v, hv⟩ := (CochainComplex.IsKProjective.Qh_map_bijective C
    ((HomotopyCategory.quotient _ _).obj C')).surjective (ι.hom.app C ≫ ψ ≫ ι.inv.app C')
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective v
  refine ⟨u, ?_⟩
  have h := NatIso.naturality_2 ι.symm u
  dsimp at h hv
  rw [← h, hv]
  simp

end AlgebraicGeometry.Space

end
