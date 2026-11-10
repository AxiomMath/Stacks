module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.PointsSheaf

/-!
# The lifting step for the points over an affine base

Let `T'` be an affine object of the big fppf site over `S`, `A' = Γ(T', ⊤)`, and let `X` be an
fppf sheaf over `T'`. The lifting step
`AlgebraicGeometry.Stack.GroupoidLift.exists_lift_of_chart_of_isSheaf` applies to the points of
`X` over `T'` along a faithfully flat étale `A' → C'`: the sheaf condition and the separatedness
it asks for are `AlgebraicGeometry.Stack.GroupoidLift.exists_relPoints_map_eq` and
`AlgebraicGeometry.Stack.GroupoidLift.relPoints_map_injective`, and the chart is the chart of a
formally étale point (`AlgebraicGeometry.Stack.GroupoidLift.relChart_isFormallyEtale`).

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.isPushout_red`: `A' ⧸ I → C' ⧸ I C'` is the base change
  of `A' → C'`.
* `AlgebraicGeometry.Stack.GroupoidLift.exists_relPoints_lift`: a point over `A' ⧸ I` that comes
  from a formally étale point over `C' ⧸ I C'` lifts to a point over `A'`.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

section Algebra

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ)
  (C' : Type u) [CommRing C'] [Algebra A' C'] (hC : Cardinal.mk C' < κ) (I : Ideal A')
  (hI : I ^ 2 = ⊥) (hA : Cardinal.mk A' < κ)

/-- Extending `I` to `A'` along the identity and then to `C'` gives the extension `I C'`. -/
theorem map_map_algebraMap_self :
    (I.map (algebraMap A' A')).map (algebraMap A' C') = I.map (algebraMap A' C') := by
  rw [Ideal.map_map, Algebra.algebraMap_self, RingHom.comp_id]

/-- `C' ⊗[A'] (A' ⧸ I)` is `C' ⧸ I C'`. -/
noncomputable def tensorQuotEquivRed :
    C' ⊗[A'] (red I (baseAlg hA)).obj ≃+* (red I (nerve (A' := A') hκ C' hC 0)).obj :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C'
      (I.map (algebraMap A' A'))).symm.toRingEquiv.trans
    (Ideal.quotEquivOfEq (map_map_algebraMap_self C' I))

/-- **The reduction is a base change**: `A' ⧸ I → C' ⧸ I C'` is the pushout of `A' → C'` along
`A' → A' ⧸ I`. -/
theorem isPushout_red :
    IsPushout (CommRingCat.ofHom (algebraMap A' C'))
      (CommRingCat.ofHom ((thk I hI (baseAlg hA)).q.hom.hom : A' →+* (red I (baseAlg hA)).obj))
      (CommRingCat.ofHom ((thk I hI (nerve (A' := A') hκ C' hC 0)).q.hom.hom :
        C' →+* (red I (nerve (A' := A') hκ C' hC 0)).obj))
      (CommRingCat.ofHom ((baseThk hκ hC hI hA).bot.hom.hom :
        (red I (baseAlg hA)).obj →+* (red I (nerve (A' := A') hκ C' hC 0)).obj)) := by
  refine IsPushout.of_iso (CommRingCat.isPushout_tensorProduct A' C' (red I (baseAlg hA)).obj)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (tensorQuotEquivRed hκ C' hC I hA).toCommRingCatIso
    rfl rfl ?_ ?_
  · ext c
    exact congrArg (Ideal.Quotient.mk _) (one_smul A' c)
  · ext a
    change Ideal.Quotient.mk _ (a • (1 : C')) = Ideal.Quotient.mk _ (algebraMap A' C' a)
    rw [Algebra.smul_def, mul_one]

/-- The two inclusions `C' → C' ⊗[A'] C'` form the pushout of `A' → C'` along itself. -/
theorem isPushout_nerve_one :
    IsPushout (CommRingCat.ofHom ((baseMap hκ hC hA).hom.hom :
        (baseAlg hA).obj →+* (nerve (A' := A') hκ C' hC 0).obj))
      (CommRingCat.ofHom ((baseMap hκ hC hA).hom.hom :
        (baseAlg hA).obj →+* (nerve (A' := A') hκ C' hC 0).obj))
      (CommRingCat.ofHom ((SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 0)
        (R' := nerve (A' := A') hκ C' hC 1) (v₀ A' C' 1)).hom.hom :
          (nerve (A' := A') hκ C' hC 0).obj →+* (nerve (A' := A') hκ C' hC 1).obj))
      (CommRingCat.ofHom ((SmallAlg.homMk (R := nerve (A' := A') hκ C' hC 0)
        (R' := nerve (A' := A') hκ C' hC 1) (vₗ A' C' 1)).hom.hom :
          (nerve (A' := A') hκ C' hC 0).obj →+* (nerve (A' := A') hκ C' hC 1).obj)) :=
  (CommRingCat.isPushout_tensorProduct A' C' C').flip

end Algebra

section Points

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : X ⟶ yoneda.obj T')

/-- **The lifting step for the points over an affine base.** Let `X` be an fppf sheaf over an
affine `T'`, `A' = Γ(T', ⊤)`, let `C'` be a faithfully flat étale `A'`-algebra and `I ⊆ A'` a
square-zero ideal. If a point `x` of `X` over `A' ⧸ I` comes, over `C' ⧸ I C'`, from a formally
étale point over a formally smooth `A'`-algebra `P` of finite type, then `x` lifts to a point
over `A'`. -/
theorem exists_relPoints_lift (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff)
    {C' : Type u} [CommRing C'] [Algebra (ringOf B S hS T') C'] (hC : Cardinal.mk C' < B.cutoff)
    [Module.FaithfullyFlat (ringOf B S hS T') C'] [Algebra.Etale (ringOf B S hS T') C']
    {I : Ideal (ringOf B S hS T')} (hI : I ^ 2 = ⊥)
    (P : SmallAlg (ringOf B S hS T') B.cutoff) [Algebra.FormallySmooth (ringOf B S hS T') P.obj]
    [Algebra.FiniteType (ringOf B S hS T') P.obj] (p : (relPoints T' π).obj P)
    (hp : Space.FormallyEtale (yonedaEquiv.symm p.1))
    (x : (relPoints T' π).obj (red I (baseAlg hA)))
    (ubar : P.obj →ₐ[ringOf B S hS T'] (red I (nerve (A' := ringOf B S hS T')
      B.aleph0_lt_cutoff C' hC 0)).obj)
    (hubar : (relChart π P p).app _ ubar =
      (relPoints T' π).map (baseThk B.aleph0_lt_cutoff hC hI hA).bot x) :
    ∃ x' : (relPoints T' π).obj (baseAlg hA),
      (relPoints T' π).map (thk I hI (baseAlg hA)).q x' = x := by
  have hκ := B.aleph0_lt_cutoff
  have hEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have hFF := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_red hκ C' hC I hI hA)
  exact exists_lift_of_chart_of_isSheaf hκ hC hI (relChart_isFormallyEtale π P p hp) hA
    (fun z hz ↦ exists_relPoints_map_eq π hX (baseMap hκ hC hA) _ _
      (isPushout_nerve_one hκ C' hC hA) hFF.2 hEt z hz)
    (fun x₁ x₂ h ↦ relPoints_map_injective π hX (baseThk hκ hC hI hA).bot
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hFF.2)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hEt) h)
    x ubar hubar

end Points

section Affine

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- The ring of global sections of an affine object `V` of the big fppf site has cardinality
below the cutoff. -/
theorem card_sections_lt (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    Cardinal.mk Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) < B.cutoff := by
  have hV : ((BigFppfOver.toScheme B S hS).obj V).size < B.cutoff := V.left.property
  rw [Scheme.size_of_isAffine] at hV
  exact (le_max_right _ _).trans_lt hV

/-- **The sections of an affine object over `T'`**, a small `Γ(T')`-algebra. -/
noncomputable def sectionsAlg (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (j : V ⟶ T') :
    SmallAlg (ringOf B S hS T') B.cutoff :=
  letI : Algebra (ringOf B S hS T') Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map j).appTop.hom.toAlgebra
  SmallAlg.mk Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) (card_sections_lt V)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The structure map of `sectionsAlg V j` is the map on global sections induced by `j`. -/
theorem algebraMap_sectionsAlg (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (j : V ⟶ T') :
    algebraMap (ringOf B S hS T') (sectionsAlg V j).obj =
      ((BigFppfOver.toScheme B S hS).map j).appTop.hom :=
  rfl

/-- The structure morphism `Spec Γ(V) → T'` is the inverse of `V ≅ Spec Γ(V)` followed by `j`. -/
theorem specToBase_sectionsAlg (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (j : V ⟶ T') :
    specToBase (sectionsAlg V j) = ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫
      (BigFppfOver.toScheme B S hS).map j := by
  rw [specToBase, ← Scheme.isoSpec_inv_naturality]
  rfl

/-- The identification of `Spec Γ(V)` with `V`, over `T'`. -/
noncomputable def sectionsHom (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (j : V ⟶ T') :
    specOver (sectionsAlg V j) ⟶ V :=
  Over.homMk (ObjectProperty.homMk ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv) (by
    apply ObjectProperty.hom_ext
    change ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map V.hom =
      specToBase (sectionsAlg V j) ≫ B.inclusion.map T'.hom
    rw [specToBase_sectionsAlg]
    change ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map V.hom =
      (((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv ≫ B.inclusion.map j.left) ≫
        B.inclusion.map T'.hom
    rw [Category.assoc, ← Functor.map_comp, Over.w j])

/-- The underlying morphism of schemes of `sectionsHom V j` is the inverse of `V ≅ Spec Γ(V)`. -/
theorem toScheme_map_sectionsHom (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (j : V ⟶ T') :
    (BigFppfOver.toScheme B S hS).map (sectionsHom V j) =
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv :=
  rfl

/-- The identification `sectionsHom V j` of `Spec Γ(V)` with `V` is an isomorphism. -/
instance (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (j : V ⟶ T') : IsIso (sectionsHom V j) := by
  have : IsIso ((BigFppfOver.toScheme B S hS).map (sectionsHom V j)) :=
    (Scheme.isoSpec ((BigFppfOver.toScheme B S hS).obj V)).isIso_inv
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

/-- The identification `sectionsHom V j` followed by `j` is the structure morphism of
`Spec Γ(V)` over `T'`. -/
theorem sectionsHom_comp (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (j : V ⟶ T') :
    sectionsHom V j ≫ j = specOverToBase (sectionsAlg V j) := by
  apply BigFppfOver.map_toScheme_injective B S hS
  dsimp only
  rw [Functor.map_comp, toScheme_map_sectionsHom]
  exact (specToBase_sectionsAlg V j).symm

/-- The map of sections induced by a morphism over `T'`. -/
noncomputable def sectionsMap {V₁ V₂ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₂)] {j₁ : V₁ ⟶ T'} {j₂ : V₂ ⟶ T'}
    (g : V₁ ⟶ V₂) (hg : g ≫ j₂ = j₁) : sectionsAlg V₂ j₂ ⟶ sectionsAlg V₁ j₁ :=
  SmallAlg.homMk
    { toRingHom := ((BigFppfOver.toScheme B S hS).map g).appTop.hom
      commutes' := fun r ↦ by
        change ((BigFppfOver.toScheme B S hS).map g).appTop.hom
          (((BigFppfOver.toScheme B S hS).map j₂).appTop.hom r) =
            ((BigFppfOver.toScheme B S hS).map j₁).appTop.hom r
        rw [← hg, Functor.map_comp, Scheme.Hom.comp_appTop]
        rfl }

/-- The identifications `sectionsHom` are natural in morphisms over `T'`. -/
theorem specOverMap_sectionsMap {V₁ V₂ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₂)] {j₁ : V₁ ⟶ T'} {j₂ : V₂ ⟶ T'}
    (g : V₁ ⟶ V₂) (hg : g ≫ j₂ = j₁) :
    specOverMap (sectionsMap g hg) ≫ sectionsHom V₂ j₂ = sectionsHom V₁ j₁ ≫ g := by
  apply BigFppfOver.map_toScheme_injective B S hS
  dsimp only
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_sectionsHom, toScheme_map_sectionsHom,
    toScheme_map_specOverMap]
  exact Scheme.isoSpec_inv_naturality _

/-- The structure morphism of `Spec Γ(T', ⊤)` over `T'` is an isomorphism. -/
theorem isIso_specOverToBase_baseAlg (hA : Cardinal.mk (ringOf B S hS T') < B.cutoff) :
    IsIso (specOverToBase (T' := T') (baseAlg hA)) := by
  have : IsIso ((BigFppfOver.toScheme B S hS).map (specOverToBase (T' := T') (baseAlg hA))) := by
    change IsIso (Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') _)) ≫ _)
    rw [Algebra.algebraMap_self]
    change IsIso (Spec.map (𝟙 _) ≫ _)
    rw [Spec.map_id, Category.id_comp]
    infer_instance
  exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)

end Affine

end AlgebraicGeometry.Stack.GroupoidLift

end
