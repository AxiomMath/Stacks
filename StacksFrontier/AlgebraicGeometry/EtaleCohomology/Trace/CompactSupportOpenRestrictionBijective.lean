module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelCoefficientMap

/-!
# The restriction to `X_k̄` of maps on `X̄_k̄` is bijective

For sheaves `F` of `Λ`-modules and `G` of `R`-modules on a smooth curve `X` with compactification
`j : X ⟶ X̄`, every map `res_ψ(F|_{X_k̄}) ⟶ G|_{X_k̄}` is the restriction
(`Stacks.EtaleCohomology.compactSupportOpenRestriction`) of exactly one map
`res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}`: `(j_! F)|_{X̄_k̄} ≅ j'_!(F|_{X_k̄})` with
`j' : X_k̄ ⟶ X̄_k̄` an open immersion, the restriction along `j_C ≫ f̄ = j'` is `j'^{-1}`, and
`j'^{-1}` is bijective on maps out of `j'_!(-)` because the unit of `j'_! ⊣ j'^{-1}` is invertible.

## Main results

* `Stacks.EtaleCohomology.bijective_compactSupportOpenRestriction`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Abstract

variable {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]

/-- **A right adjoint is bijective on maps out of the image of an object at which the unit is
invertible.** -/
theorem bijective_map_of_iso_of_isIso_unit {L : 𝒞 ⥤ 𝒟} {Rt : 𝒟 ⥤ 𝒞} (adj : L ⊣ Rt) {A : 𝒟}
    (a : 𝒞) (e : A ≅ L.obj a) [IsIso (adj.unit.app a)] (B : 𝒟) :
    Function.Bijective (fun ψ : A ⟶ B => Rt.map ψ) := by
  let E := (e.homCongr (Iso.refl B)).trans ((adj.homEquiv a B).trans
    ((asIso (adj.unit.app a) ≪≫ (Rt.mapIso e).symm).homCongr (Iso.refl (Rt.obj B))))
  have hE : (fun ψ : A ⟶ B => Rt.map ψ) = E := by
    funext ψ
    simp only [E, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
      Adjunction.homEquiv_unit, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, asIso_inv,
      Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc]
  rw [hE]
  exact E.bijective

/-- **Bijectivity of a functor on a hom-set transports along a natural isomorphism.** -/
theorem bijective_map_of_natIso {K K' : 𝒞 ⥤ 𝒟} (e : K ≅ K') {A B : 𝒞}
    (h : Function.Bijective (fun ψ : A ⟶ B => K'.map ψ)) :
    Function.Bijective (fun ψ : A ⟶ B => K.map ψ) := by
  have hE : (fun ψ : A ⟶ B => K.map ψ) =
      ((e.app A).symm.homCongr (e.app B).symm) ∘ (fun ψ : A ⟶ B => K'.map ψ) := by
    funext ψ
    exact (NatIso.naturality_2 e ψ).symm
  rw [hE]
  exact (Equiv.bijective _).comp h

/-- **Conjugating by isomorphisms keeps bijectivity**, in the shape of
`Stacks.EtaleCohomology.compactSupportOpenRestriction`. -/
theorem bijective_iso_comp_map_comp (Fb : 𝒞 ⥤ 𝒟) (Jr : 𝒟 ⥤ ℰ) {A B : 𝒞} {D₁ D₂ : 𝒟}
    {X X₁ Y : ℰ} (h : Function.Bijective (fun θ : A ⟶ B => Jr.map (Fb.map θ)))
    (p : X ≅ X₁) (q : X₁ ≅ Jr.obj D₁) (T : Fb.obj A ≅ D₁) (s : Fb.obj B ≅ D₂)
    (t : Jr.obj D₂ ≅ Y) :
    Function.Bijective
      (fun θ : A ⟶ B => p.hom ≫ q.hom ≫ Jr.map (T.inv ≫ Fb.map θ ≫ s.hom) ≫ t.hom) := by
  have hE : (fun θ : A ⟶ B => p.hom ≫ q.hom ≫ Jr.map (T.inv ≫ Fb.map θ ≫ s.hom) ≫ t.hom) =
      ((p ≪≫ q ≪≫ Jr.mapIso T.symm).symm.homCongr (Jr.mapIso s ≪≫ t)) ∘
        (fun θ : A ⟶ B => Jr.map (Fb.map θ)) := by
    funext θ
    simp only [Function.comp_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [hE]
  exact (Equiv.bijective _).comp h

end Abstract

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ)

/-- **The restriction along `j_C` of the inverse image along `f̄` is the restriction along
`j' = j_C ≫ f̄ : X_k̄ ⟶ X̄_k̄`.** -/
def geometricSmoothModelInverseImageRestrictionCompIso (S : Type) [Ring S] :
    etaleModuleInverseImage.{u, 0} S (geometricSmoothModel f j kbar).fb ⋙
        etaleModuleRestriction.{u, 0} S (geometricSmoothModel f j kbar).j ≅
      etaleModuleRestriction.{u, 0} S (compactificationFieldBaseChangeImmersion f j kbar) :=
  Functor.isoWhiskerLeft (etaleModuleInverseImage.{u, 0} S (geometricSmoothModel f j kbar).fb)
      (etaleModuleInverseImageRestrictionIso.{u, 0} S (geometricSmoothModel f j kbar).j).symm ≪≫
    (etaleModuleInverseImageCompIso.{u, 0} S (geometricSmoothModel f j kbar).j
      (geometricSmoothModel f j kbar).fb).symm ≪≫
    eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} S m)
      (geometricSmoothModel_j_fb f j kbar)) ≪≫
    etaleModuleInverseImageRestrictionIso.{u, 0} S
      (compactificationFieldBaseChangeImmersion f j kbar)

/-- **Every map `res_ψ(F|_{X_k̄}) ⟶ G|_{X_k̄}` is the restriction of exactly one map
`res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}`.** -/
theorem bijective_compactSupportOpenRestriction (F : EtaleModules.{u, 0} Λ X)
    (G : EtaleModules.{u, 0} R X) :
    Function.Bijective (compactSupportOpenRestriction f j kbar ψ F G) := by
  have hcore := bijective_map_of_natIso
    (geometricSmoothModelInverseImageRestrictionCompIso f j kbar R)
    (bijective_map_of_iso_of_isIso_unit
      (etaleModuleExtensionByZeroAdj.{u, 0} R (compactificationFieldBaseChangeImmersion f j kbar))
      ((etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F))
      ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).mapIso
          ((compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).app F).symm ≪≫
        ((etaleModuleExtensionByZeroRestrictScalars ψ
          (compactificationFieldBaseChangeImmersion f j kbar)).app
            ((etaleModuleInverseImage.{u, 0} Λ
              (pullback.fst f (specAlgebraMap k kbar))).obj F)).symm)
      ((etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)))
  exact bijective_iso_comp_map_comp _ _ hcore
    ((etaleModuleRestrictScalars ψ (pullback f (specAlgebraMap k kbar))).mapIso
      (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F).symm)
    (restrictionRestrictScalarsIso ψ (geometricSmoothModel f j kbar).j _)
    (geometricSmoothModelRestrictScalarsInverseImageIso f j kbar ψ F)
    ((selfMapRestrictionIso.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))
      (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).app
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (geometricSmoothModelInverseImageRestrictionIso f j kbar R G)

end Stacks.EtaleCohomology

end
