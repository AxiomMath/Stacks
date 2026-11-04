module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricSmoothModelOpenRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural

/-!
# Naturality of the identifications of `q^{-1}(j_! ℱ)` on the smooth model

Let `C` be the smooth projective model of `X_k̄` (`Stacks.EtaleCohomology.geometricSmoothModel`),
`q : C ⟶ X̄` its structure morphism over the compactification `j : X ⟶ X̄` and `j_C : X_k̄ ⟶ C`
the open immersion. The two identifications used by the trace on `C`,

* `κ : q^{-1}(j_! ℱ) ≅ j_{C!}(ℱ|_{X_k̄})`
  (`Stacks.EtaleCohomology.geometricSmoothModelInverseImageIso`) and
* `l : j_C^{-1} q^{-1}(j_! ℱ) ≅ ℱ|_{X_k̄}`
  (`Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso`),

are natural in the sheaf `ℱ` of `Λ`-modules on `X`. Neither is built as a component of a natural
isomorphism (`κ` is an adjoint of an isomorphism, `l` uses the inverse of a unit), so this is
proved here, through the naturality of their constituents.

## Main results

* `Stacks.EtaleCohomology.geometricSmoothModelInverseImageIso_hom_naturality`,
  `Stacks.EtaleCohomology.geometricSmoothModelInverseImageIso_inv_naturality`.
* `Stacks.EtaleCohomology.geometricSmoothModelInverseImageRestrictionIso_hom_naturality`.
* `Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso_hom_naturality`, the general form of the
  latter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-! ### Two naturality chases, for abstract functors -/

section Chase

variable {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞] [Category 𝒟]
  (Iq : 𝒜 ⥤ ℬ) (Ig : ℬ ⥤ 𝒞) (IfU : 𝒜 ⥤ 𝒞) (Im : 𝒜 ⥤ 𝒟) (Ip : 𝒟 ⥤ 𝒞)
  (e₁ : Iq ⋙ Ig ≅ IfU) (e₂ : Im ⋙ Ip ≅ IfU)

/-- **`e₁ ≪≫ e₂⁻¹ ≪≫ Ip(ν)` is natural** in `(M, ν)`: for `ψ : M ⟶ M'` and `φ : F ⟶ F'` with
`Im(ψ) ≫ ν' = ν ≫ φ`. -/
public lemma iso_trans_symm_mapIso_hom_naturality {M M' : 𝒜} (ψ : M ⟶ M') {F F' : 𝒟}
    (ν : Im.obj M ≅ F) (ν' : Im.obj M' ≅ F') (φ : F ⟶ F')
    (hν : Im.map ψ ≫ ν'.hom = ν.hom ≫ φ) :
    (Iq ⋙ Ig).map ψ ≫ (e₁.app M' ≪≫ (e₂.app M').symm ≪≫ Ip.mapIso ν').hom =
      (e₁.app M ≪≫ (e₂.app M).symm ≪≫ Ip.mapIso ν).hom ≫ Ip.map φ := by
  have h₁ : (Iq ⋙ Ig).map ψ ≫ e₁.hom.app M' = e₁.hom.app M ≫ IfU.map ψ := e₁.hom.naturality ψ
  have h₂ : IfU.map ψ ≫ e₂.inv.app M' = e₂.inv.app M ≫ Ip.map (Im.map ψ) := e₂.inv.naturality ψ
  have h₃ : Ip.map (Im.map ψ) ≫ Ip.map ν'.hom = Ip.map ν.hom ≫ Ip.map φ :=
    (Ip.map_comp _ _).symm.trans ((congrArg Ip.map hν).trans (Ip.map_comp _ _))
  have h₄ : IfU.map ψ ≫ e₂.inv.app M' ≫ Ip.map ν'.hom =
      e₂.inv.app M ≫ Ip.map ν.hom ≫ Ip.map φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Ip.map ν'.hom) h₂).trans
      ((Category.assoc _ _ _).trans (congrArg (e₂.inv.app M ≫ ·) h₃)))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e₂.inv.app M' ≫ Ip.map ν'.hom) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (e₁.hom.app M ≫ ·) h₄).trans
      ((congrArg (e₁.hom.app M ≫ ·) (Category.assoc _ _ _).symm).trans
        (Category.assoc _ _ _).symm))))

/-- **`Stacks.EtaleCohomology.restrictionCompIso` is natural** in `(M, λ)`. -/
public lemma restrictionCompIso_hom_naturality (R : ℬ ⥤ 𝒞) (ε : Ig ≅ R) {M M' : 𝒜} (ψ : M ⟶ M')
    {E E' : 𝒞} (lam : (Iq ⋙ Ig).obj M ≅ E) (lam' : (Iq ⋙ Ig).obj M' ≅ E') (φ : E ⟶ E')
    (h : (Iq ⋙ Ig).map ψ ≫ lam'.hom = lam.hom ≫ φ) :
    R.map (Iq.map ψ) ≫ (restrictionCompIso Iq Ig R ε M' lam').hom =
      (restrictionCompIso Iq Ig R ε M lam).hom ≫ φ := by
  have hn : R.map (Iq.map ψ) ≫ ε.inv.app (Iq.obj M') = ε.inv.app (Iq.obj M) ≫ Ig.map (Iq.map ψ) :=
    ε.inv.naturality (Iq.map ψ)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ lam'.hom) hn).trans
    ((Category.assoc _ _ _).trans ((congrArg (ε.inv.app (Iq.obj M) ≫ ·) h).trans
      (Category.assoc _ _ _).symm)))

end Chase

section ExtensionByZero

variable (Λ : Type) [Ring Λ]

/-- **`m^{-1} m_! F ≅ F` is natural in `F`.** -/
public theorem inverseImageExtensionByZeroIso_hom_naturality {V S : Scheme.{u}} (m : V ⟶ S)
    [Etale m] [Mono m] {F F' : EtaleModules.{u, 0} Λ V} (φ : F ⟶ F') :
    (etaleModuleInverseImage.{u, 0} Λ m).map ((etaleModuleExtensionByZero.{u, 0} Λ m).map φ) ≫
        (inverseImageExtensionByZeroIso Λ m F').hom =
      (inverseImageExtensionByZeroIso Λ m F).hom ≫ φ := by
  have h₁ := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ m).hom.naturality
    ((etaleModuleExtensionByZero.{u, 0} Λ m).map φ)
  have h₂ := (asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ m).unit).inv.naturality φ
  dsimp only [Functor.comp_map, Functor.id_map] at h₂
  simp only [inverseImageExtensionByZeroIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [reassoc_of% h₁, h₂, Category.assoc]

end ExtensionByZero

section Square

variable (Λ : Type) [Ring Λ] {U Y S V : Scheme.{u}} (g : U ⟶ Y) [Etale g] [Mono g] (q : Y ⟶ S)
  (p : U ⟶ V) (m : V ⟶ S) (h : p ≫ m = g ≫ q)

omit [Mono g] in
/-- **`g^{-1} q^{-1} M ≅ p^{-1} F` is natural** in `(M, ν)`
(`Stacks.EtaleCohomology.selfMapTwistOpenRestrictionIso`): for `ψ : M ⟶ M'` and `φ : F ⟶ F'` with
`m^{-1}(ψ) ≫ ν' = ν ≫ φ`. -/
public theorem selfMapTwistOpenRestrictionIso_hom_naturality {M M' : EtaleModules.{u, 0} Λ S}
    (ψ : M ⟶ M') {F F' : EtaleModules.{u, 0} Λ V}
    (ν : (etaleModuleInverseImage.{u, 0} Λ m).obj M ≅ F)
    (ν' : (etaleModuleInverseImage.{u, 0} Λ m).obj M' ≅ F') (φ : F ⟶ F')
    (hν : (etaleModuleInverseImage.{u, 0} Λ m).map ψ ≫ ν'.hom = ν.hom ≫ φ) :
    (etaleModuleRestriction.{u, 0} Λ g).map ((etaleModuleInverseImage.{u, 0} Λ q).map ψ) ≫
        (selfMapTwistOpenRestrictionIso Λ g q p m h M' ν').hom =
      (selfMapTwistOpenRestrictionIso Λ g q p m h M ν).hom ≫
        (etaleModuleInverseImage.{u, 0} Λ p).map φ :=
  restrictionCompIso_hom_naturality _ _ _ _ ψ _ _ _
    (iso_trans_symm_mapIso_hom_naturality _ _ _ _ _ _ _ ψ ν ν' φ hν)

end Square

section SmoothModel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ]

/-- **`j_C^{-1} q^{-1}(j_! ℱ) ≅ ℱ|_{X_k̄}` is natural in `ℱ`.** -/
public theorem geometricSmoothModelInverseImageRestrictionIso_hom_naturality
    {F F' : EtaleModules.{u, 0} Λ X} (φ : F ⟶ F') :
    (etaleModuleRestriction.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map φ)) ≫
        (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F').hom =
      (geometricSmoothModelInverseImageRestrictionIso f j kbar Λ F).hom ≫
        (etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map φ :=
  selfMapTwistOpenRestrictionIso_hom_naturality Λ (geometricSmoothModel f j kbar).j
    (geometricSmoothModelProj f j kbar) (pullback.fst f (specAlgebraMap k kbar)) j.immersion
    (geometricSmoothModel_j_comp_proj f j kbar).symm
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map φ)
    (inverseImageExtensionByZeroIso Λ j.immersion F)
    (inverseImageExtensionByZeroIso Λ j.immersion F')
    φ (inverseImageExtensionByZeroIso_hom_naturality Λ j.immersion φ)

/-- **`(j_! ℱ)|_{X̄_k̄} ≅ f̄_* j_{C!}(ℱ|_{X_k̄})` is natural in `ℱ`.** -/
public theorem geometricSmoothModelRestrictionIso_hom_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (φ : F ⟶ F') :
    (etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map φ) ≫
        (geometricSmoothModelRestrictionIso f j kbar Λ F').hom =
      (geometricSmoothModelRestrictionIso f j kbar Λ F).hom ≫
        (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).map
          ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
            ((etaleModuleInverseImage.{u, 0} Λ
              (pullback.fst f (specAlgebraMap k kbar))).map φ)) := by
  have h₁ := (compactificationFieldBaseChangeExtensionByZeroIso Λ f j kbar).inv.naturality φ
  have h₂ := extensionByZeroGeometricSmoothModelIso_hom_naturality f j kbar Λ
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map φ)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- The forward map of `κ : q^{-1}(j_! ℱ) ≅ j_{C!}(ℱ|_{X_k̄})`. -/
public theorem geometricSmoothModelInverseImageIso_hom (F : EtaleModules.{u, 0} Λ X) :
    (geometricSmoothModelInverseImageIso f j kbar Λ F).hom =
      (selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
          (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).inv.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F) ≫
        ((etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb).homEquiv
          _ _).symm (geometricSmoothModelRestrictionIso f j kbar Λ F).hom :=
  rfl

/-- **`κ : q^{-1}(j_! ℱ) ≅ j_{C!}(ℱ|_{X_k̄})` is natural in `ℱ`.** -/
public theorem geometricSmoothModelInverseImageIso_hom_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (φ : F ⟶ F') :
    (etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map φ) ≫
        (geometricSmoothModelInverseImageIso f j kbar Λ F').hom =
      (geometricSmoothModelInverseImageIso f j kbar Λ F).hom ≫
        (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map φ) := by
  have h₁ := (selfMapRestrictionIso.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))
    (geometricSmoothModel f j kbar).fb (geometricSmoothModelProj f j kbar) rfl).inv.naturality
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map φ)
  have h₂ := (Adjunction.homEquiv_naturality_left_symm
    (etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb)
    ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map φ))
    (geometricSmoothModelRestrictionIso f j kbar Λ F').hom).symm
  have h₃ := congrArg
    ((etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb).homEquiv
      _ _).symm (geometricSmoothModelRestrictionIso_hom_naturality f j kbar Λ φ)
  have h₄ := Adjunction.homEquiv_naturality_right_symm
    (etaleModuleInverseImageAdj.{u, 0} Λ (geometricSmoothModel f j kbar).fb)
    (geometricSmoothModelRestrictionIso f j kbar Λ F).hom
    ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map φ))
  rw [geometricSmoothModelInverseImageIso_hom, geometricSmoothModelInverseImageIso_hom]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (h₂.trans (h₃.trans h₄))).trans
      (Category.assoc _ _ _).symm)))

/-- **`κ⁻¹ : j_{C!}(ℱ|_{X_k̄}) ≅ q^{-1}(j_! ℱ)` is natural in `ℱ`.** -/
public theorem geometricSmoothModelInverseImageIso_inv_naturality {F F' : EtaleModules.{u, 0} Λ X}
    (φ : F ⟶ F') :
    (etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).map
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).map φ) ≫
        (geometricSmoothModelInverseImageIso f j kbar Λ F').inv =
      (geometricSmoothModelInverseImageIso f j kbar Λ F).inv ≫
        (etaleModuleInverseImage.{u, 0} Λ (geometricSmoothModelProj f j kbar)).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map φ) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← geometricSmoothModelInverseImageIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SmoothModel

end Stacks.EtaleCohomology

end
