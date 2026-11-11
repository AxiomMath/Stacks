module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal

/-!
# Relative differentials are unchanged by an isomorphism of the base

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site and `a : O₁' ⟶ O₁` an
isomorphism of sheaves of commutative rings. A derivation of `O₂` with values in a sheaf of
`O₂`-modules kills the image of `O₁'` under `a ≫ φ` exactly when it kills the image of `O₁` under
`φ`, since `a` is surjective on sections. So the two functors of relative derivations agree, and
so do the sheaves of relative differentials `Ω_{O₂/O₁'}` and `Ω_{O₂/O₁}` corepresenting them.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.derivationEquivOfIsIso`: the derivations relative to
  `a ≫ φ` are the derivations relative to `φ`.
* `AlgebraicGeometry.SheafOfModules.derivationsFunctorIsoOfIsIso`: the two functors of relative
  derivations are isomorphic.
* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSiteIsoOfIsIso`:
  `Ω_{O₂/O₁'} ≅ Ω_{O₂/O₁}`.
* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSiteIsoOfEqComp`: the same, for a
  morphism `ψ` given with an equation `ψ = a ≫ φ`.

## References

* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public section

open CategoryTheory

universe v u w m

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁' O₁ O₂ : Sheaf J CommRingCat.{w}} (a : O₁' ⟶ O₁) [IsIso a] (φ : O₁ ⟶ O₂)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Every section of `O₁` is the image under `a` of a section of `O₁'`, `a` being an
isomorphism. -/
theorem exists_hom_app_eq_of_isIso (X : Cᵒᵖ) (t : O₁.obj.obj X) :
    ∃ s : O₁'.obj.obj X, a.hom.app X s = t :=
  ⟨(((sheafToPresheaf J CommRingCat.{w}).mapIso (asIso a)).app X).inv t,
    Iso.inv_hom_id_apply (((sheafToPresheaf J CommRingCat.{w}).mapIso (asIso a)).app X) t⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The derivations relative to `a ≫ φ` are the derivations relative to `φ`**, for an
isomorphism `a`: both are the derivations of `O₂` killing the image of `O₁`. -/
def derivationEquivOfIsIso
    (M : PresheafOfModules.{m} (O₂.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    PresheafOfModulesOfCommRing.Derivation' M (a ≫ φ).hom ≃
      PresheafOfModulesOfCommRing.Derivation' M φ.hom where
  toFun D :=
    { D with
      d_app := fun {X} t => by
        obtain ⟨s, rfl⟩ := exists_hom_app_eq_of_isIso a X t
        exact D.d_app s }
  invFun D :=
    { D with
      d_app := fun {X} s => D.d_app (a.hom.app X s) }
  left_inv _ := rfl
  right_inv _ := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The derivation relative to `φ` attached to a derivation relative to `a ≫ φ` has the same
underlying maps. -/
@[simp]
theorem derivationEquivOfIsIso_apply_d
    (M : PresheafOfModules.{m} (O₂.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    (D : PresheafOfModulesOfCommRing.Derivation' M (a ≫ φ).hom) {X : Cᵒᵖ} (x : O₂.obj.obj X) :
    (derivationEquivOfIsIso a φ M D).d x = D.d x :=
  rfl

/-- **The functors of derivations relative to `a ≫ φ` and to `φ` are isomorphic**, for an
isomorphism `a`. -/
noncomputable def derivationsFunctorIsoOfIsIso :
    derivationsFunctor.{m} O₁' O₂ (a ≫ φ) ≅ derivationsFunctor.{m} O₁ O₂ φ :=
  NatIso.ofComponents (fun F => Equiv.toIso (derivationEquivOfIsIso a φ F.val)) (fun _ => rfl)

/-- **`Ω_{O₂/O₁'} ≅ Ω_{O₂/O₁}`** for an isomorphism `a : O₁' ⟶ O₁`: the sheaf of differentials
of `a ≫ φ` is that of `φ`, the two corepresenting isomorphic functors of derivations. -/
noncomputable def moduleOfDifferentialsOfSiteIsoOfIsIso :
    moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂ (a ≫ φ) ≅
      moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ :=
  ((derivationsFunctor.{m} O₁' O₂ (a ≫ φ)).corepresentableBy.ofIso
    (derivationsFunctorIsoOfIsIso a φ)).isoCoreprX

/-- **`Ω_{O₂/O₁'} ≅ Ω_{O₂/O₁}`** for a morphism `ψ : O₁' ⟶ O₂` that factors as `a ≫ φ` through an
isomorphism `a : O₁' ⟶ O₁`. -/
noncomputable def moduleOfDifferentialsOfSiteIsoOfEqComp {ψ : O₁' ⟶ O₂} (h : ψ = a ≫ φ) :
    moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂ ψ ≅
      moduleOfDifferentialsOfSite.{v, u, w, m} O₁ O₂ φ :=
  eqToIso (congrArg (fun χ => moduleOfDifferentialsOfSite.{v, u, w, m} O₁' O₂ χ) h) ≪≫
    moduleOfDifferentialsOfSiteIsoOfIsIso a φ

end AlgebraicGeometry.SheafOfModules

end
