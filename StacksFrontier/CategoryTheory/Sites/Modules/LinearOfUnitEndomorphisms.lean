module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality

/-!
# A colimit-preserving functor out of `A`-modules is linear over the scalars it induces

Let `A` be a commutative ring, `(C, R)` a site with a sheaf of commutative rings, and
`Φ : Mod(A) ⥤ Mod(R)` an additive functor preserving colimits together with an isomorphism
`e : Φ(A) ≅ R`.  The endomorphisms `a · -` of the free module `A` are carried by `Φ` and `e` to
endomorphisms of the free `R`-module of rank one, which are multiplications by global sections of
`R`; this is a ring homomorphism `ψ : A →+* Γ(C, R)`.  Then `Φ` is `A`-linear for the linear
structure on `R`-modules induced by `ψ` (`Stacks.SheafOfModules.linearOver`).

## Main definitions

* `Stacks.SheafOfModules.unitIsoRingHom`: the ring homomorphism `A →+* Γ(C, R)` induced by `Φ`
  and `e`.

## Main results

* `CategoryTheory.NatTrans.ext_of_app_moduleCat_self`: natural endomorphisms of a
  colimit-preserving functor out of `Mod(A)` are determined by their value at `A`.
* `Stacks.SheafOfModules.linear_of_unitIso`: `Φ` is `A`-linear.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped IsMulCommutative

universe w v u r

namespace CategoryTheory

variable {A : Type u} [CommRing A] {D : Type*} [Category D]
  (Φ : ModuleCat.{u} A ⥤ D) [PreservesColimitsOfSize.{u, u} Φ]

/-- **Natural endomorphisms of a colimit-preserving functor out of `Mod(A)` are determined by
their value at the free module `A`.** -/
theorem NatTrans.ext_of_app_moduleCat_self {α β : Φ ⟶ Φ}
    (h : α.app (ModuleCat.of A A) = β.app (ModuleCat.of A A)) : α = β := by
  ext M
  let p : (∐ fun _ : M => ModuleCat.of A A) ⟶ M :=
    Sigma.desc fun m => ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)
  have hp : Epi p := by
    rw [ModuleCat.epi_iff_surjective]
    intro m
    refine ⟨(Sigma.ι (fun _ : M => ModuleCat.of A A) m).hom (1 : A), ?_⟩
    show (Sigma.ι (fun _ : M => ModuleCat.of A A) m ≫ p).hom (1 : A) = m
    simp [p]
  have : Epi (Φ.map p) := by
    have : PreservesColimitsOfSize.{0, 0} Φ := preservesColimitsOfSize_shrink Φ
    exact Φ.map_epi p
  have hcoprod : IsColimit (Φ.mapCocone (Cofan.mk _ (Sigma.ι fun _ : M => ModuleCat.of A A))) :=
    isColimitOfPreserves Φ (coproductIsCoproduct _)
  have hsum :
      α.app (∐ fun _ : M => ModuleCat.of A A) = β.app (∐ fun _ : M => ModuleCat.of A A) := by
    refine hcoprod.hom_ext fun ⟨m⟩ => ?_
    show Φ.map (Sigma.ι _ m) ≫ _ = Φ.map (Sigma.ι _ m) ≫ _
    rw [α.naturality, β.naturality, h]
  rw [← cancel_epi (Φ.map p), α.naturality, β.naturality, hsum]

end CategoryTheory

namespace Stacks.SheafOfModules

open Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (R.obj.obj X)]
  {A : Type w} [CommRing A]
  (Φ : ModuleCat.{w} A ⥤ _root_.SheafOfModules.{r} R) [Φ.Additive]
  (e : Φ.obj (ModuleCat.of A A) ≅ _root_.SheafOfModules.unit R)

omit [∀ X : Cᵒᵖ, IsMulCommutative (R.obj.obj X)] [Φ.Additive] in
/-- On an `A`-module, the identity scaled by `a * b` is the composite of the identity scaled by `a`
and the identity scaled by `b`. -/
lemma smul_id_mul (a b : A) (M : ModuleCat.{w} A) :
    (a * b) • 𝟙 M = (a • 𝟙 M) ≫ (b • 𝟙 M) := by
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, mul_comm]

/-- The endomorphism of the free module of rank one carried by `Φ` and `e` from multiplication by
`a` on `A`. -/
def unitIsoEnd (a : A) : _root_.SheafOfModules.unit R ⟶ _root_.SheafOfModules.unit R :=
  e.inv ≫ Φ.map (a • 𝟙 (ModuleCat.of A A)) ≫ e.hom

/-- **The ring homomorphism `A →+* Γ(C, R)` induced by `Φ` and `e`.** -/
def unitIsoRingHom : A →+* GlobalSectionRing R where
  toFun a := unitEndSection R (unitIsoEnd R Φ e a)
  map_one' := by
    apply (unitEndEquiv R).injective
    change unitEnd R (unitEndSection R _) = unitEnd R 1
    rw [unitEnd_unitEndSection, unitEnd_one, unitIsoEnd, one_smul, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]
  map_mul' a b := by
    apply (unitEndEquiv R).injective
    change unitEnd R (unitEndSection R _) = unitEnd R (unitEndSection R _ * unitEndSection R _)
    rw [unitEnd_mul, unitEnd_unitEndSection, unitEnd_unitEndSection, unitEnd_unitEndSection,
      unitIsoEnd, unitIsoEnd, unitIsoEnd, smul_id_mul, Functor.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  map_zero' := by
    apply (unitEndEquiv R).injective
    change unitEnd R (unitEndSection R _) = unitEnd R 0
    rw [unitEnd_unitEndSection, unitEnd_zero, unitIsoEnd, zero_smul, Functor.map_zero,
      Limits.zero_comp, Limits.comp_zero]
  map_add' a b := by
    apply (unitEndEquiv R).injective
    change unitEnd R (unitEndSection R _) = unitEnd R (unitEndSection R _ + unitEndSection R _)
    rw [unitEnd_add, unitEnd_unitEndSection, unitEnd_unitEndSection, unitEnd_unitEndSection,
      unitIsoEnd, unitIsoEnd, unitIsoEnd, add_smul, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add]

/-- The endomorphism of the free module of rank one given by the global section
`unitIsoRingHom R Φ e a` is `unitIsoEnd R Φ e a`. -/
lemma unitEnd_unitIsoRingHom (a : A) :
    unitEnd R (unitIsoRingHom R Φ e a) = unitIsoEnd R Φ e a :=
  unitEnd_unitEndSection R _

/-- Multiplication by a global section on the free module of rank one is `unitEnd`. -/
lemma globalSmul_unit (a : GlobalSectionRing R) :
    globalSmul R a (_root_.SheafOfModules.unit R) = unitEnd R a := by
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun X =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact mul_comm (a.1 X) (show R.obj.obj X from x)

variable [PreservesColimitsOfSize.{w, w} Φ]

/-- **`Φ` carries multiplication by `a` to multiplication by its induced global section.** -/
theorem map_smul_id_eq_globalSmul (a : A) (M : ModuleCat.{w} A) :
    Φ.map (a • 𝟙 M) = globalSmul R (unitIsoRingHom R Φ e a) (Φ.obj M) := by
  let α : Φ ⟶ Φ :=
    { app M := Φ.map (a • 𝟙 M)
      naturality M N f := by
        rw [← Φ.map_comp, ← Φ.map_comp, Linear.comp_smul, Linear.smul_comp, Category.id_comp,
          Category.comp_id] }
  let β : Φ ⟶ Φ :=
    { app M := globalSmul R (unitIsoRingHom R Φ e a) (Φ.obj M)
      naturality M N f := comp_globalSmul R _ (Φ.map f) }
  have hαβ : α = β := by
    refine NatTrans.ext_of_app_moduleCat_self Φ ?_
    show Φ.map (a • 𝟙 (ModuleCat.of A A)) =
      globalSmul R (unitIsoRingHom R Φ e a) (Φ.obj (ModuleCat.of A A))
    have h₁ := comp_globalSmul R (unitIsoRingHom R Φ e a) e.hom
    rw [globalSmul_unit, unitEnd_unitIsoRingHom, unitIsoEnd, Iso.hom_inv_id_assoc] at h₁
    rw [← cancel_mono e.hom, ← h₁]
  exact NatTrans.congr_app hαβ M

/-- **A colimit-preserving additive functor `Mod(A) ⥤ Mod(R)` with `Φ(A) ≅ R` is `A`-linear** for
the linear structure on `R`-modules induced by `unitIsoRingHom`. -/
theorem linear_of_unitIso :
    letI := linearOver R (unitIsoRingHom R Φ e)
    Φ.Linear A := by
  let _ : Linear A (_root_.SheafOfModules.{r} R) := linearOver R (unitIsoRingHom R Φ e)
  rw [Functor.linear_iff]
  intro M a
  rw [linearOver_smul_id, map_smul_id_eq_globalSmul]

end Stacks.SheafOfModules

end
