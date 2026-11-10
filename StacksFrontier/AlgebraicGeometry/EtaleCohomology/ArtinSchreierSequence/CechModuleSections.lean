module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ZariskiCechResolution

/-!
# The sections of the Zariski Čech complex of `𝐆_a` as a complex of modules

Let `g : Y ⟶ X` and `q : Y ⟶ T` be morphisms of schemes. The presheaf `V ↦ Γ(Y ×_X V)` on the
opens of `X` (`Stacks.ArtinSchreier.pullbackSectionsPresheaf g`) is a presheaf of modules over
`Γ(T, 𝒪_T)`, a function `b` on `T` acting on `Γ(Y ×_X V)` through multiplication by its pullback.
Forgetting the module structure recovers `pullbackSectionsPresheaf g`.

## Main definitions

* `Stacks.ArtinSchreier.moduleCoefficients`: forgetting the module structure, into the
  coefficient category `AddCommGrpCat.{u + 1}` of `𝐆_a`.
* `Stacks.ArtinSchreier.sectionsModulePresheaf`: `V ↦ Γ(Y ×_X V)` as a presheaf of
  `Γ(T, 𝒪_T)`-modules.
* `Stacks.ArtinSchreier.sectionsModulePresheafIso`: forgetting its module structure gives
  `pullbackSectionsPresheaf g`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace

universe u

namespace Stacks.ArtinSchreier

/-- Forgetting the module structure, into the coefficients of `𝐆_a`. -/
abbrev moduleCoefficients (B : Type u) [CommRing B] : ModuleCat.{u} B ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- A commutative ring `P` over `R`, as an `R`-module. -/
def algebraModule {R P : CommRingCat.{u}} (d : R ⟶ P) : ModuleCat.{u} R :=
  letI := d.hom.toAlgebra
  ModuleCat.of R P

variable {X Y T : Scheme.{u}} (g : Y ⟶ X) (q : Y ⟶ T)

/-- The ring map `Γ(T) ⟶ Γ(Y ×_X V)` pulling functions back along `Y ×_X V ⟶ Y ⟶ T`. -/
abbrev sectionsRingHom (V : X.Opens) : Γ(T, ⊤) →+* Γ(pullback g V.ι, ⊤) :=
  (pullback.fst g V.ι ≫ q).appTop.hom

/-- `Γ(Y ×_X V)` as a module over `Γ(T)`. -/
def sectionsModule (V : X.Opens) : ModuleCat.{u} Γ(T, ⊤) :=
  algebraModule (pullback.fst g V.ι ≫ q).appTop

/-- Restricting along `Y ×_X V' ⟶ Y ×_X V` the pullback of a function `b` on `T` to `Y ×_X V`
gives its pullback to `Y ×_X V'`. -/
theorem sectionsRingHom_comp {V' V : X.Opens} (h : V' ≤ V) (b : Γ(T, ⊤)) :
    (pullbackOpenMap g h).appTop.hom (sectionsRingHom g q V b) = sectionsRingHom g q V' b := by
  change ((pullback.fst g V.ι ≫ q).appTop ≫ (pullbackOpenMap g h).appTop).hom b =
    (pullback.fst g V'.ι ≫ q).appTop.hom b
  rw [← Scheme.Hom.comp_appTop, ← Category.assoc, pullbackOpenMap_fst]

/-- Restriction `Γ(Y ×_X V) ⟶ Γ(Y ×_X V')`, as a map of `Γ(T)`-modules. -/
def sectionsModuleMap {V' V : X.Opens} (h : V' ≤ V) :
    sectionsModule g q V ⟶ sectionsModule g q V' :=
  letI := (sectionsRingHom g q V).toAlgebra
  letI := (sectionsRingHom g q V').toAlgebra
  ModuleCat.ofHom
    { toFun := (pullbackOpenMap g h).appTop.hom
      map_add' := map_add _
      map_smul' := fun b x => by
        change (pullbackOpenMap g h).appTop.hom (sectionsRingHom g q V b * x) =
          sectionsRingHom g q V' b * (pullbackOpenMap g h).appTop.hom x
        rw [map_mul, sectionsRingHom_comp] }

/-- **`V ↦ Γ(Y ×_X V)` as a presheaf of `Γ(T)`-modules.** -/
def sectionsModulePresheaf : X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(T, ⊤) where
  obj V := sectionsModule g q V.unop
  map h := sectionsModuleMap g q h.unop.le
  map_id V := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (pullbackOpenMap g (𝟙 V.unop).le).appTop.hom x = x
    rw [pullbackOpenMap_id]
    rfl
  map_comp h₁ h₂ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (pullbackOpenMap g (h₁ ≫ h₂).unop.le).appTop.hom x =
      (pullbackOpenMap g h₂.unop.le).appTop.hom ((pullbackOpenMap g h₁.unop.le).appTop.hom x)
    rw [pullbackOpenMap_comp g h₂.unop.le h₁.unop.le, Scheme.Hom.comp_appTop]
    rfl

/-- **Forgetting the module structure of `V ↦ Γ(Y ×_X V)` gives `pullbackSectionsPresheaf g`.** -/
def sectionsModulePresheafIso :
    sectionsModulePresheaf g q ⋙ moduleCoefficients.{u} Γ(T, ⊤) ≅ pullbackSectionsPresheaf g :=
  NatIso.ofComponents (fun _ =>
      AddEquiv.toAddCommGrpIso
        { toFun := fun x => ULift.up x.down
          invFun := fun x => ULift.up x.down
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl })
    (fun _ => rfl)

end Stacks.ArtinSchreier

end
