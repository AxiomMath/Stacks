module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence

/-!
# Twisting global sections along an adjunction, read on the corepresentation by `R_C`

Let `(C, J)` be a site with a terminal object and `R` a commutative ring. Global sections of
sheaves of `R`-modules are corepresented by the constant sheaf `R_C`
(`Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation`): a global section `s`
of `F` is the morphism `R_C ⟶ F` taking `1` to `s`.

Let `Φ ⊣ Ψ` be an adjunction of endofunctors of `Sheaf J (ModuleCat R)` and `θ : Γ(Ψ -) ⟶ Γ(-)`
a natural transformation which, read on sections over terminal objects `T`, `T'`, is a given
identification `ρ : Ψ(-)(T) ≅ (-)(T')`. Then `c ⋙ Φ` and `c` (with `c` the constant sheaf
functor) are both left adjoint to `Ψ(-)(T)`, so there is a canonical isomorphism
`κ : c ⋙ Φ ≅ c`, and for a global section `s` of `Ψ M`:

`[θ_M(s)] = κ⁻¹ ≫ (the Φ ⊣ Ψ transpose of [s]) : R_C ⟶ M`.

This is the degree-zero input of the identification of a twisted endomorphism of cohomology with
a twisted action on `Ext` out of `R_C` (`Stacks.ExtCup.rightDerivedPlusIsoExt_conj_edge`), used
for the geometric Frobenius in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.Cohomology.GlobalSections.moduleGlobalSectionsCorepresentation_hom_app_twist`.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.GlobalSections

variable (R : Type w) [CommRing R] {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J (ModuleCat.{max u w} R)] [HasTerminal C]

/-- The corepresentation by `R_C` of a global section, read back through the constant sheaf
adjunction, is the linear map taking `1` to that section. -/
theorem constantSheafΓAdj_homEquiv_moduleGlobalSectionsCorepresentation_hom_app
    (M : Sheaf J (ModuleCat.{max u w} R))
    (s : (Sheaf.Γ J (ModuleCat.{max u w} R)).obj M) :
    (constantSheafΓAdj J (ModuleCat.{max u w} R)).homEquiv _ M
        (((moduleGlobalSectionsCorepresentation R J).hom.app M).hom s) =
      (moduleULiftHomAddEquiv.{w, u} R _).symm s :=
  ((constantSheafΓAdj J (ModuleCat.{max u w} R)).homAddEquiv _ M).apply_symm_apply _

/-- The linear map out of `ULift R` taking `1` to `φ y` is the one taking `1` to `y`, then `φ`. -/
theorem moduleULiftHomAddEquiv_symm_apply_hom {N N' : ModuleCat.{max u w} R} (φ : N ⟶ N')
    (y : N) :
    (moduleULiftHomAddEquiv.{w, u} R N').symm (φ y) =
      (moduleULiftHomAddEquiv.{w, u} R N).symm y ≫ φ := by
  apply (moduleULiftHomAddEquiv.{w, u} R N').injective
  rw [AddEquiv.apply_symm_apply, moduleULiftHomAddEquiv_apply, ModuleCat.comp_apply,
    ← moduleULiftHomAddEquiv_apply R N, AddEquiv.apply_symm_apply]

/-- **A twist of global sections, read on the corepresentation by `R_C`.** Let `G : C ⥤ C` be a
continuous functor, `Φ ⊣ G_*` an adjunction with the pushforward along `G`, `T` a terminal object
with `G T` terminal, and `θ : Γ(G_* -) ⟶ Γ(-)` a natural transformation which, on sections over
`T` and `G T`, is the identity of `M(G T) = (G_* M)(T)`. Then for a global section `s` of `G_* M`,
the morphism `R_C ⟶ M` corepresenting `θ_M(s)` is the `Φ ⊣ G_*` transpose of the morphism
corepresenting `s`, precomposed with the canonical comparison `R_C ⟶ Φ(R_C)` of the two left
adjoints `c ⋙ Φ` and `c` of the sections over `G T`. -/
theorem moduleGlobalSectionsCorepresentation_hom_app_twist (G : C ⥤ C) [G.IsContinuous J J]
    {Φ : Sheaf J (ModuleCat.{max u w} R) ⥤ Sheaf J (ModuleCat.{max u w} R)}
    (adj : Φ ⊣ G.sheafPushforwardContinuous (ModuleCat.{max u w} R) J J)
    (θ : G.sheafPushforwardContinuous (ModuleCat.{max u w} R) J J ⋙
      Sheaf.Γ J (ModuleCat.{max u w} R) ⟶ Sheaf.Γ J (ModuleCat.{max u w} R))
    {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T))
    (hθ : ∀ M, θ.app M ≫ (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{max u w} R) hGT).hom.app M =
      (Sheaf.ΓNatIsoSheafSections J (ModuleCat.{max u w} R) hT).hom.app
        ((G.sheafPushforwardContinuous (ModuleCat.{max u w} R) J J).obj M))
    (M : Sheaf J (ModuleCat.{max u w} R))
    (s : (Sheaf.Γ J (ModuleCat.{max u w} R)).obj
      ((G.sheafPushforwardContinuous (ModuleCat.{max u w} R) J J).obj M)) :
    ((moduleGlobalSectionsCorepresentation R J).hom.app M).hom (θ.app M s) =
      (((constantSheafAdj J (ModuleCat.{max u w} R) hT).comp adj).leftAdjointUniq
          (constantSheafAdj J (ModuleCat.{max u w} R) hGT)).inv.app
          (ModuleCat.of R (ULift.{u} R)) ≫
        (adj.homEquiv _ _).symm
          (((moduleGlobalSectionsCorepresentation R J).hom.app
            ((G.sheafPushforwardContinuous (ModuleCat.{max u w} R) J J).obj M)).hom s) := by
  let A := ModuleCat.{max u w} R
  let Ψ := G.sheafPushforwardContinuous A J J
  let cΓ := constantSheafΓAdj J A
  let cT := constantSheafAdj J A hT
  let cT' := constantSheafAdj J A hGT
  have hΓ : ∀ {T₀ : C} (hT₀ : IsTerminal T₀), Sheaf.ΓNatIsoSheafSections J A hT₀ =
      cΓ.rightAdjointUniq (constantSheafAdj J A hT₀) := fun _ => rfl
  let g : constantModuleSheaf R J ⟶ Ψ.obj M :=
    ((moduleGlobalSectionsCorepresentation R J).hom.app (Ψ.obj M)).hom s
  let f₁ : constantModuleSheaf R J ⟶ M :=
    ((moduleGlobalSectionsCorepresentation R J).hom.app M).hom (θ.app M s)
  have hg : cΓ.homEquiv _ _ g = (moduleULiftHomAddEquiv.{w, u} R _).symm s :=
    constantSheafΓAdj_homEquiv_moduleGlobalSectionsCorepresentation_hom_app R J _ s
  have hf₁ : cΓ.homEquiv _ _ f₁ = (moduleULiftHomAddEquiv.{w, u} R _).symm (θ.app M s) :=
    constantSheafΓAdj_homEquiv_moduleGlobalSectionsCorepresentation_hom_app R J _ _
  change f₁ = _ ≫ (adj.homEquiv _ _).symm g
  apply (cT'.homEquiv _ M).injective
  -- the left side
  have hL : cT'.homEquiv _ M f₁ = cT.homEquiv _ _ g := by
    rw [← Adjunction.homEquiv_comp_rightAdjointUniq_hom_app cΓ cT' _ _ f₁, hf₁,
      moduleULiftHomAddEquiv_symm_apply_hom, Category.assoc, ← hΓ hGT, hθ M, hΓ hT,
      ← Adjunction.homEquiv_comp_rightAdjointUniq_hom_app cΓ cT _ _ g, hg]
    rfl
  have h4 : (cT.comp adj).homEquiv _ _ ((adj.homEquiv _ _).symm g) = cT.homEquiv _ _ g := by
    rw [Adjunction.comp_homEquiv]
    simp only [Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj, Equiv.trans_apply,
      Equiv.apply_symm_apply]
    rfl
  exact hL.trans (h4.symm.trans (Adjunction.homEquiv_leftAdjointUniq_inv_app_comp (cT.comp adj) cT'
    (ModuleCat.of R (ULift.{u} R)) ((adj.homEquiv _ _).symm g)).symm)

end Stacks.Cohomology.GlobalSections
