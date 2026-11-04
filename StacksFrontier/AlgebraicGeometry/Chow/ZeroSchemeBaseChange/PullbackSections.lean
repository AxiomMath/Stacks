module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections

/-!
# Functoriality of the pullback map on global sections

For a morphism of schemes `f : X ⟶ Y` and a sheaf of modules `F` on `Y`, the canonical map
`AlgebraicGeometry.pullbackGlobalSections f F : Γ(F, ⊤) ⟶ Γ(f^* F, ⊤)` is the unit of the
pullback--pushforward adjunction read at the top open, transported along `f⁻¹(⊤) = ⊤`. This file
proves that the transport is the identity, and that the map is functorial in `f`: pulling back
along `g` and then along `f` agrees with pulling back along `f ≫ g`, under the canonical
comparison `(f ≫ g)^* F ≅ f^* g^* F`.

## Main results

* `AlgebraicGeometry.pullbackGlobalSections_eq_unit` — the map is the unit of the adjunction at the
  top open, with no transport.
* `AlgebraicGeometry.pullbackGlobalSections_comp_hom` — functoriality, as an identity of morphisms.
* `AlgebraicGeometry.pullbackGlobalSections_injective_pullbackComp` — the comparison map is
  injective on global sections.

## Implementation notes

`Γ((Scheme.Modules.pushforward f).obj M, ⊤)` and `Γ(M, f ⁻¹ᵁ ⊤)` and `Γ(M, ⊤)` are definitionally
equal but pairwise distinct as terms, and `rw` builds its motive at a transparency at which they
are not interchangeable. So `pullbackGlobalSections_eq_unit` cannot be closed by `simp` or by
`rw [Category.comp_id]`: the identity it needs is `φ ≫ 𝟙 = φ` where the `𝟙` is at
`Γ(f^* F, ⊤)` and `φ` has codomain `Γ((Scheme.Modules.pushforward f).obj (f^* F), ⊤)`. It is
proved instead as a `congrArg` composed with `Category.comp_id`, a term whose type is checked at
default transparency, where the two agree.

## References

* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- Restriction along `f ⁻¹ᵁ ⊤ = ⊤` on the sections of a pullback is the identity. -/
private theorem pullbackMapTop_id {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (by simp : (⊤ : X.Opens) = f ⁻¹ᵁ (⊤ : Y.Opens))).op =
        𝟙 Γ((Scheme.Modules.pullback f).obj M, ⊤) := by
  simp

/-- The pullback map on global sections is the unit of the pullback--pushforward adjunction read at
the top open: the transport along `f ⁻¹ᵁ ⊤ = ⊤` in its definition is the identity. -/
public theorem pullbackGlobalSections_eq_unit {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    pullbackGlobalSections f F =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app ⊤ :=
  (congrArg (fun ψ => ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app ⊤ ≫ ψ)
    (pullbackMapTop_id f F)).trans (Category.comp_id _)

/-- **Functoriality of the pullback map on global sections.** Pulling back along `g` and then along
`f`, followed by the canonical comparison `f^* g^* L ≅ (f ≫ g)^* L`, is pulling back along
`f ≫ g`. -/
public theorem pullbackGlobalSections_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) :
    pullbackGlobalSections g L ≫ pullbackGlobalSections f ((Scheme.Modules.pullback g).obj L) ≫
        ((Scheme.Modules.pullbackComp f g).hom.app L).app ⊤ =
      pullbackGlobalSections (f ≫ g) L := by
  let adj₁ := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let adj₂ := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  have hconj : CategoryTheory.conjugateEquiv adj₁ adj₂
      ((Scheme.Modules.pullbackComp f g).hom) = (Scheme.Modules.pushforwardComp f g).inv := by
    have hInv : CategoryTheory.conjugateEquiv adj₂ adj₁
        ((Scheme.Modules.pullbackComp f g).inv) = (Scheme.Modules.pushforwardComp f g).hom :=
      CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv
        (Scheme.Modules.pullbackPushforwardAdjunction g)
        (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
        (Scheme.Modules.pushforwardComp f g)
    have hprod := CategoryTheory.conjugateEquiv_comm adj₁ adj₂
      (Iso.inv_hom_id (Scheme.Modules.pullbackComp f g))
    apply (cancel_mono (Scheme.Modules.pushforwardComp f g).hom).1
    rw [hInv] at hprod
    exact hprod.trans (Iso.inv_hom_id _).symm
  have h := CategoryTheory.unit_conjugateEquiv adj₁ adj₂
    (Scheme.Modules.pullbackComp f g).hom L
  rw [hconj] at h
  have h' := congrArg (fun t => Scheme.Modules.Hom.app t ⊤) h
  rw [pullbackGlobalSections_eq_unit, pullbackGlobalSections_eq_unit,
    pullbackGlobalSections_eq_unit]
  have key := h'.symm
  simp [adj₁, adj₂] at key
  exact key.trans (Category.comp_id _)

/-- The comparison map `f^* g^* L ≅ (f ≫ g)^* L` is injective on global sections. -/
public theorem pullbackGlobalSections_injective_pullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (L : Z.Modules) :
    Function.Injective (fun s : Γ((Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback g).obj L), ⊤) =>
      ((Scheme.Modules.pullbackComp f g).hom.app L).app ⊤ s) := by
  apply Function.LeftInverse.injective (g := fun s =>
    ((Scheme.Modules.pullbackComp f g).inv.app L).app ⊤ s)
  intro s
  have hidM := congrArg (fun η => η.app L)
    (Iso.hom_inv_id (Scheme.Modules.pullbackComp f g))
  rw [CategoryTheory.NatTrans.comp_app] at hidM
  change (Scheme.Modules.pullbackComp f g).hom.app L ≫
    (Scheme.Modules.pullbackComp f g).inv.app L = 𝟙 _ at hidM
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) hidM
  have h' := congrArg (fun φ => φ s) h
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply] using h'

end AlgebraicGeometry

end

end
