module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison

/-!
# Derived global sections are invariant under isomorphisms of schemes over `A`

Let `f : X ⟶ Spec A` and let `g : Y ⟶ X` be an isomorphism of schemes. Then for every
`E ∈ D(𝒪_X)` the `A`-linear derived global sections of the restriction of `E` along `g`, computed
on `Y` through `g ≫ f`, are those of `E`: `RΓ(Y, g^*E) ≅ RΓ(X, E)` in `D(A)`.

## Main results

* `AlgebraicGeometry.restrictFunctorGlobalSectionsOverIso`: `Γ(Y, g^*M) ≅ Γ(X, M)` as
  `A`-modules, naturally in `M`.
* `AlgebraicGeometry.nonempty_iso_derivedGlobalSectionsOver_restrictFunctor`:
  `RΓ(Y, g^*E) ≅ RΓ(X, E)` in `D(A)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- Evaluation at an open equal to `⊤`, followed by restriction of scalars along the composite
with the corresponding restriction map, is `A`-linear global sections. -/
def evaluationRestrictScalarsTopIso {W : X.Opens} (h : W = ⊤) :
    ∀ (r : A →+* ↥Γ(X, W)),
      r = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop ≫
        X.presheaf.map (eqToHom h).op).hom →
      (SheafOfModules.evaluation X.ringCatSheaf (op W) ⋙ ModuleCat.restrictScalars r ≅
        globalSectionsOver f) := by
  subst h
  intro r hr
  rw [Scheme.presheaf_map_eq_id, Category.comp_id] at hr
  subst hr
  exact Iso.refl _

variable (g : Y ⟶ X) [IsIso g]

/-- The image of the whole of `Y` under an isomorphism of schemes `g : Y ⟶ X` is the whole of
`X`. -/
theorem image_top_eq_top_of_isIso : g ''ᵁ (⊤ : Y.Opens) = ⊤ :=
  (Scheme.Hom.image_top_eq_opensRange g).trans (eq_top_iff.2 fun x _ =>
    ⟨(inv g).base x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩)

/-- For an isomorphism `g : Y ⟶ X`, the map `g.appTop : Γ(X, ⊤) ⟶ Γ(Y, ⊤)` followed by the
inverse of `g.appIso ⊤ : Γ(X, g ''ᵁ ⊤) ≅ Γ(Y, ⊤)` is the restriction map of `X` along
`g ''ᵁ ⊤ = ⊤`. -/
theorem appTop_comp_appIso_inv :
    g.appTop ≫ (g.appIso ⊤).inv = X.presheaf.map (eqToHom (image_top_eq_top_of_isIso g)).op := by
  rw [Iso.comp_inv_eq, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  simp only [Scheme.Hom.appLE]
  exact (Category.comp_id _).symm.trans (congrArg (Scheme.Hom.app g ⊤ ≫ ·)
    (Y.presheaf.map_id _).symm)

/-- **`Γ(Y, g^*M) = Γ(X, M)` over `A`** for an isomorphism `g : Y ⟶ X`. -/
def restrictFunctorGlobalSectionsOverIso :
    Scheme.Modules.restrictFunctor g ⋙ globalSectionsOver (g ≫ f) ≅ globalSectionsOver f :=
  evaluationRestrictScalarsTopIso f (image_top_eq_top_of_isIso g)
    ((g.appIso ⊤).inv.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (g ≫ f).appTop).hom)
    (by
      rw [← appTop_comp_appIso_inv g, Scheme.Hom.comp_appTop, ← CommRingCat.hom_comp]
      simp only [Category.assoc])

/-- **`RΓ(Y, g^*E) ≅ RΓ(X, E)` over `A`** for an isomorphism `g : Y ⟶ X`, computed on a
K-injective representative. -/
theorem nonempty_iso_derivedGlobalSectionsOver_restrictFunctor (E : DerivedCategory X.Modules) :
    Nonempty ((derivedGlobalSectionsOver (g ≫ f)).obj
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj E) ≅
        (derivedGlobalSectionsOver f).obj E) := by
  have hres := Stacks.Cohomology.Localization.enoughKInjectives (C := X.Modules)
  have hresY := Stacks.Cohomology.Localization.enoughKInjectives (C := Y.Modules)
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative hres E
  have hI' := Scheme.Modules.isKInjective_mapHomologicalComplex_restrictFunctor_of_isIso g I hI
  have eY := rightDerivedObjIso hresY (globalSectionsOver (g ≫ f)) inferInstance
    (derivedGlobalSectionsOver (g ≫ f)) (derivedGlobalSectionsOverUnit (g ≫ f)) inferInstance _ hI'
  have eX := rightDerivedObjIso hres (globalSectionsOver f) inferInstance
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) inferInstance I hI
  have f₁ := (Scheme.Modules.restrictFunctor g).mapDerivedCategoryFactors.app I
  have g₁ := (Functor.mapHomologicalComplexCompIso (restrictFunctorGlobalSectionsOverIso f g)
    (ComplexShape.up ℤ)).app I
  exact ⟨(derivedGlobalSectionsOver (g ≫ f)).mapIso
      ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.mapIso e.symm ≪≫ f₁) ≪≫
    eY.symm ≪≫ DerivedCategory.Q.mapIso g₁ ≪≫ eX ≪≫ (derivedGlobalSectionsOver f).mapIso e⟩

end AlgebraicGeometry

end
