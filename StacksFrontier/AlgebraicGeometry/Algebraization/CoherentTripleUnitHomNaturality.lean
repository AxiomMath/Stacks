module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleInvertible
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionTransport
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# `hcompat` reduces to an equation of global sections

`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` needs a hypothesis `hcompat` identifying
two morphisms out of the unit module after cancelling `Scheme.Modules.pullbackUnitIso` on each
side. Both morphisms come from global sections through `Scheme.Modules.unitHomEquivTop`, and
`Scheme.Modules.pullbackUnitIso_sections_naturality` identifies each side, after the same
cancellation, with the morphism attached to a single global section: on the punctured side, to
`Stacks.Algebraization.globalSectionsMap A f L x` (by
`Stacks.Algebraization.globalSectionsMap_apply`); on the closed side, to the pullback of `x₀`
itself (reading the triple's own identifying morphism as the identity). Since
`Scheme.Modules.unitHomEquivTop` is injective, `hcompat` for the morphisms attached to `x` and
`x₀` reduces to the single equation of global sections that these two coincide.

## Main results

* `Stacks.Algebraization.hcompat_of_eq_globalSectionsMap`: `hcompat` holds for the morphisms
  attached to `x : Γ(L.F, ⊤)` and `x₀ : Γ(L.F₀, ⊤)` whenever `globalSectionsMap A f L x` equals
  the pullback of `x₀` to the punctured closed fibre.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

private theorem presheafMapTop_apply {X Y : Scheme.{u}} (g : X ⟶ Y) (M : X.Modules)
    (y : Γ(M, ⊤)) :
    M.presheaf.map (eqToHom (by simp : (⊤ : X.Opens) = g ⁻¹ᵁ ⊤)).op y = y := by
  have h : M.presheaf.map (eqToHom (by simp : (⊤ : X.Opens) = g ⁻¹ᵁ ⊤)).op = 𝟙 Γ(M, ⊤) := by
    simp
  exact (ConcreteCategory.congr_hom h y).trans (CategoryTheory.id_apply y)

private theorem moduleHom_app_restrict {X : Scheme.{u}} {M N : X.Modules} (a : M ⟶ N)
    {V W : X.Opens} (i : V ⟶ W) (y : Γ(M, W)) :
    a.app V (M.presheaf.map i.op y) = N.presheaf.map i.op (a.app W y) :=
  ConcreteCategory.congr_hom (a.mapPresheaf.naturality i.op) y

private theorem adjunction_homEquiv_app_top {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (k : (Scheme.Modules.pullback g).obj M ⟶ N)
    (x : Γ(M, ⊤)) :
    N.presheaf.map (eqToHom (show (⊤ : X.Opens) = g ⁻¹ᵁ ⊤ by simp)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N k).app ⊤ x) =
      k.app ⊤ (pullbackGlobalSections g M x) := by
  rw [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app]
  exact (moduleHom_app_restrict k
    (eqToHom (show (⊤ : X.Opens) = g ⁻¹ᵁ ⊤ by simp))
    (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ x)).symm

/-- **`unitHomEquivTop` is natural along a morphism out of a pullback.** The pullback of the
morphism attached to `x : Γ(M, ⊤)` followed by `k`, read through `Scheme.Modules.pullbackUnitIso`,
is the morphism attached to `k` applied to the pullback of `x`. -/
private theorem unitHomEquivTop_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (k : (Scheme.Modules.pullback g).obj M ⟶ N)
    (x : Γ(M, ⊤)) :
    (Scheme.Modules.pullbackUnitIso g).hom ≫
        Scheme.Modules.unitHomEquivTop N (k.app ⊤ (pullbackGlobalSections g M x)) =
      (Scheme.Modules.pullback g).map (Scheme.Modules.unitHomEquivTop M x) ≫ k := by
  rw [← adjunction_homEquiv_app_top g k x]
  exact Scheme.Modules.pullbackUnitIso_sections_naturality g M N k x

/-- **`hcompat` reduces to an equation of global sections.** Given `x : Γ(L.F, ⊤)` and
`x₀ : Γ(L.F₀, ⊤)` whose images under `Stacks.Algebraization.globalSectionsMap A f L` and
`AlgebraicGeometry.pullbackGlobalSections (puncturedClosedFibre A f).ι` agree, the morphisms
`Scheme.Modules.unitHomEquivTop L.F x` and `Scheme.Modules.unitHomEquivTop L.F₀ x₀` satisfy the
hypothesis `hcompat` of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`. -/
public theorem hcompat_of_eq_globalSectionsMap {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {L : CoherentTriple A f}
    (x : Γ(L.F, ⊤)) (x₀ : Γ(L.F₀, ⊤))
    (hx : globalSectionsMap A f L x =
      pullbackGlobalSections (puncturedClosedFibre A f).ι L.F₀ x₀) :
    ((Scheme.Modules.pullbackUnitIso (puncturedClosedFibreRestriction A f)).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibreRestriction A f)).map
            (Scheme.Modules.unitHomEquivTop L.F x)) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            (Scheme.Modules.unitHomEquivTop L.F₀ x₀) := by
  have h1 := unitHomEquivTop_naturality (puncturedClosedFibreRestriction A f) L.alpha.hom x
  rw [← globalSectionsMap_apply] at h1
  have h2 := unitHomEquivTop_naturality (puncturedClosedFibre A f).ι
    (𝟙 ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀)) x₀
  simp only [Scheme.Modules.Hom.id_app, CategoryTheory.id_apply, Category.comp_id] at h2
  rw [Category.assoc, ← h1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp, hx, ← h2,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Stacks.Algebraization

end
