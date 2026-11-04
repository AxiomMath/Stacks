module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Natural isomorphisms of functors of modules from natural additive equivalences

Let `F G : ModuleCat A ⥤ ModuleCat A` be two functors on which `r : A` acts on `F(M)`, `G(M)` as
`F(r • 𝟙_M)`, `G(r • 𝟙_M)`. A family of additive equivalences `F(M) ≃+ G(M)` natural in `M` is then
`A`-linear, by naturality at `r • 𝟙_M`, and so it is a natural isomorphism `F ≅ G`.

## Main definitions

* `Deformation.Artin.natIsoOfNaturalAddEquiv`: the natural isomorphism.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Deformation.Artin

variable {A : Type u} [CommRing A] {F G : ModuleCat.{u} A ⥤ ModuleCat.{u} A}

/-- **A natural family of additive equivalences is a natural isomorphism.** If `r : A` acts on
the values of `F` and `G` through `F(r • 𝟙)` and `G(r • 𝟙)`, then additive equivalences
`ε_M : F(M) ≃+ G(M)` natural in `M` are `A`-linear, and form a natural isomorphism `F ≅ G`. -/
def natIsoOfNaturalAddEquiv (ε : ∀ M : ModuleCat.{u} A, F.obj M ≃+ G.obj M)
    (hnat : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (y : F.obj M),
      ε N (F.map g y) = G.map g (ε M y))
    (hF : ∀ (M : ModuleCat.{u} A) (r : A) (y : F.obj M), F.map (r • 𝟙 M) y = r • y)
    (hG : ∀ (M : ModuleCat.{u} A) (r : A) (y : G.obj M), G.map (r • 𝟙 M) y = r • y) :
    F ≅ G :=
  NatIso.ofComponents
    (fun M => LinearEquiv.toModuleIso ((ε M).toLinearEquiv fun r y => by
      rw [← hF M r y, hnat, hG]))
    (fun g => by
      ext y
      exact hnat g y)

/-- The component of `natIsoOfNaturalAddEquiv ε hnat hF hG` at `M` sends `y : F(M)` to
`ε M y`. -/
theorem natIsoOfNaturalAddEquiv_hom_app_apply (ε : ∀ M : ModuleCat.{u} A, F.obj M ≃+ G.obj M)
    (hnat : ∀ {M N : ModuleCat.{u} A} (g : M ⟶ N) (y : F.obj M),
      ε N (F.map g y) = G.map g (ε M y))
    (hF : ∀ (M : ModuleCat.{u} A) (r : A) (y : F.obj M), F.map (r • 𝟙 M) y = r • y)
    (hG : ∀ (M : ModuleCat.{u} A) (r : A) (y : G.obj M), G.map (r • 𝟙 M) y = r • y)
    (M : ModuleCat.{u} A) (y : F.obj M) :
    (natIsoOfNaturalAddEquiv ε hnat hF hG).hom.app M y = ε M y :=
  rfl

end Deformation.Artin

end
