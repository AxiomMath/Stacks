module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback

/-!
# Local morphism data of restrictions along a refinement of the covering member

`StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict` glues a family of morphisms of
restrictions `M|_{Z i} ⟶ N|_{Z i}` along the members of a cover of a scheme `Y` by open
subschemes, and its compatibility hypothesis is an equality of the maps
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` on the sections over an open of `Y` seen by two
members. `StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback` discharges that hypothesis
for local data presented as morphisms of *inverse images*.

This file does the same for local data presented as morphisms of *restrictions*, which is the form
in which the comparison maps on the standard opens of a homogeneous spectrum arise. The content is
one lemma: pushing a morphism of restrictions along an open immersion `k` into one along the
composite does not change its action on the sections over an open of `Y`. Together with the
sheaf-theoretic rigidity of a morphism out of a quasi-coherent module on a spectrum
(`Stacks.AlgebraicGeometry.ModuleLimits.restrict_hom_ext_app_top`) this turns the glueing
hypothesis into an equality of the local comparisons on the sections over one standard open — a
statement about elements, which is where the mathematics of a comparison map lives.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleHomGlue.restrictComp` — the morphism of restrictions along
  `k ≫ g` induced by one along `g`, conjugating the restriction along `k` by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_restrictComp` — **the action on the sections
  over an open of `Y` is unchanged by passing to a refinement of the covering member.**
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_eq_of_refinement` — **the compatibility
  hypothesis of the glueing for an arbitrary pair of members of a cover, moved onto a common
  refinement.** This is `…ModuleHomGlue.localApp_ofPullback_eq_of_refinement` with the local data
  given on restrictions rather than on inverse images, so that no comparison between restriction
  and inverse image enters.

## Implementation notes

The proof of `localApp_restrictComp` is the tail of
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq` with the passage through the
inverse images removed: `…ModuleHomGlue.localApp_eq_map` writes each side as the action on the
image open flanked by the two presheaf restriction maps along an equality of opens, and
`…ModuleHomGlue.appImage_restrictFunctorComp` — which holds by `rfl` — identifies the action of
the refined morphism on an open of the refinement with the action of the original on its image.
The remaining bookkeeping is thinness of the lattice of opens,
`Stacks.Tag01XLCoefficientNat.thin_map_comp₂`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

variable {Y Z₁ Z₂ : Scheme.{u}} {M N : Y.Modules}

/-- **The morphism of restrictions along `k ≫ g` induced by one along `g`**: restrict along `k`
and conjugate by `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`. -/
public def restrictComp (g : Z₁ ⟶ Y) [IsOpenImmersion g] (k : Z₂ ⟶ Z₁) [IsOpenImmersion k]
    (χ : M.restrict g ⟶ N.restrict g) :
    M.restrict (k ≫ g) ⟶ N.restrict (k ≫ g) :=
  (Scheme.Modules.restrictFunctorComp k g).hom.app M ≫
    (Scheme.Modules.restrictFunctor k).map χ ≫
    (Scheme.Modules.restrictFunctorComp k g).inv.app N

/-- **Refining the covering member does not change the action on the sections over an open of the
base.** For open immersions `k : Z₂ ⟶ Z₁` and `g : Z₁ ⟶ Y` and a morphism `χ : M|_g ⟶ N|_g`, the
refined morphism `restrictComp g k χ` acts on the sections over an open `V` of `Y` exactly as `χ`
does, however `V` is presented as an image on either side. -/
public theorem localApp_restrictComp (g : Z₁ ⟶ Y) [IsOpenImmersion g] (k : Z₂ ⟶ Z₁)
    [IsOpenImmersion k] (χ : M.restrict g ⟶ N.restrict g)
    {W₁ : Z₁.Opens} {W₂ : Z₂.Opens} {V : Y.Opens}
    (h₁ : g ''ᵁ W₁ = V) (h₂ : (k ≫ g) ''ᵁ W₂ = V) :
    localApp g χ h₁ = localApp (k ≫ g) (restrictComp g k χ) h₂ := by
  obtain rfl : W₁ = k ''ᵁ W₂ :=
    g.image_injective (h₁.trans (h₂.symm.trans (Scheme.Hom.comp_image k g W₂)))
  rw [restrictComp, localApp_eq_map, localApp_eq_map, appImage_restrictFunctorComp]
  simp only [Category.assoc]
  rw [Stacks.Tag01XLCoefficientNat.thin_map_comp₂ N.presheaf _ _ (eqToHom h₁.symm).op]
  conv_rhs => rw [← Category.assoc]
  rw [Stacks.Tag01XLCoefficientNat.thin_map_comp₂ M.presheaf _ _ (eqToHom h₁).op]

/-- **The compatibility hypothesis of the glueing for an arbitrary pair of members of a cover,
reduced to the pair of refinements over a common refining member.** Let `g₁ : Z₁ ⟶ Y` and
`g₂ : Z₂ ⟶ Y` be open immersions and let `k₁ : Z ⟶ Z₁`, `k₂ : Z ⟶ Z₂` be open immersions. If the
refinements of `χ₁` and `χ₂` to `Z` have the same action on the sections over every open of `Y`
seen by `Z` through either composite, then `χ₁` and `χ₂` have the same action on the sections over
every open of `Y` seen by both `Z₁` and `Z₂` and by `Z`.

This is the hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for an arbitrary pair
of members, moved onto the refinement — where, the refining member being one scheme and the
sections over its whole image being a single module, rigidity of a morphism out of a
quasi-coherent module applies. The companion
`Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` covers the case of an open of `Y`
*not* seen by the refining member, by covering it with such opens. -/
public theorem localApp_eq_of_refinement {Z : Scheme.{u}}
    (g₁ : Z₁ ⟶ Y) [IsOpenImmersion g₁] (g₂ : Z₂ ⟶ Y) [IsOpenImmersion g₂]
    (k₁ : Z ⟶ Z₁) [IsOpenImmersion k₁] (k₂ : Z ⟶ Z₂) [IsOpenImmersion k₂]
    (χ₁ : M.restrict g₁ ⟶ N.restrict g₁) (χ₂ : M.restrict g₂ ⟶ N.restrict g₂)
    (hχ : ∀ (W' : Z.Opens) (V' : Y.Opens) (e₁ : (k₁ ≫ g₁) ''ᵁ W' = V')
      (e₂ : (k₂ ≫ g₂) ''ᵁ W' = V'),
        localApp (k₁ ≫ g₁) (restrictComp g₁ k₁ χ₁) e₁
          = localApp (k₂ ≫ g₂) (restrictComp g₂ k₂ χ₂) e₂)
    {W₁ : Z₁.Opens} {W₂ : Z₂.Opens} {W : Z.Opens} {V : Y.Opens}
    (h₁ : g₁ ''ᵁ W₁ = V) (h₂ : g₂ ''ᵁ W₂ = V)
    (h : (k₁ ≫ g₁) ''ᵁ W = V) (h' : (k₂ ≫ g₂) ''ᵁ W = V) :
    localApp g₁ χ₁ h₁ = localApp g₂ χ₂ h₂ := by
  rw [localApp_restrictComp g₁ k₁ χ₁ h₁ h, localApp_restrictComp g₂ k₂ χ₂ h₂ h']
  exact hχ W V h h'

end Stacks.AlgebraicGeometry.ModuleHomGlue

end
