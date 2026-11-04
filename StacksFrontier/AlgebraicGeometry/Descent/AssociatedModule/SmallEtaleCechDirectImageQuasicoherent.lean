module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImageAcyclic

/-!
# The direct image along `ε_a` of a Čech direct image is quasi-coherent on the site

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site `B` and let `V` be an object of the
small étale site of `X`.  The terms of the sheaf-level Čech complex of [Stacks, Tag 071N] are
built from `Stacks.CechSite.SheafLevel.directImage` at the iterated fibre products of a covering
family, and
`AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_sheafLevelCech` asks
of those terms **two** things:  that they be acyclic for `(ε_a)_*`, which is
`AlgebraicGeometry.SmallEtale.acyclic_pushforward_directImage`, and that their direct images along
`ε_a` be **quasi-coherent on the site**, which is what this module supplies for a single
`Stacks.CechSite.SheafLevel.directImage`.

## The route

The same identification the acyclicity uses, and nothing else.
`AlgebraicGeometry.SmallEtale.directImageIsoPushforward` turns `j_{V,*} j_V^{-1} 𝓖` into
`(ε_{p_V})_*` of the crossover of `𝓖` to the small étale site of the scheme of `V`, and
`SheafOfModules.pushforwardComp` together with
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso` identifies
`(ε_a)_* (ε_{p_V})_*` with `(ε_{p_V ∘ a})_*`.  So the module in question is isomorphic to
`(ε_{p_V ∘ a})_*` of a module quasi-coherent on the site
(`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_objRestrict`), which is quasi-coherent on the
site by `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward` as soon as `p_V ∘ a` is
affine;  quasi-coherence on a site is closed under isomorphism, being an
`CategoryTheory.ObjectProperty` closed under isomorphisms.

## One affineness hypothesis, not two

`AlgebraicGeometry.SmallEtale.acyclic_pushforward_directImage` needs **both** `p_V` and `p_V ∘ a`
affine:  the first for the acyclicity that Leray's collapse `Stacks.RightDerivedComp.objIso`
consumes, the second for the vanishing it produces.  Quasi-coherence needs **only `p_V ∘ a`**,
there being no derived functor and so no collapse in the argument.  The statements below therefore
carry one affineness instance where the acyclicity carries two, and that is deliberate rather than
an oversight.

## The hypotheses carried, all named

* `p_V ∘ a` affine over `Y`, as the instance argument `[IsAffineHom (schemeHom B (V.obj.hom ≫ a))]`
  of `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward_directImage`.
* `𝓖` quasi-coherent on the site — the tag's own hypothesis on the coefficients.
* **Nothing on `a`** in the general statement, and **nothing on `X` or `Y`**;  in the Čech
  specialization `a` is additionally **separated**, which is where
  `AlgebraicGeometry.SmallEtale.isAffineHom_toBaseHom_piObj_of_isSeparatedHom` needs it and which
  is named in that declaration.
* **No finiteness of any index set**:  the statements below are about one
  `Stacks.CechSite.SheafLevel.directImage`, i.e. one iterated fibre product, not about the product
  over `Fin (q + 1) → E.I₀` that a Čech term is.

## Main results

* `isQuasicoherentOnSite_pushforward_directImage`: **`(ε_a)_* (j_{V,*} j_V^{-1} 𝓖)` is
  quasi-coherent on the site** when `V` is affine over `Y`, for `𝓖` quasi-coherent on the site.
* `isQuasicoherentOnSite_pushforward_directImage_piObj_of_isSeparatedHom`: the same at an
  iterated fibre product of a covering family whose members are affine over `Y`, for a separated
  `a`.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The direct image along `ε_a` of a Čech direct image is quasi-coherent on the site as soon as
its object is affine over `Y`.**  For `V` an object of the small étale site of `X` whose structure
morphism to `Y` is affine, and `𝓖` an `𝒪_{X_étale}`-module quasi-coherent on the site, the module
`(ε_a)_* (j_{V,*} j_V^{-1} 𝓖)` is quasi-coherent on the site.

`AlgebraicGeometry.SmallEtale.directImageIsoPushforward` turns `j_{V,*} j_V^{-1} 𝓖` into
`(ε_{p_V})_*` of the crossover of `𝓖`, and
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso` identifies `(ε_a)_* (ε_{p_V})_*` with
`(ε_{p_V ∘ a})_*`, whose value at a module quasi-coherent on the site is quasi-coherent on the
site because `p_V ∘ a` is affine.

**Only one affineness hypothesis is taken**, on the composite `p_V ∘ a`;  unlike
`AlgebraicGeometry.SmallEtale.acyclic_pushforward_directImage`, affineness of `p_V` itself is not
needed, there being no acyclicity collapse in this argument.  **Nothing is assumed of `a`**, of
`X`, of `Y` or of any index set. -/
public theorem isQuasicoherentOnSite_pushforward_directImage
    (V : SmallEtale B X.obj X.property)
    [IsAffineHom (schemeHom B (V.obj.hom ≫ a))]
    (G : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (hG : G.IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      ((Stacks.CechSite.SheafLevel.directImage (structureSheaf B X.obj X.property) V).obj
        G)).IsQuasicoherentOnSite := by
  have hAq : ((objRestrict B X.obj X.property V).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_objRestrict B X.obj X.property V G hG
  have hcompIso : SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B V.obj.hom) ⋙
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ≅
      SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B (V.obj.hom ≫ a)) :=
    SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing B a)
        (smallEtaleStructureMapRing B V.obj.hom) ≪≫
      (smallEtalePushforwardCompIso B V.obj.hom a).symm
  have hcomp : ((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B (V.obj.hom ≫ a))).obj
        ((objRestrict B X.obj X.property V).obj G)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_pushforward B (V.obj.hom ≫ a) _ hAq
  refine (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso ?_ hcomp
  exact (hcompIso.app ((objRestrict B X.obj X.property V).obj G)).symm ≪≫
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).mapIso
      ((directImageIsoPushforward B X.obj X.property V).app G).symm

/-- **The direct images along `ε_a` of the Čech direct images of a covering family whose members
are affine over `Y` are quasi-coherent on the site, for a separated `a`.**  At an iterated fibre
product over `X` of the members of such a family — that is, at the object of `X_étale` indexing a
factor of a term of the sheaf-level Čech complex — the module
`(ε_a)_* (j_{V,*} j_V^{-1} 𝓖)` is quasi-coherent on the site, for `𝓖` quasi-coherent on the site.

The affineness hypothesis of
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward_directImage` is supplied by
`AlgebraicGeometry.SmallEtale.isAffineHom_toBaseHom_piObj_of_isSeparatedHom`.

**Separatedness of `a` is carried and is named**;  it is where that declaration needs it, and it
is not removable by this argument:  for a non-separated `a` an intersection of two affine opens of
`X` need not be affine over `Y`.  Nothing is assumed of `X`, of `Y`, or of the finiteness of
`E.I₀`. -/
public theorem isQuasicoherentOnSite_pushforward_directImage_piObj_of_isSeparatedHom
    [IsSeparated (schemeHom B a)]
    (E : PreZeroHypercover.{u} (final B X.obj X.property))
    (hE : ∀ j, IsAffineHom (toBaseHom B a (E.X j)))
    (G : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (hG : G.IsQuasicoherentOnSite) (p : ℕ) (i : Fin (p + 1) → E.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
        HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
      Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      ((Stacks.CechSite.SheafLevel.directImage (structureSheaf B X.obj X.property)
        (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left).obj G)).IsQuasicoherentOnSite := by
  let : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
      HasProduct (fun b ↦ Over.mk (E.f (j b))) := fun q j ↦
    Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
  have h2 : IsAffineHom (schemeHom B
      ((∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left.obj.hom ≫ a)) := by
    rw [schemeHom, B.inclusion.map_comp]
    exact isAffineHom_toBaseHom_piObj_of_isSeparatedHom B a E hE p i
  exact isQuasicoherentOnSite_pushforward_directImage B a _ G hG

end AlgebraicGeometry.SmallEtale

end
