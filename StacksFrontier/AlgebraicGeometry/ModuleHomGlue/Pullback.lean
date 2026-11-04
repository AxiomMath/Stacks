module

public import StacksFrontier.AlgebraicGeometry.CoefficientNat.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Restrict

/-!
# Local morphism data presented as morphisms of inverse images

`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/Restrict.lean` glues a family of morphisms of
*restrictions* `M|_{Z i} ⟶ N|_{Z i}` along the members of a cover of `Y` by open subschemes. A
construction that pulls sheaves of modules back, however, produces its local morphisms as
morphisms of *inverse images* `g^* M ⟶ g^* N`. Along an open immersion the two functors are
identified by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and this file carries
the local data across that identification.

Everything here is at the level of arbitrary schemes and arbitrary sheaves of modules: `Y` is any
scheme, the morphisms are arbitrary open immersions, and `M` and `N` are arbitrary sheaves of
`𝒪_Y`-modules.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback`: the morphism of restrictions corresponding
  to a morphism of inverse images, namely the conjugate by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback_pullback_map` and
  `Stacks.AlgebraicGeometry.ModuleHomGlue.pullback_map_eq_of_restrictFunctor_map_eq`: the two
  round trips at a *global* morphism `θ : M ⟶ N`. The restriction of `θ` is the `ofPullback` of
  its inverse image, and conversely a morphism of inverse images whose `ofPullback` is the
  restriction of `θ` is the inverse image of `θ` — the conversion is a bijection, so recognising a
  morphism of inverse images as coming from a global one is the same problem on either side.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback_pullbackComp`: **the conversion is
  compatible with composition.** A morphism of inverse images along `g` whose inverse image along
  `k` is transported to `k ≫ g` by `AlgebraicGeometry.Scheme.Modules.pullbackComp` becomes, on
  restrictions, the restriction along `k` of `ofPullback g φ`, conjugated by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`. No comparison between restriction and
  inverse image appears in that statement; it is an identity of morphisms of restrictions.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq`: the two morphisms of
  restrictions then have the *same* action on the sections over an open of `Y` seen by both
  covering schemes. This is the compatibility hypothesis of
  `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for a pair of
  members of the cover one of which factors through the other.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq_of_refinement`: **that
  hypothesis for an arbitrary pair of members, reduced to an equation of morphisms of sheaves of
  modules over a common refinement.** A pair of members both seeing the open `V` is refined by
  `V` itself, so the previous statement applied to each member in turn replaces the equation of
  maps on sections by an equation of morphisms of inverse images — which is the form in which a
  construction that produces its local data by pulling sheaves of modules back has them.

## Implementation notes

The mathematical input is the pseudofunctoriality of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` —
`Stacks.Tag01XLCoefficientNat.restrictFunctorIsoPullback_comp`, which carries
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` to
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. It is used only through the two
cancellations `restrictFunctorComp_hom_comp_isoPullback` and
`isoPullback_inv_comp_restrictFunctorComp_inv`, which solve that identity for the comparison at
the composite; with those in hand `ofPullback_pullbackComp` is a composite of five morphisms
rewritten at both ends.

Descending to sections is then bookkeeping about equal opens. The sections of a restriction over
`W` *are* the sections over the image `f ''ᵁ W`, so `localApp_eq_map` writes `localApp` as the
action on the image open flanked by the two restriction maps along the equality of opens, and
`appImage_restrictFunctorComp` is `rfl`: the components of `restrictFunctorComp` are presheaf
restriction maps, and the identification of the sections of a restriction with the sections over
the image is `Iso.refl`. That lemma has to be *stated* with the opens written out, because the
composite assembled by rewriting has its intermediate objects in two spellings of one open and
then `CategoryTheory.Category.assoc` no longer rewrites it. The last step is thinness of the
lattice of opens, `Stacks.Tag01XLCoefficientNat.thin_map_comp₂`: the two restriction maps on
either side of the action compose to the single one on the other side.

No `stacks` attribute is attached: the file states no clause of a tag, it converts between two
presentations of local morphism data.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

universe u

/-- The morphism of restrictions corresponding to a morphism of inverse images. -/
public def ofPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    M.restrict f ⟶ N.restrict f :=
  (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫ φ ≫
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app N

/-- `ofPullback` takes the inverse image of a global morphism to its restriction. -/
public theorem ofPullback_pullback_map {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (θ : M ⟶ N) :
    ofPullback f ((Scheme.Modules.pullback f).map θ) =
      (Scheme.Modules.restrictFunctor f).map θ := by
  simp only [ofPullback]
  rw [← Category.assoc,
    ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality θ, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- A morphism of inverse images whose `ofPullback` is the restriction of a global morphism is the
inverse image of that morphism. -/
public theorem pullback_map_eq_of_restrictFunctor_map_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {M N : Y.Modules} (θ : M ⟶ N)
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (h : (Scheme.Modules.restrictFunctor f).map θ = ofPullback f φ) :
    (Scheme.Modules.pullback f).map θ = φ := by
  have h' : ofPullback f ((Scheme.Modules.pullback f).map θ) = ofPullback f φ :=
    (ofPullback_pullback_map f θ).trans h
  simp only [ofPullback] at h'
  exact (cancel_mono _).mp ((cancel_epi _).mp h')

section Comp

variable {Y Z₁ Z₂ : Scheme.{u}} (g : Z₁ ⟶ Y) [IsOpenImmersion g] (k : Z₂ ⟶ Z₁)
  [IsOpenImmersion k]

/-- One half of the pseudofunctoriality of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, solved for the comparison at the
composite: travelling from the restriction along `k ≫ g` to the inverse image along `k` of the
inverse image along `g` is the comparison for `k ≫ g` followed by the inverse of
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
@[reassoc]
public theorem restrictFunctorComp_hom_comp_isoPullback (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorComp k g).hom.app M ≫
        (Scheme.Modules.restrictFunctor k).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).hom.app
          ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.restrictFunctorIsoPullback (k ≫ g)).hom.app M ≫
        (Scheme.Modules.pullbackComp k g).inv.app M := by
  have pf := (Category.assoc _ _ _).symm.trans
    (Stacks.Tag01XLCoefficientNat.restrictFunctorIsoPullback_comp k g M)
  rw [← cancel_mono ((Scheme.Modules.pullbackComp k g).hom.app M)]
  simp only [Category.assoc, pf, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The other half of the pseudofunctoriality of
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`: the same identity read backwards,
from the inverse image along `k` of the inverse image along `g` to the restriction along
`k ≫ g`. -/
public theorem isoPullback_inv_comp_restrictFunctorComp_inv (N : Y.Modules) :
    (Scheme.Modules.restrictFunctorIsoPullback k).inv.app
          ((Scheme.Modules.pullback g).obj N) ≫
        (Scheme.Modules.restrictFunctor k).map
          ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app N) ≫
        (Scheme.Modules.restrictFunctorComp k g).inv.app N =
      (Scheme.Modules.pullbackComp k g).hom.app N ≫
        (Scheme.Modules.restrictFunctorIsoPullback (k ≫ g)).inv.app N := by
  have h := (IsIso.inv_eq_inv (f := _ ≫ _ ≫ _)).mpr (restrictFunctorComp_hom_comp_isoPullback g k N)
  simpa [IsIso.inv_comp, ← Functor.map_inv] using h

/-- **A morphism of inverse images along a composite is the restriction of the corresponding
morphism of inverse images along the second factor.** Transporting `φ` along the comparison
`AlgebraicGeometry.Scheme.Modules.pullbackComp` produces, on restrictions, the restriction of
`ofPullback g φ` along `k`, conjugated by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`. No comparison between restriction and
inverse image survives in the conclusion: it is an identity between restrictions only. -/
public theorem ofPullback_pullbackComp {M N : Y.Modules}
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)
    (φ' : (Scheme.Modules.pullback (k ≫ g)).obj M ⟶ (Scheme.Modules.pullback (k ≫ g)).obj N)
    (hφ : (Scheme.Modules.pullbackComp k g).inv.app M ≫
            (Scheme.Modules.pullback k).map φ ≫
            (Scheme.Modules.pullbackComp k g).hom.app N = φ') :
    ofPullback (k ≫ g) φ' =
      (Scheme.Modules.restrictFunctorComp k g).hom.app M ≫
        (Scheme.Modules.restrictFunctor k).map (ofPullback g φ) ≫
        (Scheme.Modules.restrictFunctorComp k g).inv.app N := by
  subst hφ
  simp only [ofPullback, Functor.map_comp, Category.assoc]
  rw [← ofPullback_pullback_map k φ]
  simp only [ofPullback, Category.assoc]
  rw [restrictFunctorComp_hom_comp_isoPullback_assoc,
    isoPullback_inv_comp_restrictFunctorComp_inv]

end Comp

section LocalApp

/-- The congruence isomorphism of the inverse image along a reflexive equality is the identity.

Stated at `rfl` rather than at a hypothesis `f = f`: by proof irrelevance the two are
definitionally equal, so nothing is lost, and `rw`/`simp` still match an arbitrary proof. -/
public theorem pullbackCongr_rfl {X Y : Scheme.{u}} {f : X ⟶ Y} :
    Scheme.Modules.pullbackCongr (rfl : f = f) = Iso.refl (Scheme.Modules.pullback f) :=
  eqToIso_refl _

/-- `localApp` as a composite of restriction maps: the action on the sections over the image open,
with the two sides put over `V` by the restriction maps of `M` and `N` along the equality of
opens. -/
public theorem localApp_eq_map {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (ψ : M.restrict f ⟶ N.restrict f) {W : X.Opens} {V : Y.Opens}
    (hWV : f ''ᵁ W = V) :
    localApp f ψ hWV =
      M.presheaf.map (eqToHom hWV).op ≫ appImage f ψ W ≫
        N.presheaf.map (eqToHom hWV.symm).op := by
  subst hWV
  rw [localApp_image]
  simp

/-- The action on sections of a morphism of restrictions along `k ≫ g` obtained from one along `g`
by conjugating with `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`: it is the action of the
original morphism on the sections over the image of `k ''ᵁ W`, read through the equality
`(k ≫ g) ''ᵁ W = g ''ᵁ k ''ᵁ W` of opens of the target. -/
public theorem appImage_restrictFunctorComp {Y Z₁ Z₂ : Scheme.{u}} (g : Z₁ ⟶ Y)
    [IsOpenImmersion g] (k : Z₂ ⟶ Z₁) [IsOpenImmersion k] {M N : Y.Modules}
    (ψ : M.restrict g ⟶ N.restrict g) (W : Z₂.Opens) :
    appImage (k ≫ g) ((Scheme.Modules.restrictFunctorComp k g).hom.app M ≫
        (Scheme.Modules.restrictFunctor k).map ψ ≫
        (Scheme.Modules.restrictFunctorComp k g).inv.app N) W =
      M.presheaf.map (eqToHom (Scheme.Hom.comp_image k g W).symm).op ≫
        appImage g ψ (k ''ᵁ W) ≫
        N.presheaf.map (eqToHom (Scheme.Hom.comp_image k g W)).op :=
  rfl

/-- **Local morphism data given on inverse images is compatible along a refinement.** Let
`g : Z₁ ⟶ Y` and `g' : Z₂ ⟶ Y` be open immersions with `g' = k ≫ g` for an open immersion
`k : Z₂ ⟶ Z₁`, and let `φ` and `φ'` be morphisms of the inverse images of `M` and `N` along `g`
and along `g'`. If `φ'` is the inverse image of `φ` along `k`, read through the comparisons
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, then the two induced morphisms of restrictions
act in the same way on the sections over an open `V` of `Y`, however `V` is presented as an image
on either side.

This is the hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for the pair of
members of a cover one of which factors through the other. -/
public theorem localApp_ofPullback_eq {Y Z₁ Z₂ : Scheme.{u}}
    (g : Z₁ ⟶ Y) [IsOpenImmersion g] (k : Z₂ ⟶ Z₁) [IsOpenImmersion k]
    {g' : Z₂ ⟶ Y} [IsOpenImmersion g'] (hk : k ≫ g = g')
    {M N : Y.Modules}
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)
    (φ' : (Scheme.Modules.pullback g').obj M ⟶ (Scheme.Modules.pullback g').obj N)
    (hφ : (Scheme.Modules.pullbackCongr hk).inv.app M ≫
            (Scheme.Modules.pullbackComp k g).inv.app M ≫
            (Scheme.Modules.pullback k).map φ ≫
            (Scheme.Modules.pullbackComp k g).hom.app N ≫
            (Scheme.Modules.pullbackCongr hk).hom.app N = φ')
    {W₁ : Z₁.Opens} {W₂ : Z₂.Opens} {V : Y.Opens}
    (h₁ : g ''ᵁ W₁ = V) (h₂ : g' ''ᵁ W₂ = V) :
    localApp g (ofPullback g φ) h₁ = localApp g' (ofPullback g' φ') h₂ := by
  subst hk
  rw [pullbackCongr_rfl] at hφ
  simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.id_comp,
    Category.comp_id] at hφ
  have hres := ofPullback_pullbackComp g k φ φ' hφ
  obtain rfl : W₁ = k ''ᵁ W₂ :=
    g.image_injective (h₁.trans (h₂.symm.trans (Scheme.Hom.comp_image k g W₂)))
  rw [hres, localApp_eq_map, localApp_eq_map, appImage_restrictFunctorComp]
  simp only [Category.assoc]
  rw [Stacks.Tag01XLCoefficientNat.thin_map_comp₂ N.presheaf _ _ (eqToHom h₁.symm).op]
  conv_rhs => rw [← Category.assoc]
  rw [Stacks.Tag01XLCoefficientNat.thin_map_comp₂ M.presheaf _ _ (eqToHom h₁).op]

/-- **Local morphism data given on inverse images is compatible along an arbitrary pair of
members of a cover, as soon as it agrees over a common refinement.** Let `g₁ : Z₁ ⟶ Y` and
`g₂ : Z₂ ⟶ Y` be open immersions, both factoring a third open immersion `g : Z ⟶ Y`, and let
`φ₁`, `φ₂` be morphisms of the inverse images of `M` and `N` along `g₁` and `g₂`. If the inverse
images of `φ₁` and `φ₂` along the two factorisations are the *same* morphism `φ` of the inverse
images along `g`, then the two induced morphisms of restrictions act in the same way on the
sections over an open `V` of `Y`, however `V` is presented as an image on either side.

This is the compatibility hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for an **arbitrary**
pair of members of a cover, reduced to an equation of *morphisms of sheaves of modules* over a
common refinement. `...ModuleHomGlue.localApp_ofPullback_eq` is the special case where one member
is itself that refinement, and this is that statement applied to each member in turn: a pair of
members both seeing the open `V` is refined by `V` itself, over which the two local data are then
compared as morphisms rather than on sections. -/
public theorem localApp_ofPullback_eq_of_refinement {Y Z Z₁ Z₂ : Scheme.{u}}
    (g₁ : Z₁ ⟶ Y) [IsOpenImmersion g₁] (g₂ : Z₂ ⟶ Y) [IsOpenImmersion g₂]
    {g : Z ⟶ Y} [IsOpenImmersion g]
    (k₁ : Z ⟶ Z₁) [IsOpenImmersion k₁] (hk₁ : k₁ ≫ g₁ = g)
    (k₂ : Z ⟶ Z₂) [IsOpenImmersion k₂] (hk₂ : k₂ ≫ g₂ = g)
    {M N : Y.Modules}
    (φ₁ : (Scheme.Modules.pullback g₁).obj M ⟶ (Scheme.Modules.pullback g₁).obj N)
    (φ₂ : (Scheme.Modules.pullback g₂).obj M ⟶ (Scheme.Modules.pullback g₂).obj N)
    (φ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N)
    (hφ₁ : (Scheme.Modules.pullbackCongr hk₁).inv.app M ≫
            (Scheme.Modules.pullbackComp k₁ g₁).inv.app M ≫
            (Scheme.Modules.pullback k₁).map φ₁ ≫
            (Scheme.Modules.pullbackComp k₁ g₁).hom.app N ≫
            (Scheme.Modules.pullbackCongr hk₁).hom.app N = φ)
    (hφ₂ : (Scheme.Modules.pullbackCongr hk₂).inv.app M ≫
            (Scheme.Modules.pullbackComp k₂ g₂).inv.app M ≫
            (Scheme.Modules.pullback k₂).map φ₂ ≫
            (Scheme.Modules.pullbackComp k₂ g₂).hom.app N ≫
            (Scheme.Modules.pullbackCongr hk₂).hom.app N = φ)
    {W₁ : Z₁.Opens} {W₂ : Z₂.Opens} {W : Z.Opens} {V : Y.Opens}
    (h₁ : g₁ ''ᵁ W₁ = V) (h₂ : g₂ ''ᵁ W₂ = V) (h : g ''ᵁ W = V) :
    localApp g₁ (ofPullback g₁ φ₁) h₁ = localApp g₂ (ofPullback g₂ φ₂) h₂ :=
  (localApp_ofPullback_eq g₁ k₁ hk₁ φ₁ φ hφ₁ h₁ h).trans
    (localApp_ofPullback_eq g₂ k₂ hk₂ φ₂ φ hφ₂ h₂ h).symm

end LocalApp

end Stacks.AlgebraicGeometry.ModuleHomGlue

end
