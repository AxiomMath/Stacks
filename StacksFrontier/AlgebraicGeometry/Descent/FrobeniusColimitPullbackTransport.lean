module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictPullback
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitSquarePaste

/-!
# Transporting local data along a morphism that factors through an open subscheme

The trivialising-cover step of [Stacks, Tag 0EXD] covers `Spec A` by basic opens `D(g)`, because
over a basic open — and over no other open — the almost blowup square of
[Stacks, Example 0EVH] is again a two-generator square, namely the one over the localisation
`A_g`. The corner of that square is `Spec (A_g)` itself, not the open subscheme `D(g)`, and the
two are identified by `AlgebraicGeometry.basicOpenIsoSpecAway`. So the local data the argument
produces lives over `Spec (A_g)`, while the trivialisations and the gluing of morphisms both
live over `D(g)`.

This file crosses between them, for an arbitrary morphism `j : Y ⟶ X` factored as `θ ≫ V.ι`
through an open `V` of `X`. Nothing here is special to `Spec`: the factorisation is a hypothesis,
and that is what keeps the opens out of the statements — the identification of `Y` with `V` is
carried by the single morphism `θ`, exactly as ladder rungs 1 and 3 prescribe.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitPullbackEquivOfIso`: **the transition functor of
  [Stacks, Tag 0EXE] along an isomorphism of schemes is an equivalence**, with
  `AlgebraicGeometry.isEquivalence_frobeniusColimitPullback_of_isIso` as the instance form. This
  is what lets a statement proved over `D(g)` be read over `Spec (A_g)` and back.
* `AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfFactor`: **a module trivialised over `V` is
  carried to a free module by the transition functor of any morphism factoring through `V`**, and
  `AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfOpenImmersion`, its instance at an open
  immersion factored through its own image.

## Main results

* `AlgebraicGeometry.frobeniusColimitPullback_map_injective`: **two morphisms of
  `colim_F 𝒪_X`-modules agreeing after the transition functors of the members of an open cover of
  `X` are equal.** This is the separatedness half of the trivialising-cover argument, in the
  transition-functor spelling that the square comparison and the free case of full faithfulness
  speak.
* `AlgebraicGeometry.frobeniusColimitPullback_map_injective_of_factor` and
  `…_of_openImmersion`: the same for a family of morphisms factoring through a cover, which is
  the form the cover by the spectra of the localisations `A_g` presents.

## Implementation notes

That the transition functor along an isomorphism is an equivalence is **not** in the tree, and is
built here from the pseudofunctoriality that is:
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso` composes the two transitions and absorbs
the equation `e.inv ≫ e.hom = 𝟙` into the comparison, and
`AlgebraicGeometry.frobeniusColimitPullbackId` identifies the transition of an identity with the
identity functor. No new mathematics enters: this is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackEquivOfIso` for the Frobenius-colimit structure sheaf.

Freeness crosses without the equivalence, because the pullback of a free sheaf of modules is free
for *any* morphism of sheaves of rings — Mathlib's
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`. The equivalence is needed only for
separatedness, where a map on Hom-sets has to be *reflected*.

Separatedness itself is `Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`, which
is stated for the slice restriction `M.over U`; the passage to the transition functor is
`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`, used by conjugation rather than by
rewriting, and the last step strips
`AlgebraicGeometry.frobeniusColimitModuleOpenEquiv`, which is faithful because it is an
equivalence.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-! ### The transition functor along an isomorphism -/

/-- **Two transition functors whose morphisms compose to the identity compose to the identity
functor.**

This is `AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`, which absorbs the equation
`g ≫ f = 𝟙 Y` into the comparison, followed by
`AlgebraicGeometry.frobeniusColimitPullbackId`. -/
noncomputable def frobeniusColimitPullbackCompIsoId {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (h : g ≫ f = 𝟙 Y) :
    _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hX hY) ⋙
        _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p g hY hX) ≅
      𝟭 (_root_.SheafOfModules.{u} (frobeniusColimitRingSheaf Y p hY)) :=
  frobeniusColimitPullbackTriangleIso p g f (𝟙 Y) hY hX hY h ≪≫ frobeniusColimitPullbackId Y p hY

/-- **The transition functor of [Stacks, Tag 0EXE] along an isomorphism of schemes is an
equivalence**, with the transition of the inverse as its quasi-inverse.

This is the Frobenius-colimit analogue of `AlgebraicGeometry.Scheme.Modules.pullbackEquivOfIso`,
and it is what lets the two-generator square over a localisation `A_g` be compared with the
restriction of the square over `A` to the basic open `D(g)`: the two corners are isomorphic
schemes, not equal ones. -/
noncomputable def frobeniusColimitPullbackEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf Y p hY) ≌
      _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX) :=
  CategoryTheory.Equivalence.mk
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p e.hom hX hY))
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p e.inv hY hX))
    (frobeniusColimitPullbackCompIsoId p e.hom e.inv hX hY e.inv_hom_id).symm
    (frobeniusColimitPullbackCompIsoId p e.inv e.hom hY hX e.hom_inv_id)

/-- **The transition functor along an isomorphism of schemes is an equivalence**, as an
instance. -/
instance isEquivalence_frobeniusColimitPullback_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) :
    (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p f hX hY)).IsEquivalence :=
  inferInstanceAs (frobeniusColimitPullbackEquivOfIso p (asIso f) hX hY).functor.IsEquivalence

/-! ### Freeness along a morphism factoring through an open -/

/-- **A module trivialised over an open `V` of `X` is carried to a free module by the transition
functor of any morphism `j : Y ⟶ X` that factors through `V`.**

Only the factorisation `θ ≫ V.ι = j` is assumed: `θ` need not be an isomorphism and `j` need not
be an open immersion. The proof is
`AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfIso` over `V` followed by Mathlib's
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`, which says that the transition of a free
module is free — so no equivalence and no inverse functor are needed here. -/
noncomputable def frobeniusColimitPullbackObjFreeOfFactor (X : Scheme.{u})
    (hX : IsInCharacteristic X p) (V : X.Opens) (hV : IsInCharacteristic V.toScheme p)
    {Y : Scheme.{u}} (j : Y ⟶ X) (hY : IsInCharacteristic Y p)
    (θ : Y ⟶ V.toScheme) (hθ : θ ≫ V.ι = j)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) (I : Type u)
    (e : M.over V ≅ _root_.SheafOfModules.free I) :
    (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p j hY hX)).obj M ≅
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) I :=
  ((frobeniusColimitPullbackTriangleIso p θ V.ι j hY hV hX hθ).app M).symm ≪≫
    (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p θ hY hV)).mapIso
      (frobeniusColimitPullbackObjFreeOfIso X p hX V hV M I e) ≪≫
    _root_.SheafOfModules.pullbackObjFreeIso (frobeniusColimitStructureSheafHom p θ hY hV) I

/-- **A module trivialised over the image of an open immersion `j` is carried to a free module by
the transition functor of `j`.**

This is `AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfFactor` at the canonical
factorisation of an open immersion through its own image,
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`. -/
noncomputable def frobeniusColimitPullbackObjFreeOfOpenImmersion (X : Scheme.{u})
    (hX : IsInCharacteristic X p) {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (hY : IsInCharacteristic Y p)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) (I : Type u)
    (e : M.over j.opensRange ≅ _root_.SheafOfModules.free I) :
    (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p j hY hX)).obj M ≅
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf Y p hY) I :=
  frobeniusColimitPullbackObjFreeOfFactor p X hX j.opensRange
    (isInCharacteristic_toScheme hX _) j hY
    (IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by simp)).hom
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) M I e

/-! ### Separatedness in the transition-functor spelling -/

/-- Two morphisms with equal image under `G` have equal image under any `F ≅ G`. -/
private theorem map_eq_of_iso_hom_app {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ≅ G) {M N : C} (f₁ f₂ : M ⟶ N) (h : G.map f₁ = G.map f₂) : F.map f₁ = F.map f₂ := by
  rw [← cancel_mono (α.hom.app N), α.hom.naturality f₁, α.hom.naturality f₂, h]

/-- **Two morphisms of `colim_F 𝒪_X`-modules agreeing after the transition functors of the
members of an open cover of `X` are equal.**

This is the separatedness half of the trivialising-cover argument for [Stacks, Tag 0EXD]. The
content is `Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective`, which is stated
for the slice restriction `M.over (V i)`; what this adds is the passage to the transition functor
of [Stacks, Tag 0EXE], which is the functor the square comparison and the free case of full
faithfulness are stated for.

The passage is by conjugation with
`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback` — its naturality at the two
morphisms, then cancellation of the isomorphism — followed by faithfulness of
`AlgebraicGeometry.frobeniusColimitModuleOpenEquiv`. No rewriting under a functor occurs, which
is why no motive has to be built. -/
theorem frobeniusColimitPullback_map_injective (X : Scheme.{u})
    (hX : IsInCharacteristic X p) {ι : Type*} (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)} (f₁ f₂ : M ⟶ N)
    (h : ∀ i, (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (V i).ι
        (isInCharacteristic_toScheme hX (V i)) hX)).map f₁ =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (V i).ι
        (isInCharacteristic_toScheme hX (V i)) hX)).map f₂) :
    f₁ = f₂ := by
  refine Stacks.SheafOfModules.SliceRestriction.overFunctor_map_injective
    ((Opens.coversTop_iff _ V).mpr hV) f₁ f₂ fun i => ?_
  exact (frobeniusColimitModuleOpenEquiv X p hX (V i)
    (isInCharacteristic_toScheme hX (V i))).functor.map_injective
    (map_eq_of_iso_hom_app (frobeniusColimitModuleRestrictIsoPullback X p hX (V i)
      (isInCharacteristic_toScheme hX (V i))) f₁ f₂ (h i))

/-- **Two morphisms of `colim_F 𝒪_X`-modules agreeing after the transition functors of a family
of morphisms that factor isomorphically through an open cover of `X` are equal.**

The family the trivialising-cover argument for [Stacks, Tag 0EXD] actually presents is
`Spec (A_g) ⟶ Spec A`, whose source is not the open subscheme `D(g)` but a scheme isomorphic to
it. Reflecting an equation across that isomorphism is where
`AlgebraicGeometry.isEquivalence_frobeniusColimitPullback_of_isIso` is needed: the transition of
`θ i` is faithful because it is an equivalence. -/
theorem frobeniusColimitPullback_map_injective_of_factor (X : Scheme.{u})
    (hX : IsInCharacteristic X p) {ι : Type*} (V : ι → X.Opens) (hV : ⨆ i, V i = ⊤)
    {Y : ι → Scheme.{u}} (j : ∀ i, Y i ⟶ X) (hY : ∀ i, IsInCharacteristic (Y i) p)
    (θ : ∀ i, Y i ⟶ (V i).toScheme) [∀ i, IsIso (θ i)]
    (hθ : ∀ i, θ i ≫ (V i).ι = j i)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)} (f₁ f₂ : M ⟶ N)
    (h : ∀ i, (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p (j i) (hY i) hX)).map f₁ =
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p (j i) (hY i) hX)).map f₂) :
    f₁ = f₂ := by
  refine frobeniusColimitPullback_map_injective p X hX V hV f₁ f₂ fun i => ?_
  have hτ := frobeniusColimitPullbackTriangleIso p (θ i) (V i).ι (j i) (hY i)
    (isInCharacteristic_toScheme hX (V i)) hX (hθ i)
  refine (_root_.SheafOfModules.pullback.{u}
    (frobeniusColimitStructureSheafHom p (θ i) (hY i)
      (isInCharacteristic_toScheme hX (V i)))).map_injective ?_
  exact map_eq_of_iso_hom_app hτ f₁ f₂ (h i)

/-- **Two morphisms of `colim_F 𝒪_X`-modules agreeing after the transition functors of a family
of open immersions whose images cover `X` are equal.**

This is `AlgebraicGeometry.frobeniusColimitPullback_map_injective_of_factor` at the canonical
factorisation of each open immersion through its own image, and it is the form in which the
cover of `Spec A` by the spectra of the localisations `A_g` is given. -/
theorem frobeniusColimitPullback_map_injective_of_openImmersion (X : Scheme.{u})
    (hX : IsInCharacteristic X p) {ι : Type*} {Y : ι → Scheme.{u}} (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hY : ∀ i, IsInCharacteristic (Y i) p)
    (hcov : ⨆ i, (j i).opensRange = ⊤)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)} (f₁ f₂ : M ⟶ N)
    (h : ∀ i, (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p (j i) (hY i) hX)).map f₁ =
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p (j i) (hY i) hX)).map f₂) :
    f₁ = f₂ :=
  frobeniusColimitPullback_map_injective_of_factor p X hX (fun i => (j i).opensRange) hcov j hY
    (fun i => (IsOpenImmersion.isoOfRangeEq (j i) (j i).opensRange.ι (by simp)).hom)
    (fun i => IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _) f₁ f₂ h

end AlgebraicGeometry

end
