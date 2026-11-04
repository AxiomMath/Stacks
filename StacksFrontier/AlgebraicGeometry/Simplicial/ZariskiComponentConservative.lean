module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModulePushforward

/-!
# The component functors on the total Zariski site are jointly conservative

For a simplicial scheme `X`, the degree-`n` component `F_n` of a sheaf of `𝒪_X`-modules on the
total Zariski site has as sections over an open `V` of `X_n` the sections of `F` over the object
`(n, V)` of the total site. Every object of the total site is of that form, so a morphism of
sheaves of modules on the total site is an isomorphism exactly when all its component morphisms
are.

This is the conservativity of the family of component functors of Stacks 09WG. It is what reduces
a statement about `F` on the total site to the family of statements about the `F_n`, and in
particular it is the step by which an isomorphism built degreewise is recognised as an
isomorphism of modules on the total site. The source does not state it as a numbered result; see
the implementation notes.

## Main results

* `Stacks.SheafOfModules.isIso_of_forall_isIso_forget_app`: a morphism of sheaves of modules
  on a site that is invertible on sections over every object is invertible.
* `AlgebraicGeometry.SimplicialScheme.isIso_iff_forall_isIso_componentModule`: **joint
  conservativity of the component functors.** A morphism of sheaves of `𝒪_X`-modules on the total
  Zariski site is an isomorphism if and only if each of its degree-`n` components is.

## Implementation notes

The generic lemma is stated for the composite of the forgetful functors to presheaves of abelian
groups, because that is the composite Mathlib provides a `ReflectsIsomorphisms` instance for;
and it is stated at that composite rather than at `SheafOfModules.Hom.app` so that the two sides
of the component identification are objects of `AddCommGrpCat`, which do not mention the ring
over which the sections are a module. The degree-`n` component of `F` has as its sections over
`V` the sections of `F` over `(n, V)` — a module over `Γ(X_n, V)` on one side and over the
sections of `𝒪_X` on the other — and the two rings, while definitionally equal, are not
syntactically so; after the forgetful functor the comparison is an identity, which is what
`componentModule_forget_app` records.

The hypothesis is stated at the composite functor rather than at the underlying morphism of
presheaves of modules, because `CategoryTheory.Functor.map_isIso` matches the image of a
morphism under a named functor, and `SheafOfModules.Hom.val` is that image only definitionally;
with the composite written out, invertibility of a component functor's image gives invertibility
on sections in one step.

**Why nothing here carries a tag.** The source does not state joint conservativity of the
component functors as a numbered result. Stacks 09WG, the lemma about the component morphisms of
topoi `g_n`, asserts continuity and cocontinuity of the component inclusion and the existence and
properties of the left adjoint `g_{n!}`; it does not assert that the `g_n^{-1}` are jointly
conservative. Conservativity is a consequence of the equivalence of Stacks 09VM between sheaves
on the total site and systems of degreewise sheaves, and is used without comment in the proofs
that reduce a statement about a module on a total site to its components — among them the proof
of Stacks 0D7M. It is therefore recorded here untagged.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Topology.Simplicial

namespace Stacks.SheafOfModules

universe u v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **A morphism of sheaves of modules invertible on sections over every object is
invertible.** The underlying presheaf of abelian groups is then invertible objectwise, hence
invertible, and the forgetful functor to presheaves of abelian groups reflects isomorphisms. -/
theorem isIso_of_forall_isIso_forget_app {F G : SheafOfModules.{u} R} (α : F ⟶ G)
    (h : ∀ A : Cᵒᵖ, IsIso (((SheafOfModules.forget.{u} R ⋙
      PresheafOfModules.toPresheaf R.obj).map α).app A)) :
    IsIso α := by
  have : IsIso ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj).map α) :=
    (NatTrans.isIso_iff_isIso_app _).2 h
  exact isIso_of_reflects_iso α
    (SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SimplicialScheme

universe u

variable {X : SimplicialObject Scheme.{u}}

/-- On sections over an open `V` of `X_n`, the degree-`n` component of a morphism of sheaves of
`𝒪_X`-modules is the morphism itself on sections over the object `(n, V)` of the total Zariski
site. -/
public theorem componentModule_forget_app (n : SimplexCategoryᵒᵖ) {F G : Modules X}
    (α : F ⟶ G) (V : Opens ((zariskiSpace X).obj n)) :
    (((SheafOfModules.forget (X.obj n).ringCatSheaf ⋙
        PresheafOfModules.toPresheaf _).map ((componentModule X n).map α)).app (op V)) =
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map α).app
        (op (⟨n, V⟩ : ZariskiOpen X)) := rfl

/-- **Joint conservativity of the component functors on the total Zariski site.** A morphism of
sheaves of `𝒪_X`-modules on the total Zariski site of a simplicial scheme is an isomorphism if
and only if its degree-`n` component is an isomorphism for every simplicial degree `n`.

Every object of the total Zariski site is an open subset of the scheme in a single simplicial
degree, and the sections of the degree-`n` component over an open of `X_n` are the sections of
the module over that object; so invertibility of all the components is invertibility on sections
over every object of the site. -/
public theorem isIso_iff_forall_isIso_componentModule {F G : Modules X} (α : F ⟶ G) :
    IsIso α ↔ ∀ n : SimplexCategoryᵒᵖ, IsIso ((componentModule X n).map α) := by
  refine ⟨fun _ n => inferInstance, fun h => ?_⟩
  refine Stacks.SheafOfModules.isIso_of_forall_isIso_forget_app α fun A => ?_
  have hn := h A.unop.degree
  have hiso : IsIso ((SheafOfModules.forget (X.obj A.unop.degree).ringCatSheaf ⋙
      PresheafOfModules.toPresheaf _).map ((componentModule X A.unop.degree).map α)) :=
    Functor.map_isIso _ ((componentModule X A.unop.degree).map α)
  have happ : IsIso ((((SheafOfModules.forget (X.obj A.unop.degree).ringCatSheaf ⋙
      PresheafOfModules.toPresheaf _).map ((componentModule X A.unop.degree).map α))).app
        (op A.unop.toOpens)) := NatIso.isIso_app_of_isIso _ _
  exact happ

/-- **The component functors on the total Zariski site are jointly conservative.** The family of
degree-`n` component functors reflects isomorphisms. -/
public theorem isIso_of_forall_isIso_componentModule {F G : Modules X} (α : F ⟶ G)
    (h : ∀ n : SimplexCategoryᵒᵖ, IsIso ((componentModule X n).map α)) : IsIso α :=
  (isIso_iff_forall_isIso_componentModule α).2 h

end AlgebraicGeometry.SimplicialScheme

end
