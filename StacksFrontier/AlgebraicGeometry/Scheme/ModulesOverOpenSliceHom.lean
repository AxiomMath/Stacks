module

public import StacksFrontier.AlgebraicGeometry.Scheme.ModulesOverOpenSlice

/-!
# Building a morphism over the slice at an open from a family of maps on sections

For a scheme `T`, an open `W` of `T` and two `AlgebraicGeometry.Scheme.Modules` `G` and `F` on
`T`, a morphism `G|_W ⟶ F|_W` of the restrictions to the slice of the small Zariski site at `W`
is determined by its values on sections: two such morphisms agreeing on the sections over every
open contained in `W` are equal, which is
`Stacks.AlgebraicGeometry.IdealPowerColimit.over_hom_ext`.

This file supplies the *existence* half.  A family of `Γ(T, V)`-linear maps
`Γ(G, V) → Γ(F, V)`, one for every open `V ≤ W`, commuting with restriction to a smaller open,
assembles into a morphism `G|_W ⟶ F|_W` whose value on sections is the given family.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.overHomOfSections`: **a compatible family of linear maps on
  the sections over the opens contained in `W` is a morphism `G|_W ⟶ F|_W`.**

## Main results

* `AlgebraicGeometry.Scheme.Modules.overHomOfSections_val_app_apply`: its component at an object
  of the slice site is the given linear map, by `rfl`.
* `AlgebraicGeometry.Scheme.Modules.overHomOfSections_apply`: **its value on the sections over an
  open `V ≤ W` is the given map**, which together with
  `Stacks.AlgebraicGeometry.IdealPowerColimit.over_hom_ext` pins it down uniquely.
* `AlgebraicGeometry.Scheme.Modules.exists_over_hom_of_sections`: the existence statement in the
  shape a consumer wants — a compatible family of maps on sections is realized by a morphism of
  the restrictions to the slice.

## Implementation notes

**An object of the slice site is an open together with a proof that it is contained in `W`.**
The slice of `TopologicalSpace.Opens T` at `W` has as objects the morphisms `V ⟶ W`, and in a
preorder category a morphism is a proposition, so the data of such an object is exactly an open
`V` and the inequality `V ≤ W`; `CategoryTheory.homOfLE` and `CategoryTheory.leOfHom` move
between the two readings, and `CategoryTheory.subsingleton_hom` makes any two morphisms with the
same source and target equal.  That is what lets the naturality hypothesis be stated for
inclusions of opens only.

**The sections of a restriction to the slice are the sections themselves.**
`CategoryTheory.SheafOfModules.over` is the direct image along `CategoryTheory.Over.forget` with
the *identity* morphism of sheaves of rings, so the sections of `G|_W` over an object `V ⟶ W` of
the slice site are the sections of `G` over `V` with scalars restricted along the identity, which
is the same module.  Every component below is therefore the given linear map on the nose and
every `obj` statement is `rfl`; only the naturality square has content, and it is the hypothesis.

A morphism of `CategoryTheory.SheafOfModules` is a morphism of the underlying
`CategoryTheory.PresheafOfModules`, i.e. a family of linear maps together with a naturality
square — `CategoryTheory.PresheafOfModules.Hom` — so no sheaf condition has to be checked.

No declaration here carries a `stacks` tag: this is plumbing for morphisms of modules over the
slice at an open, not an assertion of any tag.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}} {G F : T.Modules}

/-- **A compatible family of linear maps on sections is a morphism of the restrictions to the
slice of the small Zariski site at an open.**

Given, for every open `V` of `T` contained in `W`, a `Γ(T, V)`-linear map
`Γ(G, V) → Γ(F, V)` commuting with restriction to a smaller open contained in `W`, this is the
morphism `G|_W ⟶ F|_W` whose value on sections is that family.

This is the existence half of
`Stacks.AlgebraicGeometry.IdealPowerColimit.over_hom_ext`, which says that there is at most one
such morphism. -/
noncomputable def overHomOfSections (W : T.Opens)
    (f : ∀ (V : T.Opens), V ≤ W → (Γ(G, V) →ₗ[Γ(T, V)] Γ(F, V)))
    (hf : ∀ (V V' : T.Opens) (hVW : V ≤ W) (hV'V : V' ≤ V) (g : Γ(G, V)),
      F.presheaf.map (homOfLE hV'V).op (f V hVW g)
        = f V' (hV'V.trans hVW) (G.presheaf.map (homOfLE hV'V).op g)) :
    G.over W ⟶ F.over W where
  val :=
    { app := fun Y => ModuleCat.ofHom (X := (G.over W).val.obj Y) (Y := (F.over W).val.obj Y)
        (f Y.unop.left (leOfHom Y.unop.hom))
      naturality := fun {Y Z} i => by
        ext g
        exact (hf Y.unop.left Z.unop.left (leOfHom Y.unop.hom) (leOfHom i.unop.left) g).symm }

/-- The component of `AlgebraicGeometry.Scheme.Modules.overHomOfSections` at an object of the
slice site is the given linear map, read on an element. -/
theorem overHomOfSections_val_app_apply (W : T.Opens)
    (f : ∀ (V : T.Opens), V ≤ W → (Γ(G, V) →ₗ[Γ(T, V)] Γ(F, V)))
    (hf : ∀ (V V' : T.Opens) (hVW : V ≤ W) (hV'V : V' ≤ V) (g : Γ(G, V)),
      F.presheaf.map (homOfLE hV'V).op (f V hVW g)
        = f V' (hV'V.trans hVW) (G.presheaf.map (homOfLE hV'V).op g))
    (Y : (Over W)ᵒᵖ) (g : Γ(G, Y.unop.left)) :
    ((overHomOfSections W f hf).val.app Y).hom g
      = f Y.unop.left (leOfHom Y.unop.hom) g := rfl

/-- **The value of `AlgebraicGeometry.Scheme.Modules.overHomOfSections` on the sections over an
open contained in `W` is the given map.**  Together with
`Stacks.AlgebraicGeometry.IdealPowerColimit.over_hom_ext` this pins the morphism down. -/
theorem overHomOfSections_apply (W : T.Opens)
    (f : ∀ (V : T.Opens), V ≤ W → (Γ(G, V) →ₗ[Γ(T, V)] Γ(F, V)))
    (hf : ∀ (V V' : T.Opens) (hVW : V ≤ W) (hV'V : V' ≤ V) (g : Γ(G, V)),
      F.presheaf.map (homOfLE hV'V).op (f V hVW g)
        = f V' (hV'V.trans hVW) (G.presheaf.map (homOfLE hV'V).op g))
    {V : T.Opens} (hVW : V ≤ W) (g : Γ(G, V)) :
    ((overHomOfSections W f hf).val.app (op (Over.mk (homOfLE hVW)))).hom g = f V hVW g := rfl

/-- **A compatible family of linear maps on the sections over the opens contained in `W` is
realized by a morphism of the restrictions to the slice at `W`.**  This is the shape in which a
construction performed open by open is turned into a morphism `G|_W ⟶ F|_W`. -/
theorem exists_over_hom_of_sections (W : T.Opens)
    (f : ∀ (V : T.Opens), V ≤ W → (Γ(G, V) →ₗ[Γ(T, V)] Γ(F, V)))
    (hf : ∀ (V V' : T.Opens) (hVW : V ≤ W) (hV'V : V' ≤ V) (g : Γ(G, V)),
      F.presheaf.map (homOfLE hV'V).op (f V hVW g)
        = f V' (hV'V.trans hVW) (G.presheaf.map (homOfLE hV'V).op g)) :
    ∃ θ : G.over W ⟶ F.over W, ∀ (V : T.Opens) (hVW : V ≤ W) (g : Γ(G, V)),
      (θ.val.app (op (Over.mk (homOfLE hVW)))).hom g = f V hVW g :=
  ⟨overHomOfSections W f hf, fun _ hVW g => overHomOfSections_apply W f hf hVW g⟩

end AlgebraicGeometry.Scheme.Modules

end
