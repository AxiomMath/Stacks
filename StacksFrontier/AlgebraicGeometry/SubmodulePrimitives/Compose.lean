module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Composing a submodule of a submodule into a submodule of the ambient module

Let `M` be a sheaf of modules on a site, let `N : M.Submodule` be a submodule of `M` — a family of
`R(U)`-submodules of `M(U)`, stable under restriction and local — and let
`G : N.toSheafOfModules.Submodule` be a submodule of the sheaf of modules `N` determines. This
file constructs the submodule `compose N G` of `M` itself: over every object it is the image of
`G` under the inclusion of `N`.

## Main definitions

* `composeObj`: the image over one object, as an `R(U)`-submodule of `M(U)`.
* `compose`: the composed submodule, `compose N G : M.Submodule`.
* `composeIso`: the isomorphism of `(compose N G).toSheafOfModules` with `G.toSheafOfModules`.

## Main results

* `mem_compose_iff`: a section of `M` over `U` lies in `compose N G` exactly when it lies in `N`
  and the resulting section of `N` lies in `G`.
* `compose_le`: `compose N G ≤ N`.
* `compose_obj_of_eq_top`: over an object where `G` is everything, `compose N G` is `N`.
* `composeIso_hom_ι`: `composeIso` is compatible with the inclusions into `M`.
* `subobjectMk_compose_ι`: the two inclusions into `M` define the same subobject.

## Why this is needed

An extension step producing a submodule of `M` and then truncating it produces a submodule of
the extension, not of `M`. The affine case of [Stacks, Tag 01PF]
(`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on`) is
applied, in the induction of that tag, to the quasi-coherent module `N.toSheafOfModules` obtained
from the extension step [Stacks, Tag 01PE], and returns a submodule of *that*; this file reads it
back as a submodule of the ambient module.

## Implementation notes

Mathlib and this tree have the pullback of a submodule along a morphism
(`AlgebraicGeometry.sheafSubmoduleComap`) but no pushforward. This is the special case of a
pushforward that needs no sheafification: the inclusion of a submodule is sectionwise injective,
so the sectionwise image of a submodule of `N` under `N.ι` is already local, `compose_obj` is an
equality of submodules, and no local-image closure is involved.

Everything is stated for a sheaf of modules on an arbitrary site rather than for
`AlgebraicGeometry.Scheme.Modules`, which is a `def` with its own `Hom` and `Category` instances:
at that spelling neither `Mono N.ι` nor the zero morphism nor `CompleteLattice M.Submodule` is
synthesized, while at the `SheafOfModules` spelling all three
are Mathlib's instances. The results apply to `F : X.Modules` directly, since `X.Modules` unfolds
to `SheafOfModules.{u} X.ringCatSheaf`.

`N.toSheafOfModules` and `M` are modules over the same `R`, and
`PresheafOfModules.Submodule.toPresheafOfModules` restricts no scalars, so every comparison of
restriction maps is `PresheafOfModules.Submodule.toPresheafOfModules_map_apply`, a `rfl`.

## No stacks attribute

No stacks attribute is attached, and none is earned: nothing here is an assertion of
[Stacks, Tag 01PF], of [Stacks, Tag 01PE] or of any other tag. This is one of the three primitives
the affine induction of Tag 01PF is built from, a step of a proof rather than a lemma.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v v₁ u₁ u

namespace Stacks.AlgebraicGeometry.SubmodulePrimitives

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M : SheafOfModules.{v} R}

/-! ### The composed submodule -/

/-- The image over one object of a submodule `G` of `N.toSheafOfModules` under the inclusion of
`N` into `M`, as an `R(U)`-submodule of `M(U)`. -/
def composeObj (N : M.Submodule) (G : N.toSheafOfModules.Submodule) (U : Cᵒᵖ) :
    Submodule ↑(R.obj.obj U) ↑(M.val.obj U) :=
  Submodule.map (N.obj U).subtype (G.obj U)

/-- A section `s` of `M` over `U` lies in `composeObj N G U` if and only if it lies in `N` and
the corresponding section of `N` lies in `G`. -/
theorem mem_composeObj_iff (N : M.Submodule) (G : N.toSheafOfModules.Submodule)
    (U : Cᵒᵖ) (s : ↑(M.val.obj U)) :
    s ∈ composeObj N G U ↔ ∃ h : s ∈ N.obj U, (⟨s, h⟩ : ↥(N.obj U)) ∈ G.obj U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hG⟩
    exact ⟨⟨s, h⟩, hG, rfl⟩

/-- Over every object, `composeObj N G U` is contained in the sections of `N`. -/
theorem composeObj_le (N : M.Submodule) (G : N.toSheafOfModules.Submodule) (U : Cᵒᵖ) :
    composeObj N G U ≤ N.obj U := by
  rintro s ⟨y, _, rfl⟩
  exact y.2

/-- A section of the composed submodule, read as a section of `N`, lies in `G`. -/
theorem mem_of_mem_composeObj (N : M.Submodule) (G : N.toSheafOfModules.Submodule) (U : Cᵒᵖ)
    {s : ↑(M.val.obj U)} (hs : s ∈ composeObj N G U) :
    (⟨s, composeObj_le N G U hs⟩ : ↥(N.obj U)) ∈ G.obj U := by
  obtain ⟨_, hG⟩ := (mem_composeObj_iff N G U s).1 hs
  exact hG

/-- The composed family, as a submodule of the underlying presheaf of modules of `M`. Stability
under restriction is stability of `G`, the restriction maps of `N.toSheafOfModules` being those
of `M` on the underlying sections. -/
def preCompose (N : M.Submodule) (G : N.toSheafOfModules.Submodule) : M.val.Submodule where
  obj U := composeObj N G U
  map {U V} g := by
    rintro s ⟨y, hy, rfl⟩
    exact ⟨N.toSheafOfModules.val.map g y, G.map_mem g hy, rfl⟩

/-- The composed submodule of `M`. Over an object `U` its sections are the sections of `N`
over `U` which, read as sections of `N.toSheafOfModules`, lie in `G`. -/
def compose (N : M.Submodule) (G : N.toSheafOfModules.Submodule) : M.Submodule where
  toSubmodule := preCompose N G
  isSheaf := by
    intro U s hs
    have hsN : s ∈ N.obj U := by
      refine N.isSheaf s (J.superset_covering (fun V i hi => ?_) hs)
      exact composeObj_le N G _ hi
    refine (mem_composeObj_iff N G U s).2 ⟨hsN, ?_⟩
    refine G.isSheaf (⟨s, hsN⟩ : ↥(N.obj U)) (J.superset_covering (fun V i hi => ?_) hs)
    have key : (⟨M.val.map i.op s, composeObj_le N G _ hi⟩ : ↥(N.obj (op V))) ∈ G.obj (op V) :=
      mem_of_mem_composeObj N G _ hi
    exact key

/-! ### The sections identity -/

/-- The sections of `compose N G` over `U` are the image of the sections of `G` under the
inclusion of `N` into `M`. -/
theorem compose_obj (N : M.Submodule) (G : N.toSheafOfModules.Submodule) (U : Cᵒᵖ) :
    (compose N G).obj U = Submodule.map (N.obj U).subtype (G.obj U) :=
  rfl

/-- A section of `M` over `U` lies in `compose N G` exactly when it lies in `N` and the section
of `N.toSheafOfModules` it determines lies in `G`. -/
theorem mem_compose_iff (N : M.Submodule) (G : N.toSheafOfModules.Submodule) (U : Cᵒᵖ)
    (s : ↑(M.val.obj U)) :
    s ∈ (compose N G).obj U ↔ ∃ h : s ∈ N.obj U, (⟨s, h⟩ : ↥(N.obj U)) ∈ G.obj U :=
  mem_composeObj_iff N G U s

/-- The composed submodule is contained in `N`. -/
theorem compose_le (N : M.Submodule) (G : N.toSheafOfModules.Submodule) : compose N G ≤ N :=
  fun U => composeObj_le N G U

/-- Over an object where `G` is everything, the composed submodule is `N`. This is the form in
which the affine case of [Stacks, Tag 01PF] states its conclusion. -/
theorem compose_obj_of_eq_top (N : M.Submodule) (G : N.toSheafOfModules.Submodule)
    {U : Cᵒᵖ} (hG : G.obj U = ⊤) : (compose N G).obj U = N.obj U := by
  refine le_antisymm (composeObj_le N G U) fun s hs => ?_
  refine (mem_composeObj_iff N G U s).2 ⟨hs, ?_⟩
  rw [hG]
  trivial

/-! ### The comparison with the sheaf of modules of `G` -/

/-- The comparison over one object: the sections of `G` and their image in `M(U)`. -/
def composeEquiv (N : M.Submodule) (G : N.toSheafOfModules.Submodule) (U : Cᵒᵖ) :
    ↥(G.obj U) ≃ₗ[↑(R.obj.obj U)] ↥(composeObj N G U) where
  toFun y := ⟨(y.1 : ↥(N.obj U)).1, Submodule.mem_map_of_mem (f := (N.obj U).subtype) y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨(⟨x.1, composeObj_le N G U x.2⟩ : ↥(N.obj U)), mem_of_mem_composeObj N G U x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sheaf of modules of the composed submodule is isomorphic to the sheaf of modules of `G`;
over `U` it is the inverse of `composeEquiv N G U`. -/
def composeIso (N : M.Submodule) (G : N.toSheafOfModules.Submodule) :
    (compose N G).toSheafOfModules ≅ G.toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U => (composeEquiv N G U).symm.toModuleIso)
      (fun {U V} g => by
        ext x
        refine Subtype.ext (Subtype.ext ?_)
        rfl))

/-- The comparison commutes with the inclusions into `M`: the inclusion of the composed
submodule is the inclusion of `G` into `N` followed by the inclusion of `N` into `M`. -/
@[reassoc]
theorem composeIso_hom_ι (N : M.Submodule) (G : N.toSheafOfModules.Submodule) :
    (composeIso N G).hom ≫ G.ι ≫ N.ι = (compose N G).ι := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U => ?_)
  ext x
  rfl

/-- The composed submodule and `G` define the same subobject of `M`. -/
theorem subobjectMk_compose_ι (N : M.Submodule) (G : N.toSheafOfModules.Submodule) :
    Subobject.mk (compose N G).ι = Subobject.mk (G.ι ≫ N.ι) :=
  Subobject.mk_eq_mk_of_comm _ _ (composeIso N G) (composeIso_hom_ι N G)

end Stacks.AlgebraicGeometry.SubmodulePrimitives

end
