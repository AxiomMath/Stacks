module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# Restricting a submodule of a module on a scheme along an open immersion

Let `f : Y ⟶ X` be an open immersion of schemes and `F` an `𝒪_X`-module. A submodule of `F` in
Mathlib's sense (`SheafOfModules.Submodule`) is *concrete*: a family of `Γ(X, U)`-submodules of
`Γ(F, U)`, one for every open `U` of `X`, stable under restriction and local. This file carries
such a submodule across `f`, producing a submodule `restrictTo f N` of the `𝒪_Y`-module
`F.restrict f` whose sections over an open `V` of `Y` are the sections of `N` over the image open
`f ''ᵁ V`.

The case the consumers use is `f = W.ι` for an open `W` of `X`, i.e. the restriction of a
submodule of `F` to an open subscheme; nothing below is special to it, so the open immersion is
taken general.

## Why this is needed

Every locality statement about `𝒪_X`-modules in either tree — quasi-coherence
(`AlgebraicGeometry.isQuasicoherent_of_restrict_isAffineOpen`,
`SheafOfModules.IsQuasicoherent.of_coversTop`), being of finite type
(`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections`,
`Stacks.SheafOfModules.isFiniteType_of_coversTop`) — is stated about
`AlgebraicGeometry.Scheme.Modules.restrict` or about `SheafOfModules.over`, i.e. about a module on
the *open subscheme*. A concrete submodule of `F`, on the other hand, is data on the opens of `X`.
Feeding the former to the latter is the passage this file performs, and it is the one declaration
standing between the unconditional glueing step of
`StacksFrontier/AlgebraicGeometry/SubmoduleGlueOpens/Basic.lean` and [Stacks, Tag 01PF]; the same
gap is recorded, for a different glued object, in
`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean`.

## Main definitions

* `restrictToObj`: the `Γ(Y, V)`-submodule of `Γ(F.restrict f, V)` of sections lying in
  `N.obj (op (f ''ᵁ V))`.
* `preRestrictTo`: those submodules as a submodule of the underlying presheaf of modules.
* `restrictTo`: **the restricted submodule**, `restrictTo f N : (F.restrict f).Submodule`.

## Main results

* `mem_restrictTo_iff`: **the sections identity.** A section of `F.restrict f` over `V` lies in
  `restrictTo f N` exactly when its image under
  `AlgebraicGeometry.Scheme.Modules.restrictAppIso` lies in `N.obj (op (f ''ᵁ V))`. This is the
  statement in the form in which the sections of a restriction are meant to be named; the same
  fact with the isomorphism left implicit is `mem_restrictTo`.
* `restrictTo_toSheafOfModules`: **the comparison, as an equality.** The sheaf of modules of the
  restricted submodule *is* the restriction of the sheaf of modules of the submodule:
  `(restrictTo f N).toSheafOfModules = (N.toSheafOfModules).restrict f`. It is a `rfl`, and that
  is the measurement this file turns on — see the implementation notes.
* `restrictToIso` and `restrictToIso_hom_ι`: the comparison as an isomorphism, together with the
  commutation with the two inclusions into `F.restrict f`.

## Implementation notes

**The comparison is an equality and not merely an isomorphism**, which is more than was expected
and is what makes the second half of this file four lines rather than a `PresheafOfModules.isoMk`
with a semilinearity obligation at every open. The reason is that the twist is *the same twist on
both sides*. Writing `α V := (f.appIso V).inv` for the ring map that
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` restricts scalars along:

* the sections of `F.restrict f` over `V` are `Γ(F, f ''ᵁ V)` with the `Γ(Y, V)`-action
  `r • x = α V r • x` (`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom`), so the
  submodule `restrictToObj f N V` has underlying module `↥(N.obj (op (f ''ᵁ V)))` with that same
  action;
* the sections of `(N.toSheafOfModules).restrict f` over `V` are the sections of
  `N.toSheafOfModules` over `f ''ᵁ V`, which are `↥(N.obj (op (f ''ᵁ V)))`, with the
  `Γ(Y, V)`-action `r • x = α V r • x`.

So both sides are the submodule `N.obj (op (f ''ᵁ V))` with scalars restricted along `α V`, and
the two `Module` instances — `Submodule.module` over a `ModuleCat.restrictScalars`, and
`ModuleCat.restrictScalars` of a `Submodule.module` — are definitionally equal field by field.
`restrictTo_toSheafOfModules` is therefore a kernel-checked `rfl`, and `restrictToIso` is
`Iso.refl`.

This is the reason the construction does **not** need
`set_option backward.isDefEq.respectTransparency false`, which the notes in
`StacksFrontier/AlgebraicGeometry/NormMapInvertible/Covering.lean` and in the implementation notes
of `StacksFrontier/AlgebraicGeometry/AffineSubsheaf/Basic.lean` call for in a passage
across an open immersion on module sheaves. The difficulty those record is identifying the
`Γ(Y, V)`-action with the `Γ(X, f ''ᵁ V)`-action, which is *not* definitional; nothing here does
that. The only place a scalar is moved is `restrictToObj`'s `smul_mem'`, and it is moved by
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply` — the scalar that ends up acting
is `α V c`, a section over `f ''ᵁ V`, so the step closes with `Submodule.smul_mem` and no
comparison of actions is ever asked for.

Three further elaboration facts:

* The carrier is written as the bare membership `x ∈ N.obj (op (f ''ᵁ V))` rather than as
  `(F.restrictAppIso f V).hom x ∈ …`, because `Γ(F.restrict f, V)` and `Γ(F, f ''ᵁ V)` are the
  same type by `rfl` and the bare spelling makes `mem_restrictTo` and `restrictTo_toSheafOfModules`
  both `rfl`. `mem_restrictTo_iff` recovers the `restrictAppIso` spelling, also by `rfl`.
* Stability under restriction is `N.map_mem (f.opensFunctor.map g).op`: the restriction map of
  `F.restrict f` along `g : V' ⟶ V` *is* the restriction map of `F` along
  `f.opensFunctor.map g : f ''ᵁ V' ⟶ f ''ᵁ V` (`AlgebraicGeometry.Scheme.Modules.restrict_map`,
  a `rfl`), so no transport is needed. Note `f.opensFunctor.map g` and
  `CategoryTheory.homOfLE (f.image_mono g.le)` are the same morphism, the category of opens being
  a partial order.
* The sheaf condition is the only step with content. Membership of
  `TopologicalSpace.Opens.grothendieckTopology` is pointwise by `rfl`
  (`TopologicalSpace.Opens.mem_grothendieckTopology`), so a covering of `V` by opens on which the
  section lies in `restrictTo f N` is turned into a covering of `f ''ᵁ V` by taking images: a
  point of `f ''ᵁ V` is `f x` for some `x ∈ V`, the given covering supplies a `V' ∋ x` inside `V`,
  and `f ''ᵁ V'` is an open of `X` inside `f ''ᵁ V` containing `f x` over which the section lies
  in `N`. This uses only that `f ''ᵁ` is monotone and that the image of a point of `V'` is a point
  of `f ''ᵁ V'`; no quasi-compactness, no quasi-separatedness, and no hypothesis on `F`.

## What this does not do, and what is not claimed

**No stacks attribute is attached**: nothing here is an assertion of
[Stacks, Tag 01PF] or of any other tag. This is a step of that lemma's affine induction — the
construction that lets the locality theorems be applied to a concrete submodule — not a
statement of the lemma.

The locality statements phrased over `SheafOfModules.over` rather than over
`AlgebraicGeometry.Scheme.Modules.restrict` (`SheafOfModules.IsQuasicoherent.of_coversTop`,
`Stacks.SheafOfModules.isFiniteType_of_coversTop` and its two namesakes in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorExactnessSheafify.lean` and
`StacksFrontier/AlgebraicGeometry/CoherentKernel/Basic.lean`) are **not** reached by this file.
Those need the independent `over`-versus-`restrict` bridge that
`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean` names
(`AlgebraicGeometry.Scheme.Modules.overEquiv` and `overFunctorEquiv`), which is a different
crossing. The ones phrased over `restrict` are reached, and
`StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Locality.lean` applies two of them.

Nothing is proved about how `restrictTo` interacts with the lattice structure of
`SheafOfModules.Submodule`, and nothing needs to be: `InfSet (SheafOfModules.Submodule F)` is not
synthesized for `F : X.Modules` at all, the `def`-versus-`abbrev` issue described in
`StacksFrontier/AlgebraicGeometry/SubmoduleGlueOpens/Basic.lean`.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SubmoduleRestrict

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {F : X.Modules}

/-! ### The restricted submodule -/

/-- The sections of `F.restrict f` over an open `V` of `Y` that lie in `N` over the image open
`f ''ᵁ V`, as a `Γ(Y, V)`-submodule.

The underlying sets of `Γ(F.restrict f, V)` and `Γ(F, f ''ᵁ V)` agree, so the condition is a bare
membership; only the scalar action differs, by `(f.appIso V).inv`, and that is exactly what
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply` supplies for `smul_mem'`. -/
def restrictToObj (N : F.Submodule) (V : Y.Opensᵒᵖ) :
    Submodule ↑(Y.ringCatSheaf.obj.obj V) ↑((F.restrict f).val.obj V) where
  carrier := {x | x ∈ N.obj (op (f ''ᵁ V.unop))}
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' c x hx := by
    have h := Scheme.Modules.smul_restrictAppIso_hom_apply f F V.unop c x
    exact h ▸ Submodule.smul_mem _ _ hx

/-- The family `restrictToObj f N`, as a submodule of the underlying presheaf of modules of
`F.restrict f`. Stability under restriction is stability of `N` along the image of the morphism of
opens, the restriction maps of `F.restrict f` being those of `F` on the image opens. -/
def preRestrictTo (N : F.Submodule) : (F.restrict f).val.Submodule where
  obj V := restrictToObj f N V
  map {V V'} g := by
    rintro s hs
    exact N.map_mem (f.opensFunctor.map g.unop).op hs

/-- **The restriction of a submodule along an open immersion.** For `N` a submodule of an
`𝒪_X`-module `F`, this is the submodule of `F.restrict f` whose sections over an open `V` of `Y`
are the sections of `N` over `f ''ᵁ V`.

Locality is inherited from locality of `N`: a point of `f ''ᵁ V` is the image of a point of `V`,
a covering of `V` on which a section lies in the family gives — by taking images of its members —
a covering of `f ''ᵁ V` on which the section lies in `N`. -/
def restrictTo (N : F.Submodule) : (F.restrict f).Submodule where
  toSubmodule := preRestrictTo f N
  isSheaf := by
    intro V s hs
    refine N.isSheaf s fun y hy ↦ ?_
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨V', g, hg, hxV'⟩ := hs x hx
    exact ⟨f ''ᵁ V', homOfLE (f.image_mono g.le), hg, ⟨x, hxV', rfl⟩⟩

/-! ### The sections identity -/

/-- **The sections identity**, in the spelling that names the comparison of the sections of a
restriction: a section of `F.restrict f` over `V` lies in `restrictTo f N` exactly when its image
under `AlgebraicGeometry.Scheme.Modules.restrictAppIso` lies in `N` over `f ''ᵁ V`. -/
theorem mem_restrictTo_iff (N : F.Submodule) {V : Y.Opens} (x : Γ(F.restrict f, V)) :
    x ∈ (restrictTo f N).obj (op V) ↔
      (F.restrictAppIso f V).hom x ∈ N.obj (op (f ''ᵁ V)) :=
  Iff.rfl

/-- `mem_restrictTo_iff` with the comparison isomorphism left implicit, which is possible because
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `CategoryTheory.Iso.refl`. This is the form
used in proofs. -/
theorem mem_restrictTo (N : F.Submodule) {V : Y.Opens} (x : Γ(F.restrict f, V)) :
    x ∈ (restrictTo f N).obj (op V) ↔ x ∈ N.obj (op (f ''ᵁ V)) :=
  Iff.rfl

/-- The restricted submodule over an open of `Y`, as a set of sections of `F` over the image
open. -/
theorem coe_restrictTo_obj (N : F.Submodule) (V : Y.Opensᵒᵖ) :
    ((restrictTo f N).obj V : Set ↑((F.restrict f).val.obj V)) =
      (N.obj (op (f ''ᵁ V.unop)) : Set ↑(F.val.obj (op (f ''ᵁ V.unop)))) :=
  rfl

/-! ### The comparison with the restriction of the associated sheaf of modules -/

/-- **The comparison, as an equality.** The `𝒪_Y`-module of the restricted submodule is the
restriction of the `𝒪_X`-module of the submodule.

Both sides are `N.obj (op (f ''ᵁ V))` over `f ''ᵁ V`, with scalars restricted along
`(f.appIso V).inv`; the two ways of saying that — a submodule of a restriction of scalars, and a
restriction of scalars of a submodule — are definitionally equal. See the implementation notes. -/
theorem restrictTo_toSheafOfModules (N : F.Submodule) :
    (restrictTo f N).toSheafOfModules =
      Scheme.Modules.restrict (N.toSheafOfModules : X.Modules) f :=
  rfl

/-- `restrictTo_toSheafOfModules` with the restriction written as the value of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

Both spellings are needed, and this is not redundancy. `AlgebraicGeometry.Scheme.Modules.restrict`
is an `abbrev` for `(restrictFunctor f).obj`, so the two statements are the same proposition up to
reducible unfolding — but a `rw` or a `▸` matches *syntactically*, and the locality
theorems are stated in both spellings (`isQuasicoherent_of_restrict_isAffineOpen` in the first,
`AlgebraicGeometry.Modules.isFiniteType_of_restrict` and `isCoherent_of_restrict` in the second).
Indeed, `▸` with the `restrict` form against a goal in the `restrictFunctor` form fails with
"does not contain the expected result type on either the left or the right hand side". -/
theorem restrictTo_toSheafOfModules' (N : F.Submodule) :
    (restrictTo f N).toSheafOfModules =
      (Scheme.Modules.restrictFunctor f).obj (N.toSheafOfModules : X.Modules) :=
  rfl

/-- **The comparison, as an isomorphism** -- the form the statement of this step is usually given
in. It is the identity, by `restrictTo_toSheafOfModules`. -/
def restrictToIso (N : F.Submodule) :
    (restrictTo f N).toSheafOfModules ≅
      Scheme.Modules.restrict (N.toSheafOfModules : X.Modules) f :=
  Iso.refl _

/-- **The comparison commutes with the two inclusions into `F.restrict f`**: the inclusion of the
restricted submodule and the restriction of the inclusion of the submodule. -/
@[reassoc]
theorem restrictToIso_hom_ι (N : F.Submodule) :
    (restrictToIso f N).hom ≫ (Scheme.Modules.restrictFunctor f).map N.ι =
      (restrictTo f N).ι :=
  rfl

/-- `restrictToIso_hom_ι` in the direction that rewrites the restriction of the inclusion. -/
@[reassoc]
theorem restrictToIso_inv_ι (N : F.Submodule) :
    (restrictToIso f N).inv ≫ (restrictTo f N).ι =
      (Scheme.Modules.restrictFunctor f).map N.ι :=
  rfl

end Stacks.AlgebraicGeometry.SubmoduleRestrict

end
