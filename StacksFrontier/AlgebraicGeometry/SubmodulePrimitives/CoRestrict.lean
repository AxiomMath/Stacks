module

public import StacksFrontier.AlgebraicGeometry.SubmoduleGlueOpens.Basic
public import StacksFrontier.AlgebraicGeometry.SubmoduleRestrict.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# Carrying a submodule back across an open immersion

Let `f : Y ⟶ X` be an open immersion of schemes and `F` an `𝒪_X`-module. A submodule `N` of `F`
restricts to a submodule `restrictTo f N` of `F.restrict f`. Conversely, a submodule `P` of
`F.restrict f` determines a submodule `coRestrict f P` of `F`, and
`restrictTo f (coRestrict f P) = P`, so `coRestrict f` is a section of `restrictTo f`.

Over an open `U` of `X` the sections of `coRestrict f P` are the sections of `F` whose
restriction to `f ''ᵁ V` lies in `P` for **every** open `V` of `Y` with `f ''ᵁ V ≤ U`. Away from
the image of `f` nothing is required, so `coRestrict f P` is the *largest* submodule of `F`
restricting into `P`; in particular it is `⊤` over any open disjoint from the image.

## Main definitions

* `coRestrictObj`: the condition over one open, as a `Γ(X, U)`-submodule of `Γ(F, U)`.
* `preCoRestrict`: that family, as a submodule of the underlying presheaf of modules.
* `coRestrict`: the co-restricted submodule `coRestrict f P : F.Submodule`.

## Main results

* `mem_coRestrict_iff`: the membership condition.
* `restrictTo_coRestrict`: `restrictTo f (coRestrict f P) = P`.
* `mem_coRestrict_image_iff`: over an open of the form `f ''ᵁ V` a section lies in
  `coRestrict f P` exactly when it lies in `P` over `V`.
* `le_coRestrict_iff`: `N ≤ coRestrict f P ↔ restrictTo f N ≤ P`.
* `coRestrict_mono`, `restrictTo_mono`: `coRestrict f` and `restrictTo f` are monotone.
* `smul_eq_restrict_smul`: scalars of `X` over `f ''ᵁ V` act on sections of `F.restrict f` over
  `V` through `AlgebraicGeometry.Scheme.Hom.appIso`.

## Why this is needed

The affine induction of [Stacks, Tag 01PF] produces its pieces on open subschemes: the inductive
hypothesis is applied to `F.restrict (W i).ι`, and the affine case
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on` is
applied on an affine open. The glueing step `Stacks.AlgebraicGeometry.SubmoduleGlueOpens.glue`
takes pieces that are submodules of `F` itself, to avoid the open-immersion crossing recorded in
that file's module documentation. Without a co-restriction the pieces of the induction cannot be
fed to the glue; with it, `glue W (fun i => coRestrict (W i).ι (P i))` is a submodule of `F`
whose restriction to `W j` is `P j`, by `restrictTo_coRestrict` and
`Stacks.AlgebraicGeometry.SubmoduleGlueLocality.restrictTo_glue_of_le`.

## Implementation notes

The membership condition quantifies over the opens `V` of `Y` with `f ''ᵁ V ≤ U`, rather than
being a single membership at the open `f ⁻¹ᵁ U` of `Y`. The two are equivalent, but the single
membership makes `restrictTo_coRestrict` need the equality of opens `f ⁻¹ᵁ f ''ᵁ V = V`
(`AlgebraicGeometry.Scheme.Hom.preimage_image_eq`) inside `P.obj (op _)`, whose type depends on
the open, hence an `eqToHom` transport. The quantified form only uses the inequality
`AlgebraicGeometry.Scheme.Hom.image_le_image_iff`, a `Prop`, and the file has no `eqToHom`.

Elaboration facts:

* The only scalar that moves is in `coRestrictObj`'s `smul_mem'`, by
  `AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_inv_apply` (isolated as
  `smul_eq_restrict_smul`). That is the *inv* direction of the comparison;
  `SubmoduleRestrict/Basic.lean` needs the *hom* direction, because there the scalar starts on
  `Y`. No identification of the `Γ(Y, V)`-action with the `Γ(X, f ''ᵁ V)`-action is needed, so
  none of the `backward.isDefEq.respectTransparency` escapes needed elsewhere for this crossing
  is used.
* `(F.restrict f).val.map (homOfLE h).op` is `F.val.map (homOfLE (f.image_mono h)).op` by `rfl`
  (`AlgebraicGeometry.Scheme.Modules.restrict_map`), so the sheaf condition and stability under
  restriction need no transport across the immersion, only
  `Stacks.AlgebraicGeometry.SubmoduleGlueOpens.valRes_res` and
  `Stacks.AlgebraicGeometry.GabberColimit.res_res` to compose restrictions.
* Locality is pointwise, through `AlgebraicGeometry.Scheme.Hom.image_preimage_le`. No
  quasi-compactness and no hypothesis on `F` is used anywhere in this file.

Since `restrictTo f` is not injective, `coRestrict f` is a section and not an inverse:
`le_coRestrict_restrictTo` is an inequality, which is not an equality in general.

## No stacks attribute

No stacks attribute is attached, and none is earned: nothing here asserts [Stacks, Tag 01PF] or
any other tag. This is one of the three primitives the affine induction of Tag 01PF is built
from, a step of a proof and not a statement of a lemma.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SubmodulePrimitives

open Stacks.AlgebraicGeometry.GabberColimit Stacks.AlgebraicGeometry.SubmoduleGlueOpens
open Stacks.AlgebraicGeometry.SubmoduleRestrict

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {F : X.Modules}

/-! ### Scalars over the image -/

/-- A scalar over the image open `f ''ᵁ V` acts on a section of `F` there exactly as its image
under `AlgebraicGeometry.Scheme.Hom.appIso` acts on the same section read as a section of
`F.restrict f` over `V`. -/
theorem smul_eq_restrict_smul (V : Y.Opens) (r : Γ(X, f ''ᵁ V)) (x : Γ(F.restrict f, V)) :
    (F.smul r).hom x = ((f.appIso V).hom r) • x :=
  Scheme.Modules.smul_restrictAppIso_inv_apply f F V r x

/-- A submodule `P` of `F.restrict f` is stable, over an open `V` of `Y`, under the action of
the sections of `𝒪_X` over `f ''ᵁ V`. The action is written `(F.smul r).hom x` rather than
`r • x`: the carriers `Γ(F, f ''ᵁ V)` and `Γ(F.restrict f, V)` are equal but not syntactically
so, and `•` chooses its `Module` instance from the spelling. -/
theorem smul_mem_obj (P : (F.restrict f).Submodule) (V : Y.Opens) (r : Γ(X, f ''ᵁ V))
    {x : Γ(F.restrict f, V)} (hx : x ∈ P.obj (op V)) :
    (F.smul r).hom x ∈ P.obj (op V) := by
  rw [smul_eq_restrict_smul f V r x]
  exact Submodule.smul_mem _ _ hx

/-! ### The co-restricted submodule -/

/-- The sections of `F` over `U` whose restriction to `f ''ᵁ V` lies in `P` for every open `V`
of `Y` whose image is inside `U`, as a `Γ(X, U)`-submodule. -/
def coRestrictObj (P : (F.restrict f).Submodule) (U : X.Opens) :
    Submodule Γ(X, U) Γ(F, U) where
  carrier := {s | ∀ (V : Y.Opens) (h : f ''ᵁ V ≤ U),
    F.presheaf.map (homOfLE h).op s ∈ P.obj (op V)}
  add_mem' := by
    intro a b ha hb V h
    rw [map_add]
    exact Submodule.add_mem _ (ha V h) (hb V h)
  zero_mem' := by
    intro V h
    rw [map_zero]
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c s hs V h
    rw [F.map_smul (homOfLE h) c s]
    exact smul_mem_obj f P V _ (hs V h)

/-- A section `s` of `F` over `U` lies in `coRestrictObj f P U` if and only if its restriction
to `f ''ᵁ V` lies in `P` over `V` for every open `V` of `Y` with `f ''ᵁ V ≤ U`. -/
theorem mem_coRestrictObj_iff (P : (F.restrict f).Submodule) {U : X.Opens} (s : Γ(F, U)) :
    s ∈ coRestrictObj f P U ↔
      ∀ (V : Y.Opens) (h : f ''ᵁ V ≤ U), F.presheaf.map (homOfLE h).op s ∈ P.obj (op V) :=
  Iff.rfl

/-- The family `coRestrictObj f P`, as a submodule of the underlying presheaf of modules of
`F`. -/
def preCoRestrict (P : (F.restrict f).Submodule) : F.val.Submodule where
  obj U := coRestrictObj f P U.unop
  map {U U'} g := by
    rintro s hs V h
    have key := hs V (h.trans g.unop.le)
    rw [← res_valRes g.unop.le h s] at key
    exact key

/-- The co-restriction of a submodule along an open immersion: for `P` a submodule of
`F.restrict f`, the submodule of `F` whose sections over an open `U` of `X` are the sections of
`F` restricting into `P` over every open of `Y` with image inside `U`. -/
def coRestrict (P : (F.restrict f).Submodule) : F.Submodule where
  toSubmodule := preCoRestrict f P
  isSheaf := by
    intro U s hs V h
    refine P.isSheaf _ fun y hy => ?_
    obtain ⟨W, i, hW, hyW⟩ := hs (f.base y) (h ⟨y, hy, rfl⟩)
    have hle : f ''ᵁ (V ⊓ f ⁻¹ᵁ W) ≤ W :=
      (f.image_mono inf_le_right).trans (f.image_preimage_le W)
    refine ⟨V ⊓ f ⁻¹ᵁ W, homOfLE inf_le_left, ?_, hy, hyW⟩
    change F.val.map (homOfLE (f.image_mono (inf_le_left : V ⊓ f ⁻¹ᵁ W ≤ V))).op
        (F.presheaf.map (homOfLE h).op s) ∈ P.obj (op (V ⊓ f ⁻¹ᵁ W))
    rw [valRes_res h (f.image_mono (inf_le_left : V ⊓ f ⁻¹ᵁ W ≤ V)) s]
    have hW' : F.presheaf.map (homOfLE i.le).op s ∈ coRestrictObj f P W := hW
    have key := hW' (V ⊓ f ⁻¹ᵁ W) hle
    rw [res_res F i.le hle s] at key
    exact key

/-- The sections of `coRestrict f P` over `U` form the submodule `coRestrictObj f P U`. -/
theorem coRestrict_obj (P : (F.restrict f).Submodule) (U : X.Opens) :
    (coRestrict f P).obj (op U) = coRestrictObj f P U :=
  rfl

/-- A section of `F` over `U` lies in `coRestrict f P` if and only if its restriction to
`f ''ᵁ V` lies in `P` over `V` for every open `V` of `Y` with `f ''ᵁ V ≤ U`. -/
theorem mem_coRestrict_iff (P : (F.restrict f).Submodule) {U : X.Opens} (s : Γ(F, U)) :
    s ∈ (coRestrict f P).obj (op U) ↔
      ∀ (V : Y.Opens) (h : f ''ᵁ V ≤ U), F.presheaf.map (homOfLE h).op s ∈ P.obj (op V) :=
  Iff.rfl

/-! ### The section identity -/

/-- A section over `f ''ᵁ V` lying in `coRestrict f P` lies in `P` over `V`. -/
private theorem mem_of_mem_coRestrict_image (P : (F.restrict f).Submodule) (V : Y.Opens)
    {x : Γ(F, f ''ᵁ V)} (hx : x ∈ (coRestrict f P).obj (op (f ''ᵁ V))) : x ∈ P.obj (op V) :=
  res_self (F := F) (U := f ''ᵁ V) x ▸ hx V le_rfl

/-- The restriction to `Y` of the co-restriction of `P` is `P`. -/
theorem restrictTo_coRestrict (P : (F.restrict f).Submodule) :
    restrictTo f (coRestrict f P) = P := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
  refine SetLike.ext fun x => ⟨fun hx => ?_, fun hx V' h => ?_⟩
  · exact mem_of_mem_coRestrict_image f P V.unop hx
  · exact P.map_mem (homOfLE ((f.image_le_image_iff V' V.unop).1 h)).op hx

/-- Over an open of `X` of the form `f ''ᵁ V`, a section of `F` lies in `coRestrict f P` if
and only if it lies in `P` over `V`. This is a membership statement and not an equality of
submodules because the two live over different rings, `Γ(X, f ''ᵁ V)` and `Γ(Y, V)`. -/
theorem mem_coRestrict_image_iff (P : (F.restrict f).Submodule) (V : Y.Opens)
    (x : Γ(F, f ''ᵁ V)) :
    x ∈ (coRestrict f P).obj (op (f ''ᵁ V)) ↔ x ∈ P.obj (op V) := by
  have e : (x ∈ (restrictTo f (coRestrict f P)).obj (op V)) = (x ∈ P.obj (op V)) :=
    congrArg (fun Q : (F.restrict f).Submodule => x ∈ Q.obj (op V)) (restrictTo_coRestrict f P)
  exact ⟨fun hx => Eq.mp e hx, fun hx => Eq.mpr e hx⟩

/-! ### Monotonicity and the adjunction -/

/-- The co-restriction is monotone in the submodule. -/
theorem coRestrict_mono {P Q : (F.restrict f).Submodule} (h : P ≤ Q) :
    coRestrict f P ≤ coRestrict f Q :=
  fun _ _ hs V hV => h (op V) (hs V hV)

/-- The restriction along `f` is monotone in the submodule. -/
theorem restrictTo_mono {N N' : F.Submodule} (h : N ≤ N') : restrictTo f N ≤ restrictTo f N' :=
  fun V _ hs => h (op (f ''ᵁ V.unop)) hs

/-- A submodule `N` of `F` is contained in `coRestrict f P` if and only if `restrictTo f N` is
contained in `P`. -/
theorem le_coRestrict_iff (N : F.Submodule) (P : (F.restrict f).Submodule) :
    N ≤ coRestrict f P ↔ restrictTo f N ≤ P := by
  constructor
  · intro h V x hx
    exact mem_of_mem_coRestrict_image f P V.unop (h (op (f ''ᵁ V.unop)) hx)
  · intro h U s hs V hV
    exact h (op V) (N.map_mem (homOfLE hV).op hs)

/-- Every submodule `N` of `F` is contained in the co-restriction of its restriction. -/
theorem le_coRestrict_restrictTo (N : F.Submodule) : N ≤ coRestrict f (restrictTo f N) :=
  (le_coRestrict_iff f N (restrictTo f N)).2 le_rfl

end Stacks.AlgebraicGeometry.SubmodulePrimitives

end
