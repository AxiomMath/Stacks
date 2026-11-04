module

public import StacksFrontier.AlgebraicGeometry.SubmodulePrimitives.Image
public import StacksFrontier.AlgebraicGeometry.SubmoduleGlueOpens.Basic
public import StacksFrontier.AlgebraicGeometry.SubmoduleRestrict.Basic

/-!
# The sectionwise image, across an open immersion and up to isomorphism

`StacksFrontier/AlgebraicGeometry/SubmodulePrimitives/Image.lean` sends a morphism `φ : A ⟶ F` of
`𝒪_X`-modules to the concrete submodule `ofHom φ` of sections locally in its image, and shows
that for a monomorphism this is the sectionwise image. That is the passage from the `Subobject`
spelling, in which [Stacks, Tag 01PE] is formalized, to the concrete-submodule spelling the glueing
step of [Stacks, Tag 01PF] is written in. **It is not enough on its own**: what [Stacks, Tag 01PE]
delivers is not a submodule but a subobject `H` of `F` together with an *isomorphism over*
`F.restrict j` between the restriction of `H` and the given subobject, and turning that into the
equality of concrete submodules the induction needs takes the two statements proved here.

## Main results

* `restrictTo_ofHom`: **restriction commutes with the sectionwise image.**
  `restrictTo f (ofHom φ) = ofHom ((Scheme.Modules.restrictFunctor f).map φ)`, with no hypothesis
  on `φ` at all.
* `ofHom_eq_of_iso`: **two morphisms with the same image define the same submodule.** If
  `e : A ≅ B` and `e.hom ≫ ψ = φ`, then `ofHom φ = ofHom ψ`.
* `restrictTo_ofHom_eq_of_iso`: the two composed, in the shape [Stacks, Tag 01PE] produces its
  conclusion: from `e : (H : X.Modules).restrict j ≅ A` with
  `e.hom ≫ φ = (restrictFunctor j).map ψ`, the restriction of `ofHom ψ` to the open subscheme is
  `ofHom φ`.

## Implementation notes

`restrictTo_ofHom` is proved **without** the monomorphism hypothesis and therefore without
`Stacks.AlgebraicGeometry.SubmodulePrimitives.obj_ofHom_of_mono`: both sides are the
"locally in the image" condition of `Stacks.SheafOfModules.localImage`, and the two conditions
correspond because the opens of `X` inside `f ''ᵁ V` can be shrunk to image opens. Concretely, a
point of `f ''ᵁ V` is `f y` for `y ∈ V`; given an open `Z ∋ f y` inside `f ''ᵁ V` on which the
section is in the image, the open `V ⊓ f ⁻¹ᵁ Z` of `Y` contains `y`, is inside `V`, and has image
inside `Z`, so restricting the local preimage along `f ''ᵁ (V ⊓ f ⁻¹ᵁ Z) ≤ Z` gives the witness
the other side asks for. The converse direction takes images of the opens of `Y`. Avoiding the
mono hypothesis matters: monicity of a *restricted* morphism is exactly the instance whose
default resolution at the `AlgebraicGeometry.Scheme.Modules` spelling times out,
and to pick up a `sorryAx`-carrying instance when it does not.

`ofHom_eq_of_iso` does use monicity, and cannot avoid it: for a general pair of morphisms with a
commuting isomorphism the *local* images agree, but the statement is proved here through the
sectionwise images, where surjectivity of `e.hom` on sections — from
`AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app` — makes the two ranges equal. The
monicity used is of the two morphisms themselves, which a caller holding a subobject has.
`restrictTo_ofHom_eq_of_iso`, which composes the two, therefore does carry
`[Mono ((restrictFunctor f).map ψ)]` in a binder — **it is a hypothesis for the caller to
supply, deliberately not left to instance search**, for the reason above.

No scalar is moved in either proof. The sections of `A.restrict f` over `V` *are* the sections of
`A` over `f ''ᵁ V`, and the restriction maps agree, by
`AlgebraicGeometry.Scheme.Modules.restrict_map`; the two differ only in which ring acts, and
neither statement below compares the two actions.

Three elaboration facts, all of them about `rw` and all of them instances of the
transparency issue recorded in `StacksFrontier/AlgebraicGeometry/SubmoduleRestrict/Basic.lean`:

* `rw [mem_restrictTo]` and `rw [mem_ofHom_iff]` both fail with *"the target expression is not
  type-correct under the `implicit` transparency level"*, naming
  `TopCat.Sheaf RingCat ↑Y.toPresheafedSpace` against
  `Sheaf (Opens.grothendieckTopology ↥Y)` — even though both lemmas are `Iff.rfl`. The two
  membership statements are therefore chained with `Iff.trans` at term level, which succeeds.
* An opposite-category variable must be **destructured** (`obtain ⟨V⟩ := V`) before any
  statement about `op V` is used: at `V : Y.Opensᵒᵖ`, a term built at `op V.unop` is rejected
  with an *application type mismatch naming `ringCatSheaf`*, not with a mismatch of opens. That
  is §8's "`op X.unop` and `X` differ for instance search and the error names the wrong class",
  met here as a hard failure rather than a slowdown.
* `Scheme.Modules.Hom.app ((restrictFunctor f).map φ) V` and
  `φ.val.app (op (f ''ᵁ V))` are definitionally equal and not syntactically so, so the
  naturality step is finished by `exact` on an `Eq.trans` and not by `rw`; the intermediate
  equality is stated out in the `φ.val.app` spelling with `show … from ht`, which is the idiom
  `Stacks.AlgebraicGeometry.GabberColimit.preSubmodule` exists for.

## What this does not do, and no stacks attribute

**No stacks attribute is attached, and none is earned.** Nothing here is an assertion of
[Stacks, Tag 01PE], of [Stacks, Tag 01PF] or of any other tag: these are spelling changes between
two existing statements, i.e. steps of a proof.

What is still absent for the affine case of [Stacks, Tag 01PF] is the assembly itself: the
truncation of the extension to finite type over the quasi-compact open, which is
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on` applied
to the module of the extension, and the passage back along
`Stacks.AlgebraicGeometry.SubmodulePrimitives.compose`. Neither is in this file.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.SubmodulePrimitives

open Stacks.AlgebraicGeometry.SubmoduleRestrict

variable {Y X : Scheme.{u}} {F : X.Modules}

/-! ### Restriction commutes with the sectionwise image -/

/-- **The restriction of the submodule of sections locally in the image of `φ` is the submodule of
sections locally in the image of the restriction of `φ`.** No hypothesis on `φ`. -/
theorem restrictTo_ofHom (f : Y ⟶ X) [IsOpenImmersion f] {A : X.Modules} (φ : A ⟶ F) :
    restrictTo f (ofHom φ) =
      ofHom ((Scheme.Modules.restrictFunctor f).map φ) := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
  obtain ⟨V⟩ := V
  refine SetLike.ext fun x => ?_
  refine (mem_restrictTo f (ofHom φ) x).trans ((mem_ofHom_iff φ x).trans
    (Iff.trans ?_ (mem_ofHom_iff ((Scheme.Modules.restrictFunctor f).map φ) x).symm))
  constructor
  · intro h y hy
    obtain ⟨Z, hZ, hfyZ, t, ht⟩ := h (f.base y) ⟨y, hy, rfl⟩
    have hle : f ''ᵁ (V ⊓ f ⁻¹ᵁ Z) ≤ Z :=
      (f.image_mono inf_le_right).trans (f.image_preimage_le Z)
    refine ⟨V ⊓ f ⁻¹ᵁ Z, inf_le_left, ⟨hy, hfyZ⟩, A.val.map (homOfLE hle).op t, ?_⟩
    have step : (F.val.map (homOfLE hle).op).hom ((φ.val.app (op Z)).hom t) =
        (F.presheaf.map (homOfLE (hle.trans hZ)).op).hom x := by
      rw [show (φ.val.app (op Z)).hom t = (F.presheaf.map (homOfLE hZ).op).hom x from ht]
      exact Stacks.AlgebraicGeometry.SubmoduleGlueOpens.valRes_res hZ hle x
    exact (PresheafOfModules.naturality_apply φ.val (homOfLE hle).op t).trans step
  · rintro h _ ⟨y, hy, rfl⟩
    obtain ⟨V', hV', hyV', t, ht⟩ := h y hy
    exact ⟨f ''ᵁ V', f.image_mono hV', ⟨y, hyV', rfl⟩, t, ht⟩

/-! ### Two morphisms with the same image -/

/-- **Two monomorphisms into `F` related by an isomorphism of their sources define the same
concrete submodule of `F`.** For a monomorphism the submodule of sections locally in the image is
the sectionwise image (`obj_ofHom_of_mono`), and an isomorphism is surjective on sections, so the
two images coincide open by open. -/
theorem ofHom_eq_of_iso {A B : X.Modules} {φ : A ⟶ F} {ψ : B ⟶ F} [Mono φ] [Mono ψ]
    (e : A ≅ B) (he : e.hom ≫ ψ = φ) : ofHom φ = ofHom ψ := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
  obtain ⟨V⟩ := V
  have hcomp : ∀ a : Γ(A, V),
      (ψ.val.app (op V)).hom ((e.hom.val.app (op V)).hom a) = (φ.val.app (op V)).hom a :=
    fun a => DFunLike.congr_fun (congrArg (fun g : A ⟶ F => (g.val.app (op V)).hom) he) a
  rw [obj_ofHom_of_mono φ V, obj_ofHom_of_mono ψ V]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact ⟨(e.hom.val.app (op V)).hom t, hcomp t⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨a, ha⟩ := ((ConcreteCategory.isIso_iff_bijective (e.hom.app V)).1
      (Scheme.Modules.Hom.isIso_iff_isIso_app.1 (inferInstanceAs (IsIso e.hom)) V)).2 t
    exact ⟨a, (hcomp a).symm.trans (congrArg (ψ.val.app (op V)).hom ha)⟩

/-- **The two results composed, in the shape [Stacks, Tag 01PE] states its conclusion.** -/
theorem restrictTo_ofHom_eq_of_iso (f : Y ⟶ X) [IsOpenImmersion f] {A : Y.Modules}
    {H : X.Modules} (ψ : H ⟶ F) (φ : A ⟶ F.restrict f)
    [Mono φ] [Mono ((Scheme.Modules.restrictFunctor f).map ψ)]
    (e : Scheme.Modules.restrict H f ≅ A)
    (he : e.hom ≫ φ = (Scheme.Modules.restrictFunctor f).map ψ) :
    restrictTo f (ofHom ψ) = ofHom φ :=
  (restrictTo_ofHom f ψ).trans (ofHom_eq_of_iso e he)

end Stacks.AlgebraicGeometry.SubmodulePrimitives

end
