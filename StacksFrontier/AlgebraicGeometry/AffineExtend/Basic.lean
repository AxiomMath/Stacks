module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.SubmoduleAscendingChain
public import StacksFrontier.AlgebraicGeometry.SubmoduleImageRestrict.Basic
public import StacksFrontier.AlgebraicGeometry.SubmodulePrimitives.Compose
public import StacksFrontier.AlgebraicGeometry.SubmoduleRelativeLocality.Basic
public import StacksFrontier.AlgebraicGeometry.AffineSubsheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.QuasiCoherentExtension

/-!
# The affine case of Tag 01PF in the form its induction consumes

The affine case proved in
`StacksFrontier/AlgebraicGeometry/AffineSubsheaf/Basic.lean` produces, on an affine
scheme, a finite type quasi-coherent submodule of `F` whose sections over the opens inside a
quasi-compact open `W` are **all** of the sections of `F`. The induction of [Stacks, Tag 01PF]
needs the version that **prescribes** the submodule over `W`: given a finite type quasi-coherent
submodule of `F|_W`, a finite type quasi-coherent submodule of `F` restricting to it. That is
strictly stronger — the statement there is the special case where the prescribed submodule is
the whole of `F|_W` — and it is what this file proves.

## Main results

* `exists_isFiniteType_submodule_restrictTo_eq`: **the affine case of [Stacks, Tag 01PF] in the
  prescribing form.** On an affine scheme, a quasi-coherent submodule of `F` whose restriction to
  a quasi-compact open `W` is of finite type extends to a *globally* finite type quasi-coherent
  submodule of `F` with the **same restriction to `W`**.
* `exists_generatingSections_of_restrict_isFiniteType`: a module of finite type over an open has
  finitely many generating sections on an open **of the ambient scheme** near every point of that
  open. This is the hypothesis shape [Stacks, Tag 01PB] relative to an open is stated in, and the
  bridge that was missing between it and `SheafOfModules.IsFiniteType` on the open subscheme.
* `ofHom_submoduleι`: the sectionwise image of the inclusion of a concrete submodule is that
  submodule, so `Stacks.AlgebraicGeometry.SubmodulePrimitives.ofHom` is a retraction of the
  inclusion.
* `restrictTo_eq_of_obj_eq`: the converse of
  `Stacks.AlgebraicGeometry.SubmoduleAgree.obj_eq_of_restrictTo_eq`.

## Why the stronger form needs no new mathematics

The route is the source's own, and it is the composition the tree already named: [Stacks, Tag
01PE] extends the given submodule to a quasi-coherent — not finite type — submodule `M` of `F`
with the same restriction to `W`, the affine case above is applied **to `M` rather than to `F`**
(where its finiteness hypothesis is exactly finite type of the given submodule, by [Stacks, Tag
01PB] relative to `W`), and
`Stacks.AlgebraicGeometry.SubmodulePrimitives.compose_obj_of_eq_top` carries its conclusion — `P`
is all of `M` over the opens inside `W` — back to an equality of submodules of `F`. The three
ingredients this needs (the subobject-versus-submodule spelling of [Stacks, Tag
01PE], the co-restriction, and the composition of submodules) are all in the library.

## Implementation notes

**`Mono` for the inclusion of a concrete submodule is not found by instance search at the
`AlgebraicGeometry.Scheme.Modules` spelling, and the instance declared here does not fix that.**
Mathlib's `SheafOfModules.Submodule.instMonoι` is stated for the `SheafOfModules` category, whose
`Category` instance is not the one `X.Modules` carries, so it does not apply; `mono_submoduleι`
supplies the missing one through faithfulness of the forgetful functor to presheaves of modules,
and a bare `inferInstance` at goal `Mono (submoduleι N)` **does** find it. It is nevertheless
**not** found by the `[Mono f]` binder of an imported lemma applied to that same term — this
holds for `Stacks.AlgebraicGeometry.SubmodulePrimitives.obj_ofHom_of_mono` and for `Subobject.mk`, with
`submoduleι` declared as a `def` and as an `abbrev`, and with
`attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules` in force. Every use below
therefore passes the instance **positionally**, and `toSubobjectIso` and
`toSubobjectIso_hom_comp` exist so that it is passed once each rather than at every call site.

For the subobject itself, routing through
`SheafOfModules.Submodule.toSubobject`
(StacksFrontier/AlgebraicGeometry/Cohomology/Coherent/SubmoduleAscendingChain.lean:89) elaborates
here, and that declaration is used directly. The positional passing is needed for the other
lemmas named above.

The hypothesis of the affine case is deliberately **not** stated as a `have` before it is
discharged: writing `Module.Finite Γ(X, Z) Γ(M.toSheafOfModules, Z)` in this file fails to
synthesize `Module Γ(X, Z) Γ(M.toSheafOfModules, Z)`, which is the `instance_reducible` problem
recorded in `StacksFrontier/AlgebraicGeometry/AffineSubsheaf/Basic.lean`; passing the proof inline
takes the expected type from the lemma, which was elaborated in the file that carries that
attribute.

`exists_generatingSections_of_restrict_isFiniteType` is the body of
`AlgebraicGeometry.Modules.isFiniteType_of_restrict`'s transport step, extracted: the generating
sections `SheafOfModules.IsFiniteType` provides live on opens of the open subscheme `W`, and the
three isomorphisms (`AlgebraicGeometry.Modules.restrictCompIso`,
`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSelf` and
`Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsRestrict` along
`AlgebraicGeometry.Scheme.Hom.isoImage`) move them to the image open in `X`. The index type is
preserved by `rfl` at every step, so finiteness transfers with no argument.

## What this does not do, and no stacks attribute

**No stacks attribute is attached, and none is earned.** This is the affine case of
[Stacks, Tag 01PF], i.e. the `n = 1` reduction of its proof, and not the lemma: the lemma is
stated for a quasi-compact and quasi-separated scheme and this carries `[IsAffine X]`, which that
statement does not grant. What remains of [Stacks, Tag 01PF] is the induction over a finite
affine covering — the two-member step `X = U ∪ V` with `V` affine, which applies this result on
the open subscheme `V` and glues with
`Stacks.AlgebraicGeometry.SubmoduleRelativeLocality.isQuasicoherent_glue_pair` and its
finite-type namesake, and the recursion on the number of members.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01PFAffineExtend

open Stacks.AlgebraicGeometry.SubmodulePrimitives Stacks.AlgebraicGeometry.SubmoduleRestrict

variable {X : Scheme.{u}} {F : X.Modules}

/-! ### Finite type over an open, read as generating sections on opens of the ambient scheme -/

/-- **A module of finite type over an open has finitely many generating sections, on an open of
the ambient scheme, near every point of that open.** -/
theorem exists_generatingSections_of_restrict_isFiniteType (M : X.Modules) (W : X.Opens)
    (hft : (M.restrict W.ι).IsFiniteType) {x : X} (hx : x ∈ W) :
    ∃ (Z : X.Opens) (_ : x ∈ Z) (σ : (M.restrict Z.ι).GeneratingSections), Finite σ.I := by
  have := hft
  obtain ⟨V, hxV, σ, hσ⟩ :=
    CoherentFinite.exists_generatingSections_of_isFiniteType (M.restrict W.ι)
      (⟨x, hx⟩ : W.toScheme)
  refine ⟨W.ι ''ᵁ V, ⟨⟨x, hx⟩, hxV, rfl⟩, ?_, ?_⟩
  · exact SheafOfModules.GeneratingSections.equivOfIso
      (CoherentTFAE.restrictIsoSelf (W.ι.isoImage V).symm (M.restrict (W.ι ''ᵁ V).ι))
      (CoherentTFAE.generatingSectionsRestrict (W.ι.isoImage V).inv
        (SheafOfModules.GeneratingSections.equivOfIso
          (AlgebraicGeometry.Modules.restrictCompIso M W.ι V.ι (W.ι ''ᵁ V).ι
            (W.ι.isoImage V).hom (Scheme.Hom.isoImage_hom_ι W.ι V).symm) σ))
  · exact hσ

/-! ### The inclusion of a concrete submodule, and its subobject -/

/-- The inclusion of a concrete submodule into the ambient module, at the
`AlgebraicGeometry.Scheme.Modules` spelling. -/
def submoduleι (N : F.Submodule) : (N.toSheafOfModules : X.Modules) ⟶ F := N.ι

/-- **The inclusion of a concrete submodule is a monomorphism of `𝒪_X`-modules.** See the
implementation notes: this instance is found by `inferInstance` and not by an imported lemma's
`[Mono f]` binder, so every use below passes it positionally. -/
instance mono_submoduleι (N : F.Submodule) : Mono (submoduleι N) :=
  Functor.mono_of_mono_map (Scheme.Modules.toPresheafOfModules X)
    (inferInstanceAs (Mono N.toSubmodule.ι))

/-- The underlying module of `N.toSubobject` is the module of `N`. -/
def toSubobjectIso (N : F.Submodule) :
    ((N.toSubobject : Subobject F) : X.Modules) ≅ (N.toSheafOfModules : X.Modules) :=
  @Subobject.underlyingIso _ _ _ _ (submoduleι N) (mono_submoduleι N)

/-- The comparison of `N.toSubobject` with `N` carries the inclusion to the inclusion. -/
theorem toSubobjectIso_hom_comp (N : F.Submodule) :
    (toSubobjectIso N).hom ≫ submoduleι N = (N.toSubobject).arrow :=
  @Subobject.underlyingIso_hom_comp_eq_mk _ _ _ _ (submoduleι N) (mono_submoduleι N)

/-! ### Two identities relating the primitives -/

/-- **The sectionwise image of the inclusion of a concrete submodule is that submodule.** -/
theorem ofHom_submoduleι (N : F.Submodule) : ofHom (submoduleι N) = N := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  obtain ⟨U⟩ := U
  exact (@obj_ofHom_of_mono X F _ (submoduleι N) (mono_submoduleι N) U).trans
    (Submodule.range_subtype _)

/-- **Equal sections over the opens inside `W` give equal restrictions to `W`.** The converse of
`Stacks.AlgebraicGeometry.SubmoduleAgree.obj_eq_of_restrictTo_eq`. -/
theorem restrictTo_eq_of_obj_eq {W : X.Opens} {N M : F.Submodule}
    (h : ∀ Z : X.Opens, Z ≤ W → N.obj (op Z) = M.obj (op Z)) :
    restrictTo W.ι N = restrictTo W.ι M := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V => ?_)
  obtain ⟨V⟩ := V
  have key := h (W.ι ''ᵁ V) (W.ι_image_le V)
  refine SetLike.ext fun x => (mem_restrictTo_iff W.ι N x).trans
    (Iff.trans ?_ (mem_restrictTo_iff W.ι M x).symm)
  rw [key]

/-! ### The quasi-coherent extension, in the concrete-submodule spelling -/

/-- **[Stacks, Tag 01PE] for concrete submodules.** A concrete submodule of `F` whose restriction
to a quasi-compact open `W` is quasi-coherent has a *quasi-coherent* concrete submodule of `F`
with the same restriction to `W`.

Mathlib-side 01PE is available only in the subobject spelling, and the passage both ways is the
content of `StacksFrontier/AlgebraicGeometry/SubmodulePrimitives/Image.lean` and
`StacksFrontier/AlgebraicGeometry/SubmoduleImageRestrict/Basic.lean`; this is their composition
with it. -/
theorem exists_isQuasicoherent_submodule_restrictTo_eq [F.IsQuasicoherent] {W : X.Opens}
    (hqcW : QuasiCompact W.ι) (N₀ : F.Submodule)
    (hqc : ((restrictTo W.ι N₀).toSheafOfModules : W.toScheme.Modules).IsQuasicoherent) :
    ∃ M : F.Submodule, (M.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      restrictTo W.ι M = restrictTo W.ι N₀ := by
  have := hqcW
  obtain ⟨H, hHqc, e, he⟩ := AlgebraicGeometry.exists_quasicoherentSubobject_restrict W.ι F
    ((restrictTo W.ι N₀).toSubobject)
    (SubmoduleRelativeLocality.isQuasicoherent_of_iso
      (toSubobjectIso (restrictTo W.ι N₀)).symm hqc)
  refine ⟨ofSubobject H,
    SubmoduleRelativeLocality.isQuasicoherent_of_iso (ofSubobjectIso H) hHqc, ?_⟩
  have hassoc : (e ≪≫ toSubobjectIso (restrictTo W.ι N₀)).hom ≫ submoduleι (restrictTo W.ι N₀) =
      e.hom ≫ (toSubobjectIso (restrictTo W.ι N₀)).hom ≫ submoduleι (restrictTo W.ι N₀) :=
    Category.assoc _ _ _
  have he₂ : (e ≪≫ toSubobjectIso (restrictTo W.ι N₀)).hom ≫ submoduleι (restrictTo W.ι N₀) =
      (Scheme.Modules.restrictFunctor W.ι).map H.arrow := by
    rw [hassoc, toSubobjectIso_hom_comp]
    exact he
  have hmonoiso : Mono (e ≪≫ toSubobjectIso (restrictTo W.ι N₀)).hom :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom (e ≪≫ toSubobjectIso (restrictTo W.ι N₀)))
  have hmono : Mono ((Scheme.Modules.restrictFunctor W.ι).map H.arrow) := by
    rw [← he₂]
    exact @mono_comp _ _ _ _ _ _ hmonoiso _ (mono_submoduleι _)
  exact (@restrictTo_ofHom_eq_of_iso _ _ _ W.ι _ _ _ H.arrow (submoduleι (restrictTo W.ι N₀))
    (mono_submoduleι _) hmono _ he₂).trans (ofHom_submoduleι _)

/-! ### The affine case, prescribing the submodule over the open -/

/-- **The affine case of [Stacks, Tag 01PF], in the form that prescribes the submodule over the
quasi-compact open.** On an affine scheme, a concrete submodule `N₀` of a quasi-coherent module
`F` whose restriction to a quasi-compact open `W` is quasi-coherent and of finite type extends to
a quasi-coherent submodule of `F` which is of finite type **on the whole of `X`** and has the
same restriction to `W`.

This is strictly stronger than
`Stacks.AlgebraicGeometry.Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on`, which
is the case `N₀ = ⊤`, and it is the form the induction of [Stacks, Tag 01PF] applies on each
affine member of its covering: the agreement hypothesis of the glueing step is, by
`Stacks.AlgebraicGeometry.SubmoduleAgree.agree_pair`, exactly the prescription over the
overlap. -/
theorem exists_isFiniteType_submodule_restrictTo_eq [IsAffine X] [F.IsQuasicoherent]
    {W : X.Opens} (hW : IsCompact (W : Set X)) (hqcW : QuasiCompact W.ι) (N₀ : F.Submodule)
    (hqc : ((restrictTo W.ι N₀).toSheafOfModules : W.toScheme.Modules).IsQuasicoherent)
    (hft : ((restrictTo W.ι N₀).toSheafOfModules : W.toScheme.Modules).IsFiniteType) :
    ∃ N : F.Submodule, (N.toSheafOfModules : X.Modules).IsQuasicoherent ∧
      (N.toSheafOfModules : X.Modules).IsFiniteType ∧
      restrictTo W.ι N = restrictTo W.ι N₀ := by
  obtain ⟨M, hMqc, hMres⟩ := exists_isQuasicoherent_submodule_restrictTo_eq hqcW N₀ hqc
  have hMft : (Scheme.Modules.restrict (M.toSheafOfModules : X.Modules) W.ι).IsFiniteType := by
    rw [← restrictTo_toSheafOfModules W.ι M, hMres]
    exact hft
  have := hMqc
  obtain ⟨P, hPqc, hPft, hPtop⟩ :=
    Tag01PFAffineSubsheaf.exists_isFiniteType_submodule_eq_top_on
      (M.toSheafOfModules : X.Modules) hW
      (fun _ hZ hZW => Tag01PFAffine.finite_sections_le _
        (fun _ hx => exists_generatingSections_of_restrict_isFiniteType _ W hMft hx) hZ hZW)
  refine ⟨compose M P,
    SubmoduleRelativeLocality.isQuasicoherent_of_iso (composeIso M P).symm hPqc,
    AlgebraicGeometry.Modules.isFiniteType_of_iso (composeIso M P).symm hPft, ?_⟩
  refine (restrictTo_eq_of_obj_eq (W := W) fun Z hZ => ?_).trans hMres
  exact compose_obj_of_eq_top M P (hPtop Z hZ)

end Stacks.AlgebraicGeometry.Tag01PFAffineExtend

end
