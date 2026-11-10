module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtPowLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorComparisonSurjectivity

/-!
# Hypothesis (2) of [Stacks, Tag 07JN] passes to the exterior powers `Ω^i_{X/S}`

Work in a global crystalline situation `(p, (S, I, γ), X)`.  Hypothesis (2) of
[Stacks, Tag 07JN] on a presheaf of `𝒪_{X/S}`-modules `F` on the small crystalline site
`Cris(X/S)` is that for every morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` whose map on
ambient schemes is a closed immersion the comparison morphism `c_f : f^* F_{T'} ⟶ F_T` is locally
surjective; this is
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.IsSurjectiveComparison`.

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorComparisonSurjectivity.lean` proves
that the condition is stable under the objectwise tensor product, and deduces it for
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` **carrying the condition for `Ω^i_{X/S}` as a hypothesis**.  This file
discharges that hypothesis: the condition is stable under the objectwise **exterior power**, and
`Ω^i_{X/S}` is the `i`-th exterior power of `Ω_{X/S}`, for which the condition is
[Stacks, Tag 07KM] part (2).

The argument is the one the tensor file describes, with wedges in place of pure tensors.  The
transition maps of the presheaf of sectionwise exterior powers carry a wedge of sections to the
wedge of their restrictions, so a wedge of `i` generators of the image of `c_f` for `F`, once the
`i` generators are rewritten over a *common* open of `T'`, is itself a generator of the image of
`c_f` for `Ω^i`; and the wedges of the elements of a spanning set span the exterior power.  Two
steps are therefore needed beyond the pair case: the common-open step for an `i`-element family
rather than for a pair, and the spanning statement relative to a *submodule* rather than to the
whole module.

## Main definitions

* `...SmallSite.extPowModules` — the objectwise exterior power of a presheaf of
  `𝒪_{X/S}`-modules, at the spelling of the presheaf of rings at which Mathlib's exterior powers
  of a presheaf of modules are found.  `...SmallSite.crysDifferentialForms S i` is this for
  `Ω_{X/S}`.
* `...SmallSite.CohomologyRestriction.wedgeRestriction` — the wedge of `n` sections of `F_T` over
  an open of `T`, as a section of `(⋀^n F)_T` there.  See the implementation notes for why this is
  a definition rather than a type ascription.

## Main results

* `exteriorPower.ιMulti_mem_of_forall_mem_span` — **the spanning statement relative to a
  submodule**: a wedge of elements of a span lies in every submodule of the exterior power which
  contains the wedges of the elements of the spanning set.  Mathlib's
  `exteriorPower.ιMulti_span_of_span` is the case of a spanning set of the whole module; this is
  that statement transported along `exteriorPower.map` of the inclusion of the span.
* `...SmallSite.CohomologyRestriction.exists_common_open_fmapGenerators_fin` — **the common-open
  step for a finite family**: finitely many generators of the image of the comparison morphism,
  over the same open of `T`, can be written with the same open of `T'` and the same restriction
  morphism.
* `...SmallSite.CohomologyRestriction.wedgeRestriction_mem_fmapSubmodule` — **a wedge of
  sections in the image of `c_f` for `F` is in the image of `c_f` for the exterior power of `F`**,
  over every open of `T`.
* `...SmallSite.CohomologyRestriction.isSurjectiveComparison_extPowModules` — **hypothesis (2) of
  [Stacks, Tag 07JN] passes to an objectwise exterior power.**
* `...SmallSite.CohomologyRestriction.isSurjectiveComparison_crysDifferentialForms` —
  **hypothesis (2) of [Stacks, Tag 07JN] for `Ω^i_{X/S}`, for every `i`, with nothing carried.**
* `...SmallSite.isSurjectiveComparison_tensorDifferentialForms'` — hypothesis (2) for
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` from hypothesis (2) for `F` alone, for every `i`.

## What is and is not proved

**No `@[stacks]` attribute is placed.**  [Stacks, Tag 07KM] part (2) is already proved and tagged
on the big crystalline category, where it is
`Crystalline.GlobalCrystallineSituation.isLocallySurjective_moduleComparison`; what is added here
is the stability of that condition under exterior powers, which is a step inside the proof of
[Stacks, Tag 07LF] and inside the instantiation claim of [Stacks, Tag 07LN], not the content of a
tag.  Placing a tag again would be a second attribute for one result.

The hypotheses of `isSurjectiveComparison_extPowModules`, exactly: hypothesis (2) of
[Stacks, Tag 07JN] for the presheaf whose exterior power is taken, and nothing else.  No
affineness, no quasi-coherence, no surjectivity of the map on points of the ambient schemes, and
no description of the pullback of a presheaf of modules as a tensor product.  The statement
quantifies over *all* morphisms of `Cris(X/S)` which are closed immersions on ambient schemes,
exactly as `IsSurjectiveComparison` does.  `isSurjectiveComparison_crysDifferentialForms` carries
nothing at all, for every `i` including `i = 0` and `i = 1`; in particular the identification
`Ω^1_{X/S} = Ω_{X/S}` is *not* used, and no such identification is needed, because the exterior
power is handled in its own right.

What is **not** proved here, and what [Stacks, Tag 07LF] still needs besides it.

* Hypothesis (1), local quasi-coherence, for `Ω^i_{X/S}` or for `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`.  The
  note at the end of the docstring of
  `Crystalline.GlobalCrystallineSituation.crysDifferentials_satisfiesVanishingHypotheses` in
  `StacksFrontier/AlgebraicGeometry/Crystalline/CrystalDeRhamComplex.lean` says that for `i ≥ 2`
  "neither clause of [Stacks, Tag 07KM]" is available for the higher exterior powers; the
  clause-(2) half of that is what this file supplies, on the small crystalline site.  The
  clause-(1) half — quasi-coherence of `(Ω^i_{X/S})_T` — is untouched, and the statement there is
  on the big crystalline category, so even the clause-(2) half is not literally the declaration
  this file proves.
* The identification of the terms `M(n)` of the complex of [Stacks, Tag 07JN] for
  `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` with `lim_e (M(n)_e ⊗_{D(n)} Ω^i_{D(n)})`, which is what makes
  [Stacks, Tag 07LA] applicable.
* [Stacks, Tag 07LF] itself.

## Implementation notes

The ring of scalars is spelled `CohomologyRestriction.openSectionsRing`, that is
`(structurePresheaf S ⋙ forget₂ CommRingCat RingCat).obj Z` for `Z` the restriction of an object
of `Cris(X/S)` to an open of its ambient scheme, and not `(ringRestriction A).obj V`.  The two are
definitionally equal, but only the first has the syntactic shape `O ⋙ forget₂ CommRingCat RingCat`
that `PresheafOfModules.extPow` and the `CommRing` instance on a ring of sections are found at.
This is the same wall the implementation notes of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorComparisonSurjectivity.lean` record
for the tensor product: across that boundary `rw` and `simp` do not fire, and the identifications
are discharged by `exact` and by `congrArg` chains.  `moduleRestrictionSectionsModule` is the one
instance that has to be supplied by name, because the module structure on
`(moduleRestriction F A).obj V` over the first spelling of the ring is not found by instance
search.

What forced the shape of the file is that `moduleRestriction` is indexed by the presheaf of rings
at the `crisRing` spelling while `PresheafOfModules.extPow` is indexed by the
`structurePresheaf ⋙ forget₂` spelling, so `(moduleRestriction (⋀^n F) A).obj V` is not
type-correct at `implicit` transparency; the identification with
`⋀^n ((moduleRestriction F A).obj V)` is definitional but *costly*, and repeating it inside a
`Submodule.span` induction exhausted the heartbeat budget.
`CohomologyRestriction.wedgeRestriction` exists to pay that cost once: it is
`exteriorPower.ιMulti`, with the crystalline spelling as its declared type.  Every statement
downstream of it is at that spelling, and no statement mentions both.  The family it takes is
written `Fin n → F.obj Z` rather than `Fin n → (moduleRestriction F A).obj V`, so that the `Module`
instance inside the exterior power is the one `extPow` itself uses; with the second spelling the
instances differ and comparing the resulting `Submodule` types does not terminate inside the
budget.

`CohomologyRestriction.map_wedgeRestriction` and
`CohomologyRestriction.moduleFMap_app_wedgeRestriction` are the same lemma —
`extPowModules_map_ιMulti`, itself `ExteriorAlgebra.mapₛₗ_ιMulti` read through
`PresheafOfModules.extPowSections` — at the two spellings the proofs need separately: the
restriction maps of `F_T` and the components of the `f`-map are transition maps of `F`, but neither
is *syntactically* a transition map of `F`.

The rewrite of a generator of the image of an `f`-map over a smaller object is
`...SmallSite.CohomologyRestriction.map_app_eq_map_app_map` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorComparisonSurjectivity.lean`.  The
private `PresheafOfModules.mem_imageSieve_*_ofRingPresheaf` trio likewise repeats
`PresheafOfModules.mem_imageSieve_zero`, `mem_imageSieve_add` and `mem_imageSieve_smul` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtPowLocallySurjective`, with the one change that
makes them usable here: the presheaf of rings is an arbitrary `Cᵒᵖ ⥤ RingCat` rather than one of
the shape `O ⋙ forget₂ CommRingCat RingCat`, which `ringRestriction` is not.  The trio
of `ExtPowLocallySurjective` does not need the commutative shape and could be stated at this
generality, which would make these four redundant.
`exteriorPower.ιMulti_mem_of_forall_mem_span` is pure linear algebra and its proper home is
`StacksFrontier/LinearAlgebra/ExteriorPower/`, beside `ExteriorAlgebra.powMapₛₗ_ιMulti`.

## References

* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07LN](https://stacks.math.columbia.edu/tag/07LN)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace exteriorPower

/-- **A wedge of elements of a span lies in any submodule of the exterior power containing the
wedges of the elements of the spanning set.**

Mathlib's `exteriorPower.ιMulti_span_of_span` is the case of a set spanning the *whole* module:
the wedges of its elements then span the whole exterior power.  Relative to a submodule
`N = span R s` the same statement is obtained by applying it inside `N`, where the preimage of `s`
spans everything (`Submodule.span_setOfPred_mem_eq_top`), and pushing the conclusion forward along
`exteriorPower.map n N.subtype`, which carries a wedge to the wedge of the images
(`exteriorPower.map_apply_ιMulti`).

This is the exterior counterpart of the pure module theory that the tensor argument needs, where
the corresponding statement is `Submodule.map₂_span_span`. -/
theorem ιMulti_mem_of_forall_mem_span {R : Type u} [CommRing R] {X : Type u}
    [AddCommGroup X] [Module R X] (n : ℕ) (s : Set X) (T : Submodule R (⋀[R]^n X))
    (hT : ∀ b : Fin n → X, (∀ k, b k ∈ s) → ιMulti R n b ∈ T)
    (y : Fin n → X) (hy : ∀ k, y k ∈ Submodule.span R s) :
    ιMulti R n y ∈ T := by
  have hmem : ιMulti R n (fun k ↦ (⟨y k, hy k⟩ : Submodule.span R s)) ∈
      Submodule.span R (ιMulti R n ''
        {b : Fin n → Submodule.span R s |
          Set.range b ⊆ {z : Submodule.span R s | (z : X) ∈ s}}) := by
    rw [ιMulti_span_of_span R n (Submodule.span R s) Submodule.span_setOfPred_mem_eq_top]
    exact Submodule.mem_top
  have hle : Submodule.map (map n (Submodule.span R s).subtype)
      (Submodule.span R (ιMulti R n ''
        {b : Fin n → Submodule.span R s |
          Set.range b ⊆ {z : Submodule.span R s | (z : X) ∈ s}})) ≤ T := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    rw [map_apply_ιMulti]
    exact hT _ fun k ↦ hb (Set.mem_range_self k)
  have h := hle (Submodule.mem_map_of_mem hmem)
  rw [map_apply_ιMulti] at h
  exact h

end exteriorPower

namespace PresheafOfModules

section ImageSieveOps

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {P Q : PresheafOfModules.{u} R} (α : P ⟶ Q)

/-- Membership in the image sieve of a morphism of presheaves of modules, at the spelling a
presheaf of modules provides for its own sections. -/
private theorem mem_imageSieve_of_app_eq_ofRingPresheaf {U : C} (y : Q.obj (op U)) {V : C}
    (i : V ⟶ U) (z : P.obj (op V)) (h : α.app (op V) z = Q.map i.op y) :
    Presheaf.imageSieve ((toPresheaf R).map α) y i := ⟨z, h⟩

/-- The local lift supplied by membership in the image sieve of a morphism of presheaves of
modules, at the spelling a presheaf of modules provides for its own sections. -/
private theorem exists_app_eq_of_mem_imageSieve_ofRingPresheaf {U : C} (y : Q.obj (op U)) {V : C}
    (i : V ⟶ U) (hi : Presheaf.imageSieve ((toPresheaf R).map α) y i) :
    ∃ z : P.obj (op V), α.app (op V) z = Q.map i.op y := hi

/-- Zero lifts along a morphism of presheaves of modules, along every arrow. -/
private theorem mem_imageSieve_zero_ofRingPresheaf {U V : C} (i : V ⟶ U) :
    Presheaf.imageSieve ((toPresheaf R).map α) (0 : Q.obj (op U)) i :=
  mem_imageSieve_of_app_eq_ofRingPresheaf α 0 i 0
    ((map_zero (α.app (op V)).hom).trans (map_zero (Q.restrictₛₗ i.op)).symm)

/-- A sum of two sections liftable along one arrow is liftable along it. -/
private theorem mem_imageSieve_add_ofRingPresheaf {U : C} (y y' : Q.obj (op U)) {V : C}
    (i : V ⟶ U) (h : Presheaf.imageSieve ((toPresheaf R).map α) y i)
    (h' : Presheaf.imageSieve ((toPresheaf R).map α) y' i) :
    Presheaf.imageSieve ((toPresheaf R).map α) (y + y') i := by
  obtain ⟨z, hz⟩ := exists_app_eq_of_mem_imageSieve_ofRingPresheaf α y i h
  obtain ⟨z', hz'⟩ := exists_app_eq_of_mem_imageSieve_ofRingPresheaf α y' i h'
  refine mem_imageSieve_of_app_eq_ofRingPresheaf α (y + y') i (z + z') ?_
  exact (map_add (α.app (op V)).hom z z').trans
    ((congrArg₂ (· + ·) hz hz').trans (map_add (Q.restrictₛₗ i.op) y y').symm)

/-- A scalar multiple of a section liftable along one arrow is liftable along it. -/
private theorem mem_imageSieve_smul_ofRingPresheaf {U : C} (y : Q.obj (op U)) {V : C}
    (i : V ⟶ U) (r : R.obj (op U))
    (h : Presheaf.imageSieve ((toPresheaf R).map α) y i) :
    Presheaf.imageSieve ((toPresheaf R).map α) (r • y) i := by
  obtain ⟨z, hz⟩ := exists_app_eq_of_mem_imageSieve_ofRingPresheaf α y i h
  refine mem_imageSieve_of_app_eq_ofRingPresheaf α (r • y) i (R.map i.op r • z) ?_
  exact (map_smul (α.app (op V)).hom (R.map i.op r) z).trans
    ((congrArg (fun w ↦ R.map i.op r • w) hz).trans (Q.map_smul i.op r y).symm)

end ImageSieveOps

end PresheafOfModules

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- The objectwise `n`-th exterior power of a presheaf of `𝒪_{X/S}`-modules on the small
crystalline site, at the spelling of the presheaf of rings at which Mathlib's exterior powers of a
presheaf of modules are found.  It is `...SmallSite.crysDifferentialForms` with the presheaf whose
power is taken left general. -/
abbrev extPowModules
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (n : ℕ) :
    PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  PresheafOfModules.extPow n M

variable (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

/-- **The transition maps of an objectwise exterior power carry a wedge of sections to the wedge
of their images.**  This is `ExteriorAlgebra.mapₛₗ_ιMulti` — base change of an exterior algebra
respects the ordered product of a family — read through the sectionwise identification
`PresheafOfModules.extPowSections`. -/
theorem extPowModules_map_ιMulti (n : ℕ) {X Y : (CrystallineThickening S)ᵒᵖ} (X' : X ⟶ Y)
    (b : Fin n → M.obj X) :
    (extPowModules M n).map X'
        (exteriorPower.ιMulti
          ((structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj X) n b :
          (extPowModules M n).obj X) =
      (exteriorPower.ιMulti
          ((structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj Y) n
          fun k ↦ M.map X' (b k) :
        (extPowModules M n).obj Y) := by
  refine (PresheafOfModules.extPowSections n M Y).injective (Subtype.ext ?_)
  refine (PresheafOfModules.extPowSections_map n M X' _).trans ?_
  exact ExteriorAlgebra.mapₛₗ_ιMulti _ (M.restrictₛₗ X') n b

namespace CohomologyRestriction

variable {A B : CrystallineThickening S} (g : A ⟶ B)

/-- The ring of sections of `𝒪_{X/S}` over the restriction of an object of `Cris(X/S)` to an open
of its ambient scheme, at the spelling `O ⋙ forget₂ CommRingCat RingCat` which carries the
`CommRing` instance on a ring of sections and at which the exterior powers of a presheaf of
modules are formed.  It is `(ringRestriction A).obj V` definitionally. -/
abbrev openSectionsRing (A : CrystallineThickening S)
    (V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ) : Type u :=
  (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj
    ((CrystallineThickening.restrictOpenFunctor A).op.obj V)

/-- **The sections of a presheaf of `𝒪_{X/S}`-modules over the restriction of an object to an open
of its ambient scheme, as a module over the scalars spelled `openSectionsRing`.**  The two rings
are the same ring, but `(moduleRestriction M A).obj V` does not unfold to `M.obj Z` during
instance search, so the instance has to be supplied by name, as it is for
`Crystalline.crysDifferentialsRestrictionModule`. -/
instance moduleRestrictionSectionsModule (A : CrystallineThickening S)
    (V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    Module (openSectionsRing A V) ((moduleRestriction M A).obj V) :=
  inferInstanceAs (Module ((structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj
      ((CrystallineThickening.restrictOpenFunctor A).op.obj V))
    (M.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V)))

/-- **The wedge of `n` sections of `F_T` over an open of `T`, as a section of `(⋀^n F)_T` over
that open.**  It is `exteriorPower.ιMulti` of the sections of `F_T`; what this definition adds is
that its *type* is spelled `(moduleRestriction (⋀^n F) A).obj V` rather than
`⋀^n (moduleRestriction F A).obj V`.  Those two are definitionally equal, but checking it is
expensive (`moduleRestriction` is indexed by the presheaf of rings at the `crisRing` spelling and
the exterior power by the `structurePresheaf ⋙ forget₂` spelling), so every statement below is
made at this spelling and the check is paid once, here. -/
def wedgeRestriction (n : ℕ) (A : CrystallineThickening S)
    (V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (b : Fin n → M.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V)) :
    (moduleRestriction (extPowModules M n) A).obj V :=
  exteriorPower.ιMulti (openSectionsRing A V) n b

/-- **The wedges of `n` sections of `F_T` over an open span the sections of `(⋀^n F)_T` there.**
This is `exteriorPower.ιMulti_span` at the spelling of `wedgeRestriction`. -/
theorem span_range_wedgeRestriction (n : ℕ) (A : CrystallineThickening S)
    (V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    Submodule.span (openSectionsRing A V) (Set.range (wedgeRestriction M n A V)) = ⊤ :=
  exteriorPower.ιMulti_span (openSectionsRing A V) n
    (M.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V))

/-- **The restriction maps of `(⋀^n F)_T` carry a wedge of sections to the wedge of their
restrictions.**  `extPowModules_map_ιMulti` at the restriction spelling, which is needed
separately: a restriction map of `F_T` is a transition map of `F`, but not syntactically one. -/
theorem map_wedgeRestriction (n : ℕ) (A : CrystallineThickening S)
    {V V' : (A.obj.thickening.target.scheme.Opens)ᵒᵖ} (h : V ⟶ V')
    (b : Fin n → (moduleRestriction M A).obj V) :
    (moduleRestriction (extPowModules M n) A).map h (wedgeRestriction M n A V b) =
      wedgeRestriction M n A V' fun k ↦ (moduleRestriction M A).map h (b k) :=
  extPowModules_map_ιMulti M n ((CrystallineThickening.restrictOpenFunctor A).op.map h) b

/-- **The `f`-map of `⋀^n F` carries a wedge of sections to the wedge of the images under the
`f`-map of `F`.**  `extPowModules_map_ιMulti` at the `f`-map spelling, which is needed
separately. -/
theorem moduleFMap_app_wedgeRestriction (n : ℕ)
    (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ)
    (s : Fin n → (moduleRestriction M B).obj W) :
    (moduleFMap (extPowModules M n) g).app W (wedgeRestriction M n B W s) =
      wedgeRestriction M n A (op ((Opens.map g.hom.targetHom.hom.base).obj W.unop))
        fun k ↦ (moduleFMap M g).app W (s k) :=
  extPowModules_map_ιMulti M n (CrystallineThickening.restrictOpenMap g W.unop).op s

/-- **Finitely many generators of the image of the comparison morphism of a presheaf of modules,
over the same open `W` of `T`, can be written over a common open of `T'`.**

A generator of the image of `c_f` over `W` is the restriction to `W` of a value of the `f`-map
over some open `W₁` of `T'` with `W ⊆ f^{-1}W₁`.  Given finitely many such, an induction on the
size of the family intersects the opens one at a time: the intersection again has `W` inside its
preimage, and the naturality of the `f`-map rewrites each generator over it; the restriction
morphisms that appear agree because morphisms of a lattice of opens are unique.

This is `exists_common_open_fmapGenerators` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/TensorComparisonSurjectivity.lean` for a
`Fin n`-indexed family instead of a pair, and for one presheaf instead of two; the empty family is
handled by `W = T'` itself. -/
theorem exists_common_open_fmapGenerators_fin {V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ}
    {n : ℕ} (x : Fin n → (moduleRestriction M A).obj V)
    (hx : ∀ k, x k ∈ PresheafOfModules.pushforwardGenerators (restrictionFMap (crisRing S) g)
      (moduleFMap M g) V) :
    ∃ (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ)
      (h : op ((Opens.map g.hom.targetHom.hom.base).obj W.unop) ⟶ V)
      (s : Fin n → (moduleRestriction M B).obj W),
      ∀ k, x k = (moduleRestriction M A).map h ((moduleFMap M g).app W (s k)) := by
  induction n with
  | zero => exact ⟨op ⊤, (homOfLE fun _ _ ↦ trivial).op, Fin.elim0, fun k ↦ k.elim0⟩
  | succ n ih =>
      obtain ⟨W', h', s', hs'⟩ := ih (fun k ↦ x k.succ) fun k ↦ hx k.succ
      obtain ⟨W₀, h₀, s₀, hs₀⟩ := hx 0
      refine ⟨op (W'.unop ⊓ W₀.unop),
        (homOfLE fun _ hz ↦ ⟨leOfHom h'.unop hz, leOfHom h₀.unop hz⟩).op,
        Fin.cons ((moduleRestriction M B).map
            (homOfLE (inf_le_right (a := W'.unop) (b := W₀.unop))).op s₀)
          (fun k ↦ (moduleRestriction M B).map
            (homOfLE (inf_le_left (a := W'.unop) (b := W₀.unop))).op (s' k)), ?_⟩
      refine Fin.cases ?_ ?_
      · exact hs₀.trans (map_app_eq_map_app_map (restrictionFMap (crisRing S) g)
          (moduleFMap M g) _ _ h₀ (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) s₀)
      · intro k
        exact (hs' k).trans (map_app_eq_map_app_map (restrictionFMap (crisRing S) g)
          (moduleFMap M g) _ _ h' (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) (s' k))

/-- **A wedge of sections in the image of `c_f` for `F` is in the image of `c_f` for the `n`-th
exterior power of `F`**, over every open of the ambient scheme of the source.

Both images are the submodules generated by the values of the respective `f`-maps, by
`range_moduleComparison_app_eq_fmapSubmodule`.  A wedge of `n` generators written over a common
open of `T'` — `exists_common_open_fmapGenerators_fin` — *is* a value of the `f`-map of the
exterior power, at the wedge of the `n` sections, because the transition maps of an objectwise
exterior power carry a wedge to the wedge of the images; and a wedge of elements of a span lies in
every submodule containing the wedges of the spanning set, which is
`exteriorPower.ιMulti_mem_of_forall_mem_span`. -/
theorem wedgeRestriction_mem_fmapSubmodule (n : ℕ)
    {V : (A.obj.thickening.target.scheme.Opens)ᵒᵖ}
    (b : Fin n → (moduleRestriction M A).obj V)
    (hb : ∀ k, b k ∈ (fmapSubmodule M g).obj V) :
    wedgeRestriction M n A V b ∈ (fmapSubmodule (extPowModules M n) g).obj V := by
  refine exteriorPower.ιMulti_mem_of_forall_mem_span
    (R := openSectionsRing A V)
    (X := M.obj ((CrystallineThickening.restrictOpenFunctor A).op.obj V))
    n (PresheafOfModules.pushforwardGenerators (restrictionFMap (crisRing S) g)
      (moduleFMap M g) V)
    ((fmapSubmodule (extPowModules M n) g).obj V) ?_ b hb
  intro a ha
  obtain ⟨W, h, s, hs⟩ := exists_common_open_fmapGenerators_fin M g a ha
  have key : wedgeRestriction M n A V a =
      (moduleRestriction (extPowModules M n) A).map h
        ((moduleFMap (extPowModules M n) g).app W (wedgeRestriction M n B W s)) :=
    (congrArg (wedgeRestriction M n A V) (funext hs)).trans
      ((map_wedgeRestriction M n A h fun k ↦ (moduleFMap M g).app W (s k)).symm.trans
        (congrArg (fun y ↦ (moduleRestriction (extPowModules M n) A).map h y)
          (moduleFMap_app_wedgeRestriction M g n W s).symm))
  exact Eq.mpr
    (congrArg (fun y ↦ y ∈ (fmapSubmodule (extPowModules M n) g).obj V) key)
    ((fmapSubmodule (extPowModules M n) g).map_mem h
      (PresheafOfModules.appₛₗ_mem_generatedSubmodule (restrictionFMap (crisRing S) g)
        (moduleFMap (extPowModules M n) g) W _))

/-- **A wedge of sections of `F_T` lifts along the comparison morphism of `⋀^n F` on a covering
of the open it lives over.**  Each of the `n` factors lifts along the comparison morphism of `F` on
a covering, by hypothesis (2) for `F`; the `n` coverings have a common covering refinement
(`CategoryTheory.GrothendieckTopology.exists_mem_forall_fin`), and over a member of it the wedge of
the `n` restrictions is in the image of the comparison morphism of `⋀^n F`, by
`wedgeRestriction_mem_fmapSubmodule` and
`range_moduleComparison_app_eq_fmapSubmodule`. -/
theorem imageSieve_moduleComparison_wedgeRestriction_mem (n : ℕ)
    (hM : IsSurjectiveComparison M) (hg : IsClosedImmersion g.hom.targetHom.hom)
    (V : A.obj.thickening.target.scheme.Opens)
    (b : Fin n → (moduleRestriction M A).obj (op V)) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf (ringRestriction A)).map
        (moduleComparison (extPowModules M n) g)) (wedgeRestriction M n A (op V) b) ∈
      Opens.grothendieckTopology A.obj.thickening.target.scheme V := by
  have := hM g hg
  obtain ⟨T, hT, hTle⟩ :=
    (Opens.grothendieckTopology A.obj.thickening.target.scheme).exists_mem_forall_fin
      (U := V) _ fun k ↦ Presheaf.imageSieve_mem
        (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        ((PresheafOfModules.toPresheaf (ringRestriction A)).map (moduleComparison M g))
        (U := op V) (b k)
  refine (Opens.grothendieckTopology A.obj.thickening.target.scheme).superset_covering
    (fun V' i hi ↦ ?_) hT
  have hb : ∀ k, (moduleRestriction M A).map i.op (b k) ∈
      (fmapSubmodule M g).obj (op V') := fun k ↦
    (range_moduleComparison_app_eq_fmapSubmodule M g (op V')).le (hTle i hi k)
  obtain ⟨w, hw⟩ := (range_moduleComparison_app_eq_fmapSubmodule (extPowModules M n) g
    (op V')).ge (wedgeRestriction_mem_fmapSubmodule M g n
      (fun k ↦ (moduleRestriction M A).map i.op (b k)) hb)
  exact ⟨w, hw.trans (map_wedgeRestriction M n A i.op b).symm⟩

/-- **Every `𝒪_T`-combination of wedges of sections of `F_T` lifts along the comparison morphism
of `⋀^n F` on a covering.**  The wedges are
`imageSieve_moduleComparison_wedgeRestriction_mem`, and liftability on a covering is stable under
the module operations. -/
theorem imageSieve_moduleComparison_extPowModules_mem_of_mem_span (n : ℕ)
    (hM : IsSurjectiveComparison M) (hg : IsClosedImmersion g.hom.targetHom.hom)
    (V : A.obj.thickening.target.scheme.Opens)
    (t : (moduleRestriction (extPowModules M n) A).obj (op V))
    (ht : t ∈ Submodule.span (openSectionsRing A (op V))
      (Set.range (wedgeRestriction M n A (op V)))) :
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf (ringRestriction A)).map
        (moduleComparison (extPowModules M n) g)) t ∈
      Opens.grothendieckTopology A.obj.thickening.target.scheme V := by
  set J := Opens.grothendieckTopology A.obj.thickening.target.scheme
  induction ht using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      exact imageSieve_moduleComparison_wedgeRestriction_mem M g n hM hg V b
  | zero =>
      exact J.superset_covering
        (fun V' i _ ↦ PresheafOfModules.mem_imageSieve_zero_ofRingPresheaf _ i) (J.top_mem V)
  | add z₁ z₂ _ _ ih₁ ih₂ =>
      exact J.superset_covering (fun V' i (hi : _ ∧ _) ↦
        PresheafOfModules.mem_imageSieve_add_ofRingPresheaf _ _ _ i hi.1 hi.2)
        (J.intersection_covering ih₁ ih₂)
  | smul r z₁ _ ih₁ =>
      exact J.superset_covering (fun V' i hi ↦
        PresheafOfModules.mem_imageSieve_smul_ofRingPresheaf _ _ i r hi) ih₁

/-- **Hypothesis (2) of [Stacks, Tag 07JN] passes to an objectwise exterior power.**  If the
comparison morphisms `c_f` of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` are locally
surjective along every morphism whose map on ambient schemes is a closed immersion, then so are
the comparison morphisms of each of its objectwise exterior powers.

A section of `(⋀^n F)_T` over an open is an `𝒪_T`-combination of wedges of sections of `F_T`
(`span_range_wedgeRestriction`); each of the `n` factors of each wedge is, on the members of an
open covering, in the image of the comparison morphism of `F`, and on the common refinement of
those `n` coverings the wedge is then in the image of the comparison morphism of the exterior
power.  Liftability is stable under the module operations, which is what carries the conclusion
from the wedges to their combinations.  The two steps are
`imageSieve_moduleComparison_wedgeRestriction_mem` and
`imageSieve_moduleComparison_extPowModules_mem_of_mem_span`.

No hypothesis beyond hypothesis (2) for `F` is used: in particular the map on ambient schemes is
not assumed surjective on points, and nothing is assumed about quasi-coherence or affineness. -/
theorem isSurjectiveComparison_extPowModules (n : ℕ) (hM : IsSurjectiveComparison M) :
    IsSurjectiveComparison (extPowModules M n) := fun {A _} g hg ↦
  ⟨fun {V} z ↦ imageSieve_moduleComparison_extPowModules_mem_of_mem_span M g n hM hg V z
    ((span_range_wedgeRestriction M n A (op V)).ge Submodule.mem_top)⟩

/-- **Hypothesis (2) of [Stacks, Tag 07JN] for `Ω^i_{X/S}`, for every `i`, with nothing
carried.**  The comparison morphism `c_f : f^*(Ω^i_{X/S})_{T'} ⟶ (Ω^i_{X/S})_T` of the small-site
presheaf of crystalline `i`-forms is locally surjective along every morphism of `Cris(X/S)` whose
map on ambient schemes is a closed immersion.

This is the hypothesis `hΩ` of
`...SmallSite.isSurjectiveComparison_tensorDifferentialForms`, discharged: `Ω^i_{X/S}` is the
`i`-th objectwise exterior power of `Ω_{X/S}` by definition, hypothesis (2) passes to an exterior
power by `isSurjectiveComparison_extPowModules`, and hypothesis (2) for `Ω_{X/S}` itself is
`isSurjectiveComparison_crysDifferentials`, that is, [Stacks, Tag 07KM] part (2).

**No tag attribute is placed**: [Stacks, Tag 07KM] part (2) is already proved and tagged on the
big crystalline category, as
`Crystalline.GlobalCrystallineSituation.isLocallySurjective_moduleComparison`. -/
theorem isSurjectiveComparison_crysDifferentialForms (i : ℕ) :
    IsSurjectiveComparison (crysDifferentialForms S i) :=
  isSurjectiveComparison_extPowModules (crysDifferentials S) i
    isSurjectiveComparison_crysDifferentials

end CohomologyRestriction

/-- **Hypothesis (2) of [Stacks, Tag 07JN] for `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`, from hypothesis (2) for
`F` alone**, for every `i`.  This is the surjectivity half of the first step of the proof of
[Stacks, Tag 07LF]: that `ℋ = F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` satisfies the hypotheses of
[Stacks, Tag 07JN] when `F` does.

It is `...SmallSite.isSurjectiveComparison_tensorDifferentialForms` with its hypothesis `hΩ`
discharged by `CohomologyRestriction.isSurjectiveComparison_crysDifferentialForms`.  The only
hypothesis is hypothesis (2) of [Stacks, Tag 07JN] on `F`. -/
theorem isSurjectiveComparison_tensorDifferentialForms'
    (M : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (i : ℕ) (hM : CohomologyRestriction.IsSurjectiveComparison M) :
    CohomologyRestriction.IsSurjectiveComparison (tensorDifferentialForms M i) :=
  isSurjectiveComparison_tensorDifferentialForms M i hM
    (CohomologyRestriction.isSurjectiveComparison_crysDifferentialForms i)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
