module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.ElementaryFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.IntermediateFactorization
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.DirectImageInputs

/-!
# The splitting step of the factorization into glueings and squishings

Let `f : X' ⟶ X` be a finite morphism of algebraic schemes over an algebraically closed field
`k` with `𝒪_X ⊂ f_*𝒪_{X'}` and with `f` an isomorphism away from a finite set of points, and let
`𝒜` be a finite quasi-coherent sheaf of `𝒪_X`-algebras with `𝒪_X ⊂ 𝒜 ⊂ f_*𝒪_{X'}`. The proof of
[Stacks, Tag 0C1L] uses such an `𝒜` to split `f` as

`X' ⟶ Spec_X(𝒜) ⟶ X`

and then applies the inductive hypothesis to the two halves. For that the two halves must again
satisfy the hypotheses of the lemma. This file proves that they do: both the lower half
`Spec_X(𝒜) ⟶ X` and the upper half `X' ⟶ Spec_X(𝒜)` satisfy every clause.

## Main results

* `Stacks.GlueSquishFactor.isIso_of_isAffineHom_of_isIso_app` — an affine morphism which is an
  isomorphism on the sections over every affine open contained in an open `U` of the target is
  an isomorphism over `U`.
* `Stacks.GlueSquishFactor.isIso_hom_app_of_isIso_app` — **the squeeze**: over an open on which
  `𝒪_X ⟶ f_*𝒪_{X'}` is bijective on sections, so is `𝒪_X ⟶ 𝒜` for any `𝒜` sitting between the
  two. This is why the intermediate scheme is again an isomorphism away from the same finite
  set.
* `Stacks.GlueSquishFactor.isIso_morphismRestrict_relativeSpecToBase` — the lower half of the
  factorization is an isomorphism over the open over which `f` is one.
* `Stacks.GlueSquishFactor.injective_app_preimage_toIntermediate` — over the preimage of an open
  of `X`, the upper half of the splitting induces `ψ` on sections, hence is injective there.
* `Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_toIntermediate` — the remaining
  inclusion `𝒪_{Spec_X(𝒜)} ⊂ p_*𝒪_{X'}` of the upper half.
* `Stacks.GlueSquishFactor.mem_range_appLE_toIntermediate` — **the capture clause**: a section
  of `f_*𝒪_{X'}` coming from `𝒜` is a section of the intermediate scheme. This is what makes
  the splitting nontrivial.
* `Stacks.GlueSquishFactor.exists_split_of_algebraHom` — the splitting itself, over an arbitrary
  base: `f = p ≫ q` with `q` finite, `𝒪_X ⊂ q_*𝒪`, `q` an isomorphism over `U`, `p` finite,
  `𝒪_{Spec_X(𝒜)} ⊂ p_*𝒪_{X'}`, and `p` an isomorphism over `q⁻¹U`.
* `Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_algebraHom` — the same over
  `Spec k`, read against the hypotheses of [Stacks, Tag 0C1L]: both halves satisfy
  `Stacks.GlueSquishFactor.IsAlmostIso`.

## Implementation notes

**The inclusion `𝒜 ⊂ f_*𝒪_{X'}`** is taken as injectivity of `ψ` on the sections over every
open, which is what the source's `⊂` says and what the squeeze argument uses. The inclusion
`𝒪_X ⊂ 𝒜` is not a hypothesis at all: it follows from `CategoryTheory.Under.w` for `ψ` together
with `𝒪_X ⊂ f_*𝒪_{X'}`, and is used only through
`Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_factorization`.

**The squeeze.** Over an affine open `V` on which `f` is an isomorphism, `Γ(X, V) ⟶ 𝒜(V)` is
injective because its composite with the injective `𝒜(V) ⟶ Γ(X', f⁻¹V)` is bijective, and
surjective because any `a ∈ 𝒜(V)` has `ψ(a)` in the image of that bijective composite, so `a`
and the image of its preimage have the same image under the injective `ψ`. Transporting this to
the structure morphism of the relative spectrum is
`Stacks.AffineAlgebraEquivalence.relativeSpecToBase_app_eq`, and getting from "isomorphism on
the sections over the affine opens inside `U`" to "isomorphism over `U`" is Zariski locality of
the class of isomorphisms, applied to a cover of `U` by affine opens whose images in `X` are
again affine.

**The inclusion `𝒪_{Spec_X(𝒜)} ⊂ p_*𝒪_{X'}` of the upper half** is not a restriction of `ψ`.
Over the preimage `q ⁻¹ᵁ V` of an open of `X` it is `ψ` read through the identification
`(Spec_X(𝒜) ⟶ X)_*𝒪 ≅ 𝒜` of [Stacks, Tag 01SA], which is
`Stacks.GlueSquishFactor.injective_app_preimage_toIntermediate`; but those opens are not a basis
of `Spec_X(𝒜)`, whose charts are the basic opens of the rings `𝒜(V)`. Getting from the one to
the other is exactness of localisation, done once and for a general affine morphism in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono`.

Nothing here constructs the measure of the induction of [Stacks, Tag 0C1L], which is still open;
see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SubalgebraProducer` for what it would
take. The subalgebra `𝒜` is produced there, from a section of `f_*𝒪_{X'}` over an affine open,
by `Stacks.GlueSquishFactor.exists_split_isAlmostIso_of_section`.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.GlueSquishFactor

/-! ### An affine morphism which is bijective on sections over an open -/

/-- **An affine morphism which is an isomorphism on sections is an isomorphism.** If `q` is
affine and `q.app V` is an isomorphism for every affine open `V` of the target contained in `U`,
then `q` is an isomorphism over `U`.

Both halves of the proof are local: over an affine `V` the morphism `q ∣_ V` is a morphism of
affine schemes whose map on global sections is `q.app V` up to the two identifications
`Γ(V, ⊤) ≅ Γ(Y, V)`, hence an isomorphism; and the class of isomorphisms is Zariski-local on the
target, so this suffices on a cover of `U` by affine opens. -/
theorem isIso_of_isAffineHom_of_isIso_app {X Y : Scheme.{u}} (q : X ⟶ Y) [IsAffineHom q]
    {U : Y.Opens} (h : ∀ V : Y.Opens, IsAffineOpen V → V ≤ U → IsIso (q.app V)) :
    IsIso (q ∣_ U) := by
  have key : ∀ V : Y.Opens, IsAffineOpen V → V ≤ U → IsIso (q ∣_ V) := by
    intro V hV hVU
    have : IsAffine (V : Scheme.{u}) := hV
    have : IsAffine ((q ⁻¹ᵁ V : X.Opens) : Scheme.{u}) := hV.preimage q
    have happ : IsIso (q.app V) := h V hV hVU
    have hsec : V.topIso.hom ≫ q.app V ≫ (q ⁻¹ᵁ V).topIso.inv = Scheme.Hom.appTop (q ∣_ V) := by
      show _ = (q ∣_ V).app ⊤
      rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_app_top,
        Scheme.Hom.appLE_eq_app]
    have hcomp : IsIso (V.topIso.hom ≫ q.app V ≫ (q ⁻¹ᵁ V).topIso.inv) := inferInstance
    have : IsIso (Scheme.Hom.appTop (q ∣_ V)) := hsec ▸ hcomp
    exact (MorphismProperty.isomorphisms.iff _).mp
      ((MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
        (arrowIsoSpecΓOfIsAffine (q ∣_ V))).mpr
        ((MorphismProperty.isomorphisms.iff _).mpr inferInstance))
  refine (MorphismProperty.isomorphisms.iff _).mp
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (f := q ∣_ U) (fun W : (U : Scheme.{u}).affineOpens => (W : (U : Scheme.{u}).Opens))
      (iSup_affineOpens_eq_top _) fun W => ?_)
  have hV : IsAffineOpen (U.ι ''ᵁ (W : (U : Scheme.{u}).Opens)) :=
    W.2.image_of_isOpenImmersion U.ι
  have hVU : U.ι ''ᵁ (W : (U : Scheme.{u}).Opens) ≤ U :=
    (Scheme.Hom.image_le_opensRange U.ι _).trans (Scheme.Opens.opensRange_ι U).le
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict q U (W : (U : Scheme.{u}).Opens))).mpr
    ((MorphismProperty.isomorphisms.iff _).mpr (key _ hV hVU))

/-- Being an isomorphism over an open depends only on the morphism, which is what lets the
factorization identity of the relative spectrum be used inside a restriction. -/
private theorem isIso_morphismRestrict_of_eq {X Y : Scheme.{u}} {g g' : X ⟶ Y} (h : g = g')
    {U : Y.Opens} (hg : IsIso (g' ∣_ U)) : IsIso (g ∣_ U) := by
  subst h; exact hg

/-! ### The squeeze: an algebra between `𝒪_X` and `f_*𝒪_{X'}` -/

/-- **The squeeze of [Stacks, Tag 0C1L].** Let `ψ : 𝒜 ⟶ f_*𝒪_{X'}` be a morphism of
`𝒪_X`-algebras which is injective on the sections over the open `V`, and suppose
`𝒪_X ⟶ f_*𝒪_{X'}` is bijective on the sections over `V`. Then `𝒪_X ⟶ 𝒜` is bijective on the
sections over `V`.

This is the reason an intermediate factorization of an almost isomorphism is again an
isomorphism away from the same finite set of points: on the good open there is no room between
`𝒪_X` and `f_*𝒪_{X'}`. -/
theorem isIso_hom_app_of_isIso_app {X' X : Scheme.{u}} (f : X' ⟶ X) (A : AlgebraSheaf X)
    (ψ : A ⟶ pushforwardAlgebra f) {V : X.Opens} (hf : IsIso (f.app V))
    (hψ : Function.Injective (ψ.right.hom.app (op V)).hom) :
    IsIso (A.hom.hom.app (op V)) := by
  have := hf
  have hcomp : ∀ x : Γ(X, V),
      (ψ.right.hom.app (op V)).hom ((A.hom.hom.app (op V)).hom x) = (f.app V).hom x :=
    fun x => congrArg (fun t : X.sheaf ⟶ (pushforwardAlgebra f).right => (t.hom.app (op V)).hom x)
      (Under.w ψ)
  have hbij := ConcreteCategory.bijective_of_isIso (f.app V)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy => hbij.1 ?_, fun a => ?_⟩
  · rw [← hcomp x, ← hcomp y, hxy]
  · obtain ⟨x, hx⟩ := hbij.2 ((ψ.right.hom.app (op V)).hom a)
    exact ⟨x, hψ (by rw [hcomp x, hx])⟩

/-- The structure morphism of the relative spectrum of `𝒜` is an isomorphism on the sections
over an affine open on which `𝒪_X ⟶ 𝒜` is: the two maps agree up to the identification
`Γ(Spec_X(𝒜), q⁻¹V) ≅ 𝒜(V)` of [Stacks, Tag 01S8]. -/
theorem isIso_app_relativeSpecToBase {X : Scheme.{u}} (A : AlgebraSheaf X)
    [AlgebraSheaf.IsQuasicoherent A] (V : X.affineOpens)
    (h : IsIso (A.hom.hom.app (op (V : X.Opens)))) :
    IsIso ((relativeSpecToBase A).app (V : X.Opens)) := by
  have := h
  have hcomp :
      IsIso (A.hom.hom.app (op (V : X.Opens)) ≫ (sectionsIso A V).inv) := inferInstance
  rw [relativeSpecToBase_app_eq A V]
  exact hcomp

/-- **The lower half of the splitting is an isomorphism over the good open.** If `f` is an
isomorphism over `U` and `ψ : 𝒜 ⟶ f_*𝒪_{X'}` is injective on sections, then `Spec_X(𝒜) ⟶ X` is
an isomorphism over `U`. -/
theorem isIso_morphismRestrict_relativeSpecToBase {X' X : Scheme.{u}} (f : X' ⟶ X)
    (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] (ψ : A ⟶ pushforwardAlgebra f)
    (hψ : ∀ V : X.Opens, Function.Injective (ψ.right.hom.app (op V)).hom)
    {U : X.Opens} (hU : IsIso (f ∣_ U)) : IsIso (relativeSpecToBase A ∣_ U) := by
  have := hU
  refine isIso_of_isAffineHom_of_isIso_app _ fun V hV hVU => ?_
  exact isIso_app_relativeSpecToBase A ⟨V, hV⟩
    (isIso_hom_app_of_isIso_app f A ψ (Stacks.PicFinite.isIso_app_of_le f hVU) (hψ V))

/-! ### The inclusion `𝒪_{Spec_X(𝒜)} ⊂ p_*𝒪_{X'}` -/

/-- The identification `(Spec_X(𝒜) ⟶ X)_*𝒪 ≅ 𝒜` is bijective on the sections over any open. -/
private theorem bijective_pushforwardAlgebraIso_app {X : Scheme.{u}} (A : AlgebraSheaf X)
    [AlgebraSheaf.IsQuasicoherent A] (V : X.Opens) :
    Function.Bijective ((pushforwardAlgebraIso A).hom.right.hom.app (op V)).hom := by
  have h1 : IsIso ((Under.forget X.sheaf).map (pushforwardAlgebraIso A).hom) := inferInstance
  have h2 : IsIso ((pushforwardAlgebraIso A).hom.right) := h1
  have h3 : IsIso ((TopCat.Sheaf.forget CommRingCat.{u} X.toTopCat).map
      ((pushforwardAlgebraIso A).hom.right)) := inferInstance
  have h4 : IsIso ((pushforwardAlgebraIso A).hom.right.hom) := h3
  exact ConcreteCategory.bijective_of_isIso _

/-- On sections over `q ⁻¹ᵁ V`, the upper half `X' ⟶ Spec_X(𝒜)` induces `ψ` read through the
identification `(Spec_X(𝒜) ⟶ X)_*𝒪 ≅ 𝒜`. -/
private theorem appLE_toIntermediate_eq {X' X : Scheme.{u}} (f : X' ⟶ X)
    (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] (ψ : A ⟶ pushforwardAlgebra f)
    (V : X.Opens)
    (hle : f ⁻¹ᵁ V ≤ toIntermediate f A ψ ⁻¹ᵁ (relativeSpecToBase A ⁻¹ᵁ V)) :
    ((toIntermediate f A ψ).appLE (relativeSpecToBase A ⁻¹ᵁ V) (f ⁻¹ᵁ V) hle).hom =
      (ψ.right.hom.app (op V)).hom.comp
        ((pushforwardAlgebraIso A).hom.right.hom.app (op V)).hom := by
  have hfac := toIntermediate_comp_relativeSpecToBase f A ψ
  have hL : (factorizationAlgebraHom f (toIntermediate f A ψ) (relativeSpecToBase A)
        hfac).right.hom.app (op V)
      = (toIntermediate f A ψ).appLE (relativeSpecToBase A ⁻¹ᵁ V) (f ⁻¹ᵁ V) hle :=
    pushforwardAlgebraMap_app _ V hle
  rw [← hL, factorizationAlgebraHom_toIntermediate]
  rfl

/-- **The upper half of the splitting is injective on the sections over the preimage of an open
of `X`.** Over `q ⁻¹ᵁ V` the map `𝒪_{Spec_X(𝒜)} ⟶ p_*𝒪_{X'}` is `ψ` read through the
identification `(Spec_X(𝒜) ⟶ X)_*𝒪 ≅ 𝒜` of [Stacks, Tag 01SA], so it is injective because `ψ`
is.

This is the half of the inclusion `𝒜 ⊂ f_*𝒪_{X'}` that *is* a restriction of `ψ`: the opens
`q ⁻¹ᵁ V` are not a basis of `Spec_X(𝒜)`, which is why
`Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_toIntermediate` is needed to get from here
to the sections over an arbitrary open. -/
theorem injective_app_preimage_toIntermediate {X' X : Scheme.{u}} (f : X' ⟶ X)
    (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] (ψ : A ⟶ pushforwardAlgebra f)
    (hψ : ∀ V : X.Opens, Function.Injective (ψ.right.hom.app (op V)).hom) (V : X.Opens) :
    Function.Injective ((toIntermediate f A ψ).app (relativeSpecToBase A ⁻¹ᵁ V)).hom := by
  have hle : f ⁻¹ᵁ V ≤ toIntermediate f A ψ ⁻¹ᵁ (relativeSpecToBase A ⁻¹ᵁ V) :=
    preimage_le_preimage_preimage (toIntermediateOver f A ψ) V
  have hinj : Function.Injective ((toIntermediate f A ψ).appLE
      (relativeSpecToBase A ⁻¹ᵁ V) (f ⁻¹ᵁ V) hle).hom := by
    rw [appLE_toIntermediate_eq f A ψ V hle]
    exact (hψ V).comp (bijective_pushforwardAlgebraIso_app A V).1
  exact Function.Injective.of_comp (f := (X'.presheaf.map (homOfLE hle).op).hom) hinj

/-- **The missing clause of the upper half: `𝒪_{Spec_X(𝒜)} ⊂ p_*𝒪_{X'}`.** If `ψ` is injective
on the sections over every open of `X` and the morphism `p : X' ⟶ Spec_X(𝒜)` it determines is
affine, then `𝒪_{Spec_X(𝒜)} ⟶ p_*𝒪_{X'}` is a monomorphism.

The preimages `q ⁻¹ᵁ V` of the affine opens of `X` are an affine open cover of `Spec_X(𝒜)`
([Stacks, Tag 01LX]) on which the map is `ψ`, and
`Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_of_injective_app` propagates injectivity
from such a cover to every open: the charts of `Spec_X(𝒜)` are the basic opens of the rings
`𝒜(V)` rather than preimages of opens of `X`, and the passage to them is the exactness of
localisation. -/
theorem mono_hom_pushforwardAlgebra_toIntermediate {X' X : Scheme.{u}} (f : X' ⟶ X)
    (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] (ψ : A ⟶ pushforwardAlgebra f)
    (hψ : ∀ V : X.Opens, Function.Injective (ψ.right.hom.app (op V)).hom)
    [IsAffineHom (toIntermediate f A ψ)] :
    Mono (pushforwardAlgebra (toIntermediate f A ψ)).hom := by
  refine mono_hom_pushforwardAlgebra_of_injective_app _ fun z => ?_
  obtain ⟨V, hV, hzV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show (relativeSpecToBase A).base z ∈ (⊤ : X.Opens) from trivial)
  exact ⟨relativeSpecToBase A ⁻¹ᵁ V, isAffineOpen_preimage_relativeSpecToBase A ⟨V, hV⟩, hzV,
    injective_app_preimage_toIntermediate f A ψ hψ V⟩

/-! ### The sections of `𝒜` are sections of the intermediate scheme -/

/-- **Every section of `f_*𝒪_{X'}` coming from `𝒜` is a section of the intermediate scheme.**
Over the preimage `q ⁻¹ᵁ V` of an open of `X` the map `𝒪_{Spec_X(𝒜)} ⟶ p_*𝒪_{X'}` is `ψ` read
through the identification `(Spec_X(𝒜) ⟶ X)_*𝒪 ≅ 𝒜` of [Stacks, Tag 01SA], so its image on
sections is the image of `ψ`.

This is the companion of `Stacks.GlueSquishFactor.injective_app_preimage_toIntermediate`: that
one says the map is injective, this one says what its image contains. It is what makes the
intermediate factorization *nontrivial*: a section of `f_*𝒪_{X'}` which is captured by `𝒜` but
is not a section of `𝒪_X` is a section of `𝒪_{Spec_X(𝒜)}` which is not one of `𝒪_X`, so the
lower half of the splitting is not an isomorphism. -/
theorem mem_range_appLE_toIntermediate {X' X : Scheme.{u}} (f : X' ⟶ X)
    (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] (ψ : A ⟶ pushforwardAlgebra f)
    (V : X.Opens)
    (hle : f ⁻¹ᵁ V ≤ toIntermediate f A ψ ⁻¹ᵁ (relativeSpecToBase A ⁻¹ᵁ V))
    (s : Γ(X', f ⁻¹ᵁ V)) (hs : s ∈ Set.range (ψ.right.hom.app (op V)).hom) :
    s ∈ Set.range ((toIntermediate f A ψ).appLE
      (relativeSpecToBase A ⁻¹ᵁ V) (f ⁻¹ᵁ V) hle).hom := by
  obtain ⟨a, ha⟩ := hs
  obtain ⟨b, hb⟩ := (bijective_pushforwardAlgebraIso_app A V).2 a
  exact ⟨b, by rw [appLE_toIntermediate_eq f A ψ V hle]; exact (congrArg _ hb).trans ha⟩

/-! ### The splitting attached to a finite intermediate algebra -/

/-- **The splitting step of [Stacks, Tag 0C1L].** Let `f : X' ⟶ X` be a finite morphism of
schemes over a base `S` with `𝒪_X ⊂ f_*𝒪_{X'}` which is an isomorphism over an open `U` of `X`,
and let `𝒜` be a finite quasi-coherent sheaf of `𝒪_X`-algebras with an injection
`ψ : 𝒜 ⟶ f_*𝒪_{X'}` of `𝒪_X`-algebras. Then `f` factors over `S` as `p ≫ q` with

* `q : Spec_X(𝒜) ⟶ X` finite, with `𝒪_X ⊂ q_*𝒪`, and an isomorphism over `U`;
* `p : X' ⟶ Spec_X(𝒜)` finite, with `𝒪_{Spec_X(𝒜)} ⊂ p_*𝒪_{X'}`, and an isomorphism over
  `q⁻¹U`.

Finiteness of `q` is the finiteness of `𝒜`; finiteness of `p` is finiteness of `f` cancelled
against it; `𝒪_X ⊂ q_*𝒪` is the chain `𝒪_X ⊂ 𝒜 ⊂ f_*𝒪_{X'}`;
`𝒪_{Spec_X(𝒜)} ⊂ p_*𝒪_{X'}` is `ψ` propagated from the preimages of the affine opens of `X`
to every open of `Spec_X(𝒜)` by
`Stacks.GlueSquishFactor.mono_hom_pushforwardAlgebra_toIntermediate`; and the two statements
over `U` are the squeeze
`Stacks.GlueSquishFactor.isIso_morphismRestrict_relativeSpecToBase` together with cancellation
of `q ∣_ U` out of `f ∣_ U`.

The last clause is the *capture* clause: over every open `V` of `X` the sections of `𝒜` are
sections of the intermediate scheme, by
`Stacks.GlueSquishFactor.mem_range_appLE_toIntermediate`. It is what makes the splitting
nontrivial — without it a splitting is produced even by `𝒜 = 𝒪_X`, for which `q` is an
isomorphism and nothing has happened. -/
@[stacks 0C1L "the splitting attached to a finite intermediate subalgebra"]
theorem exists_split_of_algebraHom {S : Scheme.{u}} {W' W : Over S} (f : W' ⟶ W)
    [IsFinite f.left] [Mono (pushforwardAlgebra f.left).hom] (A : AlgebraSheaf W.left)
    [AlgebraSheaf.IsQuasicoherent A] (hAfin : AlgebraSheaf.IsFinite A)
    (ψ : A ⟶ pushforwardAlgebra f.left)
    (hψ : ∀ V : W.left.Opens, Function.Injective (ψ.right.hom.app (op V)).hom)
    {U : W.left.Opens} (hU : IsIso (f.left ∣_ U)) :
    ∃ (Z : Over S) (p : W' ⟶ Z) (q : Z ⟶ W), p ≫ q = f ∧ IsFinite q.left ∧
      Mono (pushforwardAlgebra q.left).hom ∧ IsIso (q.left ∣_ U) ∧ IsFinite p.left ∧
      Mono (pushforwardAlgebra p.left).hom ∧ IsIso (p.left ∣_ (q.left ⁻¹ᵁ U)) ∧
      ∀ (V : W.left.Opens) (hle : f.left ⁻¹ᵁ V ≤ p.left ⁻¹ᵁ (q.left ⁻¹ᵁ V))
        (s : Γ(W'.left, f.left ⁻¹ᵁ V)), s ∈ Set.range (ψ.right.hom.app (op V)).hom →
          s ∈ Set.range (p.left.appLE (q.left ⁻¹ᵁ V) (f.left ⁻¹ᵁ V) hle).hom := by
  have hfac : toIntermediate f.left A ψ ≫ relativeSpecToBase A = f.left :=
    toIntermediate_comp_relativeSpecToBase f.left A ψ
  have hq : IsFinite (relativeSpecToBase A) :=
    Stacks.AffineAlgebraEquivalence.isFinite_relativeSpecToBase A hAfin
  have hqU : IsIso (relativeSpecToBase A ∣_ U) :=
    isIso_morphismRestrict_relativeSpecToBase f.left A ψ hψ hU
  have hp : IsFinite (toIntermediate f.left A ψ) := by
    have : IsFinite (toIntermediate f.left A ψ ≫ relativeSpecToBase A) := by
      rw [hfac]; infer_instance
    exact IsFinite.of_comp _ (relativeSpecToBase A)
  have hpU : IsIso (toIntermediate f.left A ψ ∣_ (relativeSpecToBase A ⁻¹ᵁ U)) := by
    have hcomp : IsIso ((toIntermediate f.left A ψ ≫ relativeSpecToBase A) ∣_ U) :=
      isIso_morphismRestrict_of_eq hfac hU
    rw [morphismRestrict_comp] at hcomp
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance hcomp
  refine ⟨Over.mk (relativeSpecToBase A ≫ W.hom),
    Over.homMk (toIntermediate f.left A ψ) ?_, Over.homMk (relativeSpecToBase A) rfl,
    Over.OverMorphism.ext ?_, hq,
    mono_hom_pushforwardAlgebra_of_factorization f.left (toIntermediate f.left A ψ)
      (relativeSpecToBase A) hfac, hqU, hp,
    mono_hom_pushforwardAlgebra_toIntermediate f.left A ψ hψ, hpU,
    fun V hle s hs => mem_range_appLE_toIntermediate f.left A ψ V hle s hs⟩
  · show toIntermediate f.left A ψ ≫ relativeSpecToBase A ≫ W.hom = W'.hom
    rw [← Category.assoc, hfac, Over.w]
  · show toIntermediate f.left A ψ ≫ relativeSpecToBase A = f.left
    exact hfac

/-- **The splitting step of [Stacks, Tag 0C1L], read against the hypotheses of the lemma.** An
almost isomorphism of algebraic `k`-schemes and a finite quasi-coherent `𝒪_X`-subalgebra `𝒜` of
`f_*𝒪_{X'}` give a factorization `f = p ≫ q` over `Spec k` in which *both* halves are again
almost isomorphisms, so both satisfy every hypothesis of the source.

Together with a measure which drops along this factorization, this is the hypothesis `hsplit`
of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`. No measure is constructed
here. The last clause records that the splitting *captures* the sections of `𝒜`, which is what
distinguishes it from the trivial splitting by `𝒜 = 𝒪_X`. -/
@[stacks 0C1L "the splitting, read against the hypotheses of the lemma"]
theorem exists_split_isAlmostIso_of_algebraHom {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Over (Spec (.of k))} (f : X' ⟶ X) (hf : IsAlmostIso f) (A : AlgebraSheaf X.left)
    [AlgebraSheaf.IsQuasicoherent A] (hAfin : AlgebraSheaf.IsFinite A)
    (ψ : A ⟶ pushforwardAlgebra f.left)
    (hψ : ∀ V : X.left.Opens, Function.Injective (ψ.right.hom.app (op V)).hom) :
    ∃ (Z : Over (Spec (.of k))) (p : X' ⟶ Z) (q : Z ⟶ X),
      p ≫ q = f ∧ IsAlmostIso q ∧ IsAlmostIso p ∧
      ∀ (V : X.left.Opens) (hle : f.left ⁻¹ᵁ V ≤ p.left ⁻¹ᵁ (q.left ⁻¹ᵁ V))
        (s : Γ(X'.left, f.left ⁻¹ᵁ V)), s ∈ Set.range (ψ.right.hom.app (op V)).hom →
          s ∈ Set.range (p.left.appLE (q.left ⁻¹ᵁ V) (f.left ⁻¹ᵁ V) hle).hom := by
  obtain ⟨⟨hX'ft, hX'qc, hXft, hXqc, hffin, U, hUfin, hUiso⟩, hmono⟩ := hf
  have := hX'ft
  have := hX'qc
  have := hXft
  have := hXqc
  have := hffin
  have := hmono
  obtain ⟨Z, p, q, hpq, hqfin, hqmono, hqU, hpfin, hpmono, hpU, hcap⟩ :=
    exists_split_of_algebraHom f A hAfin ψ hψ hUiso
  have := hqfin
  have hZ : (Z.left ↘ Spec (.of k)) = q.left ≫ (X.left ↘ Spec (.of k)) := (Over.w q).symm
  have : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) := by rw [hZ]; infer_instance
  have : QuasiCompact (Z.left ↘ Spec (.of k)) := by rw [hZ]; infer_instance
  refine ⟨Z, p, q, hpq, ⟨⟨?_, ?_, hXft, hXqc, hqfin, U, hUfin, hqU⟩, hqmono⟩,
    ⟨⟨hX'ft, hX'qc, ?_, ?_, hpfin, q.left ⁻¹ᵁ U, ?_, hpU⟩, hpmono⟩, hcap⟩
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · have hpre : ((q.left ⁻¹ᵁ U : Z.left.Opens) : Set Z.left)ᶜ =
        ⋃ y ∈ ((U : Set X.left)ᶜ), q.left.base ⁻¹' {y} := by
      ext z
      simp [Set.mem_compl_iff]
    rw [hpre]
    exact hUfin.biUnion fun y _ => Scheme.Hom.finite_preimage_singleton q.left y

end Stacks.GlueSquishFactor

end
