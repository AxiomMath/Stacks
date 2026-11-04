module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherentAnyModel
public import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of pushforward for a closed immersion is derived sheaf Hom, at the locally
small model

Let `i : Z ⟶ W` be a pseudo-coherent closed immersion of schemes and let `a` be a right adjoint
of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. Then on bounded-below complexes `a` is derived sheaf Hom
out of the structure sheaf of the closed subscheme, `a(K) = R𝓗om_{𝒪_W}(𝒪_Z, K)`. This is
[Stacks, Tag 0A9X], proved in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHom.lean` at
`CategoryTheory.HasDerivedCategory.standard`. `HasDerivedCategory` carries the localized category
as *data*, so that statement says nothing about the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which is the only model at which the
existence of `i^!` ([Stacks, Tag 0A9E]) is available. This file restates the tag there, and
thereby **discharges the hypothesis `Stacks.Duality.LocallySmall.Tag0A9XHypothesis`** that
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageLocallySmall.lean` left
on [Stacks, Tag 0AA2].

## Main definitions

* `Stacks.Duality.LocallySmall.closedImmersionPushforwardModelIso` — [Stacks, Tag 0E2K] at this
  model: the comparison of the two models of `Ri_*` on unbounded derived categories.
* `Stacks.Duality.LocallySmall.rightAdjointToDerivedSheafHom` — the canonical comparison
  `a(K) ⟶ R𝓗om_{𝒪_W}(𝒪_Z, K)`, the mate of the counit of `a`.

## Main results

* `Stacks.Duality.LocallySmall.derivedCategoryB_derivedSheafHomExactSupport_obj` — part (1)
  of [Stacks, Tag 0A78] at this model, in the packaging the proof below consumes.
* `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_pseudoCoherent` — the
  identification for the restriction of `Ri_*` to `D_QCoh` at an arbitrary proof that `Ri_*`
  preserves quasi-coherent cohomology.
* `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion` —
  **[Stacks, Tag 0A9X] at the locally small derived categories**, for the canonical restriction
  of `Ri_*`, with no hypothesis beyond the pseudo-coherence of `i`.
* `Stacks.Duality.LocallySmall.tag0A9XHypothesis` — **the hypothesis
  `Stacks.Duality.LocallySmall.Tag0A9XHypothesis` holds**, so nothing about [Stacks, Tag 0A9X] is
  assumed at this model any more.
* `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts_closedImmersion` —
  **[Stacks, Tag 0AA2] at this model with that hypothesis discharged.**
* `exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional` — the same with `i^!`
  produced rather than assumed, for an affine source: the composition with [Stacks, Tag 0A9E] that
  the standard model cannot express at all, now with no hypothesis about [Stacks, Tag 0A9X].

## Implementation notes

**The proof is uniqueness of adjoints, and that argument is model-free.** Derived sheaf Hom with
exact support is a right adjoint of `Ri_*` on all module sheaves — at this model,
`Stacks.Duality.LocallySmall.derivedModulePushforwardSheafHomExactSupportAdjunction`, which is
[Stacks, Tag 0A76] here — and it carries `D⁺_QCoh(𝒪_W)` into `D⁺_QCoh(𝒪_Z)`. So for `K` in
`D⁺_QCoh(𝒪_W)` both `a(K)` and `R𝓗om(𝒪_Z, K)` represent the same functor on `D_QCoh(𝒪_Z)`, and
the canonical comparison between them — the mate of the counit of `a`, written here as
`rightAdjointToDerivedSheafHom` — is invertible by Yoneda. Every step of that is pure category
theory: the two model files differ only in which `HasDerivedCategory` instance the functors are
taken at.

**The one non-formal input, and how it crosses.** Part (1) of [Stacks, Tag 0A78] —
`AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus` — rests on
part (1) of [Stacks, Tag 0A6H] and so on [Stacks, Tag 06Z0], a spine of a dozen files, one of
which (`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportQuasicoherent.lean`) would have to be split because its part (2) genuinely
uses the standard model. None of that is re-pinned. Instead
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportQuasicoherentAnyModel.lean`
restates part (1) **with no derived category in it at all** — for `s : K ⟶ J` a K-injective
resolution, the complex `ℰom(𝒪_Z, J)` has quasi-coherent cohomology vanishing in low degrees —
proves *that* from the standard-model statement, and reads it back at an arbitrary model. A
statement about complexes and quasi-isomorphisms only is model-agnostic, so it crosses for free.
This is the route [Stacks, Tag 08D5] was transported by, in both of its parts.

**No `attribute [local instance] HasDerivedCategory.standard`.** The derived categories here are
the global instances `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and
`SheafOfModules.hasDerivedCategory` of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which agree by `rfl` on the two
interchangeable spellings `AlgebraicGeometry.Scheme.Modules W` and
`SheafOfModules (structureSheafRing W.toRingedSpace)` of the category of
`𝒪_W`-modules. That is what lets the quasi-coherent subcategory, stated in the first spelling,
and sheaf Hom with exact support, stated in the second, meet in one statement. A free
`[HasDerivedCategory.{w} _]` binder would *not* do: a binder is found for the spelling it is
written in and not for the other, which is why the arbitrary-model statement imported here is
phrased entirely in the second spelling and `derivedCategoryB_derivedSheafHomExactSupport_obj`
is the repackaging.

**The form that produces `i^!`.** The affine-source form below obtains `i^!` from
[Stacks, Tag 0A9E] by Brown representability, which needs the compact generation of
`D_QCoh(𝒪_X)` ([Stacks, Tag 09IS]), available here for affine schemes. The statement for an
arbitrary object of `FTS S` does not go through compact generation at all: it builds `i^!` as
`DQ_X ∘ R𝓗om(𝒪_X, -)` from the coherator of [Stacks, Tag 0CR0], and is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`.

## References

* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality.LocallySmall

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-! ### Part (1) of Tag 0A78 at this model, in the packaging the proof consumes -/

/-- **Part (1) of [Stacks, Tag 0A78] at the locally small derived categories**, in the form the
proof of [Stacks, Tag 0A9X] below consumes: for a pseudo-coherent closed immersion `i : Z ⟶ W`
and an object `K` of `D⁺_QCoh(𝒪_W)`, the object `R ℰom(𝒪_Z, K)` lies in `D_QCoh(𝒪_Z)`, so it is
an object of `Stacks.Duality.quasiCoherentDerivedCategory Z`.

This is the arbitrary-model
`Stacks.Duality.AnyModel.isBoundedBelow_isQuasicoherent_derivedSheafHomExactSupport_obj` read at
the global locally small instances. Both its hypotheses and its conclusion are written in the
spelling `SheafOfModules (structureSheafRing _)` of the category of modules,
which is the spelling `R ℰom(𝒪_Z, -)` is stated in and the one in which a free
`HasDerivedCategory` binder is found; the crossing to `AlgebraicGeometry.Scheme.Modules`, in which
`SheafOfModules.isQuasicoherent` and the quasi-coherent subcategory are stated, happens at the one
call site, where the two global instances agree by `rfl`.

Only the `D_QCoh` half is returned: the boundedness below of `R ℰom(𝒪_Z, K)`, which is
`Stacks.Duality.LocallySmall.isBoundedBelow_derivedSheafHomExactSupport_obj`, is not what the
Yoneda argument needs. -/
theorem derivedCategoryB_derivedSheafHomExactSupport_obj (hi : PseudoCoherent i)
    (K : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing W.toRingedSpace)))
    (hbdd : DerivedCategoryB.IsBoundedBelow K)
    (hcoh : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (structureSheafRing W.toRingedSpace)) n).obj K).IsQuasicoherent) :
    DerivedCategoryB.derivedCategoryB
      (A := SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf)
      ((derivedSheafHomExactSupport i).obj K) := by
  obtain ⟨b, hb⟩ := hbdd
  exact (Stacks.Duality.AnyModel.isBoundedBelow_isQuasicoherent_derivedSheafHomExactSupport_obj
    i hi K hcoh b hb).2

/-- `R ℰom(𝒪_Z, K)` as an object of `D_QCoh(𝒪_Z)`, for `K` a bounded-below object of
`D_QCoh(𝒪_W)`: this is `derivedCategoryB_derivedSheafHomExactSupport_obj` packaged as the object
the Yoneda argument of [Stacks, Tag 0A9X] tests the comparison map against. -/
abbrev quasiCoherentDerivedSheafHomObj (hi : PseudoCoherent i)
    (K : (isBoundedBelowQuasiCoherent W).FullSubcategory) : quasiCoherentDerivedCategory Z :=
  ⟨(derivedSheafHomExactSupport i).obj K.obj.obj,
    derivedCategoryB_derivedSheafHomExactSupport_obj i hi K.obj.obj K.property K.obj.property⟩

/-! ### The two models of `Ri_*` -/

/-- **[Stacks, Tag 0E2K] for a closed immersion of schemes, at the locally small derived
categories.** The comparison isomorphism between the two models of `Ri_*` on unbounded derived
categories of module sheaves: the functor induced by the exact functor `i_*`, which is what the
adjunction of [Stacks, Tag 0A76] uses, and the total right derived functor, out of which `D_QCoh`
is cut.

The input `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived` is stated for an
arbitrary exact additive functor between abelian categories with chosen derived categories, so
the only thing the standard-model form was supplying is the model itself. -/
abbrev closedImmersionPushforwardModelIso :
    (modulePushforward (closedQuotient i).i).mapDerivedCategory ≅ derivedPushforward i :=
  Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived _

/-! ### The comparison map and its invertibility -/

section

variable
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : quasiCoherentDerivedPushforward i hpush ⊣ a)

/-- The canonical comparison `a(K) ⟶ R𝓗om_{𝒪_W}(𝒪_Z, K)` in `D(𝒪_Z)`, natural in `K` in
`D_QCoh(𝒪_W)`: the mate, under the adjunction of [Stacks, Tag 0A76] at this model, of the counit
of `a` read through the comparison of the two models of `Ri_*`.

[Stacks, Tag 0A9X] says that this map is invertible on bounded-below complexes. -/
def rightAdjointToDerivedSheafHom :
    a ⋙ (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
        (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι ⟶
      (DerivedCategoryB.derivedCategoryB (A := W.Modules)
        (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι ⋙
        derivedSheafHomExactSupport i :=
  Functor.whiskerLeft
      (a ⋙ (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
        (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι)
      (derivedModulePushforwardSheafHomExactSupportAdjunction i).unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft a
          (Functor.whiskerLeft (DerivedCategoryB.derivedCategoryB (A := Z.Modules)
              (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι
            (closedImmersionPushforwardModelIso i).hom) ≫
        Functor.whiskerRight adj.counit (DerivedCategoryB.derivedCategoryB (A := W.Modules)
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι)
      (derivedSheafHomExactSupport i)

/-- The comparison map of `rightAdjointToDerivedSheafHom` is the mate of the counit of `a`: it
is the image of `Ri_*(a K) ⟶ K` under the adjunction bijection of [Stacks, Tag 0A76]. -/
theorem rightAdjointToDerivedSheafHom_app (K : quasiCoherentDerivedCategory W) :
    (rightAdjointToDerivedSheafHom i hpush a adj).app K =
      (derivedModulePushforwardSheafHomExactSupportAdjunction i).homEquiv
        ((a.obj K).obj) K.obj
        ((closedImmersionPushforwardModelIso i).hom.app ((a.obj K).obj) ≫
          (adj.counit.app K).hom) :=
  rfl

/-- Precomposing the comparison map of `rightAdjointToDerivedSheafHom` with a morphism out of an
object of `D_QCoh(𝒪_Z)` gives the adjunction bijection of [Stacks, Tag 0A76] applied to the
corresponding morphism `Ri_* M ⟶ K`. This is what makes the comparison invertible. -/
theorem hom_comp_rightAdjointToDerivedSheafHom_app
    (K : quasiCoherentDerivedCategory W) (M : quasiCoherentDerivedCategory Z) (g : M ⟶ a.obj K) :
    g.hom ≫ (rightAdjointToDerivedSheafHom i hpush a adj).app K =
      (derivedModulePushforwardSheafHomExactSupportAdjunction i).homEquiv M.obj K.obj
        ((closedImmersionPushforwardModelIso i).hom.app M.obj ≫
          ((adj.homEquiv M K).symm g).hom) := by
  have hu : (modulePushforward (closedQuotient i).i).mapDerivedCategory.map g.hom ≫
        ((closedImmersionPushforwardModelIso i).hom.app ((a.obj K).obj) ≫
          (adj.counit.app K).hom) =
      (closedImmersionPushforwardModelIso i).hom.app M.obj ≫
        ((adj.homEquiv M K).symm g).hom :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ (adj.counit.app K).hom)
        ((closedImmersionPushforwardModelIso i).hom.naturality g.hom))).trans
      (Category.assoc _ _ _)
  rw [rightAdjointToDerivedSheafHom_app, ← hu]
  exact (Adjunction.homEquiv_naturality_left _ g.hom _).symm

/-- Composition with the comparison map of `rightAdjointToDerivedSheafHom` is a bijection on
morphisms out of any object of `D_QCoh(𝒪_Z)`: it is the composite of the adjunction bijections
of [Stacks, Tag 0A76] and of `a`, of full faithfulness of the inclusion of `D_QCoh(𝒪_Z)`, and of
composition with the comparison isomorphism of the two models of `Ri_*`. -/
theorem bijective_comp_rightAdjointToDerivedSheafHom_app
    (K : quasiCoherentDerivedCategory W) (M : quasiCoherentDerivedCategory Z) :
    Function.Bijective (fun g : M.obj ⟶ (a.obj K).obj =>
      g ≫ (rightAdjointToDerivedSheafHom i hpush a adj).app K) := by
  have hiso : Function.Bijective (fun f : (derivedPushforward i).obj M.obj ⟶ K.obj =>
      (closedImmersionPushforwardModelIso i).hom.app M.obj ≫ f) :=
    ⟨fun _ _ h => (cancel_epi ((closedImmersionPushforwardModelIso i).app M.obj).hom).1 h,
      fun f => ⟨(closedImmersionPushforwardModelIso i).inv.app M.obj ≫ f,
        Iso.hom_inv_id_app_assoc _ _ _⟩⟩
  refine Eq.mpr (congrArg Function.Bijective (funext fun g =>
    hom_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K M (ObjectProperty.homMk g)))
    (((derivedModulePushforwardSheafHomExactSupportAdjunction i).homEquiv
      M.obj K.obj).bijective.comp <| hiso.comp <|
    (ObjectProperty.fullyFaithfulι _).homEquiv.bijective.comp <|
    (adj.homEquiv M K).symm.bijective.comp
      (ObjectProperty.fullyFaithfulι _).homEquiv.symm.bijective)

/-- **The comparison map of `rightAdjointToDerivedSheafHom` is invertible at a bounded-below
object of `D_QCoh(𝒪_W)`.** This is the Yoneda step of [Stacks, Tag 0A9X]: composition with the
map is a bijection on morphisms out of every object of `D_QCoh(𝒪_Z)`
(`bijective_comp_rightAdjointToDerivedSheafHom_app`), and `R𝓗om(𝒪_Z, K)` is itself such an object
by part (1) of [Stacks, Tag 0A78], so the map has a two-sided inverse. -/
theorem isIso_rightAdjointToDerivedSheafHom_app (hpc : PseudoCoherent i)
    (K : (isBoundedBelowQuasiCoherent W).FullSubcategory) :
    IsIso ((rightAdjointToDerivedSheafHom i hpush a adj).app K.obj) := by
  obtain ⟨s, hs⟩ := (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K.obj
    (quasiCoherentDerivedSheafHomObj i hpc K)).surjective (𝟙 _)
  refine ⟨s, ?_, hs⟩
  refine (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K.obj
    (a.obj K.obj)).injective ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (rightAdjointToDerivedSheafHom i hpush a adj).app K.obj ≫ t) hs).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))

end

/-! ### Tag 0A9X at the locally small derived categories -/

/-- **Stacks Project, Tag 0A9X (Lemma 48.9.7), at the locally small derived categories.** Let
`i : Z ⟶ W` be a pseudo-coherent closed immersion of schemes and let `a` be a right adjoint of
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. Then on bounded-below complexes with quasi-coherent
cohomology `a` is derived sheaf Hom out of the structure sheaf of the closed subscheme:
`a(K) = R𝓗om_{𝒪_W}(𝒪_Z, K)` for `K` in `D⁺_QCoh(𝒪_W)`.

This is `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_pseudoCoherent` transported off
`CategoryTheory.HasDerivedCategory.standard`. The argument is uniqueness of adjoints and is
model-free; its one non-formal input, part (1) of [Stacks, Tag 0A78], crosses as
`Stacks.Duality.LocallySmall.derivedCategoryBPlus_derivedSheafHomExactSupport_obj`.

This form is stated for the restriction of `Ri_*` to `D_QCoh` at an arbitrary proof `hpush` that
`Ri_*` preserves quasi-coherent cohomology; it is not registered as [Stacks, Tag 0A9X]. The
registered statement, at the canonical restriction
`Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward` with that preservation
proved, is `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion`. -/
theorem isDerivedSheafHomRightAdjoint_of_pseudoCoherent
    (hpc : PseudoCoherent i)
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : quasiCoherentDerivedPushforward i hpush ⊣ a) :
    IsDerivedSheafHomRightAdjoint i a :=
  ⟨NatIso.ofComponents
    (fun K => @asIso _ _ _ _ ((rightAdjointToDerivedSheafHom i hpush a adj).app K.obj)
      (isIso_rightAdjointToDerivedSheafHom_app i hpush a adj hpc K))
    fun _ => (rightAdjointToDerivedSheafHom i hpush a adj).naturality _⟩

/-- **Stacks Project, Tag 0A9X (Lemma 48.9.7).** Let `i : Z ⟶ W` be a pseudo-coherent closed
immersion of schemes and let `a : D_QCoh(𝒪_W) ⥤ D_QCoh(𝒪_Z)` be the right adjoint of
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. Then there is a functorial isomorphism
`a(K) ≅ R𝓗om_{𝒪_W}(𝒪_Z, K)` for `K` in `D⁺_QCoh(𝒪_W)`.

Here `Ri_*` is the canonical restriction
`Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward` of the total derived
direct image to `D_QCoh`: that `Ri_*` carries `D_QCoh(𝒪_Z)` into `D_QCoh(𝒪_W)` is proved
(part (1) of [Stacks, Tag 08D5] for the affine morphism `i`,
`Stacks.Duality.LocallySmall.isQuasicoherent_homology_derivedPushforward_of_isAffineHom`), not
assumed. The right adjoint is quantified over together with its adjunction, which determines it
up to unique isomorphism. The derived categories are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which the right adjoint exists
([Stacks, Tag 0A9E]).

The quasi-compactness and quasi-separatedness of `W` are dropped: the source uses them only to
produce `a`, and the proof is uniqueness of adjoints against `R𝓗om(𝒪_Z, -)`, the right adjoint of
`Ri_*` on all of `D(𝒪_W)` ([Stacks, Tag 0A76]) which maps `D⁺_QCoh(𝒪_W)` into `D⁺_QCoh(𝒪_Z)`
([Stacks, Tag 0A78]). -/
@[stacks 0A9X "at the locally small derived categories, the model at which the right adjoint \
  a of Ri_* exists (Tag 0A9E); the quasi-compactness and quasi-separatedness of X are dropped, \
  the source using them only to produce a"]
theorem isDerivedSheafHomRightAdjoint_of_isClosedImmersion (hpc : PseudoCoherent i)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : affineHomQuasiCoherentDerivedPushforward i ⊣ a) :
    IsDerivedSheafHomRightAdjoint i a :=
  isDerivedSheafHomRightAdjoint_of_pseudoCoherent i hpc
    (isQuasicoherent_homology_derivedPushforward_of_isAffineHom i) a adj

/-- **The hypothesis `Stacks.Duality.LocallySmall.Tag0A9XHypothesis` holds.** It is
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion` — [Stacks,
Tag 0A9X] at this model — quantified over all closed immersions.

So nothing at this model assumes [Stacks, Tag 0A9X] any more; the two statements of
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageLocallySmall.lean` that
carried `h0A9X` are discharged below. -/
theorem tag0A9XHypothesis : Tag0A9XHypothesis.{u} :=
  fun j _ _ _ hpc a adj => isDerivedSheafHomRightAdjoint_of_isClosedImmersion j hpc a adj

/-! ### Tag 0AA2 at this model, unconditionally -/

/-- **Stacks Project, Tag 0AA2 (Lemma 48.17.4), at the locally small derived categories, with
nothing about [Stacks, Tag 0A9X] assumed.** In Situation 48.16.1, let `i : X ⟶ Y` be a morphism of
`FTS S` whose underlying morphism of schemes is a closed immersion, and let `a` be a right adjoint
of `Ri_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then `a`, which is `i^!`, is derived sheaf Hom out of
`𝒪_X`: `i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)` on bounded-below complexes with quasi-coherent cohomology.

This is `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_fts` with its hypothesis
`h0A9X` discharged by `Stacks.Duality.LocallySmall.tag0A9XHypothesis`. The reduction form is kept
because it is the restatement step on its own, independent of how [Stacks, Tag 0A9X] is proved.

What remains a parameter is `i^!` itself, the functor `a` together with the adjunction `adj`
characterising it, exactly as in [Stacks, Tag 0A9X] and in `Stacks.Duality.sheafyTrace`; a right
adjoint being unique up to canonical isomorphism, the statement about an arbitrary one says what
the tag says. For an affine source it is not a parameter either — see
`exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional`.

This declaration is not registered as [Stacks, Tag 0AA2]: the full statement, with `i^!`
produced for every object of `FTS S` and no affineness or quasi-affineness hypothesis, is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`. -/
theorem isDerivedSheafHomRightAdjoint_of_fts_closedImmersion
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (i : X ⟶ Y)
    [IsClosedImmersion i.left]
    (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
    (adj : affineHomQuasiCoherentDerivedPushforward i.left ⊣ a) :
    IsDerivedSheafHomRightAdjoint i.left a :=
  isDerivedSheafHomRightAdjoint_of_fts tag0A9XHypothesis.{u} i a adj

/-- **Stacks Project, Tag 0AA2 (Lemma 48.17.4) with `i^!` produced rather than assumed, for an
affine source, and with nothing about [Stacks, Tag 0A9X] assumed.** In Situation 48.16.1, let
`i : X ⟶ Y` be a morphism of `FTS S` whose underlying morphism of schemes is a closed immersion,
and let `X` be affine. Then `Ri_*` *has* a right adjoint, and that right adjoint — `i^!` — is
derived sheaf Hom out of `𝒪_X`: `i^!(-) = R𝓗om_{𝒪_Y}(𝒪_X, -)` on bounded-below complexes with
quasi-coherent cohomology.

This is `Stacks.Duality.LocallySmall.exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine`
with its hypothesis `h0A9X` discharged by
`Stacks.Duality.LocallySmall.tag0A9XHypothesis`. **The statement is now unconditional apart from
the affineness of `X`**, which is the hypothesis under which [Stacks, Tag 09IS] — the compact
generation of `D_QCoh(𝒪_X)` that Brown representability consumes — is available
(`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/AffineQuasiCoherent.lean`). The
affineness is not used by the restatement itself.

This declaration is not registered as [Stacks, Tag 0AA2]: the full statement, with `i^!`
produced for every object of `FTS S` and no affineness or quasi-affineness hypothesis, is
`Stacks.Duality.LocallySmall.upperShriek_closedImmersion_of_fts` in
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageQcqs.lean`. -/
theorem exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine_unconditional
    {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (i : X ⟶ Y)
    [IsClosedImmersion i.left] [IsAffine X.left] :
    ∃ (a : quasiCoherentDerivedCategory Y.left ⥤ quasiCoherentDerivedCategory X.left)
      (adj : affineHomQuasiCoherentDerivedPushforward i.left ⊣ a),
      IsDerivedSheafHomRightAdjoint i.left a :=
  exists_isDerivedSheafHomRightAdjoint_of_fts_of_isAffine tag0A9XHypothesis.{u} i

end Stacks.Duality.LocallySmall

end
