module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicate
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of pushforward for a closed immersion is derived sheaf Hom

Let `i : Z ⟶ W` be a pseudo-coherent closed immersion of schemes and let `a` be a right adjoint
of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. Then on bounded-below complexes `a` is derived sheaf Hom
out of the structure sheaf of the closed subscheme, `a(K) = R𝓗om_{𝒪_W}(𝒪_Z, K)`.

## Main results

* `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_pseudoCoherent` — [Stacks, Tag 0A9X] at
  `CategoryTheory.HasDerivedCategory.standard`; the registered form, at the locally small model, is
  `Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion`.
* `Stacks.Duality.tag0A9X` — the same statement in the uniform form, quantified over
  all closed immersions, that `Stacks.Duality.isDerivedSheafHomRightAdjoint_of_fts`
  ([Stacks, Tag 0AA2]) consumes. It is what discharges that statement's hypothesis `h0A9X`,
  through `Stacks.Duality.tag0A9XHypothesis` in
  `StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImage.lean`.

## Implementation notes

The proof is uniqueness of adjoints. Derived sheaf Hom with exact support is a right adjoint of
`Ri_*` on *all* module sheaves ([Stacks, Tag 0A76]), and it carries `D⁺_QCoh(𝒪_W)` into
`D⁺_QCoh(𝒪_Z)` ([Stacks, Tag 0A78] part (1), which needs the pseudo-coherence of `i`, and whose
boundedness half is [Stacks, Tag 0A9I]). So for `K` in `D⁺_QCoh(𝒪_W)` both `a(K)` and
`R𝓗om(𝒪_Z, K)` represent the same functor on `D_QCoh(𝒪_Z)`, and the canonical comparison map
between them — the mate of the counit of `a`, written here as `rightAdjointToDerivedSheafHom` —
is invertible by Yoneda.

The two models of `Ri_*` are identified first: the adjunction of [Stacks, Tag 0A76] uses the
functor induced on derived categories by the exact functor `i_*`, while `D_QCoh` is cut out of
the total right derived functor; `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`
([Stacks, Tag 0E2K]) is the comparison.

Part (1) of [Stacks, Tag 0A78] is used in the form
`AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus`, which rests on
part (1) of [Stacks, Tag 0A6H] for an arbitrary scheme,
`AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPseudoCoherent`.

The quasi-compactness and quasi-separatedness that [Stacks, Tag 0A9X] asks of `W` are used in
the source only to produce `a`; since `a` and its adjunction are arguments here, they are not
hypotheses of `isDerivedSheafHomRightAdjoint_of_pseudoCoherent`.

## References

* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0684](https://stacks.math.columbia.edu/tag/0684)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-- A closed immersion of schemes, read as a closed quotient morphism of ringed spaces: the form
in which the adjunctions of [Stacks, Tag 0A75] and [Stacks, Tag 0A76], sheaf Hom with exact
support and its right derived functor are stated.

No derived category enters this abbreviation, so it is the same morphism of ringed spaces at
every choice of `CategoryTheory.HasDerivedCategory`; it is therefore shared by the standard-model
statements here and by the locally small ones of
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionTwistedInverseImageLocallySmall.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHomLocallySmall.lean`,
whose `Stacks.Duality.LocallySmall` namespace resolves the bare name `closedQuotient` to this
declaration. -/
abbrev closedQuotient : ClosedQuotientMorphismOfRingedSpaces.{u} :=
  Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i

/-- **[Stacks, Tag 0E2K] for a closed immersion of schemes.** The comparison isomorphism
between the two models of `Ri_*` on unbounded derived categories of module sheaves: the functor
induced by the exact functor `i_*`, which is what the adjunction of [Stacks, Tag 0A76] uses, and
the total right derived functor, out of which `D_QCoh` is cut. -/
abbrev closedImmersionPushforwardModelIso :
    (modulePushforward (closedQuotient i).i).mapDerivedCategory ≅ derivedPushforward i :=
  Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived _

section

variable
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : quasiCoherentDerivedPushforward i hpush ⊣ a)

/-- The canonical comparison `a(K) ⟶ R𝓗om_{𝒪_W}(𝒪_Z, K)` in `D(𝒪_Z)`, natural in `K` in
`D_QCoh(𝒪_W)`: the mate, under the adjunction of [Stacks, Tag 0A76], of the counit of `a` read
through the comparison of the two models of `Ri_*`.

[Stacks, Tag 0A9X] says that this map is invertible on bounded-below complexes. -/
def rightAdjointToDerivedSheafHom :
    a ⋙ (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι ⟶
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι ⋙
        (closedQuotient i).derivedSheafHomExactSupport :=
  Functor.whiskerLeft
      (a ⋙ (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι)
      (closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.unit ≫
    Functor.whiskerRight
      (Functor.whiskerLeft a
          (Functor.whiskerLeft (DerivedCategoryB.derivedCategoryB
              (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι
            (closedImmersionPushforwardModelIso i).hom) ≫
        Functor.whiskerRight adj.counit (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι)
      (closedQuotient i).derivedSheafHomExactSupport

/-- The comparison map of `rightAdjointToDerivedSheafHom` is the mate of the counit of `a`: it
is the image of `Ri_*(a K) ⟶ K` under the adjunction bijection of [Stacks, Tag 0A76]. -/
theorem rightAdjointToDerivedSheafHom_app (K : quasiCoherentDerivedCategory W) :
    (rightAdjointToDerivedSheafHom i hpush a adj).app K =
      (closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv
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
      (closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv
        M.obj K.obj
        ((closedImmersionPushforwardModelIso i).hom.app M.obj ≫
          ((adj.homEquiv M K).symm g).hom) := by
  have hu : (modulePushforward (closedQuotient i).i).mapDerivedCategory.map g.hom ≫
        ((closedImmersionPushforwardModelIso i).hom.app ((a.obj K).obj) ≫
          (adj.counit.app K).hom) =
      (closedImmersionPushforwardModelIso i).hom.app M.obj ≫
        ((adj.homEquiv M K).symm g).hom :=
    (closedImmersionPushforwardModelIso i).hom.naturality_assoc g.hom _
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
  constructor
  · intro g₁ g₂ h
    replace h : (ObjectProperty.homMk g₁ : M ⟶ a.obj K).hom ≫
        (rightAdjointToDerivedSheafHom i hpush a adj).app K =
      (ObjectProperty.homMk g₂ : M ⟶ a.obj K).hom ≫
        (rightAdjointToDerivedSheafHom i hpush a adj).app K := h
    rw [hom_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K M (ObjectProperty.homMk g₁),
      hom_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K M
        (ObjectProperty.homMk g₂)] at h
    replace h := ((closedQuotient
      i).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv M.obj K.obj).injective h
    replace h := (((closedImmersionPushforwardModelIso i).app M.obj).cancel_iso_hom_left _ _).1 h
    exact congrArg (fun p => p.hom)
      ((adj.homEquiv M K).symm.injective (ObjectProperty.hom_ext _ h))
  · intro h
    refine ⟨(adj.homEquiv M K (ObjectProperty.homMk
      ((closedImmersionPushforwardModelIso i).inv.app M.obj ≫
        ((closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv
          M.obj K.obj).symm h))).hom, ?_⟩
    have h2 : (closedImmersionPushforwardModelIso i).hom.app M.obj ≫
        ((adj.homEquiv M K).symm (adj.homEquiv M K (ObjectProperty.homMk
          ((closedImmersionPushforwardModelIso i).inv.app M.obj ≫
            ((closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv
              M.obj K.obj).symm h)))).hom =
        ((closedQuotient i).derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv
          M.obj K.obj).symm h := by
      rw [Equiv.symm_apply_apply]
      exact Iso.hom_inv_id_app_assoc _ _ _
    dsimp only
    rw [hom_comp_rightAdjointToDerivedSheafHom_app, h2]
    exact Equiv.apply_symm_apply _ h

end

/-- **Stacks Project, Tag 0A9X (Lemma 48.9.7).** Let `i : Z ⟶ W` be a pseudo-coherent closed
immersion of schemes and let `a` be a right adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. Then
on bounded-below complexes with quasi-coherent cohomology `a` is derived sheaf Hom out of the
structure sheaf of the closed subscheme: `a(K) = R𝓗om_{𝒪_W}(𝒪_Z, K)` for `K` in
`D⁺_QCoh(𝒪_W)`.

This is the statement at `CategoryTheory.HasDerivedCategory.standard`, for the restriction of
`Ri_*` to `D_QCoh` at an arbitrary proof `hpush` that `Ri_*` preserves quasi-coherent cohomology.
It is not registered as [Stacks, Tag 0A9X]: the registered statement is
`Stacks.Duality.LocallySmall.isDerivedSheafHomRightAdjoint_of_isClosedImmersion`, at the locally
small model where the right adjoint exists, for the canonical restriction of `Ri_*` with that
preservation proved. -/
theorem isDerivedSheafHomRightAdjoint_of_pseudoCoherent
    (hpc : PseudoCoherent i)
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : quasiCoherentDerivedPushforward i hpush ⊣ a) :
    IsDerivedSheafHomRightAdjoint i a := by
  have hiso (K : (isBoundedBelowQuasiCoherent W).FullSubcategory) :
      IsIso ((rightAdjointToDerivedSheafHom i hpush a adj).app K.obj) := by
    obtain ⟨s, hs⟩ := (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K.obj
      ⟨(closedQuotient i).derivedSheafHomExactSupport.obj K.obj.obj,
        (AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus
          i hpc K.obj.obj ⟨K.property, K.obj.property⟩).2⟩).surjective (𝟙 _)
    refine ⟨s, (bijective_comp_rightAdjointToDerivedSheafHom_app i hpush a adj K.obj
      (a.obj K.obj)).injective ?_, hs⟩
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => (rightAdjointToDerivedSheafHom i hpush a adj).app K.obj ≫ t) hs).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  exact ⟨NatIso.ofComponents
    (fun K => @asIso _ _ _ _ ((rightAdjointToDerivedSheafHom i hpush a adj).app K.obj) (hiso K))
    fun _ => (rightAdjointToDerivedSheafHom i hpush a adj).naturality _⟩

/-- **Stacks Project, Tag 0A9X**, in the uniform form that [Stacks, Tag 0AA2] consumes: for
*every* pseudo-coherent closed immersion into a quasi-compact and quasi-separated scheme, any
right adjoint of derived direct image on complexes with quasi-coherent cohomology is derived
sheaf Hom out of the structure sheaf of the closed subscheme on bounded-below complexes.

The quasi-compactness and quasi-separatedness of the target are not used — they are what the
source needs in order to produce the right adjoint, which here is an explicit parameter — but
they are part of the statement of the tag and are therefore kept. -/
theorem tag0A9X :
    ∀ {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i],
      CompactSpace W → QuasiSeparatedSpace W → PseudoCoherent i →
      ∀ (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
          ((DerivedCategory.homologyFunctor W.Modules n).obj
            ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
        (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z),
        (quasiCoherentDerivedPushforward i hpush ⊣ a) →
          IsDerivedSheafHomRightAdjoint i a :=
  fun j _ _ _ hpc => isDerivedSheafHomRightAdjoint_of_pseudoCoherent j hpc

end Stacks.Duality

end
