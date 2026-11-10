module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoveringSingletonReduction
public import Mathlib.AlgebraicGeometry.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The product of the algebras of a finite affine covering

A finite standard affine `τ`-covering `{Spec(A'ⱼ) → Spec(A)}` is replaced, in the source's proof
of [Stacks, Tag 06VI], by the single morphism `Spec(A') → Spec(A)` for the product algebra
`A' = A'₁ × … × A'ₘ`, so that the descent of [Stacks, Tag 06VH] — which is stated for one ring
map — applies. This module supplies what that replacement needs about the product algebra: its
spectrum is the coproduct of the spectra of the factors, it therefore belongs to the chosen big
site as soon as the factors do, and the ring map it receives from the base is faithfully flat.

## Main definitions

* `AlgebraicGeometry.specPiIso` — the spectrum of a finite product of rings is the coproduct of
  the spectra of the factors. This is Mathlib's `AlgebraicGeometry.sigmaSpec` together with the
  instance making it an isomorphism for a finite index type, read as an isomorphism.
* `AlgebraicGeometry.piDesc` — the ring map from the base to the product of the algebras of a
  family of morphisms of affine spectra over it.

## Main results

* `AlgebraicGeometry.sigmaSpec_comp_specMap_piDesc` — `Spec` of `piDesc` is the morphism out of
  the coproduct determined by the family. This is what identifies the coproduct morphism
  `∐ Spec(A'ᵢ) → Spec(A)`, in whose terms the standard-covering results of the draft are
  stated, with `Spec` of a single ring map out of `A`.
* `AlgebraicGeometry.faithfullyFlat_piDesc` — for a standard affine `τ`-covering that ring map
  is faithfully flat, which is the shape the descent of [Stacks, Tag 06VH] consumes.
* `AlgebraicGeometry.size_Spec_pi_lt` — the size bound: the spectrum of a finite product of
  rings has size below an uncountable cardinal of uncountable cofinality as soon as each factor
  does. This is [Stacks, Tag 000R] (2), the coproduct bound, transported along `specPiIso`.
* `Stacks.Adequate.BigSite.aleph0_lt_cutoff_cof` — the cutoff of a chosen big site has
  uncountable cofinality.
* `Stacks.Adequate.schemeSizeBelow_Spec_pi` — the product of a finite family of algebras of a
  chosen big site is again an algebra of that site.

## Implementation notes

Faithful flatness is not proved here: it is
`AlgebraicGeometry.IsStandardCovering.faithfullyFlat_appTop_sigmaDesc`, a statement about the
global functions along the morphism out of the coproduct. What
`AlgebraicGeometry.faithfullyFlat_piDesc` adds is the passage from that morphism to the ring map
`piDesc`, which is three isomorphisms — `specPiIso` and the two identifications of an affine
scheme's global functions with its ring — each cancelled by
`RingHom.FaithfullyFlat.respectsIso`.

`Stacks.Adequate.BigSite.aleph0_lt_cutoff_cof` is the eliminator for the field
`Stacks.Adequate.BigSite.chosen`, five cases, each reading off the cofinality field of the
underlying accepted big site; it is the companion of
`Stacks.Adequate.BigSite.aleph0_lt_cutoff`, which instead follows from the base scheme
belonging to the site and so needs no case analysis.

The index type of a coproduct of schemes in `Scheme.{u}` lies in `Type u`, while the coverings
of [Stacks, Tag 06VI] are indexed by `Fin n`. `Stacks.Adequate.schemeSizeBelow_Spec_pi` is
therefore stated for `Fin n` and proved by transporting the general statement along
`RingEquiv.piCongrLeft'` for `Equiv.ulift`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u w

namespace AlgebraicGeometry

/-- The spectrum of a finite product of rings is the coproduct of the spectra of the factors.
This is Mathlib's comparison morphism `AlgebraicGeometry.sigmaSpec`, which is an isomorphism
for a finite index type. -/
public noncomputable def specPiIso {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u}) :
    (∐ fun i => Spec (A i)) ≅ Spec (CommRingCat.of (∀ i, A i)) :=
  asIso (sigmaSpec A)

/-- The spectrum of a finite product of rings has size below `κ` as soon as the spectrum of
each factor does, for `κ` uncountable of uncountable cofinality. This is the coproduct bound
of [Stacks, Tag 000R] (2) read through `AlgebraicGeometry.specPiIso`. -/
public theorem size_Spec_pi_lt {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hcof : ℵ₀ < κ.ord.cof)
    {ι : Type u} [Finite ι] (A : ι → CommRingCat.{u})
    (hA : ∀ i, (Spec (A i)).size < κ) :
    (Spec (CommRingCat.of (∀ i, A i))).size < κ := by
  rw [← Scheme.size_congr (specPiIso A)]
  exact Scheme.size_sigmaObj_lt hκ hcof Cardinal.mk_le_aleph0 _ hA

/-- The ring map to a finite product of rings determined by a family of morphisms of affine
spectra over a common base: its `i`-th component is the ring map of the `i`-th morphism, which
exists and is unique because `Spec` is fully faithful. -/
public noncomputable def piDesc {A : CommRingCat.{u}} {ι : Type u} (A' : ι → CommRingCat.{u})
    (g : ∀ i, Spec (A' i) ⟶ Spec A) : A ⟶ CommRingCat.of (∀ i, A' i) :=
  CommRingCat.ofHom (RingHom.pi fun i => (Spec.preimage (g i)).hom)

/-- The `i`-th component of `AlgebraicGeometry.piDesc` is the ring map of the `i`-th morphism
of the family. -/
@[simp] public theorem piDesc_comp_eval {A : CommRingCat.{u}} {ι : Type u}
    (A' : ι → CommRingCat.{u}) (g : ∀ i, Spec (A' i) ⟶ Spec A) (i : ι) :
    piDesc A' g ≫ CommRingCat.ofHom (Pi.evalRingHom (fun i => (A' i : Type u)) i) =
      Spec.preimage (g i) :=
  rfl

/-- The spectrum of `AlgebraicGeometry.piDesc` is the morphism out of the coproduct determined
by the family: this identifies the coproduct morphism `∐ Spec(A'ᵢ) → Spec(A)`, in whose terms
the standard-covering results of the draft are stated, with `Spec` of a single ring map out of
`A`, which is the shape the descent of [Stacks, Tag 06VH] consumes. -/
public theorem sigmaSpec_comp_specMap_piDesc {A : CommRingCat.{u}} {ι : Type u} [Finite ι]
    (A' : ι → CommRingCat.{u}) (g : ∀ i, Spec (A' i) ⟶ Spec A) :
    sigmaSpec A' ≫ Spec.map (piDesc A' g) = Sigma.desc g := by
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ι_sigmaSpec, Sigma.ι_comp_desc, ← Spec.map_comp, piDesc_comp_eval,
    Spec.map_preimage]

/-- **The ring map to the product algebra of a finite standard affine `τ`-covering is faithfully
flat.** This is `AlgebraicGeometry.IsStandardCovering.faithfullyFlat_appTop_sigmaDesc` read
through `AlgebraicGeometry.sigmaSpec_comp_specMap_piDesc`: the morphism out of the coproduct is
`Spec` of `AlgebraicGeometry.piDesc` up to `AlgebraicGeometry.specPiIso` and the two
identifications of an affine scheme's global functions with its ring, and all three of those
isomorphisms are cancelled by `RingHom.FaithfullyFlat.respectsIso`.

Together with `Stacks.Adequate.schemeSizeBelow_Spec_pi` this is the "passage through the product
`A' = A'₁ × … × A'ₘ`" of the source's proof of [Stacks, Tag 06VI]: it produces exactly the single
faithfully flat ring map out of `A` which the descent of [Stacks, Tag 06VH] consumes. -/
@[sga "3 VIB 11.9.1" "partial"]
public theorem faithfullyFlat_piDesc (τ : CoveringTopology) {A : CommRingCat.{u}} {ι : Type u}
    (A' : ι → CommRingCat.{u}) (g : ∀ i, Spec (A' i) ⟶ Spec A)
    (h : IsStandardCovering τ (fun i => Spec (A' i)) g) :
    (piDesc A' g).hom.FaithfullyFlat := by
  have hfin : Finite ι := h.finite_index
  have hFF : (Sigma.desc g).appTop.hom.FaithfullyFlat :=
    IsStandardCovering.faithfullyFlat_appTop_sigmaDesc τ _ g h
  have hiso : IsIso ((sigmaSpec A').appTop) := by
    refine ⟨(inv (sigmaSpec A')).appTop, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, Scheme.Hom.id_appTop]
    · rw [← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]
  have key : ((Spec.map (piDesc A' g)).appTop ≫ (sigmaSpec A').appTop).hom.FaithfullyFlat := by
    rw [← Scheme.Hom.comp_appTop, sigmaSpec_comp_specMap_piDesc]
    exact hFF
  have hstep : ((Spec.map (piDesc A' g)).appTop).hom.FaithfullyFlat :=
    (RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso
      ((Spec.map (piDesc A' g)).appTop) ((sigmaSpec A').appTop)).mp
      (by rw [← CommRingCat.hom_comp]; exact key)
  have hpost : ((Spec.map (piDesc A' g)).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (∀ i, A' i))).hom).hom.FaithfullyFlat := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso _ _).mpr hstep
  rw [Scheme.ΓSpecIso_naturality] at hpost
  exact (RingHom.FaithfullyFlat.respectsIso.cancel_left_isIso
    (Scheme.ΓSpecIso A).hom (piDesc A' g)).mp
    (by rw [← CommRingCat.hom_comp]; exact hpost)

end AlgebraicGeometry

namespace Stacks.Adequate

/-- The cutoff of a chosen big site has uncountable cofinality. Each of the five accepted
big-site constructions of `Stacks.Adequate.BigSite.chosen` carries this as a field. -/
public theorem BigSite.aleph0_lt_cutoff_cof {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : ℵ₀ < B.cutoff.ord.cof := by
  obtain ⟨cut, base_mem, J, isSheaf, chosen⟩ := B
  rcases chosen with ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩ |
    ⟨hτ, C, hC, he, hJ⟩ | ⟨hτ, C, hC, he, hJ⟩
  · subst he; exact C.aleph0_lt_schemeCardinal_cof
  · subst he; exact C.aleph0_lt_cutoff_cof
  · subst he; exact C.aleph0_lt_cutoff_cof
  · subst he; exact C.aleph0_lt_cutoff_cof
  · subst he; exact C.aleph0_lt_cutoff_cof

/-- The product of a finite family of algebras whose spectra belong to a chosen big site is
again an algebra whose spectrum belongs to that site: its spectrum is the coproduct of the
spectra of the factors, and the cutoff is uncountable of uncountable cofinality. -/
public theorem schemeSizeBelow_Spec_pi {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) {n : ℕ} (A : Fin n → CommRingCat.{u})
    (hA : ∀ j, schemeSizeBelow B.cutoff (Spec (A j))) :
    schemeSizeBelow B.cutoff (Spec (CommRingCat.of (∀ j, A j))) := by
  have key : (Spec (CommRingCat.of
      (∀ i : ULift.{u} (Fin n), A (Equiv.ulift i)))).size < B.cutoff :=
    size_Spec_pi_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      (fun i => A (Equiv.ulift i)) fun i => hA _
  have e : CommRingCat.of (∀ j, A j) ≅
      CommRingCat.of (∀ i : ULift.{u} (Fin n), A (Equiv.ulift i)) :=
    (RingEquiv.piCongrLeft' (fun j => (A j : Type u))
      (Equiv.ulift.{u, 0} (α := Fin n)).symm).toCommRingCatIso
  have hiso : Spec (CommRingCat.of (∀ j, A j)) ≅
      Spec (CommRingCat.of (∀ i : ULift.{u} (Fin n), A (Equiv.ulift i))) :=
    { hom := Spec.map e.inv
      inv := Spec.map e.hom
      hom_inv_id := by rw [← Spec.map_comp, e.hom_inv_id, Spec.map_id]
      inv_hom_id := by rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id] }
  change (Spec (CommRingCat.of (∀ j, A j))).size < B.cutoff
  rw [Scheme.size_congr hiso]
  exact key

end Stacks.Adequate

end
