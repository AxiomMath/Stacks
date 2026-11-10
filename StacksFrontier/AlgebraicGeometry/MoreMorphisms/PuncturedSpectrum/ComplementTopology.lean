module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs

/-!
# Topology of the complement of an open subscheme

Let `X` be a scheme and `U ⊆ X` an open subscheme. The irreducible components of the closed
complement `Uᶜ` are governed by their generic points, and each such generic point `ξ` lets one
compare the local situation at `ξ` with the global one: the canonical morphism
`Spec 𝒪_{X, ξ} ⟶ X` meets `U` in exactly the punctured spectrum of the local ring at `ξ`, and
that intersection is affine as soon as the inclusion of `U` is an affine morphism. On a locally
Noetherian scheme one also knows that every point in the closure of `U` is a specialization of a
point of `U`. These are the three purely topological ingredients used to compare the
punctured spectrum of a local ring with the complement of an open subscheme.

## Main results

* `Stacks.PuncturedSpectrum.fromSpecStalk_preimage_eq_puncturedSpectrum`: if `ξ` is the generic
  point of an irreducible component of the complement of an open `U ⊆ X`, then the preimage of
  `U` under `Spec 𝒪_{X, ξ} ⟶ X` is the punctured spectrum of `𝒪_{X, ξ}`.
* `Stacks.PuncturedSpectrum.isAffineOpen_fromSpecStalk_preimage`: if the inclusion of `U` is an
  affine morphism, then the preimage of `U` under `Spec 𝒪_{X, ξ} ⟶ X` is an affine open.
* `Stacks.PuncturedSpectrum.exists_mem_open_specializes_of_mem_closure`: on a locally Noetherian
  scheme, every point of the closure of an open `U` is a specialization of a point of `U`.

## Implementation notes

The complement `(U : Set X)ᶜ` is used as a topological subspace, so its points, its irreducible
components and its generic points all live in the subtype `↑((U : Set X)ᶜ)` and are transported
to `X` along `Subtype.val`; `Topology.IsInducing.subtypeVal` moves specialization relations
across that coercion in both directions.

The first result is proved pointwise. One inclusion is immediate from
`AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint`, since `ξ` lies outside `U`. For the other,
a point of `Spec 𝒪_{X, ξ}` landing outside `U` is a point of the complement specializing to `ξ`,
hence lies on an irreducible component containing `ξ`; maximality forces that component to be
the given one, so `ξ` specializes back and the two points coincide.

The second result unfolds `AlgebraicGeometry.IsAffineOpen` to `IsAffine` and uses that
`AlgebraicGeometry.isPullback_morphismRestrict` exhibits the preimage as a pullback of `U` along
the morphism, hence isomorphic to an affine scheme over the affine `Spec 𝒪_{X, ξ}`.

The third result is local: one restricts to an affine open `V` containing the point, where the
coordinate ring is Noetherian and the space is therefore a Noetherian space. The closure of
`U ∩ V` inside `V` is then a Noetherian, quasi-sober subspace, so the irreducible component
through the point has a generic point, and a nonempty open subset of that component meets the
dense set `U ∩ V`; the generic point therefore lies in `U` and specializes to the given point.
-/

@[expose] public section

open TopologicalSpace AlgebraicGeometry CategoryTheory Limits IsLocalRing

universe u

namespace Stacks.PuncturedSpectrum

/-- If `ξ` is the generic point of an irreducible component `Z` of the complement of an open
subscheme `U ⊆ X`, then the preimage of `U` under the canonical morphism
`Spec 𝒪_{X, ξ} ⟶ X` is the punctured spectrum of the local ring `𝒪_{X, ξ}`. -/
theorem fromSpecStalk_preimage_eq_puncturedSpectrum
    (X : Scheme.{u}) (U : X.Opens) {Z : Set ↑((U : Set X)ᶜ)}
    (hZ : Z ∈ irreducibleComponents ↑((U : Set X)ᶜ))
    {ξ : ↑((U : Set X)ᶜ)} (hξ : IsGenericPoint ξ Z) :
    X.fromSpecStalk (ξ : X) ⁻¹ᵁ U = Stacks.puncturedSpectrum (X.presheaf.stalk (ξ : X)) := by
  let A := X.presheaf.stalk (ξ : X)
  let f := X.fromSpecStalk (ξ : X)
  have hfclosed : f (closedPoint A) = (ξ : X) := Scheme.fromSpecStalk_closedPoint
  apply Opens.ext
  ext p
  change f p ∈ U ↔ p ∈ ({closedPoint A} : Set (PrimeSpectrum A))ᶜ
  constructor
  · rintro hpU rfl
    rw [hfclosed] at hpU
    exact ξ.2 hpU
  · intro hp
    by_contra hpU
    let y : ↑((U : Set X)ᶜ) := ⟨f p, hpU⟩
    have hspec : f p ⤳ (ξ : X) := by
      simpa only [f, Scheme.range_fromSpecStalk, Set.mem_ofPred_eq] using
        Set.mem_range_self (f := ⇑f) p
    have hspec' : y ⤳ ξ := Topology.IsInducing.subtypeVal.specializes_iff |>.1 hspec
    let C : Set ↑((U : Set X)ᶜ) := closure ({y} : Set ↑((U : Set X)ᶜ))
    obtain ⟨W, hW, hCW⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible C isIrreducible_singleton.closure
    have hξW : ξ ∈ W := hCW (by simpa [C, specializes_iff_mem_closure] using hspec')
    have hZW : Z ⊆ W := by
      rw [← hξ.def]
      exact (isClosed_of_mem_irreducibleComponents W hW).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hξW)
    have hWZ : W ⊆ Z := hZ.2 hW.1 hZW
    have hback : (ξ : X) ⤳ f p :=
      (hξ.specializes (hWZ (hCW (subset_closure (Set.mem_singleton y))))).map
        continuous_subtype_val
    exact hp (f.isEmbedding.injective
      (by rw [hfclosed, (inseparable_iff_specializes_and.mpr ⟨hspec, hback⟩).eq]))

/-- If the inclusion of an open subscheme `U ⊆ X` is an affine morphism, then the preimage of
`U` under the canonical morphism `Spec 𝒪_{X, ξ} ⟶ X` is an affine open of `Spec 𝒪_{X, ξ}`. -/
theorem isAffineOpen_fromSpecStalk_preimage
    (X : Scheme.{u}) (U : X.Opens) [IsAffineHom U.ι] (ξ : X) :
    IsAffineOpen (X.fromSpecStalk ξ ⁻¹ᵁ U) := by
  change IsAffine ((X.fromSpecStalk ξ ⁻¹ᵁ U).toScheme)
  exact IsAffine.of_isIso (isPullback_morphismRestrict (X.fromSpecStalk ξ) U).isoPullback.hom

/-- On a locally Noetherian scheme, every point in the closure of an open subscheme `U` is a
specialization of a point of `U`. -/
theorem exists_mem_open_specializes_of_mem_closure
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) {ξ : X}
    (hξ : ξ ∈ closure (U : Set X)) : ∃ η : X, η ∈ U ∧ η ⤳ ξ := by
  obtain ⟨V, hVaff, hξV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (x := ξ) (U := ⊤) (Set.mem_univ ξ)
  let Y := V.toScheme
  let xV : Y := ⟨ξ, hξV⟩
  let W : Y.Opens := V.ι ⁻¹ᵁ U
  have hclV : xV ∈ closure (W : Set Y) := by
    refine mem_closure_iff.mpr fun O hO hxO => ?_
    obtain ⟨_, ⟨z, hzO, rfl⟩, hyU⟩ := mem_closure_iff.mp hξ _
      (V.2.isOpenEmbedding_subtypeVal.isOpenMap O hO) ⟨xV, hxO, rfl⟩
    exact ⟨z, hzO, hyU⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hVaff⟩
  have : NoetherianSpace Y := noetherianSpace_of_isAffineOpen V hVaff
  let C : Set Y := closure (W : Set Y)
  have : NoetherianSpace C := NoetherianSpace.of_subset (show C ⊆ Set.univ from Set.subset_univ _)
  have : QuasiSober C :=
    Topology.IsClosedEmbedding.quasiSober
      (Topology.IsClosedEmbedding.subtypeVal isClosed_closure)
  let xC : C := ⟨xV, hclV⟩
  obtain ⟨D, hD, hxD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({xC} : Set C)) isIrreducible_singleton.closure
  let η : genericPoints C := genericPoints.ofComponent ⟨D, hD⟩
  have hηD : IsGenericPoint η.1 D := genericPoints.isGenericPoint_ofComponent ⟨D, hD⟩
  let W' : Set C := {c | (c.1 : Y) ∈ W}
  have hW'open : IsOpen W' := W.2.preimage continuous_subtype_val
  have hW'dense : closure W' = Set.univ := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himage : Subtype.val '' W' = (W : Set Y) := Set.ext fun y =>
      ⟨fun ⟨_, hzW, h⟩ => h ▸ hzW, fun hyW => ⟨⟨y, subset_closure hyW⟩, hyW, rfl⟩⟩
    rw [himage]
    exact Set.eq_univ_of_forall fun c => c.2
  obtain ⟨O, hOopen, hOne, hOD⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent D hD
  obtain ⟨c, hcO, hcW⟩ :=
    (dense_iff_closure_eq.mpr hW'dense).inter_open_nonempty O hOopen hOne
  exact ⟨V.ι η.1.1, hηD.mem_open_set_iff hW'open |>.2 ⟨c, hOD hcO, hcW⟩,
    (hηD.specializes (hxD (subset_closure (Set.mem_singleton xC)))).map
      (continuous_subtype_val.comp continuous_subtype_val)⟩

end Stacks.PuncturedSpectrum

end
