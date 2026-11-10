module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksCore.Tactic.StacksAttribute

/-!
# Openness of the Cohen–Macaulay locus

For a flat morphism of schemes locally of finite presentation, the locus where the morphism is
Cohen–Macaulay is open in its source.

## Main results

* `AlgebraicGeometry.isOpen_setOf_isCohenMacaulayAt` proves openness of the Cohen–Macaulay
  locus.

## Implementation notes

Local finite presentation makes every fibre locally Noetherian, so the locally Noetherian
witness used by `AlgebraicGeometry.Scheme.Hom.IsCohenMacaulayAt` is constructed from the
morphism rather than added as a hypothesis.

The proof reduces to the affine case. Over `Spec R → Spec T`, the local ring of a fibre at a
prime `q` of `T` is identified with the localization of the fibre algebra
`κ(q ∩ R) ⊗_R T` at the corresponding prime, where
`Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber` applies. Passing from the
affine case to the general one needs three transport lemmas for the fibre local ring: along an
open immersion of the source, along an open immersion of the target, and along an isomorphism
of arrows.

## References

* [Stacks Project, Tag 045U](https://stacks.math.columbia.edu/tag/045U)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Openness of the Cohen–Macaulay locus for a morphism of spectra. -/
@[ega "IV 12.1.7" "(iii), special case"]
private theorem isOpen_affine_cm_locus
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R T)))]
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R T)))]
    (hf : ∀ y : Spec (.of R), IsLocallyNoetherian
      ((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber y)) :
    IsOpen {q : PrimeSpectrum T | Scheme.Hom.IsCohenMacaulayAt
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) hf q} := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R T))
  have _ : Module.Flat R T :=
    RingHom.flat_algebraMap_iff.mp
      ((Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R T))).mp inferInstance)
  have _ : Algebra.FinitePresentation R T :=
    RingHom.finitePresentation_algebraMap.mp
      ((LocallyOfFinitePresentation.SpecMap_iff
        (CommRingCat.ofHom (algebraMap R T))).mp inferInstance)
  have hset : {q : PrimeSpectrum T | Scheme.Hom.IsCohenMacaulayAt f hf q} =
      {q : PrimeSpectrum T | Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T)))))
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T)))))} := by
    ext q
    change Scheme.Hom.IsCohenMacaulayAt f hf q ↔ _
    simp only [Scheme.Hom.IsCohenMacaulayAt]
    exact ⟨fun ⟨_, hcm⟩ => (affineFiberPoint_cm_iff_ring_locus hf q).mp
        ((affineFiber_cm_iff hf q).mp hcm),
      fun hcm => ⟨Flat.stalkMap f q, (affineFiber_cm_iff hf q).mpr
        ((affineFiberPoint_cm_iff_ring_locus hf q).mpr hcm)⟩⟩
  rw [hset]
  exact (Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber R T).1

/-- Openness of the Cohen–Macaulay locus for a morphism of affine schemes. -/
@[ega "IV 12.1.7" "(iii), special case", ega "IV 6.11.3" "special case"]
private theorem isOpen_affine_scheme_cm_locus {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine X] [IsAffine S] [Flat f] [LocallyOfFinitePresentation f]
    (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y)) :
    IsOpen {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} := by
  let f' := Spec.map f.appTop
  let e := arrowIsoSpecΓOfIsAffine f
  have : Flat f' := Flat.SpecMap_iff.mpr f.flat_appTop
  have : LocallyOfFinitePresentation f' :=
    LocallyOfFinitePresentation.SpecMap_iff f.appTop |>.mpr f.finitePresentation_appTop
  let hf' : ∀ y : Spec Γ(S, ⊤), IsLocallyNoetherian (f'.fiber y) :=
    fun y => isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f' y
  have hAffine : IsOpen {q : PrimeSpectrum Γ(X, ⊤) |
      Scheme.Hom.IsCohenMacaulayAt f' hf' q} := by
    let _ : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    have halg : algebraMap Γ(S, ⊤) Γ(X, ⊤) = f.appTop.hom := rfl
    have _ : Flat (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(S, ⊤) Γ(X, ⊤)))) :=
      Flat.SpecMap_iff.mpr (by rw [halg]; exact f.flat_appTop)
    have _ : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
        (algebraMap Γ(S, ⊤) Γ(X, ⊤)))) :=
      LocallyOfFinitePresentation.SpecMap_iff _ |>.mpr (by
        rw [halg]
        exact f.finitePresentation_appTop)
    change IsOpen {q : PrimeSpectrum Γ(X, ⊤) |
      Scheme.Hom.IsCohenMacaulayAt
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)))) hf' q}
    exact isOpen_affine_cm_locus (R := Γ(S, ⊤)) (T := Γ(X, ⊤)) hf'
  have hpoint (x : X) :
      Scheme.Hom.IsCohenMacaulayAt f hf x ↔
        Scheme.Hom.IsCohenMacaulayAt f' hf' (e.hom.left x) := by
    have _ : IsLocallyNoetherian (f.fiber (f x)) := hf _
    have _ : IsLocallyNoetherian (f'.fiber (f' (e.hom.left x))) := hf' _
    have _ : IsLocallyNoetherian
        ((f ≫ e.hom.right).fiber (e.hom.right (f x))) :=
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (f ≫ e.hom.right) _
    have _ : IsNoetherianRing
        (((f ≫ e.hom.right).fiber (e.hom.right (f x))).presheaf.stalk
          ((f ≫ e.hom.right).asFiber x)) :=
      noetherianStalk_of_locallyNoetherian _
        (isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (f ≫ e.hom.right) _)
    have _ : IsLocalRing
        (((f ≫ e.hom.right).fiber (e.hom.right (f x))).presheaf.stalk
          ((f ≫ e.hom.right).asFiber x)) := LocallyRingedSpace.isLocalRing _ _
    have hcomp : IsLocallyNoetherian
        ((e.hom.left ≫ f').fiber (f' (e.hom.left x))) :=
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation (e.hom.left ≫ f') _
    have _ : IsNoetherianRing
        (((e.hom.left ≫ f').fiber (f' (e.hom.left x))).presheaf.stalk
          ((e.hom.left ≫ f').asFiber x)) :=
      noetherianStalk_of_locallyNoetherian _ hcomp
    have _ : IsLocalRing
        (((e.hom.left ≫ f').fiber (f' (e.hom.left x))).presheaf.stalk
          ((e.hom.left ≫ f').asFiber x)) := LocallyRingedSpace.isLocalRing _ _
    simp only [Scheme.Hom.IsCohenMacaulayAt]
    exact ⟨fun ⟨_, hcm⟩ => ⟨Flat.stalkMap f' (e.hom.left x),
        (localFiberCM_iff_arrowIso f f' e hf hf' x hcomp).mp hcm⟩,
      fun ⟨_, hcm⟩ => ⟨Flat.stalkMap f x,
        (localFiberCM_iff_arrowIso f f' e hf hf' x hcomp).mpr hcm⟩⟩
  have hset : {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} =
      {x : X | Scheme.Hom.IsCohenMacaulayAt f' hf' (e.hom.left x)} :=
    Set.ext hpoint
  rw [hset]
  exact hAffine.preimage e.hom.left.continuous

/-- **Stacks Project, Tag 045U (Cohen–Macaulay locus).** For a flat morphism locally of finite
presentation, the locus of points at which the morphism is Cohen–Macaulay is open. -/
@[stacks 045U "cm_locus_open", ega "IV 12.1.7" "(iii), flat case", ega "IV 6.11.3" "special case"]
public theorem isOpen_setOf_isCohenMacaulayAt
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] :
    let hf : ∀ y : S, IsLocallyNoetherian (f.fiber y) := fun y =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation f y
    IsOpen {x : X | Scheme.Hom.IsCohenMacaulayAt f hf x} := by
  intro hf
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨V, hV, hfxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x)
      (by simp : f x ∈ (⊤ : S.Opens))
  obtain ⟨U, hU, hxU, hUsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := x) hfxV
  have hle : U ≤ f ⁻¹ᵁ V := hUsub
  have _ : IsAffine (U : Scheme) := hU
  have _ : IsAffine (V : Scheme) := hV
  let g := f.resLE V U hle
  let hg : ∀ y : V, IsLocallyNoetherian (g.fiber y) := fun y =>
    isLocallyNoetherian_fiber_of_locallyOfFinitePresentation g y
  let c₁ := U.ι ≫ f
  let c₂ := g ≫ V.ι
  let e : Arrow.mk c₁ ≅ Arrow.mk c₂ :=
    Arrow.isoMk (Iso.refl _) (Iso.refl _) (Scheme.Hom.resLE_comp_ι f hle)
  have hpoint (z : U) :
      Scheme.Hom.IsCohenMacaulayAt f hf (U.ι z) ↔
        Scheme.Hom.IsCohenMacaulayAt g hg z := by
    have hc₁ : ∀ y : S, IsLocallyNoetherian (c₁.fiber y) := fun y =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation c₁ y
    have hc₂ : ∀ y : S, IsLocallyNoetherian (c₂.fiber y) := fun y =>
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation c₂ y
    let hcompMap := e.hom.left ≫ c₂
    have hcomp : IsLocallyNoetherian (hcompMap.fiber (c₂ (e.hom.left z))) :=
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation hcompMap _
    have _ : IsLocallyNoetherian (f.fiber (f (U.ι z))) := hf _
    have _ : IsLocallyNoetherian (g.fiber (g z)) := hg _
    have _ : IsLocallyNoetherian (c₁.fiber (f (U.ι z))) := hc₁ _
    have _ : IsLocallyNoetherian (c₂.fiber (V.ι (g z))) := hc₂ _
    have _ : IsNoetherianRing
        ((c₁.fiber (f (U.ι z))).presheaf.stalk (c₁.asFiber z)) :=
      noetherianStalk_of_locallyNoetherian _ (hc₁ _)
    have _ : IsNoetherianRing
        ((c₂.fiber (V.ι (g z))).presheaf.stalk (c₂.asFiber z)) :=
      noetherianStalk_of_locallyNoetherian _ (hc₂ _)
    have _ : IsLocalRing
        ((c₁.fiber (f (U.ι z))).presheaf.stalk (c₁.asFiber z)) := LocallyRingedSpace.isLocalRing _ _
    have _ : IsLocalRing
        ((c₂.fiber (V.ι (g z))).presheaf.stalk (c₂.asFiber z)) := LocallyRingedSpace.isLocalRing _ _
    have _ : IsNoetherianRing
        ((hcompMap.fiber (c₂ (e.hom.left z))).presheaf.stalk (hcompMap.asFiber z)) :=
      noetherianStalk_of_locallyNoetherian _ hcomp
    have _ : IsLocalRing
        ((hcompMap.fiber (c₂ (e.hom.left z))).presheaf.stalk (hcompMap.asFiber z)) :=
      LocallyRingedSpace.isLocalRing _ _
    let targetComp := c₁ ≫ e.hom.right
    have htargetComp : IsLocallyNoetherian
        (targetComp.fiber (e.hom.right (c₁ z))) :=
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation targetComp _
    have _ : IsNoetherianRing
        ((targetComp.fiber (e.hom.right (c₁ z))).presheaf.stalk (targetComp.asFiber z)) :=
      noetherianStalk_of_locallyNoetherian _ htargetComp
    have _ : IsLocalRing
        ((targetComp.fiber (e.hom.right (c₁ z))).presheaf.stalk (targetComp.asFiber z)) :=
      LocallyRingedSpace.isLocalRing _ _
    have h := (localFiberCM_iff_sourceOpenImmersion U.ι f z (hf _) (hc₁ _)).trans
      ((localFiberCM_iff_arrowIso c₁ c₂ e hc₁ hc₂ z hcomp).trans
        (localFiberCM_iff_openTarget V.ι g (g z) z (hg _) (hc₂ _)).symm)
    simp only [Scheme.Hom.IsCohenMacaulayAt]
    exact ⟨fun ⟨_, hcm⟩ => ⟨Flat.stalkMap g z, h.mp hcm⟩,
      fun ⟨_, hcm⟩ => ⟨Flat.stalkMap f (U.ι z), h.mpr hcm⟩⟩
  exact ⟨U.ι.base '' {z | Scheme.Hom.IsCohenMacaulayAt g hg z},
    Set.image_subset_iff.mpr fun z hz => (hpoint z).mpr hz,
    U.ι.isOpenEmbedding.isOpenMap _ (isOpen_affine_scheme_cm_locus g hg),
    ⟨x, hxU⟩, (hpoint ⟨x, hxU⟩).mp hx, rfl⟩

end AlgebraicGeometry
