module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSmoothBadPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.NodalContraction.DvrStalk
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Contracting an exceptional curve in a nodal relative curve: flatness

Let `b : X ⟶ X'` contract an exceptional curve of the first kind `E ⊆ X`, presented by its ideal
sheaf `D` and an isomorphism `e : 𝐏¹_k ≅ E`, and let `f' : X' ⟶ Spec R` be a morphism to the
spectrum of a discrete valuation ring such that `b ≫ f'` is at worst nodal of relative dimension
one. This file proves that `f'` is flat.

Flatness is checked on stalks. Away from the point `z` that `b` contracts, `b` is an isomorphism,
so the structure morphism of the open complement of `z` is at worst nodal, hence flat. At `z`
itself the local ring of `X'` is regular, hence a domain, while the local ring of `Spec R` is a
localization of `R`, hence a principal ideal domain; the stalk map at `z` is injective because
`b` is surjective and `b ≫ f'` is flat, and an injective map from a Bézout domain into a domain
is flat.

## Main results

* `AlgebraicGeometry.flat_of_isContractionOfExceptionalCurve` — the contraction of an exceptional
  curve of the first kind in an at-worst-nodal relative curve over a discrete valuation ring is
  flat over that discrete valuation ring.
* `AlgebraicGeometry.flat_of_isContractionOfExceptionalCurve_of_flat_comp` — more generally, a
  morphism from the target of a contraction to the spectrum of a discrete valuation ring is flat
  as soon as its composite with the contraction is.

## References

* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An injective ring map from a Bézout domain to a domain is flat: the target is torsion-free,
and over a Bézout domain torsion-free modules are flat. -/
@[ega "0 6.3.4" "Bézout base", sga "1 IV 1.3" "(ii)"]
private theorem flat_of_injective_of_isBezout {A B : Type u} [CommRing A] [IsDomain A]
    [IsBezout A] [CommRing B] [IsDomain B] (φ : A →+* B) (hφ : Function.Injective φ) :
    φ.Flat := by
  let := φ.toAlgebra
  change Module.Flat A B
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  exact Module.isTorsionFree_iff_algebraMap_injective.mpr hφ

/-- If the composite `b ≫ f` of a surjection `b` with `f` is flat, then the stalk maps of `f`
are injective, being the right factors of the injective stalk maps of `b ≫ f`. -/
private theorem injective_stalkMap_of_surjective_of_flat_comp {X Y S : Scheme.{u}}
    (b : X ⟶ Y) (f : Y ⟶ S) [Flat (b ≫ f)] (hb : Function.Surjective b.base) (y : Y) :
    Function.Injective (f.stalkMap y).hom := by
  obtain ⟨x, rfl⟩ := hb y
  have key : ∀ w : S.presheaf.stalk (f (b x)),
      (b.stalkMap x).hom ((f.stalkMap (b x)).hom w) = ((b ≫ f).stalkMap x).hom w := by
    intro w
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  intro a a' ha
  refine Flat.injective_stalkMap (b ≫ f) x ?_
  rw [← key a, ← key a', ha]

/-- If the restriction of `f` to an open subset `U` is flat, then the stalk map of `f` at every
point of `U` is flat: the stalk maps of the open immersion are isomorphisms. -/
private theorem flat_stalkMap_of_flat_on_open {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    [Flat (U.ι ≫ f)] (x : X) (hx : x ∈ U) : (f.stalkMap x).hom.Flat := by
  have h : ((U.ι ≫ f).stalkMap ⟨x, hx⟩).hom.Flat := Flat.stalkMap (U.ι ≫ f) ⟨x, hx⟩
  have key : ∀ w : S.presheaf.stalk ((U.ι ≫ f) (⟨x, hx⟩ : U)),
      ((U.ι ≫ f).stalkMap ⟨x, hx⟩).hom w =
        (U.ι.stalkMap ⟨x, hx⟩).hom ((f.stalkMap x).hom w) := by
    intro w
    rw [Scheme.Hom.stalkMap_comp U.ι f ⟨x, hx⟩]
    rfl
  have hcomp : ((U.ι ≫ f).stalkMap ⟨x, hx⟩).hom =
      (U.ι.stalkMap ⟨x, hx⟩).hom.comp (f.stalkMap x).hom :=
    RingHom.ext fun w => key w
  rw [hcomp] at h
  refine (RingHom.Flat.comp_iff_of_bijective_left ?_).mp h
  have hbij : Function.Bijective (U.stalkIso ⟨x, hx⟩).inv.hom :=
    (U.stalkIso ⟨x, hx⟩).symm.commRingCatIsoToRingEquiv.bijective
  rwa [Scheme.Opens.stalkIso_inv] at hbij

/-- A morphism `f` to the spectrum of a discrete valuation ring is flat if it is flat off a closed
point `z` with regular local ring and `b ≫ f` is flat for a surjection `b`. -/
private theorem flat_of_flat_off_point_of_flat_comp {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X X' : Scheme.{u}} (b : X ⟶ X') (f' : X' ⟶ Spec (.of R))
    [Flat (b ≫ f')] (hsurj : Function.Surjective b.base) (z : X') (hz : IsClosed ({z} : Set X'))
    (hreg : IsRegularLocalRing (X'.presheaf.stalk z))
    [Flat (Scheme.Opens.ι (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens) ≫ f')] : Flat f' := by
  apply Flat.of_stalkMap
  intro y
  by_cases hy : y = z
  · subst hy
    have := hreg
    have : IsDomain (X'.presheaf.stalk y) := IsRegularLocalRing.isDomain _
    have : IsPrincipalIdealRing ((Spec (.of R)).presheaf.stalk (f' y)) :=
      isPrincipalIdealRing_stalk_spec (f' y)
    have : IsDomain ((Spec (.of R)).presheaf.stalk (f' y)) := isDomain_stalk_spec (f' y)
    exact flat_of_injective_of_isBezout (f'.stalkMap y).hom
      (injective_stalkMap_of_surjective_of_flat_comp b f' hsurj y)
  · exact flat_stalkMap_of_flat_on_open f' ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ y
      (by simpa using hy)

/-- **Stacks Project, Tag 0CDF** (flatness). Let `b : X ⟶ X'` contract an exceptional curve of
the first kind with ideal sheaf `D` in a scheme at worst nodal of relative dimension one over a
discrete valuation ring `R`. Then the induced morphism `f' : X' ⟶ Spec R` is flat. -/
public theorem flat_of_isContractionOfExceptionalCurve
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f')) :
    Flat f' := by
  have hsurj := surjective_of_isContractionOfExceptionalCurve D k e b hb
  have : Flat (b ≫ f') := AlgebraicGeometry.flat hf.1.1
  obtain ⟨z, hz, hreg, hdim, hD, ε, hε⟩ := hb.exists_blowUp_iso
  have hW : Flat (Scheme.Opens.ι (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens) ≫ f') :=
    AlgebraicGeometry.flat (nodal_on_compl_centre b z hz ε hε f' hf).1.1
  exact flat_of_flat_off_point_of_flat_comp b f' hsurj z hz hreg

/-- Let `b : X ⟶ X'` contract an exceptional curve of the first kind with ideal sheaf `D`, and let
`f' : X' ⟶ Spec R` be a morphism to the spectrum of a discrete valuation ring `R`. If `b ≫ f'` is
flat, then so is `f'`. Away from the contracted point `b` is an isomorphism; at that point the
local ring of `X'` is a regular local ring, hence a domain, and the stalk map of `f'` is
injective, so it is flat over the principal ideal domain it starts from. -/
public theorem flat_of_isContractionOfExceptionalCurve_of_flat_comp
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (.of R)) [Flat (b ≫ f')] :
    Flat f' := by
  have hsurj := surjective_of_isContractionOfExceptionalCurve D k e b hb
  obtain ⟨z, hz, hreg, hdim, hD, ε, hε⟩ := hb.exists_blowUp_iso
  let W : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
  have hoff : IsIso (b ∣_ W) :=
    isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ε hε
  have hW : Flat (W.ι ≫ f') := by
    have hfac : W.ι ≫ f' = inv (b ∣_ W) ≫ (b ⁻¹ᵁ W).ι ≫ b ≫ f' := by
      rw [← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc]
    rw [hfac]
    infer_instance
  exact flat_of_flat_off_point_of_flat_comp b f' hsurj z hz hreg

end AlgebraicGeometry

end
