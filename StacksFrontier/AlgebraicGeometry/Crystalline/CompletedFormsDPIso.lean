module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BigradedForms

/-!
# An isomorphism of divided power rings is an isomorphism of completed de Rham complexes

`Crystalline.completedMapDifferentialForms` carries a divided power morphism
`(B, J, δ) → (C, K, ε)` over `A` up to a comparison `Ω̂^i_B → Ω̂^i_C` of the `p`-adically
completed divided power differential forms, and
`Crystalline.completedMapDifferentialForms_wedge`, `..._wedgeMul`, `..._deRham` and
`..._completedFormsDifferential_of` say that the comparison respects the wedge product in the
bidegree the de Rham complex uses, the wedge product in a general bidegree, the de Rham
differential and the universal differential.  When the morphism is an *isomorphism* of divided
power rings — a divided power morphism both ways whose composites are the identity — the
comparison is an isomorphism, by the functoriality
`Crystalline.completedMapDifferentialForms_eq_comp` and
`Crystalline.completedMapDifferentialForms_eq_self`.

This module bundles these facts as `Crystalline.CompletedFormsDPIso` and builds the bundle from a
divided power isomorphism.

## Main definitions

* `Crystalline.CompletedFormsDPIso` — the bundle: an additive equivalence
  `Ω̂^i_B ≃ Ω̂^i_C` in every degree, together with its compatibility with the two wedge
  products, the de Rham differential and the universal differential.
* `Crystalline.completedFormsDPIso` — the bundle of a divided power isomorphism over `A`.

## Main results

* `Crystalline.completedMapDifferentialForms_symm_comp` — the comparisons along the two halves of
  a divided power isomorphism are mutually inverse.

## References

* [Stacks Project, Tag 07HZ](https://stacks.math.columbia.edu/tag/07HZ)
* [Stacks Project, Lemma 60.20.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public section

open DividedPowers

universe u v

namespace Crystalline

variable (p : ℕ) (A : Type u) [CommRing A] {B : Type v} [CommRing B] [Algebra A B]
  {J : Ideal B} (hJ : DividedPowers J)
  {C : Type v} [CommRing C] [Algebra A C] {K : Ideal C} (epsilon : DividedPowers K)

/-- **An isomorphism `Ω̂^*_B ≅ Ω̂^*_C` of the completed divided power de Rham complexes**: an
additive equivalence in every exterior degree, compatible with the wedge product in the bidegree
the de Rham complex is built from, with the wedge product in a general bidegree, with the de
Rham differential, and with the universal differential `d` on the canonical image of the
uncompleted ring, along the `A`-algebra map `algHom : B → C`.

The equivalence is additive, the two sides being modules over the different rings `B̂` and
`Ĉ`. -/
public structure CompletedFormsDPIso where
  /-- The comparison of completed forms in each exterior degree. -/
  equiv : ∀ i, completedDividedPowerForms p A hJ i ≃+ completedDividedPowerForms p A epsilon i
  /-- The comparison respects the wedge product by a one-form. -/
  wedge : ∀ (i : ℕ) (x : completedDividedPowerForms p A hJ i)
    (y : completedDividedPowerForms p A hJ 1),
    equiv (i + 1) (completedDividedPowerWedge p A hJ i x y) =
      completedDividedPowerWedge p A epsilon i (equiv i x) (equiv 1 y)
  /-- The comparison respects the wedge product in a general bidegree. -/
  wedgeMul : ∀ (i j : ℕ) (x : completedDividedPowerForms p A hJ i)
    (y : completedDividedPowerForms p A hJ j),
    equiv (i + j) (completedDividedPowerWedgeMul p A hJ i j x y) =
      completedDividedPowerWedgeMul p A epsilon i j (equiv i x) (equiv j y)
  /-- The comparison respects the de Rham differential. -/
  deRham : ∀ (i : ℕ) (x : completedDividedPowerForms p A hJ i),
    equiv (i + 1) (completedDividedPowerDeRham p A hJ i x) =
      completedDividedPowerDeRham p A epsilon i (equiv i x)
  /-- The `A`-algebra map `B → C` underlying the comparison. -/
  algHom : B →ₐ[A] C
  /-- The comparison respects the universal differential `d`, on the canonical image of `B`. -/
  differential : ∀ b : B,
    equiv 1 (completedFormsDifferential p A hJ (AdicCompletion.of (pAdicIdeal (A := B) p) B b)) =
      completedFormsDifferential p A epsilon
        (AdicCompletion.of (pAdicIdeal (A := C) p) C (algHom b))

section Construction

/-- The comparisons of completed forms along the two halves of a divided power isomorphism are
mutually inverse. -/
public theorem completedMapDifferentialForms_symm_comp (e : B →ₐ[A] C) (e' : C →ₐ[A] B)
    (he : DividedPowers.IsDPMorphism hJ epsilon e.toRingHom)
    (he' : DividedPowers.IsDPMorphism epsilon hJ e'.toRingHom)
    (hee' : AlgHom.id A B = e'.comp e) (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    completedMapDifferentialForms p A epsilon hJ e' he' i
        (completedMapDifferentialForms p A hJ epsilon e he i x) = x :=
  (completedMapDifferentialForms_eq_comp p A hJ epsilon hJ e e' (AlgHom.id A B) he he'
    (DividedPowers.DPMorphism.id hJ).isDPMorphism hee' i x).symm.trans
    (completedMapDifferentialForms_eq_self p A hJ (AlgHom.id A B)
      (DividedPowers.DPMorphism.id hJ).isDPMorphism rfl i x)

/-- **The bundled isomorphism of completed de Rham complexes of a divided power isomorphism over
`A`.** For divided power morphisms `e : B → C` and `e' : C → B` over `A` that are mutually inverse,
the comparison `Crystalline.completedMapDifferentialForms` along `e`, with inverse the comparison
along `e'`. -/
public noncomputable def completedFormsDPIso (e : B →ₐ[A] C) (e' : C →ₐ[A] B)
    (he : DividedPowers.IsDPMorphism hJ epsilon e.toRingHom)
    (he' : DividedPowers.IsDPMorphism epsilon hJ e'.toRingHom)
    (hee' : AlgHom.id A B = e'.comp e) (he'e : AlgHom.id A C = e.comp e') :
    CompletedFormsDPIso p A hJ epsilon where
  equiv i :=
    { toFun := completedMapDifferentialForms p A hJ epsilon e he i
      invFun := completedMapDifferentialForms p A epsilon hJ e' he' i
      left_inv := completedMapDifferentialForms_symm_comp p A hJ epsilon e e' he he' hee' i
      right_inv := completedMapDifferentialForms_symm_comp p A epsilon hJ e' e he' he he'e i
      map_add' := map_add _ }
  wedge i x y := completedMapDifferentialForms_wedge p A hJ epsilon e he i x y
  wedgeMul i j x y := completedMapDifferentialForms_wedgeMul p A hJ epsilon e he i j x y
  deRham i x := completedMapDifferentialForms_deRham p A hJ epsilon e he i x
  algHom := e
  differential b :=
    completedMapDifferentialForms_completedFormsDifferential_of p A hJ epsilon e he b

/-- The equivalence of `Crystalline.completedFormsDPIso` is the comparison along `e`. -/
@[simp] public theorem completedFormsDPIso_equiv_apply (e : B →ₐ[A] C) (e' : C →ₐ[A] B)
    (he : DividedPowers.IsDPMorphism hJ epsilon e.toRingHom)
    (he' : DividedPowers.IsDPMorphism epsilon hJ e'.toRingHom)
    (hee' : AlgHom.id A B = e'.comp e) (he'e : AlgHom.id A C = e.comp e') (i : ℕ)
    (x : completedDividedPowerForms p A hJ i) :
    (completedFormsDPIso p A hJ epsilon e e' he he' hee' he'e).equiv i x =
      completedMapDifferentialForms p A hJ epsilon e he i x := rfl

/-- The inverse of the equivalence of `Crystalline.completedFormsDPIso` is the comparison along
`e'`. -/
@[simp] public theorem completedFormsDPIso_equiv_symm_apply (e : B →ₐ[A] C) (e' : C →ₐ[A] B)
    (he : DividedPowers.IsDPMorphism hJ epsilon e.toRingHom)
    (he' : DividedPowers.IsDPMorphism epsilon hJ e'.toRingHom)
    (hee' : AlgHom.id A B = e'.comp e) (he'e : AlgHom.id A C = e.comp e') (i : ℕ)
    (y : completedDividedPowerForms p A epsilon i) :
    ((completedFormsDPIso p A hJ epsilon e e' he he' hee' he'e).equiv i).symm y =
      completedMapDifferentialForms p A epsilon hJ e' he' i y := rfl

/-- The algebra map of `Crystalline.completedFormsDPIso` is `e`. -/
@[simp] public theorem completedFormsDPIso_algHom (e : B →ₐ[A] C) (e' : C →ₐ[A] B)
    (he : DividedPowers.IsDPMorphism hJ epsilon e.toRingHom)
    (he' : DividedPowers.IsDPMorphism epsilon hJ e'.toRingHom)
    (hee' : AlgHom.id A B = e'.comp e) (he'e : AlgHom.id A C = e.comp e') :
    (completedFormsDPIso p A hJ epsilon e e' he he' hee' he'e).algHom = e := rfl

end Construction

end Crystalline

end
