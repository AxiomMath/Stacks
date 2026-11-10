module

public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion
public import StacksFrontier.Deformation.Artin.FormalObject

/-!
# Comparing the infinitesimal thickenings of two complete local bases

An object `x` of a category over the big fppf site of `S` that lies over the spectrum of a
Noetherian complete local ring -- an object of
`Deformation.Artin.CompleteLocalObjects` -- has a *chosen* complete local base
`Deformation.Artin.chosenBase`, picked by `Classical.choose` out of the existential
defining `Deformation.Artin.IsCompleteLocalObject`, and the approximation functor of
**Stacks 07X6** restricts `x` to the infinitesimal thickenings of *that* base. So whenever
one wants to compare the approximation of `x` with a formal object presented over a base
`A` given in advance, the two bases have to be compared, and all that is known about them is
that they have the same object of the site:
`Deformation.Artin.baseOver B S hS A hA = Deformation.Artin.baseOver B S hS A' hA'`.

This file says exactly what that hypothesis gives. The two complete local rings are
**isomorphic**, not equal, and that is the best possible: the hypothesis is an equality of the
*spectra* of the two rings, and `Scheme.Spec` is fully faithful but not injective on objects,
so `baseOver B S hS A hA = baseOver B S hS A' hA'` does *not* give `A = A'` -- it gives a
ring isomorphism `A'.R ≃+* A.R`, namely `Deformation.Artin.baseRingEquiv`, whose spectrum is
the given identification and which is compatible with the two structure morphisms to `S`.
Every comparison downstream therefore has to be made along that isomorphism, and
`Deformation.Artin.chosenBase`'s `Classical.choose` cannot be sidestepped.

A ring isomorphism of local rings carries the maximal ideal to the maximal ideal, hence each
power of it to the corresponding power, hence induces isomorphisms of the adic truncations
commuting with the projections from one truncation to the next. Passing to spectra and then
into the site gives `Deformation.Artin.truncationOverIso`, a compatible family of
isomorphisms of the objects of the site over which the levels of the two formal objects live.
That family is what a positive effectivity witness is built from: this library contains no
such witness, and nothing to transport one along a change of complete local base, so this is
a missing primitive rather than a missing lemma.
`Deformation.Artin.isEffective_of_object_over_base` is the witness it supplies, for a
category *thin* over the site -- one in which a morphism of the site lifts, and a morphism is
determined by its image in the site.

## Main definitions

* `Deformation.Artin.ringIsoOfSpecEq`: the ring isomorphism realizing an equality of spectra.
* `Deformation.Artin.adicTruncationEquiv`: the induced isomorphism of adic truncations.
* `Deformation.Artin.baseRingEquiv`: the isomorphism of two complete local bases with the
  same object of the site.
* `Deformation.Artin.truncationOverIso`: the induced isomorphism of their `n`-th
  infinitesimal thickenings, in the site.

## Main results

* `Deformation.Artin.specMap_ringIsoOfSpecEq`, `Deformation.Artin.specMap_baseRingEquiv`: the
  constructed isomorphisms have the prescribed spectra.
* `Deformation.Artin.toS_eq_of_baseOver_eq`,
  `Deformation.Artin.specMap_baseRingEquiv_toS`: compatibility with the structure morphisms
  to `S`.
* `Deformation.Artin.truncationOverSucc_comp_truncationOverIso`: the isomorphisms of
  thickenings commute with the inclusion of one thickening in the next.
* `Deformation.Artin.isEffective_of_object_over_base`: a formal object of a thin category
  over the site is effective as soon as some object of the category lies over the spectrum of
  its complete local base.

## References

* [Stacks Project, Tag 07X6](https://stacks.math.columbia.edu/tag/07X6)
* [Stacks Project, Tag 07X7](https://stacks.math.columbia.edu/tag/07X7)
-/

@[expose] public noncomputable section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u v w

/-! ### Ring isomorphisms realizing an equality of spectra -/

/-- **A ring isomorphism realizing an equality of spectra.** `Scheme.Spec` is fully
faithful, so the identification of the two spectra is the spectrum of a unique ring map, and
that map is an isomorphism because its spectrum is one. The direction is the contravariant
one: an equality `Spec R = Spec R'` is realized by a map `R' ⟶ R`. -/
public def ringIsoOfSpecEq {R R' : CommRingCat.{u}}
    (h : (Spec R : Scheme.{u}) = Spec R') : R' ≅ R :=
  (Scheme.Spec.preimageIso (eqToIso h)).unop

/-- The isomorphism of `Deformation.Artin.ringIsoOfSpecEq` has the prescribed spectrum. -/
@[simp]
public theorem specMap_ringIsoOfSpecEq {R R' : CommRingCat.{u}}
    (h : (Spec R : Scheme.{u}) = Spec R') :
    Spec.map (ringIsoOfSpecEq h).hom = eqToHom h := by
  change Scheme.Spec.map (Scheme.Spec.preimage (eqToIso h).hom) = eqToHom h
  exact Scheme.Spec.map_preimage _

/-! ### Adic truncations along an isomorphism of local rings -/

section LocalRings

variable {R R' : Type u} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']

/-- **The isomorphism of adic truncations induced by an isomorphism of local rings.** A ring
isomorphism carries the maximal ideal to the maximal ideal, hence each power of it to the
corresponding power. -/
public def adicTruncationEquiv (e : R ≃+* R') (n : ℕ) :
    R ⧸ maximalIdeal R ^ (n + 1) ≃+* R' ⧸ maximalIdeal R' ^ (n + 1) :=
  Ideal.quotientEquiv _ _ e (by
    rw [Ideal.map_pow]
    exact congrArg (fun I : Ideal R' => I ^ (n + 1))
      (IsLocalRing.map_ringEquiv_maximalIdeal e).symm)

/-- `Deformation.Artin.adicTruncationEquiv` is induced by the given isomorphism. -/
@[simp]
public theorem adicTruncationEquiv_mk (e : R ≃+* R') (n : ℕ) (r : R) :
    adicTruncationEquiv e n (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) r) =
      Ideal.Quotient.mk (maximalIdeal R' ^ (n + 1)) (e r) := by
  simp [adicTruncationEquiv]

/-- The induced isomorphism of adic truncations is compatible with the quotient maps. -/
public theorem adicTruncationEquiv_comp_mk (e : R ≃+* R') (n : ℕ) :
    (adicTruncationEquiv e n).toRingHom.comp
        (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) =
      (Ideal.Quotient.mk (maximalIdeal R' ^ (n + 1))).comp e.toRingHom :=
  RingHom.ext fun r => adicTruncationEquiv_mk e n r

/-- The induced isomorphisms of adic truncations are compatible with the projections from one
truncation to the next. -/
public theorem adicTruncationEquiv_comp_factorPow (e : R ≃+* R') (n : ℕ) :
    (adicTruncationEquiv e n).toRingHom.comp
        (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))) =
      (Ideal.Quotient.factorPow (maximalIdeal R') (Nat.le_succ (n + 1))).comp
        (adicTruncationEquiv e (n + 1)).toRingHom := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  simp [Ideal.Quotient.factorPow]

/-- The induced isomorphism of adic truncations of the inverse isomorphism is the inverse. -/
public theorem adicTruncationEquiv_symm_comp (e : R ≃+* R') (n : ℕ) :
    (adicTruncationEquiv e.symm n).toRingHom.comp
        (adicTruncationEquiv e n).toRingHom = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  simp

/-- The inverse of the induced isomorphism of adic truncations is compatible with the
quotient maps. -/
public theorem adicTruncationEquiv_symm_comp_mk (e : R ≃+* R') (n : ℕ) :
    (adicTruncationEquiv e n).symm.toRingHom.comp
        (Ideal.Quotient.mk (maximalIdeal R' ^ (n + 1))) =
      (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))).comp e.symm.toRingHom :=
  RingHom.ext fun r' => by
    change (adicTruncationEquiv e n).symm
        (Ideal.Quotient.mk (maximalIdeal R' ^ (n + 1)) r') =
      Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) (e.symm r')
    rw [RingEquiv.symm_apply_eq, adicTruncationEquiv_mk, e.apply_symm_apply]

/-- The induced isomorphism of adic truncations is compatible with the canonical maps to the
spectrum of the ring. -/
public theorem specMap_adicTruncationEquiv_comp_ι (e : R ≃+* R') (n : ℕ) :
    Spec.map (CommRingCat.ofHom (adicTruncationEquiv e n).toRingHom) ≫
        adicThickeningι R (maximalIdeal R) n =
      adicThickeningι R' (maximalIdeal R') n ≫
        Spec.map (CommRingCat.ofHom e.toRingHom) := by
  rw [adicThickeningι, adicThickeningι, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (adicTruncationEquiv_comp_mk e n)

/-- The induced isomorphisms of adic truncations are compatible with the inclusion of one
thickening in the next. -/
public theorem specMap_adicTruncationEquiv_comp_succ (e : R ≃+* R') (n : ℕ) :
    adicThickeningSucc R' (maximalIdeal R') n ≫
        Spec.map (CommRingCat.ofHom (adicTruncationEquiv e (n + 1)).toRingHom) =
      Spec.map (CommRingCat.ofHom (adicTruncationEquiv e n).toRingHom) ≫
        adicThickeningSucc R (maximalIdeal R) n := by
  rw [adicThickeningSucc, adicThickeningSucc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (adicTruncationEquiv_comp_factorPow e n).symm

end LocalRings

/-! ### Complete local bases with the same object of the site -/

section Bases

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A A' : FormalBase S} {hA : B.Contains (Spec (.of A.R))}
  {hA' : B.Contains (Spec (.of A'.R))}

/-- The object of the site attached to a complete local base depends only on the base: the
containment hypothesis is a proposition. -/
public theorem baseOver_congr {A₁ A₂ : FormalBase S} (hb : A₁ = A₂)
    (h₁ : B.Contains (Spec (.of A₁.R))) (h₂ : B.Contains (Spec (.of A₂.R))) :
    baseOver B S hS A₁ h₁ = baseOver B S hS A₂ h₂ := by
  subst hb; rfl

/-- **Two complete local bases giving the same object of the site have the same spectrum.**
The site is a full subcategory of schemes cut out by a size bound, so the underlying object
of an equality in the slice category is an equality of schemes. -/
public theorem spec_eq_of_baseOver_eq (h : baseOver B S hS A hA = baseOver B S hS A' hA') :
    (Spec (.of A.R) : Scheme.{u}) = Spec (.of A'.R) :=
  congrArg ObjectProperty.FullSubcategory.obj (congrArg Over.left h)

/-- **The structure morphisms of two complete local bases giving the same object of the site
agree** through the identification of their spectra. -/
public theorem toS_eq_of_baseOver_eq (h : baseOver B S hS A hA = baseOver B S hS A' hA') :
    eqToHom (spec_eq_of_baseOver_eq B S hS h) ≫ A'.toS = A.toS := by
  have hw : B.inclusion.map
      ((eqToHom h : baseOver B S hS A hA ⟶ baseOver B S hS A' hA').left ≫
        (baseOver B S hS A' hA').hom) =
      B.inclusion.map (baseOver B S hS A hA).hom :=
    congrArg B.inclusion.map (Over.w (eqToHom h))
  rw [Functor.map_comp, Over.eqToHom_left, eqToHom_map] at hw
  exact hw

/-- **The isomorphism of complete local bases realizing an equality of their objects in the
site**, in the contravariant direction. -/
public def baseRingEquiv (h : baseOver B S hS A hA = baseOver B S hS A' hA') :
    A'.R ≃+* A.R :=
  (ringIsoOfSpecEq (spec_eq_of_baseOver_eq B S hS h)).commRingCatIsoToRingEquiv

/-- `Deformation.Artin.baseRingEquiv` has the prescribed spectrum. -/
public theorem specMap_baseRingEquiv
    (h : baseOver B S hS A hA = baseOver B S hS A' hA') :
    Spec.map (CommRingCat.ofHom (baseRingEquiv B S hS h).toRingHom) =
      eqToHom (spec_eq_of_baseOver_eq B S hS h) := by
  rw [show CommRingCat.ofHom (baseRingEquiv B S hS h).toRingHom =
      (ringIsoOfSpecEq (spec_eq_of_baseOver_eq B S hS h)).hom from rfl]
  exact specMap_ringIsoOfSpecEq _

/-- `Deformation.Artin.baseRingEquiv` is compatible with the structure morphisms. -/
public theorem specMap_baseRingEquiv_toS
    (h : baseOver B S hS A hA = baseOver B S hS A' hA') :
    Spec.map (CommRingCat.ofHom (baseRingEquiv B S hS h).toRingHom) ≫ A'.toS = A.toS := by
  rw [specMap_baseRingEquiv]
  exact toS_eq_of_baseOver_eq B S hS h

/-- **The infinitesimal thickenings of two complete local bases giving the same object of the
site agree, compatibly with the inclusions of one thickening in the next.** The two bases are
isomorphic as rings by `Deformation.Artin.baseRingEquiv` -- which is as much as can be
expected: an equality of the objects of the site is an equality of the *spectra*, and
`Scheme.Spec` is only fully faithful, not injective on objects -- and a ring isomorphism
carries each power of the maximal ideal to the corresponding power, hence induces
isomorphisms of the truncations commuting with the projections. -/
public def truncationSchemeIso (h : baseOver B S hS A hA = baseOver B S hS A' hA') (n : ℕ) :
    (A.truncation n : Scheme.{u}) ≅ A'.truncation n where
  hom := Spec.map (CommRingCat.ofHom
    (adicTruncationEquiv (baseRingEquiv B S hS h) n).toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (adicTruncationEquiv (baseRingEquiv B S hS h) n).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (adicTruncationEquiv (baseRingEquiv B S hS h) n).toRingHom.comp
          (adicTruncationEquiv (baseRingEquiv B S hS h) n).symm.toRingHom = RingHom.id _ from
        RingHom.ext fun x =>
          (adicTruncationEquiv (baseRingEquiv B S hS h) n).apply_symm_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (adicTruncationEquiv (baseRingEquiv B S hS h) n).symm.toRingHom.comp
          (adicTruncationEquiv (baseRingEquiv B S hS h) n).toRingHom = RingHom.id _ from
        RingHom.ext fun x =>
          (adicTruncationEquiv (baseRingEquiv B S hS h) n).symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]

/-- The isomorphism of `n`-th thickenings, as an isomorphism of the site's underlying
category. -/
public def truncationSchemesIso (h : baseOver B S hS A hA = baseOver B S hS A' hA')
    (cA : ∀ n, B.Contains (A.truncation n)) (cA' : ∀ n, B.Contains (A'.truncation n))
    (n : ℕ) :
    (⟨A.truncation n, cA n⟩ : B.Schemes) ≅ ⟨A'.truncation n, cA' n⟩ where
  hom := ObjectProperty.homMk (truncationSchemeIso B S hS h n).hom
  inv := ObjectProperty.homMk (truncationSchemeIso B S hS h n).inv
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact (truncationSchemeIso B S hS h n).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact (truncationSchemeIso B S hS h n).inv_hom_id

/-- **The `n`-th infinitesimal thickenings of two complete local bases giving the same object
of the site are isomorphic in the site.** -/
public def truncationOverIso (h : baseOver B S hS A hA = baseOver B S hS A' hA')
    (cA : ∀ n, B.Contains (A.truncation n)) (cA' : ∀ n, B.Contains (A'.truncation n))
    (n : ℕ) : truncationOver B S hS A cA n ≅ truncationOver B S hS A' cA' n :=
  Over.isoMk (truncationSchemesIso B S hS h cA cA' n) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    change (truncationSchemeIso B S hS h n).hom ≫ A'.truncationToS n = A.truncationToS n
    change Spec.map (CommRingCat.ofHom
        (adicTruncationEquiv (baseRingEquiv B S hS h) n).toRingHom) ≫
      A'.truncationToS n = A.truncationToS n
    rw [FormalBase.truncationToS, FormalBase.truncationToS, ← Category.assoc,
      specMap_adicTruncationEquiv_comp_ι, Category.assoc,
      specMap_baseRingEquiv_toS B S hS h])

/-- **The isomorphisms of infinitesimal thickenings commute with the inclusions of one
thickening in the next.** -/
public theorem truncationOverSucc_comp_truncationOverIso
    (h : baseOver B S hS A hA = baseOver B S hS A' hA')
    (cA : ∀ n, B.Contains (A.truncation n)) (cA' : ∀ n, B.Contains (A'.truncation n))
    (n : ℕ) :
    truncationOverSucc B S hS A cA n ≫ (truncationOverIso B S hS h cA cA' (n + 1)).hom =
      (truncationOverIso B S hS h cA cA' n).hom ≫ truncationOverSucc B S hS A' cA' n := by
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  rw [Over.comp_left, Over.comp_left, Functor.map_comp, Functor.map_comp]
  change A.truncationSucc n ≫ (truncationSchemeIso B S hS h (n + 1)).hom =
    (truncationSchemeIso B S hS h n).hom ≫ A'.truncationSucc n
  exact specMap_adicTruncationEquiv_comp_succ (baseRingEquiv B S hS h) n

end Bases

/-! ### Effectivity in a thin category over the site -/

section Effectivity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A formal object of a thin category over the site is effective as soon as some object of
the category lies over the spectrum of its complete local base.**

"Thin" is the conjunction of the two hypotheses: a morphism of the site lifts to a morphism
of `F` (`hlift`), and a morphism of `F` is determined by its image in the site (`hthin`).

Given an object `x` over `Spec` of the base of `ξ`, the approximation of `x` restricts to the
infinitesimal thickenings of the *chosen* complete local base of `x`, which the hypothesis
identifies with the base of `ξ` only up to the isomorphism of
`Deformation.Artin.baseRingEquiv`. `Deformation.Artin.truncationOverIso` turns that
isomorphism into a compatible family of isomorphisms of the objects of the site over which
the two formal objects' levels live, and `hlift` with `hthin` lifts that family to an
isomorphism of formal objects: the level maps exist by `hlift`, and every equation between
them -- the two naturality squares and the two identities -- is an equation of morphisms of
the site by `hthin`. -/
public theorem isEffective_of_object_over_base
    (hlift : ∀ {z w : F} (t : p.obj z ⟶ p.obj w), ∃ s : z ⟶ w, p.map s = t)
    (hthin : ∀ {z w : F} (s t : z ⟶ w), p.map s = p.map t → s = t)
    (ξ : FormalObject B S hS p) (hA : B.Contains (Spec (.of ξ.base.R)))
    (x : CompleteLocalObjects B S hS p)
    (hx : p.obj x.obj.1 = baseOver B S hS ξ.base hA) :
    FormalObject.IsEffective B S hS p hp ξ := by
  classical
  obtain ⟨-, hbase, -, -, -, -⟩ := (approximationFunctorData B S hS p hp).2
  refine ⟨x, ?_⟩
  set η := (approximationFunctorData B S hS p hp).1.obj x with hηdef
  have hηA : B.Contains (Spec (.of η.base.R)) := by
    rw [hbase x]; exact chosenContains B S hS p x.obj
  have hbo : baseOver B S hS η.base hηA = baseOver B S hS ξ.base hA :=
    (baseOver_congr B S hS (hbase x) hηA (chosenContains B S hS p x.obj)).trans
      ((chosenBase_eq B S hS p x.obj).symm.trans hx)
  obtain ⟨θ, hθ⟩ : ∃ θ : ∀ n, truncationOver B S hS η.base η.contains n ≅
      truncationOver B S hS ξ.base ξ.contains n,
      ∀ n, truncationOverSucc B S hS η.base η.contains n ≫ (θ (n + 1)).hom =
        (θ n).hom ≫ truncationOverSucc B S hS ξ.base ξ.contains n :=
    ⟨truncationOverIso B S hS hbo η.contains ξ.contains,
      truncationOverSucc_comp_truncationOverIso B S hS hbo η.contains ξ.contains⟩
  choose s hs using fun n => hlift (z := η.level n) (w := ξ.level n)
    (eqToHom (η.level_eq n) ≫ (θ n).hom ≫ eqToHom (ξ.level_eq n).symm)
  choose s' hs' using fun n => hlift (z := ξ.level n) (w := η.level n)
    (eqToHom (ξ.level_eq n) ≫ (θ n).inv ≫ eqToHom (η.level_eq n).symm)
  have htrans : ∀ (ζ : FormalObject B S hS p) (n : ℕ), p.map (ζ.transition n) =
      eqToHom (ζ.level_eq n) ≫ truncationOverSucc B S hS ζ.base ζ.contains n ≫
        eqToHom (ζ.level_eq (n + 1)).symm := fun ζ n => by
    let := ζ.transition_lift n
    exact IsHomLift.fac' p _ (ζ.transition n)
  have hnat_of : ∀ (ζ ζ' : FormalObject B S hS p)
      (φ : ∀ n, truncationOver B S hS ζ.base ζ.contains n ⟶
        truncationOver B S hS ζ'.base ζ'.contains n)
      (hφ : ∀ n, truncationOverSucc B S hS ζ.base ζ.contains n ≫ φ (n + 1) =
        φ n ≫ truncationOverSucc B S hS ζ'.base ζ'.contains n)
      (t : ∀ n, ζ.level n ⟶ ζ'.level n)
      (ht : ∀ n, p.map (t n) = eqToHom (ζ.level_eq n) ≫ φ n ≫ eqToHom (ζ'.level_eq n).symm)
      (n : ℕ), ζ.transition n ≫ t (n + 1) = t n ≫ ζ'.transition n := fun ζ ζ' φ hφ t ht n =>
    hthin _ _ (by
      rw [Functor.map_comp, Functor.map_comp, ht (n + 1), ht n, htrans ζ n, htrans ζ' n]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% hφ n])
  have hθ' : ∀ n, truncationOverSucc B S hS ξ.base ξ.contains n ≫ (θ (n + 1)).inv =
      (θ n).inv ≫ truncationOverSucc B S hS η.base η.contains n := fun n => by
    rw [Iso.comp_inv_eq, Category.assoc, hθ n]
    simp
  have hss' : ∀ n, s n ≫ s' n = 𝟙 (η.level n) := fun n =>
    hthin _ _ (by
      rw [Functor.map_comp, hs n, hs' n, CategoryTheory.Functor.map_id]
      simp)
  have hs's : ∀ n, s' n ≫ s n = 𝟙 (ξ.level n) := fun n =>
    hthin _ _ (by
      rw [Functor.map_comp, hs' n, hs n, CategoryTheory.Functor.map_id]
      simp)
  exact ⟨Iso.mk (X := η) (Y := ξ) ⟨s, hnat_of η ξ (fun n => (θ n).hom) hθ s hs⟩
    ⟨s', hnat_of ξ η (fun n => (θ n).inv) hθ' s' hs'⟩
    (FormalObject.Hom.ext hss') (FormalObject.Hom.ext hs's)⟩

end Effectivity

end Deformation.Artin

end
