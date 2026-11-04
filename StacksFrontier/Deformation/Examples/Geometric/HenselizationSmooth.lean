module

public import StacksFrontier.Deformation.Examples.Geometric.CompletionSmooth
public import StacksFrontier.Deformation.Examples.Geometric.Henselization
public import StacksFrontier.Deformation.Examples.Geometric.HenselizationDifferential
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationSmooth
public import StacksFrontier.Deformation.FlatAlgebraLiftHenselizationRelative

/-!
# Smoothness of the henselization functor on deformations

Let `k` be a field, `P` a finite type `k`-algebra which is smooth over `k` outside the zero set
of an ideal `J ⊆ P`, and `(Pʰ, Jʰ)` the henselization of the pair `(P, J)`. Henselization of
deformations is a functor `𝓓_P ⟶ 𝓓_{Pʰ}` over `𝒞_Λ` (**Stacks 0DYT**), and **Stacks 0DZD**
asserts that it is smooth and induces an isomorphism on tangent spaces. This file supplies one
of the two inputs of the criterion of **Stacks 0DYP**, the correspondence of liftability, and
concludes smoothness. The other input, surjectivity of the differential, is
`Deformation.Examples.bijective_differential_henselizationFunctorData`.

The correspondence is **Stacks 0DZB** for the ideal `𝔟 = π⁻¹(J)` of the flat algebra `Q` of the
deformation, `π : Q → P` being the reduction: the henselized deformation is the henselization of
the pair `(Q, 𝔟)`, by the `henselizationEquiv` clause of the functor datum. Its hypotheses hold:
`B → A` is a small extension, `Q` is flat and of finite type over the Artinian base, and
`A → Q_h` is syntomic for every `h ∈ 𝔟` — the last by
`Deformation.syntomic_localizationAway_specialFiber`, since `h ∈ 𝔟` means `π(h) ∈ J`, so
`D(π(h))` lies in the smooth locus of `P` over `k`.

Because the kernel of a small extension is square-zero, the form of Stacks 0DZB used is
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_sqZero`, which carries no
hypothesis: the case of Stacks 0DZ2 it rests on is the one proved in this repository.

## Main results

* `Deformation.Examples.lifts_henselizationFunctorData`: **the correspondence of liftability**,
  with no hypothesis beyond those of Stacks 0DZD.
* `Deformation.Examples.isSmooth_henselizationFunctorData`: **the smoothness conclusion of
  Stacks 0DZD**, for an arbitrary functor datum of Stacks 0DYT.
* `Deformation.Examples.isSmooth_henselizationFunctor`: the same at the canonical henselization
  functor.

## Implementation notes

Unlike the completion functor, a `Deformation.Examples.HenselizationFunctorData` needs no extra
base-compatibility clause: `base_comm` is one of its recorded fields, and
`henselizationEquiv_algebraMap` says that the recorded identification of the fibre with the
canonical henselization carries the structure map to the henselization map. Together they are
exactly the semilinearity `Deformation.hasFlatAlgebraLift_of_ringEquiv` consumes, which is why
the statement below is for an arbitrary datum of Stacks 0DYT — including the chosen
`Deformation.Examples.henselizationFunctor` — rather than for a refinement of it.

The flat lift is transported onto the *canonical* henselization `henselization Q 𝔟`, rather than
Stacks 0DZB being applied to the fibre of the functor directly, because Stacks 0DZB wants the
henselian-pair condition together with the universal property and those are available for the
canonical construction by `henselianPair_henselization` and `henselization_universalProperty`.

## References

* [Stacks Project, Tag 0DZD](https://stacks.math.columbia.edu/tag/0DZD)
* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
* [Stacks Project, Tag 0DYP](https://stacks.math.columbia.edu/tag/0DYP)
* [Stacks Project, Tag 0DYT](https://stacks.math.columbia.edu/tag/0DYT)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u w

namespace Deformation.Examples

attribute [local instance 100] henselizationAlgebra

/-- The `cast` of the `base_comm` clause of a henselization functor datum is inverse to
`ringEquivOfEq` on the recorded equality of Artinian bases. -/
private theorem cast_ringEquivOfEq {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : ArtinianLocalAlgCat.{u, w, w} Λ k} (h : A = B) (z : (A : Type w)) :
    cast (congrArg ArtinianLocalAlgCat.carrier h.symm) ((ringEquivOfEq h) z) = z := by
  subst h
  rfl

section Smoothness

open InfinitesimalLifting

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)

/-- **The correspondence of liftability for the henselization functor.** This is one of the two
inputs of the criterion of **Stacks 0DYP**: a deformation of `P` lifts along a small extension
of its Artinian base whenever its henselization does.

Under the translation of `Deformation.Examples.hasFlatAlgebraLift_of_flatAlgebraHom` and
`Deformation.Examples.exists_isHomLift_of_hasFlatAlgebraLift` the assertion is **Stacks 0DZB**
at a square-zero kernel, for the ideal `𝔟 = π⁻¹(J)` of the flat algebra `Q`, `π : Q → P` being
the reduction. -/
public theorem lifts_henselizationFunctorData [Algebra.FiniteType k P]
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄ (f : B ⟶ A),
      IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ x : (ringDeformationBasedCategory Λ k P).p.Fiber A,
          (∃ (y' : (ringDeformationBasedCategory Λ k (henselization P J : Type w)).obj)
              (g : y' ⟶ F.functor.obj x.1),
            (ringDeformationBasedCategory Λ k
              (henselization P J : Type w)).p.IsHomLift f g) →
            ∃ (x' : (ringDeformationBasedCategory Λ k P).obj) (h : x' ⟶ x.1),
              (ringDeformationBasedCategory Λ k P).p.IsHomLift f h := by
  intro B A f hsmall x hyp
  obtain ⟨y', g, hg⟩ := hyp
  obtain ⟨X, hXA⟩ := x
  -- the three identifications of Artinian bases in play
  have hXA : X.left.base = A := hXA
  have hdomB : y'.left.base = B :=
    IsHomLift.domain_eq (ringDeformationBasedCategory Λ k
      (henselization P J : Type w)).p f g
  have hcodA : (F.functor.obj X).left.base = A :=
    IsHomLift.codomain_eq (ringDeformationBasedCategory Λ k
      (henselization P J : Type w)).p f g
  have hb : (F.functor.obj X).left.base = X.left.base := F.functor.w_obj X
  set f₁ : y'.left.base ⟶ (F.functor.obj X).left.base :=
    eqToHom hdomB ≫ f ≫ eqToHom hcodA.symm with hf₁
  set f₂ : y'.left.base ⟶ X.left.base :=
    eqToHom hdomB ≫ f ≫ eqToHom (hcodA.symm.trans hb) with hf₂
  have hf₁₂ : f₁ ≫ eqToHom hb = f₂ := by
    simp only [hf₁, hf₂, Category.assoc, eqToHom_trans]
  have hgb : g.left.base = f₁ :=
    IsHomLift.fac' (ringDeformationBasedCategory Λ k (henselization P J : Type w)).p f g
  let : Algebra ((y'.left.base : Type w)) ((F.functor.obj X).left.base : Type w) :=
    f₁.hom.toRingHom.toAlgebra
  let : Algebra ((y'.left.base : Type w)) ((X.left.base : Type w)) :=
    f₂.hom.toRingHom.toAlgebra
  -- the flat algebra of the henselized deformation is a flat lift along the base map of `g`
  have hliftC : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((F.functor.obj X).left.base : Type w) (F.functor.obj X).left.fiber :=
    hasFlatAlgebraLift_of_flatAlgebraHom g.left (by
      rw [RingHom.algebraMap_toAlgebra, hgb])
  -- the structures of the deformation over its special fibre
  let : Algebra ((X.left.base : Type w)) k := X.hom.base.hom.toRingHom.toAlgebra
  let : Algebra X.left.fiber P := X.hom.map.hom.toAlgebra
  let : Algebra ((X.left.base : Type w)) P :=
    ((algebraMap k P).comp (algebraMap ((X.left.base : Type w)) k)).toAlgebra
  have : IsScalarTower ((X.left.base : Type w)) k P := IsScalarTower.of_algebraMap_eq' rfl
  have hwX : (algebraMap X.left.fiber P).comp
      (algebraMap ((X.left.base : Type w)) X.left.fiber)
      = (algebraMap k P).comp (algebraMap ((X.left.base : Type w)) k) :=
    congrArg CommRingCat.Hom.hom X.hom.cartesian.w
  have : IsScalarTower ((X.left.base : Type w)) X.left.fiber P :=
    IsScalarTower.of_algebraMap_eq' hwX.symm
  have : Algebra.IsPushout ((X.left.base : Type w)) k X.left.fiber P :=
    isPushout_deformationSpecialFiber X rfl rfl
  have hsurjBase : Function.Surjective (algebraMap ((X.left.base : Type w)) k) :=
    surjective_deformationHomBase P X
  have : Algebra.FiniteType ((X.left.base : Type w)) X.left.fiber :=
    Deformation.finiteType_of_isPushout_specialFiber (P := P) hsurjBase
  -- the ideal `𝔟` and the canonical henselization of the pair `(Q, 𝔟)`
  set bQ : Ideal X.left.fiber := J.comap X.hom.map.hom with hbQ
  let : Algebra ((X.left.base : Type w))
      (henselization X.left.fiber bQ : Type w) :=
    ((algebraMap X.left.fiber (henselization X.left.fiber bQ : Type w)).comp
      (algebraMap ((X.left.base : Type w)) X.left.fiber)).toAlgebra
  have : IsScalarTower ((X.left.base : Type w)) X.left.fiber
      (henselization X.left.fiber bQ : Type w) :=
    IsScalarTower.of_algebraMap_eq' rfl
  -- transport the flat lift onto the canonical henselization
  have hliftA : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((X.left.base : Type w)) (henselization X.left.fiber bQ : Type w) := by
    refine Deformation.hasFlatAlgebraLift_of_ringEquiv
      (ringEquivOfEq hb) (fun a => ?_) (F.henselizationEquiv X).symm (fun z => ?_) hliftC
    · rw [← hom_eqToHom_apply, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      exact congrArg (fun m : y'.left.base ⟶ X.left.base => m.hom a) hf₁₂
    · refine (F.henselizationEquiv X).injective ?_
      rw [RingEquiv.apply_symm_apply]
      have hrw : algebraMap ((X.left.base : Type w))
            (henselization X.left.fiber bQ : Type w) ((ringEquivOfEq hb) z)
          = algebraMap X.left.fiber (henselization X.left.fiber bQ : Type w)
            (algebraMap ((X.left.base : Type w)) X.left.fiber ((ringEquivOfEq hb) z)) := rfl
      rw [hrw, F.henselizationEquiv_algebraMap X, F.base_comm X ((ringEquivOfEq hb) z),
        cast_ringEquivOfEq hb z]
  -- the remaining hypotheses of Stacks 0DZB
  obtain ⟨-, -, hsurjf, hker2⟩ := hsmall.isSquareZeroSurjection
  obtain ⟨hsurj₂, hsq₂⟩ :=
    surjective_and_sq_ker_comp_eqToHom f hdomB (hcodA.symm.trans hb) hsurjf hker2
  have hsurjA : Function.Surjective (algebraMap ((y'.left.base : Type w))
      ((X.left.base : Type w))) := hsurj₂
  have hzeroA : (RingHom.ker (algebraMap ((y'.left.base : Type w))
      ((X.left.base : Type w)))) ^ 2 = ⊥ := hsq₂
  have hsyn : ∀ h ∈ bQ,
      Algebra.Syntomic ((X.left.base : Type w)) (Localization.Away h) := fun h hh =>
    Deformation.syntomic_localizationAway_specialFiber (P := P) hsurjBase J hsm h hh
  -- Stacks 0DZB at a square-zero kernel, read backwards
  have hliftQ : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((X.left.base : Type w)) X.left.fiber :=
    Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_sqZero
      ((y'.left.base : Type w)) ((X.left.base : Type w)) X.left.fiber hsurjA hzeroA bQ hsyn
      (henselization X.left.fiber bQ : Type w)
      (henselianPair_henselization X.left.fiber bQ)
      (henselization_universalProperty X.left.fiber bQ) hliftA
  -- translate back into the deformation category
  obtain ⟨X', mm, hmm⟩ := exists_isHomLift_of_hasFlatAlgebraLift X f₂
    (RingHom.algebraMap_toAlgebra _) hliftQ
  refine ⟨X', mm, ?_⟩
  have hinst : (ringDeformationProjection Λ k P).IsHomLift f₂ mm := hmm
  have h1 : (ringDeformationProjection Λ k P).IsHomLift (f₂ ≫ eqToHom hXA) mm :=
    IsHomLift.lift_comp_eqToHom (ringDeformationProjection Λ k P) f₂ mm hXA
  have h2 : (ringDeformationProjection Λ k P).IsHomLift
      (eqToHom hdomB.symm ≫ f₂ ≫ eqToHom hXA) mm :=
    IsHomLift.lift_eqToHom_comp (ringDeformationProjection Λ k P) (f₂ ≫ eqToHom hXA) mm
      hdomB.symm
  have heq : eqToHom hdomB.symm ≫ f₂ ≫ eqToHom hXA = f := by
    simp only [hf₂, Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  exact heq ▸ h2

/-- **Stacks 0DZD, the smoothness conclusion.** Let `k` be a field, `P` a finite type
`k`-algebra and `J ⊆ P` an ideal such that `Spec(P) → Spec(k)` is smooth on the complement of
`V(J)`. The henselization functor `𝓓_P ⟶ 𝓓_{Pʰ}` of **Stacks 0DYT** is smooth. -/
@[stacks 0DZD "the first conclusion, smoothness: the functor of Stacks 0DYT is smooth. Under \
the tag's own hypotheses and no others: (1) is `Algebra.FiniteType k P` and (2) is `hsm`, \
smoothness of `Spec(P) -> Spec(k)` at every prime outside `V(J)`. Stated for an arbitrary \
functor datum of Stacks 0DYT, with no extra hypothesis on the datum. The criterion of \
Stacks 0DYP reduces it to surjectivity of the differential, which is \
`Deformation.Examples.bijective_differential_henselizationFunctorData`, and to the \
correspondence of liftability, which is proved here in \
`Deformation.Examples.lifts_henselizationFunctorData` -- that is Stacks 0DZB, which Stacks \
0DYP needs only across small extensions, whose kernel is square-zero, so the form used is \
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_henselization_of_sqZero` and NO \
`h0DZ2`-style hypothesis is carried"]
public theorem isSmooth_henselizationFunctorData [Algebra.FiniteType k P]
    (F : HenselizationFunctorData (Λ := Λ) (k := k) (P := P) J)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth F.functor :=
  (isSmooth_iff_differential_surjective_and_lifts
      (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k) P)
      (ringDeformationCategory_isDeformationCategory (Λ := Λ) (k := k)
        (henselization P J : Type w))
      F.functor).mpr
    ⟨(bijective_differential_henselizationFunctorData P J F hsm).2,
      lifts_henselizationFunctorData P J F hsm⟩

/-- **Stacks 0DZD, the smoothness conclusion, at the canonical henselization functor.** This is
`Deformation.Examples.isSmooth_henselizationFunctorData` specialized to
`Deformation.Examples.henselizationFunctor`, the functor datum built in the proof of
**Stacks 0DYT**. -/
@[stacks 0DZD "the first conclusion, smoothness, at the canonical henselization functor \
`Deformation.Examples.henselizationFunctor` of Stacks 0DYT. Under the tag's own hypotheses and \
no others"]
public theorem isSmooth_henselizationFunctor [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth (henselizationFunctor (Λ := Λ) (k := k) J).functor :=
  isSmooth_henselizationFunctorData P J (henselizationFunctor (Λ := Λ) (k := k) J) hsm

end Smoothness

end Deformation.Examples

end
