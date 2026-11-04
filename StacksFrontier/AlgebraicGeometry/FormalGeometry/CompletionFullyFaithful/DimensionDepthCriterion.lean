module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SheafHomLocallyFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHomsOn
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsDimensionBounds
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsGlobalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayDepthDimensionBound
public import StacksFrontier.RingTheory.Depth.RingEquiv

/-!
# Completion on vector bundles over a punctured spectrum is fully faithful, Stacks 0EKQ

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `U = Spec(A) ∖ V(𝔞)`. Stacks 0EKQ says
that, under

1. `A` is `I`-adically complete and has a dualizing complex,
2. for every associated prime `𝔭` of `A` with `𝔭 ∉ V(I)` and `V(𝔭) ∩ V(I) ⊄ V(𝔞)`, and every
   `𝔮 ∈ V(𝔭) ∩ V(𝔞)`, one has `dim((A/𝔭)_𝔮) > cd(A, I) + 1`,
3. for every prime `𝔭` with `𝔭 ∉ V(I)` and `V(𝔭) ∩ V(I) ⊆ V(𝔞)`, one has `depth(A_𝔭) ≥ 2`,

the completion functor `Coh(𝒪_U) ⟶ Coh(U, I𝒪_U)` of Stacks 0880 is fully faithful on the full
subcategory of finite locally free objects. This file proves it.

## The proof

The source reduces, by Stacks 0EKP, to `Γ(U, 𝒪_U) = lim Γ(U, 𝒪_U / Iⁿ 𝒪_U)` and quotes Stacks
0EIG. Here Stacks 0EIG is applied directly to the internal hom instead, which avoids the ample
embedding of Stacks 0EKP:

* for finite locally free `ℱ`, `𝒢` on `U`, the completion map `Hom(ℱ, 𝒢) ⟶ Hom(ℱ^∧, 𝒢^∧)` is the
  arrow `H⁰(U, ℋ) ⟶ lim H⁰(U, ℋ / Iⁿ ℋ)` of Stacks 0EIG for `ℋ = SheafHom(ℱ, 𝒢)`, followed by
  isomorphisms (the identification of Stacks 0882 among them):
  `Stacks.Algebraization.bijective_completionFunctor_map_of_isIso_globalToFormalSections`;
* `ℋ` is finite locally free, so its associated points are associated points of `U`, whose
  primes are associated primes of `A`; condition (2) here is therefore condition (2) of Stacks
  0EIG for `ℋ`: `Stacks.Algebraization.associatedPointsClosureDimensionBound_of_associatedPrimes`;
* the stalk of `ℋ` at `x` is finite free over `𝒪_{U,x} ≅ A_𝔭`, so its depth is at least
  `depth(A_𝔭)`; condition (3) here is therefore condition (3) of Stacks 0EIG for `ℋ`:
  `Stacks.Algebraization.depthTwoOffFormalLocus_of_depth`.

## Main results

* `Stacks.Algebraization.completionFullyFaithful_of_associatedPrimes_of_depth` — **Stacks 0EKQ**.

## Implementation notes

The identification of the completion map with the arrow of Stacks 0EIG goes through the map of
Stacks 0EIV at the neighbourhood `U` of the formal locus,
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison`: both it and the completion functor
send the global section of `SheafHom(ℱ, 𝒢)` defined by a morphism to a completion of that
section in the sense of `Stacks.Algebraization.IsCompletionOfSection`, which is unique.

The dimension `dim((A/𝔭)_𝔮)` is written as the Krull dimension of `A_𝔮 / 𝔭 A_𝔮`, as in the
library's Stacks 0EKT;
`Stacks.Algebraization.closureLocalDimension_eq_ringKrullDim_localizedQuotient` matches it with
the dimension of `𝒪_{closure {x}, z}` used by Stacks 0EIG.

## References

* [Stacks Project, Tag 0EKQ](https://stacks.math.columbia.edu/tag/0EKQ)
* [Stacks Project, Tag 0EIG](https://stacks.math.columbia.edu/tag/0EIG)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open IsLocalRing
open scoped AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.Algebraization.NeighbourhoodHoms
  Stacks.Algebraization.FormalSectionsII

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A}

/-- **Condition (2) of Stacks 0EKQ gives condition (2) of Stacks 0EIG** for a finite locally
free module on `U`: its associated points are associated points of `U`, whose primes are
associated primes of `A`, and the dimension of `𝒪_{closure {x}, z}` is that of
`(A/𝔭)_𝔮`. -/
theorem associatedPointsClosureDimensionBound_of_associatedPrimes
    (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (hdim : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A A → ¬ I ≤ p.asIdeal →
      ¬ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
        PrimeSpectrum.zeroLocus (a : Set A)) →
      ∀ q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (a : Set A),
        ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
          krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))))) :
    AssociatedPointsClosureDimensionBound A I a F := by
  rintro x hx hxI ⟨y, hxy, hyI, hya⟩ z hxz haz
  have hass : IsAssociatedPrimeStacks A A (x.1 : PrimeSpectrum A).asIdeal :=
    Stacks.Divisors.isAssociatedPrimeStacks_of_mem_schemeAssociatedPoints
      (complementZeroLocus A a).ι
      (Stacks.Divisors.associatedPoints_subset_schemeAssociatedPoints_of_isFiniteLocallyFree F
        ((Scheme.Modules.isFiniteLocallyFree_iff F).2 hF) hx)
  refine lt_of_lt_of_eq ?_ (congrArg krullDimToEInt
    (closureLocalDimension_eq_ringKrullDim_localizedQuotient (x.1 : PrimeSpectrum A) z)).symm
  refine hdim x.1 ((isAssociatedPrimeStacks_iff_mem_associatedPrimes _).1 hass) hxI ?_ z
    ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 hxz, (PrimeSpectrum.mem_zeroLocus _ _).2 haz⟩
  intro hsub
  exact hya ((PrimeSpectrum.mem_zeroLocus _ _).1
    (hsub ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 hxy, (PrimeSpectrum.mem_zeroLocus _ _).2 hyI⟩))

/-- **Condition (3) of Stacks 0EKQ gives condition (3) of Stacks 0EIG** for a finite locally
free module on `U`: its stalk at `x` is a finite free module over `𝒪_{U,x} ≅ A_𝔭`, so its depth
is at least `depth(A_𝔭)`. A point `x ∈ U` whose closure meets `V(I)` only inside `V(𝔞)` does
not lie in `V(I)`, so the hypothesis applies at its prime. -/
theorem depthTwoOffFormalLocus_of_depth
    (F : (complementZeroLocus A a : Scheme).Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (hdepth : ∀ p : PrimeSpectrum A, ¬ I ≤ p.asIdeal →
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
        PrimeSpectrum.zeroLocus (a : Set A) →
      (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal)) :
    DepthTwoOffFormalLocus A I a F := by
  have : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion (complementZeroLocus A a).ι
  intro x hxc
  have hx : PrimeSpectrum.zeroLocus ((x.1 : PrimeSpectrum A).asIdeal : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) ⊆ PrimeSpectrum.zeroLocus (a : Set A) :=
    fun y hy => hxc ⟨(PrimeSpectrum.le_iff_mem_closure _ _).1
      ((PrimeSpectrum.mem_zeroLocus _ _).1 hy.1), hy.2⟩
  have hxI : ¬ I ≤ (x.1 : PrimeSpectrum A).asIdeal := fun hI =>
    x.2 (hx ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 le_rfl, (PrimeSpectrum.mem_zeroLocus _ _).2 hI⟩)
  have h2 := hdepth x.1 hxI hx
  -- The local ring of `U` at `x` is `A_𝔭`.
  have : (x.1 : PrimeSpectrum A).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  let e : (complementZeroLocus A a : Scheme).presheaf.stalk x ≃+*
      Localization.AtPrime (x.1 : PrimeSpectrum A).asIdeal :=
    ((complementZeroLocus A a).stalkIso x).commRingCatIsoToRingEquiv.trans
      (Spec.stalkIso (.of A) x.1).commRingCatIsoToRingEquiv
  have h2' := h2.trans_eq (Module.depth_self_eq_of_ringEquiv e).symm
  have := hF
  intro M
  exact h2'.trans (depth_stalk_le_sheafDepthAt F x)


/-! ### The completion of a morphism is the completion of its global section -/

section Bridge

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- **The completion of a morphism `g : G ⟶ F` is the completion of the global section of
`SheafHom(G, F)` it defines.** -/
theorem isCompletionOfSection_completionFunctor_map (g : G ⟶ F) :
    IsCompletionOfSection J G F ⊤
      (internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F) g.hom)
      ((completionFunctor X J).map g) := fun n T _ x =>
  ConcreteCategory.congr_hom
    (congrArg (fun f => Scheme.Modules.Hom.app (X := X) f T)
      (completionFunctor_map_quotient X J g n)) x

end Bridge

variable (A I a) in
/-- **At `U` itself, the comparison map of Stacks 0EIV sends the global section defined by a
morphism to the completion of that morphism.** Both are completions of the same section over
`U`, and such a completion is unique. -/
theorem nbhdHomComparison_ι_top
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf) (g : G ⟶ F) :
    nbhdHomComparison A I a G F (ConcreteCategory.hom
        (colimit.ι (sectionsNearVanishing A I a (internalHomNear A a G F).obj)
          (topNearVanishing A I a))
        (internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F) g.hom)) =
      (completionFunctor (complementZeroLocus A a : Scheme)
        (idealSheafNearVanishing A I a)).map g :=
  IsCompletionOfSection.unique (idealSheafNearVanishing A I a) G F
    (O := ⊤) (fun _ _ => trivial)
    (isCompletionOfSection_nbhdHomComparison A I a G F (topNearVanishing A I a) _)
    (isCompletionOfSection_completionFunctor_map (idealSheafNearVanishing A I a) G F g)

variable (A I a) in
/-- **The completion functor is bijective on `G ⟶ F` as soon as the arrow of Stacks 0EIG is an
isomorphism for `SheafHom(G, F)`.** The completion map is the arrow of Stacks 0EIG for the
internal hom, read on the global sections `Γ(U, SheafHom(G, F)) = Hom(G, F)` and followed by
isomorphisms: the commutation of global sections with the limit of the ideal-power tower, the
shift of that tower, the commutation of global sections with the limit of the completion, and
the identification of Stacks 0882. -/
theorem bijective_completionFunctor_map_of_isIso_globalToFormalSections
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf)
    (hiso : IsIso (globalToFormalSections A I a (internalHomNear A a G F).obj)) :
    Function.Bijective (fun g : G ⟶ F => (completionFunctor (complementZeroLocus A a : Scheme)
      (idealSheafNearVanishing A I a)).map g) := by
  have b1 : Function.Bijective
      (ConcreteCategory.hom (globalToFormalSections A I a (internalHomNear A a G F).obj)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hiso
  have b2 : Function.Bijective (ConcreteCategory.hom (sectionsAbLimitIso
      (adicQuotientSystem (idealSheafNearVanishing A I a)
        (internalHomNear A a G F).obj)).inv) :=
    ConcreteCategory.bijective_of_isIso _
  have b3 : Function.Bijective (ConcreteCategory.hom
      ((sectionsAb (complementZeroLocus A a : Scheme)).map
        (adicCompletionLimitIso (idealSheafNearVanishing A I a)
          (internalHomNear A a G F)).hom)) :=
    ConcreteCategory.bijective_of_isIso _
  have b4 : Function.Bijective (ConcreteCategory.hom
      (globalSectionsLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom) :=
    have : IsIso (globalSectionsLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom := Iso.isIso_hom _
    ConcreteCategory.bijective_of_isIso
      (globalSectionsLimitIso (idealSheafNearVanishing A I a) (internalHomNear A a G F)).hom
  have hcomp : Function.Bijective (fun s => nbhdHomComparison A I a G F (ConcreteCategory.hom
      (colimit.ι (sectionsNearVanishing A I a (internalHomNear A a G F).obj)
        (topNearVanishing A I a)) s)) :=
    (completionInternalHomEquiv (complementZeroLocus A a : Scheme)
      (idealSheafNearVanishing A I a) G F).bijective.comp (b4.comp (b3.comp (b2.comp b1)))
  have hhom : Function.Bijective (fun g : G ⟶ F => g.hom) :=
    ⟨fun _ _ e => ObjectProperty.hom_ext _ e, fun g => ⟨ObjectProperty.homMk g, rfl⟩⟩
  have hsrc : Function.Bijective (fun g : G ⟶ F =>
      internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F) g.hom) :=
    (internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F)).bijective.comp hhom
  have heq : (fun g : G ⟶ F => (completionFunctor (complementZeroLocus A a : Scheme)
      (idealSheafNearVanishing A I a)).map g) =
      (fun s => nbhdHomComparison A I a G F (ConcreteCategory.hom
        (colimit.ι (sectionsNearVanishing A I a (internalHomNear A a G F).obj)
          (topNearVanishing A I a)) s)) ∘
        (fun g : G ⟶ F =>
          internalHomSectionsTopMapAddEquiv (coherentObj G) (coherentObj F) g.hom) :=
    funext fun g => (nbhdHomComparison_ι_top A I a G F g).symm
  rw [heq]
  exact hcomp.comp hsrc

/-! ### Stacks 0EKQ -/

/-- **Stacks 0EKQ.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let
`U = Spec(A) ∖ V(𝔞)`. Assume

1. `A` is `I`-adically complete and has a dualizing complex,
2. for every associated prime `𝔭` of `A` with `𝔭 ∉ V(I)` and `V(𝔭) ∩ V(I) ⊄ V(𝔞)`, and every
   `𝔮 ∈ V(𝔭) ∩ V(𝔞)`, one has `dim((A/𝔭)_𝔮) > cd(A, I) + 1`,
3. for every prime `𝔭` with `𝔭 ∉ V(I)` and `V(𝔭) ∩ V(I) ⊆ V(𝔞)`, one has `depth(A_𝔭) ≥ 2`.

Then the completion functor `Coh(𝒪_U) ⟶ Coh(U, I𝒪_U)`, `ℱ ↦ ℱ^∧`, is fully faithful on the full
subcategory of finite locally free objects.

The dimension `dim((A/𝔭)_𝔮)` is written as the Krull dimension of `A_𝔮 / 𝔭 A_𝔮`, which is the
same ring. -/
@[stacks 0EKQ]
theorem completionFullyFaithful_of_associatedPrimes_of_depth
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A) (hIa : I ≤ a)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdim : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A A → ¬ I ≤ p.asIdeal →
      ¬ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
        PrimeSpectrum.zeroLocus (a : Set A)) →
      ∀ q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (a : Set A),
        ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
          krullDimToEInt (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))))
    (hdepth : ∀ p : PrimeSpectrum A, ¬ I ≤ p.asIdeal →
      PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
        PrimeSpectrum.zeroLocus (a : Set A) →
      (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal)) :
    CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus A a : Scheme)
      (idealSheafNearVanishing A I a) := by
  intro P Q hP hQ
  -- The internal hom `ℋ = SheafHom(P, Q)` is a finite locally free coherent module on `U`.
  have hH : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (internalHomNear A a P Q).obj :=
    Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent P Q hP hQ
  have : (internalHomNear A a P Q).obj.IsCoherent := (internalHomNear A a P Q).property
  -- Stacks 0EIG for `ℋ`, its conditions (2) and (3) coming from conditions (2) and (3) here.
  refine bijective_completionFunctor_map_of_isIso_globalToFormalSections A I a P Q ?_
  exact isIso_globalToFormalSections_of_depthTwoOffFormalLocus A I a _ hIa hcomplete hdualizing
    (associatedPointsClosureDimensionBound_of_associatedPrimes _ hH hdim)
    (depthTwoOffFormalLocus_of_depth _ hH hdepth)

end Stacks.Algebraization

end
