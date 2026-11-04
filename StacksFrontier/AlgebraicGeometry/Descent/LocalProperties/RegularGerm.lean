module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.RingTheory.Etale.PermanenceOfProperties

/-!
# Regularity of germs along an étale morphism

For an étale morphism of schemes, the local ring at a point of the source is regular if and
only if the local ring at its image is regular.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_iff_of_etale` shows that regularity of local
  rings is invariant along an étale morphism.

## Implementation notes

Étaleness is read on a pair of affine opens around the point and its image, where the two
stalks become the localizations of an étale ring map at a prime and the prime below it;
regularity of those localizations is then compared by
`isRegularLocalRing_localization_iff_of_etale`.

## References

* [Stacks Project, Tag 0AH7](https://stacks.math.columbia.edu/tag/0AH7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A localization of `R` at a prime `P` is regular local iff `Localization.AtPrime P` is. -/
private theorem isRegularLocalRing_iff_localization_atPrime {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime S P] :
    IsRegularLocalRing S ↔ IsRegularLocalRing (Localization.AtPrime P) :=
  let e := (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) S).toRingEquiv
  ⟨fun _ ↦ .of_ringEquiv e.symm, fun _ ↦ .of_ringEquiv e⟩

/-- **Stacks Project, Tag 0AH7.** For an étale morphism of schemes, the local ring at a
point of the source is regular if and only if the local ring at its image is regular. -/
@[stacks 0AH7]
lemma isRegularLocalRing_stalk_iff_of_etale {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U) :
    IsRegularLocalRing (U.presheaf.stalk u) ↔
      IsRegularLocalRing (V.presheaf.stalk (f u)) := by
  obtain ⟨U₀, hU₀, huU₀, V₀, hV₀, hU₀V₀, hEtale⟩ :=
    (etale_iff_forall_etaleAt f).mp inferInstance u
  let p := (hV₀.primeIdealOf ⟨f u, hU₀V₀ huU₀⟩).asIdeal
  let q := (hU₀.primeIdealOf ⟨u, huU₀⟩).asIdeal
  have : p.IsPrime := (hV₀.primeIdealOf ⟨f u, hU₀V₀ huU₀⟩).isPrime
  have : q.IsPrime := (hU₀.primeIdealOf ⟨u, huU₀⟩).isPrime
  let : Algebra Γ(V, V₀) Γ(U, U₀) := (f.appLE V₀ U₀ hU₀V₀).hom.toAlgebra
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE V₀ hV₀ U₀ hU₀ hU₀V₀ huU₀).1).symm⟩
  have : Algebra.Etale Γ(V, V₀) Γ(U, U₀) := hEtale
  let : Algebra Γ(V, V₀) (V.presheaf.stalk (f u)) :=
    V.presheaf.algebra_section_stalk ⟨f u, hU₀V₀ huU₀⟩
  let : Algebra Γ(U, U₀) (U.presheaf.stalk u) := U.presheaf.algebra_section_stalk ⟨u, huU₀⟩
  have : IsLocalization.AtPrime (V.presheaf.stalk (f u)) p :=
    hV₀.isLocalization_stalk ⟨f u, hU₀V₀ huU₀⟩
  have : IsLocalization.AtPrime (U.presheaf.stalk u) q := hU₀.isLocalization_stalk ⟨u, huU₀⟩
  exact (isRegularLocalRing_iff_localization_atPrime q).trans
    ((isRegularLocalRing_localization_iff_of_etale p q).symm.trans
      (isRegularLocalRing_iff_localization_atPrime p).symm)

end AlgebraicGeometry
