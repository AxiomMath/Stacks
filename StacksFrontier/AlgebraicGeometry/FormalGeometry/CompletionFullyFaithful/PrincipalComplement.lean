module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Neighbourhoods
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusTagInjectivity
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ComplementSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The completion functor at a principal formal locus

Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let `U = Spec(A) ∖ V(𝔞)`. The zero locus of
`f` on `U` is the closed subscheme cut out by the ideal sheaf `f 𝒪_U`, and the opens of `U`
containing it are the neighbourhoods over which the algebraization statements of Stacks chapter
52 take their sections. Stacks 0EKV asserts that, if `A` is `f`-adically complete, `f` is a
nonzerodivisor and `H¹_𝔞(A/fA)` is a finite `A`-module, then the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(U, f𝒪_U)`, `ℱ ↦ ℱ^∧`, *is fully faithful on the full subcategory of
finite locally free objects*.

This file proves that `U` is a quasi-affine Noetherian scheme, that the formal locus `U ∩ V(f)`
is a closed subscheme of `U` with ideal sheaf `f 𝒪_U`, and that the comparison map of Stacks 0EG2
on `U` is an isomorphism for a module as soon as it is one for an isomorphic module.

## Main definitions

* `Stacks.Algebraization.principalFormalLocus` and
  `Stacks.Algebraization.principalFormalLocusι` — the zero locus of `f` on `U`, as a closed
  subscheme of `U`.
* `Stacks.Algebraization.IsAmplePowerSectionsCompleteNearPrincipalLocus` — condition (2) of
  Stacks 0EK2 at that closed subscheme: an ample invertible module on `U` whose large tensor
  powers have their sections near `U ∩ V(f)` equal to the sections on the infinitesimal
  neighbourhoods.

## Main results

* `Stacks.Algebraization.isQuasiAffine_complementZeroLocus` and
  `Stacks.Algebraization.isNoetherian_complementZeroLocus` — `U` is quasi-affine and Noetherian.
* `Stacks.Algebraization.ker_principalFormalLocusι` — the ideal sheaf of the formal locus is
  `f 𝒪_U`.
* `Stacks.Algebraization.isIso_comparisonMap_of_iso` — the comparison map of Stacks 0EG2 is an
  isomorphism for a module as soon as it is one for an isomorphic module.

## References

* [Stacks Project, Tag 0EKV](https://stacks.math.columbia.edu/tag/0EKV)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)

/-! ### The complement of a closed subset of an affine spectrum -/

/-- **The complement of a closed subset of an affine spectrum is quasi-affine.** Over a
Noetherian ring `U = Spec(A) ∖ V(𝔞)` is a quasi-compact open subscheme of an affine scheme. -/
@[ega "I 1.1.10" "(ii), special case"]
instance isQuasiAffine_complementZeroLocus [IsNoetherianRing A] :
    (complementZeroLocus A a : Scheme).IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_isImmersion (complementZeroLocus A a).ι

/-- Over a Noetherian ring `U = Spec(A) ∖ V(𝔞)` is a Noetherian scheme. -/
instance isNoetherian_complementZeroLocus [IsNoetherianRing A] :
    IsNoetherian (complementZeroLocus A a : Scheme) := ⟨⟩

/-! ### The principal formal locus as a closed subscheme -/

/-- The zero locus of `f` on `U = Spec(A) ∖ V(𝔞)`, as a scheme: the closed subscheme of `U` cut
out by the ideal sheaf `f 𝒪_U`. -/
abbrev principalFormalLocus (f : A) : Scheme.{u} :=
  (idealSheafNearVanishing A (Ideal.span {f}) a).subscheme

/-- The closed immersion of the zero locus of `f` on `U = Spec(A) ∖ V(𝔞)` into `U`. -/
abbrev principalFormalLocusι (f : A) :
    principalFormalLocus A a f ⟶ (complementZeroLocus A a : Scheme) :=
  (idealSheafNearVanishing A (Ideal.span {f}) a).subschemeι

/-- The ideal sheaf of the zero locus of `f` on `U = Spec(A) ∖ V(𝔞)` is `f 𝒪_U`. -/
theorem ker_principalFormalLocusι (f : A) :
    (principalFormalLocusι A a f).ker = idealSheafNearVanishing A (Ideal.span {f}) a :=
  Scheme.IdealSheafData.ker_subschemeι _

/-! ### The comparison map of Stacks 0EG2 along an isomorphism of modules -/

/-- An isomorphism of modules on `U = Spec(A) ∖ V(𝔞)` induces an isomorphism of the diagrams of
sections over the neighbourhoods of the formal locus. -/
theorem isIso_sectionsNearVanishingMap
    {F G : (complementZeroLocus A a : Scheme).Modules} (e : F ≅ G) :
    IsIso (sectionsNearVanishingMap A I a e.hom) := by
  refine ⟨⟨sectionsNearVanishingMap A I a e.inv, ?_, ?_⟩⟩
  · refine NatTrans.ext (funext fun V => ?_)
    change e.hom.app V.openSet ≫ e.inv.app V.openSet = _
    rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  · refine NatTrans.ext (funext fun V => ?_)
    change e.inv.app V.openSet ≫ e.hom.app V.openSet = _
    rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl

/-- An isomorphism of modules on `U = Spec(A) ∖ V(𝔞)` induces an isomorphism of the inverse
systems of sections of the ideal-power quotients. -/
theorem isIso_formalSectionsMap
    {F G : (complementZeroLocus A a : Scheme).Modules} (e : F ≅ G) :
    IsIso (formalSectionsMap A I a e.hom) := by
  refine ⟨⟨formalSectionsMap A I a e.inv, ?_, ?_⟩⟩
  · refine NatTrans.ext (funext fun n => ?_)
    change (idealPowerQuotientMap (idealSheafNearVanishing A I a)
          (idealSheafNearVanishing A I a) n.unop n.unop le_rfl e.hom).app ⊤ ≫
        (idealPowerQuotientMap (idealSheafNearVanishing A I a)
          (idealSheafNearVanishing A I a) n.unop n.unop le_rfl e.inv).app ⊤ = 𝟙 _
    rw [← Scheme.Modules.Hom.comp_app, ← idealPowerQuotientMap_comp, e.hom_inv_id,
      idealPowerQuotientMap_id, Scheme.Modules.Hom.id_app]
  · refine NatTrans.ext (funext fun n => ?_)
    change (idealPowerQuotientMap (idealSheafNearVanishing A I a)
          (idealSheafNearVanishing A I a) n.unop n.unop le_rfl e.inv).app ⊤ ≫
        (idealPowerQuotientMap (idealSheafNearVanishing A I a)
          (idealSheafNearVanishing A I a) n.unop n.unop le_rfl e.hom).app ⊤ = 𝟙 _
    rw [← Scheme.Modules.Hom.comp_app, ← idealPowerQuotientMap_comp, e.inv_hom_id,
      idealPowerQuotientMap_id, Scheme.Modules.Hom.id_app]

/-- **The comparison map of Stacks 0EG2 only depends on the isomorphism class of the module.**
If it is an isomorphism for `F` and `F ≅ G`, then it is an isomorphism for `G`. -/
theorem isIso_comparisonMap_of_iso
    {F G : (complementZeroLocus A a : Scheme).Modules} (e : F ≅ G)
    (h : IsIso (comparisonMap A I a F)) : IsIso (comparisonMap A I a G) := by
  have := isIso_sectionsNearVanishingMap A I a e
  have := isIso_formalSectionsMap A I a e
  rw [(IsIso.eq_inv_comp _).2 (colimMap_comp_comparisonMap A I a e.hom)]
  infer_instance

/-- **The comparison map of Stacks 0EIH on the ring itself is the comparison for `𝒪_U`.** The
sheaf associated to `A` restricts on `U = Spec(A) ∖ V(𝔞)` to the structure sheaf. -/
theorem isIso_comparisonMap_unit (f : A)
    (h : IsIso (principalComparisonMap A f a (ModuleCat.of A A))) :
    IsIso (comparisonMap A (Ideal.span {f}) a
      (SheafOfModules.unit (complementZeroLocus A a : Scheme).ringCatSheaf)) :=
  isIso_comparisonMap_of_iso A (Ideal.span {f}) a (complementTildeRingIsoUnit A a) h

/-! ### Condition (2) of Stacks 0EK2 at a principal formal locus -/

/-- **Condition (2) of Stacks 0EK2 at the zero locus of `f` on `U = Spec(A) ∖ V(𝔞)`.** There is
an ample invertible module `L` on `U` such that, for every large `m`, the colimit of the sections
of `L^{⊗ m}` over the neighbourhoods of `U ∩ V(f)` is the limit of its sections on the
infinitesimal neighbourhoods of `U ∩ V(f)`. -/
def IsAmplePowerSectionsCompleteNearPrincipalLocus [IsNoetherianRing A] (f : A) : Prop :=
  ∃ (L : (complementZeroLocus A a : Scheme).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      (complementZeroLocus A a : Scheme).toRingedSpace.presheaf
      (structureSheafRing (complementZeroLocus A a : Scheme).toRingedSpace).property L),
    letI := hL
    AlgebraicGeometry.Scheme.Modules.IsAmple (complementZeroLocus A a : Scheme) L ∧
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        IsNeighbourhoodSectionsComplete (principalFormalLocusι A a f)
          (Stacks.SheafOfModules.Invertible.tensorPower
            (complementZeroLocus A a : Scheme).toRingedSpace.presheaf
            (structureSheafRing (complementZeroLocus A a : Scheme).toRingedSpace).property
            L (m : ℤ))

end Stacks.Algebraization

end
