module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs

/-!
# Properties of germs of schemes given by properties of their local rings

A property `P` of local rings which is invariant under étale localization — it holds at a
prime of the source of an étale ring map exactly when it holds at a prime above it — induces
an étale-local property of germs of schemes, namely `P` of the local ring at the marked point.

## Main results

* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_stalk_property`: the induced property of germs
  is étale local in the sense of Stacks 04N1.

## Implementation notes

The local ring of a germ is the stalk of its structure sheaf at the marked point. An étale
morphism of germs is represented by an étale morphism of schemes defined on an open
neighbourhood of that point, and `AlgebraicGeometry.etale_iff_forall_etaleAt` makes that
morphism étale on the rings of sections of a pair of affine open neighbourhoods of the point
and of its image. The two stalks are the localizations of those two rings at the primes the
two points correspond to, and those primes correspond under the ring map, so the hypothesis
on `P` applies.

Because a stalk is only canonically *isomorphic* to such a localization, `P` is also required
to be invariant under isomorphisms of local rings; the hypothesis on étale maps alone does not
transport `P` across the comparison isomorphisms.

## References

* [Stacks Project, Tag 04N1](https://stacks.math.columbia.edu/tag/04N1)
* [Stacks Project, Tag 0BBL](https://stacks.math.columbia.edu/tag/0BBL)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

/-- **Stacks 0BBL, the germ criterion.** A property of local rings which is invariant under
isomorphisms and unchanged on passing to a prime above it along an étale ring map induces an
étale-local property of germs of schemes, by evaluation on the local ring at the marked
point. -/
@[stacks 0BBL "germ_criterion"]
theorem GermOfScheme.isEtaleLocal_stalk_property (P : (R : Type u) → [CommRing R] → Prop)
    (hP : ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
      (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime],
      q.comap (algebraMap A B) = p →
        (P (Localization.AtPrime p) ↔ P (Localization.AtPrime q)))
    (hP_iso : ∀ {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S],
      (R ≃+* S) → (P R ↔ P S)) :
    GermOfScheme.IsEtaleLocal (fun g => P (g.scheme.presheaf.stalk g.point)) := by
  intro X S f hf
  obtain ⟨r, hr, hEtale⟩ := hf
  subst f
  show P (S.scheme.presheaf.stalk S.point) ↔ P (X.scheme.presheaf.stalk X.point)
  let xR : r.source := ⟨X.point, r.mem_source⟩
  obtain ⟨U, hU, hxU, V, hV, hUV, hAffineEtale⟩ :=
    (etale_iff_forall_etaleAt r.hom).mp hEtale xR
  let x : U := ⟨xR, hxU⟩
  have hxV : r.hom xR ∈ V := (Scheme.Hom.mem_preimage (f := r.hom)).mp (hUV hxU)
  let y : V := ⟨S.point, r.map_point ▸ hxV⟩
  let p : Ideal Γ(S.scheme, V) := (hV.primeIdealOf y).asIdeal
  let q : Ideal Γ(r.source.toScheme, U) := (hU.primeIdealOf x).asIdeal
  have hpq : q.comap (r.hom.appLE V U hUV).hom = p := by
    show ((hU.primeIdealOf x).asIdeal).comap (r.hom.appLE V U hUV).hom =
      (hV.primeIdealOf y).asIdeal
    simpa [xR, x, y, p, q, r.map_point] using congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)
  let : Algebra Γ(S.scheme, V) Γ(r.source.toScheme, U) :=
    (r.hom.appLE V U hUV).hom.toAlgebra
  let : Algebra.Etale Γ(S.scheme, V) Γ(r.source.toScheme, U) := hAffineEtale
  have hLoc := hP p q hpq
  have key {Y : Scheme.{u}} {W : Y.Opens} (hW : IsAffineOpen W) (y : W) :
      P (Y.presheaf.stalk y) ↔ P (Localization.AtPrime (hW.primeIdealOf y).asIdeal) := by
    let : Algebra Γ(Y, W) (Y.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf y
    let : IsLocalization.AtPrime (Y.presheaf.stalk y) (hW.primeIdealOf y).asIdeal :=
      hW.isLocalization_stalk y
    exact hP_iso (IsLocalization.algEquiv (hW.primeIdealOf y).asIdeal.primeCompl _ _).toRingEquiv
  exact (key hV y).trans (hLoc.trans
    ((key hU x).symm.trans (hP_iso (r.source.stalkIso xR).commRingCatIsoToRingEquiv)))

end AlgebraicGeometry

end
