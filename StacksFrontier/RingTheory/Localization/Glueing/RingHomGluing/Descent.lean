module

public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing

/-!
# Formal glueing descent along finitely many maximal ideals

Let `A` be a Noetherian ring and let `m i`, for `i` in a finite index type, be pairwise distinct
maximal ideals.  The pair `A → ∏ i, A_{m i}` and the ideal `I = ⨅ i, m i` satisfies the three
hypotheses of Stacks 0ALK, proved in
`StacksFrontier.RingTheory.Localization.Glueing.RingHomGluing`.  This file records the resulting
descent statement: a module map to or from a base change to `∏ i, A_{m i}` whose kernel and
cokernel are `I (∏ i, A_{m i})`-power torsion descends to a map of `A`-modules, with the same
kernel and cokernel.

This is the module-theoretic half of Stacks 0EAE, which glues *ring* maps
`A_{m i} → B i` with kernel and cokernel annihilated by a power of `m i` into a single ring map
out of `A`.  The algebra structure on the descended module is not supplied by this statement; see
the implementation notes.

## Main results

* `Stacks.RingHomGluing.exists_descent_pi_localizationAtPrime` — Stacks 0ALK for the pair
  `A → ∏ i, A_{m i}` and the ideal `⨅ i, m i`.

## Implementation notes

Stacks proves 0EAE by applying 0ALK to `A → ∏ i, A_{m i}` to obtain the underlying module of the
glued ring, and then appeals to the remark Stacks 05EU to transport the algebra structure.  The
formalized form of 05EU
(`FormalGlueing.formalGlueing_preserves_moduleProperties_tensor_and_algebras`) existentially
quantifies the monoidal structure on the category of glueing data, so it cannot be used to *build*
a commutative monoid object there out of the given rings `B i`; only the module half of the Stacks
argument is available from the existing results.

## References

* [Stacks Project, Tag 0ALK](https://stacks.math.columbia.edu/tag/0ALK)
* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.RingHomGluing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type v} [Finite ι]
  (m : ι → Ideal A) [∀ i, (m i).IsMaximal]

/-- **Stacks 0ALK for a finite family of maximal ideals.** Over a Noetherian ring `A`, let `m i`
be finitely many pairwise distinct maximal ideals and `I = ⨅ i, m i`.  A map of modules over
`A' = ∏ i, A_{m i}` to or from the base change of an `A`-module, whose kernel and cokernel are
`I A'`-power torsion, descends to a map of `A`-modules whose base change recovers it and which has
the same kernel and cokernel. -/
theorem exists_descent_pi_localizationAtPrime (hm : Pairwise fun i j ↦ m i ≠ m j) :
    let E := ModuleCat.extendScalars.{u, max u v, max u v w}
      (algebraMap A (∀ i, Localization.AtPrime (m i)))
    let U := ModuleCat.restrictScalars.{max u v w}
      (algebraMap A (∀ i, Localization.AtPrime (m i)))
    (∀ (N : ModuleCat.{max u v w} A)
      (M' : ModuleCat.{max u v w} (∀ i, Localization.AtPrime (m i))) (φ : M' ⟶ E.obj N),
      IsIPowerTorsion (∀ i, Localization.AtPrime (m i))
        (↥(kernel φ : ModuleCat.{max u v w} (∀ i, Localization.AtPrime (m i))))
        ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i)))) →
      IsIPowerTorsion (∀ i, Localization.AtPrime (m i))
        (↥(cokernel φ : ModuleCat.{max u v w} (∀ i, Localization.AtPrime (m i))))
        ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i)))) →
      ∃ (M : ModuleCat.{max u v w} A) (ψ : M ⟶ N) (e : E.obj M ≅ M')
          (_eKer : U.obj (kernel φ) ≅ kernel ψ)
          (_eCoker : U.obj (cokernel φ) ≅ cokernel ψ),
        e.hom ≫ φ = E.map ψ) ∧
    (∀ (M : ModuleCat.{max u v w} A)
      (N' : ModuleCat.{max u v w} (∀ i, Localization.AtPrime (m i))) (φ : E.obj M ⟶ N'),
      IsIPowerTorsion (∀ i, Localization.AtPrime (m i))
        (↥(kernel φ : ModuleCat.{max u v w} (∀ i, Localization.AtPrime (m i))))
        ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i)))) →
      IsIPowerTorsion (∀ i, Localization.AtPrime (m i))
        (↥(cokernel φ : ModuleCat.{max u v w} (∀ i, Localization.AtPrime (m i))))
        ((⨅ j, m j).map (algebraMap A (∀ i, Localization.AtPrime (m i)))) →
      ∃ (N : ModuleCat.{max u v w} A) (ψ : M ⟶ N) (e : E.obj N ≅ N')
          (_eKer : U.obj (kernel φ) ≅ kernel ψ)
          (_eCoker : U.obj (cokernel φ) ≅ cokernel ψ),
        E.map ψ ≫ e.hom = φ) :=
  FormalGlueing.exists_descent_of_idealPowerTorsion_kernel_cokernel.{u, max u v, w}
    A (∀ i, Localization.AtPrime (m i)) (⨅ j, m j) (IsNoetherian.noetherian _)
    (flat_pi_localizationAtPrime m) (quotientMap_bijective m hm)

end Stacks.RingHomGluing

end
