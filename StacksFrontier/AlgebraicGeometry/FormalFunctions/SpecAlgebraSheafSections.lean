module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.SpecReesRelativeSpec

/-!
# A quasi-coherent algebra sheaf on an affine base from a ring of global sections

Let `k` be a commutative ring and `A` a quasi-coherent sheaf of `𝒪`-algebras on `Spec k`.  If a
`k`-algebra `R` is identified with the global sections of `A` by a ring isomorphism compatible
with the two structure maps, then `A` *is* the pushed-forward structure sheaf of
`Spec R ⟶ Spec k`.

`Stacks.Cohomology.FormalFunctions.specReesAlgebraSheafIso` is this statement for the Rees
algebra of an ideal, where `R` is `Stacks.Blowup.reesAlgebra I`.  Nothing in that argument is
about the Rees algebra: the identification of global sections is a hypothesis there as much as
here, and the proof is the naturality of `AlgebraicGeometry.Scheme.ΓSpecIso` followed by
`Stacks.RelativeSpec.AlgebraSheaf.isoOfSectionsRingEquiv`.  This file states it for an arbitrary
`R`, which is what the associated graded of an ideal-power filtration needs — there the ring is
`Gr_𝔪(A)` and there is no ideal sheaf to take a Rees algebra of.

## Main results

* `Stacks.RelativeSpec.AlgebraSheaf.sectionsPushforwardRingEquiv`: the ring isomorphism of global
  sections between `A` and the pushforward along `Spec R ⟶ Spec k`.
* `Stacks.RelativeSpec.AlgebraSheaf.sectionsPushforwardRingEquiv_unitTop`: it is compatible with
  the two structure maps.
* `Stacks.RelativeSpec.AlgebraSheaf.specAlgebraSheafIsoOfSectionsRingEquiv`: **the isomorphism**
  `A ≅ pushforwardAlgebra (Spec.map (algebraMap k R))`.

## References

* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {k : Type u} [CommRing k] (A : AlgebraSheaf.{u} (Spec (CommRingCat.of k)))
  [A.IsQuasicoherent] (R : Type u) [CommRing R] [Algebra k R]

/-- **The global sections of `A` and of the pushforward along `Spec R ⟶ Spec k` agree**, given an
identification `ρ` of `R` with the global sections of `A`:  the left-hand side is `R` by `ρ` and
the right-hand side is `R` by `AlgebraicGeometry.Scheme.ΓSpecIso`.

The sections of a pushforward over `⊤` are the sections of the source over the preimage of `⊤`,
which is `⊤`, so no transport appears on the right. -/
def sectionsPushforwardRingEquiv (ρ : R ≃+* ↥(A.sections ⊤)) :
    ↥(A.sections ⊤) ≃+*
      ↥((pushforwardAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k R)))).sections ⊤) :=
  ρ.symm.trans (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv

omit [A.IsQuasicoherent] in
/-- The identification of global sections is compatible with the two structure maps:  on `A` the
structure map is `ρ ∘ algebraMap k R` by hypothesis, on the pushforward it is the global sections
of `Spec R ⟶ Spec k`, and `AlgebraicGeometry.Scheme.ΓSpecIso` is natural. -/
theorem sectionsPushforwardRingEquiv_unitTop (ρ : R ≃+* ↥(A.sections ⊤))
    (hρ : ∀ r : k, ρ (algebraMap k R r) =
      A.unitTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv r))
    (r : ↥Γ(Spec (CommRingCat.of k), ⊤)) :
    sectionsPushforwardRingEquiv A R ρ (A.unitTop.hom r) =
      (pushforwardAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k R)))).unitTop.hom r := by
  have hsym : ρ.symm (A.unitTop.hom r) = algebraMap k R
      ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.symm r) := by
    refine ρ.injective ?_
    rw [RingEquiv.apply_symm_apply, hρ]
    simp
  have hnat := congrArg (fun m : CommRingCat.of k ⟶ Γ(Spec (CommRingCat.of R), ⊤) =>
      m.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.symm r))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k R)))
  show (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ.symm (A.unitTop.hom r)) = _
  rw [hsym]
  refine hnat.trans ?_
  show (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.symm r)) = _
  congr 1
  show (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.symm r) = r
  simp

/-- **A quasi-coherent algebra sheaf on `Spec k` whose global sections are a `k`-algebra `R` is
the pushed-forward structure sheaf of `Spec R ⟶ Spec k`.**

Both algebra sheaves are quasi-coherent on the affine `Spec k` — the pushforward by
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_pushforwardAlgebra`, the morphism being affine —
and their global sections agree over `k` by
`Stacks.RelativeSpec.AlgebraSheaf.sectionsPushforwardRingEquiv`, so
`Stacks.RelativeSpec.AlgebraSheaf.isoOfSectionsRingEquiv` applies. -/
def specAlgebraSheafIsoOfSectionsRingEquiv (ρ : R ≃+* ↥(A.sections ⊤))
    (hρ : ∀ r : k, ρ (algebraMap k R r) =
      A.unitTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv r)) :
    A ≅ pushforwardAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  letI := isQuasicoherent_pushforwardAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  isoOfSectionsRingEquiv _ _ (sectionsPushforwardRingEquiv A R ρ)
    (sectionsPushforwardRingEquiv_unitTop A R ρ hρ)

end Stacks.RelativeSpec.AlgebraSheaf

end
