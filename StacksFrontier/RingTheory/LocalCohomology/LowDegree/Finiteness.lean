module

public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison

/-!
# Finiteness of sections on an affine open complement

Let `I` be a finitely generated ideal of a commutative ring `A`, let `U = Spec A \ V(I)`, let `M`
be an `A`-module and let `F` be a sheaf of modules on `U` identified with the restriction to `U`
of the sheaf associated to `M`. If `M` is a finite `A`-module, then the sections `Γ(U, F)` are a
finite `A`-module exactly when the first local cohomology module `H¹_I(M)` is.

This is the degree-zero instance of the finiteness equivalence of Stacks 0BK0: in the notation
of that lemma, conditions (b) `H^p(U, F)` finite and (c) `H^{p+1}_Z(M)` finite are equivalent,
here for `p = 0`. Both directions come from the four-term exact sequence
`0 ⟶ H⁰_I(M) ⟶ M ⟶ Γ(U, F) ⟶ H¹_I(M) ⟶ 0`
of `Stacks.LocalCohomology.exact_lowDegreeSequence`: surjectivity of the connecting map carries
finiteness from `Γ(U, F)` to `H¹_I(M)`, and exactness at `Γ(U, F)` presents `Γ(U, F)` as an
extension of `H¹_I(M)` by a quotient of the finite module `M`, which carries finiteness back.

## Main results

* `Stacks.LocalCohomology.finite_complementGlobalSections_iff_finite_localCohomologyModule` —
  for a finite module `M`, sections on `U = Spec A \ V(I)` are finite over `A` if and only if
  `H¹_I(M)` is.

## Implementation notes

No `@[stacks 0BK0]` tag is placed here. The clause `finiteness_equivalences` of tag 0BK0 asserts
a three-way equivalence — coherence of `R^p j_* F`, finiteness of `H^p(U, F)`, and finiteness of
`H^{p+1}_Z(M)` — for *every* `p ≥ 0`, and this file proves only the second equivalence at
`p = 0`. The two missing halves both need inputs that the library does not yet have:

* the comparison `H^p(U, F) ≅ H^{p+1}_Z(M)` for `p ≥ 1`, which is the higher-degree half of tag
  0DWR. The low-degree half of 0DWR is the four-term sequence used here; of 0DWR itself only the
  `extension` clause carries a tag, at
  `StacksFrontier/AlgebraicGeometry/LocalCohomology/Generalities/QuasiCoherentExtension.lean`, and
  no declaration in the library states the higher comparison.
* the identification of cohomology on `U` with the global sections of the derived pushforward
  along `j`, which is the content of tag 01XK; no declaration in the library carries that tag.

Everything proved here is therefore stated for a finitely generated ideal rather than for a
Noetherian ring, and it needs neither coherence of `F` nor the auxiliary choice of `M` that tag
0BK0 makes: finiteness of the given `M` is the only finiteness hypothesis. Both are
generalisations of the source statement.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- **Stacks 0BK0, finiteness equivalences in degree zero.** Let `I` be a finitely generated
ideal of `A`, let `U = Spec A \ V(I)` and let `F` be a sheaf of modules on `U` identified with
the restriction to `U` of the sheaf associated to a finite `A`-module `M`. Then `Γ(U, F)` is a
finite `A`-module if and only if `H¹_I(M)` is.

Finiteness of `H¹_I(M)` follows from that of `Γ(U, F)` because the connecting map
`Γ(U, F) ⟶ H¹_I(M)` of the low-degree sequence is surjective; the converse holds because that
sequence exhibits `Γ(U, F)` as an extension of `H¹_I(M)` by the image of `M`. -/
theorem finite_complementGlobalSections_iff_finite_localCohomologyModule
    (M : ModuleCat.{max u v} A) [Module.Finite A M]
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    Module.Finite A (complementGlobalSections A I F) ↔
      Module.Finite A (localCohomologyModule A I hI M 1) := by
  obtain ⟨-, -, hexact, hsurj⟩ := exact_lowDegreeSequence.{v} A I hI M F e
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact Module.Finite.of_surjective
      (localizationBoundary (localizationTriangleData.{v} A I hI) M F e) hsurj
  · exact Module.Finite.of_exact hexact hsurj

end Stacks.LocalCohomology

end
