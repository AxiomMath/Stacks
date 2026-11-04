module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Sections
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData

/-!
# Vanishing of `H¹` and the sections of the structure sheaf on the complement

Let `I` be a finitely generated ideal of a commutative ring `A` and `U = Spec A \ V(I)`. The
low-degree exact sequence of local cohomology (Stacks 0DWR),

  `0 ⟶ H⁰_{V(I)}(M) ⟶ M ⟶ Γ(U, M̃|_U) ⟶ H¹_{V(I)}(M) ⟶ 0`,

is available as `Stacks.LocalCohomology.lowDegreeExactSequence`. Applied to `M = A`, where the
restriction map is the map `A ⟶ Γ(U, 𝒪_U)` on global functions, it identifies the vanishing of
`H¹_{V(I)}(A)` with the surjectivity of that map. This file records that identification.

It is the step by which the `d = 0` clause of [Stacks, Tag 0DX7] produces a closed immersion: the
inclusion `U ⟶ Spec A` of the complement is an affine morphism onto an open, and surjectivity on
global functions makes it a closed immersion, so `U` is closed and `V(I)` is open and closed.

## Main results

* `Stacks.LocalCohomology.restrictionToComplement_ring_apply` — on `M = A` and the unit module,
  the restriction map of the low-degree sequence is
  `Stacks.LocalCohomology.complementTopScalars`, the map `A ⟶ Γ(U, 𝒪_U)` on global functions.
* `Stacks.LocalCohomology.isZero_localCohomologyModule_one_iff_surjective` — `H¹_{V(I)}(A) = 0`
  if and only if `A ⟶ Γ(U, 𝒪_U)` is surjective.

## Implementation notes

The exactness statements of the low-degree sequence are about
`Stacks.LocalCohomology.restrictionToComplement`, which is defined for an arbitrary module `M`
together with an identification of a sheaf `F` on `U` with the restriction of the sheaf associated
to `M`. For `M = A` the canonical choice of `F` is the unit module of `𝒪_U` and the
identification is `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`; the sections of `F` are then
the global functions on `U` and the restriction map is `complementTopScalars`, which is the
content of `restrictionToComplement_ring_apply`.

That computation is made on `1` and extended by `A`-linearity rather than evaluated at a general
element: the restriction map sends `m` to the family of fractions `m/1`, so on `1` it is the unit
of the sections ring, and a linear map out of `A` is determined by its value at `1`.

No `@[stacks]` attribute is placed. Stacks 0DWR is the exact sequence itself, which is
`StacksFrontier.RingTheory.LocalCohomology.LowDegree.LocalizationData`, and the clause of Stacks
0DX7 this serves also needs the sheaf-cohomology comparison in degrees above one, which this
library does not have.

## References

* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- The restriction of the sheaf associated to `A` itself to `U = Spec A \ V(I)` is the unit
module of the structure sheaf of `U`. -/
def complementTildeRingIsoUnit :
    complementTilde A I (ModuleCat.of A A) ≅
      SheafOfModules.unit (complementZeroLocus A I : Scheme).ringCatSheaf :=
  Scheme.Modules.restrictUnitIso (complementZeroLocus A I).ι

/-- **The restriction map of the low-degree sequence on the ring itself.** For `M = A` and the
unit module of `𝒪_U`, the restriction map of Stacks 0DWR is the map
`Stacks.LocalCohomology.complementTopScalars` on global functions, `A ⟶ Γ(U, 𝒪_U)`.

The restriction map sends `m` to the family of fractions `m/1`; at `m = 1` that family is the
unit of the sections ring, and the general case follows by `A`-linearity. -/
theorem restrictionToComplement_ring_apply
    (D : LocalizationTriangleData.{u, u} A I hI) (a : A) :
    restrictionToComplement D (ModuleCat.of A A)
        (SheafOfModules.unit (complementZeroLocus A I : Scheme).ringCatSheaf)
        (complementTildeRingIsoUnit A I).symm a =
      complementTopScalars I a := by
  set ρ := restrictionToComplement D (ModuleCat.of A A)
    (SheafOfModules.unit (complementZeroLocus A I : Scheme).ringCatSheaf)
    (complementTildeRingIsoUnit A I).symm with hρ
  have h1 : ρ 1 = (1 : Γ((complementZeroLocus A I : Scheme), ⊤)) := by
    rw [hρ, restrictionToComplement_apply]
    show ((complementZeroLocus A I).ι.appIso ⊤).hom _ = 1
    convert map_one ((complementZeroLocus A I).ι.appIso ⊤).hom.hom using 1
    congr 1
    apply Subtype.ext
    funext x
    show LocalizedModule.mk (1 : A) (1 : x.1.asIdeal.primeCompl) =
      (1 : LocalizedModule x.1.asIdeal.primeCompl A)
    exact (LocalizedModule.numeratorRingHom (S := x.1.asIdeal.primeCompl) (A := A)).map_one
  have h2 := map_smul ρ a (1 : ModuleCat.of A A)
  rw [smul_eq_mul, mul_one] at h2
  rw [h2, h1]
  show (complementTopScalars I a) * (1 : Γ((complementZeroLocus A I : Scheme), ⊤)) = _
  exact mul_one _

/-- **Vanishing of `H¹` is surjectivity of the restriction on global functions.**
`H¹_{V(I)}(A) = 0` if and only if `A ⟶ Γ(Spec A \ V(I), 𝒪)` is surjective.

Both directions read off the low-degree exact sequence of Stacks 0DWR at `M = A`: its connecting
map `Γ(U, 𝒪_U) ⟶ H¹_{V(I)}(A)` is surjective with kernel the image of the restriction map, so it
vanishes exactly when the restriction map is surjective. The restriction map is
`Stacks.LocalCohomology.complementTopScalars` by
`Stacks.LocalCohomology.restrictionToComplement_ring_apply`. -/
theorem isZero_localCohomologyModule_one_iff_surjective :
    Limits.IsZero (localCohomologyModule A I hI (ModuleCat.of A A) 1) ↔
      Function.Surjective (complementTopScalars I) := by
  obtain ⟨D, hD⟩ := lowDegreeExactSequence.{u} A I hI
  obtain ⟨-, -, hex, hsur⟩ := hD (ModuleCat.of A A)
    (SheafOfModules.unit (complementZeroLocus A I : Scheme).ringCatSheaf)
    (complementTildeRingIsoUnit A I).symm
  have hfun := restrictionToComplement_ring_apply A I hI D
  have hρ : Function.Surjective (restrictionToComplement D (ModuleCat.of A A)
        (SheafOfModules.unit (complementZeroLocus A I : Scheme).ringCatSheaf)
        (complementTildeRingIsoUnit A I).symm) ↔
      Function.Surjective (complementTopScalars I) :=
    ⟨fun h x => (h x).imp fun a ha => (hfun a).symm.trans ha,
      fun h x => (h x).imp fun a ha => (hfun a).trans ha⟩
  rw [← hρ, ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun hz x => (hex x).mp (Subsingleton.elim _ _),
    fun hs => subsingleton_of_forall_eq 0 fun z => ?_⟩
  obtain ⟨s, rfl⟩ := hsur z
  exact (hex s).mpr (hs s)

/-- **Vanishing of `H¹` is surjectivity of restriction of sections**, in terms of the map
`Γ(Spec A, 𝒪) ⟶ Γ(U, 𝒪)` induced by the open immersion rather than of the map out of `A`.

The two differ by the isomorphism `Stacks.LocalCohomology.complementTopScalars` is composed with,
`AlgebraicGeometry.Scheme.ΓSpecIso`, so surjectivity of one is surjectivity of the other. -/
theorem isZero_localCohomologyModule_one_iff_surjective_appTop :
    Limits.IsZero (localCohomologyModule A I hI (ModuleCat.of A A) 1) ↔
      Function.Surjective (complementZeroLocus A I).ι.appTop := by
  rw [isZero_localCohomologyModule_one_iff_surjective A I hI]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨a, ha⟩ := h x
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv a, ha⟩
  · obtain ⟨b, hb⟩ := h x
    obtain ⟨a, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 b
    exact ⟨a, hb⟩

end Stacks.LocalCohomology

end
