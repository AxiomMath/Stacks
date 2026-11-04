module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.LocalEquationMultiplicity
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf
import all StacksFrontier.AlgebraicGeometry.Blowup.Colength.LocalBound
import all StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
import all StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic

/-!
# The coefficient of a fibre cycle as a colength in the local ring of the family

Let `f : X ⟶ S` and let `Z ⊆ X ×_S 𝐏¹_S` be a closed subscheme with zero fibre
`Z₀ = Z ∩ (X × \{0\})`, read as a closed subscheme of `X`. Stacks Tag 02S5 compares `[Z₀]_k` with
`[Z_∞]_k`, and the local identity its proof rests on is stated in
`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/LocalMultiplicity.lean` as
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`: an
identity of lengths in the local ring `A = 𝒪_{X ×_S 𝐏¹_S, ξ}` at the point `ξ = (ξ', 0)`, whose
left-hand side is `length_A A/(t, I)` for `I ⊆ A` the stalk of the ideal sheaf of `Z` and `t ∈ A`
a local equation of the zero section.

This file identifies that left-hand side with the geometry: the coefficient of `[Z₀]_k` at `ξ'`
*is* `length_A A/(t, I)`. Nothing here is specific to the projective line until the last two
statements — the comparison holds for the inverse image of an ideal sheaf along an arbitrary
closed immersion, and the projective line enters only in producing `t`, which exists because the
ideal sheaf cut out by either distinguished section is locally principal
(`Stacks.Chow.isLocallyPrincipal_ker_zeroSection`).

## Main results

* `Stacks.Chow.ker_stalkMap_eq_idealStalk_ker` — for a closed immersion the kernel of the stalk
  map at a point is the stalk at the image of the kernel ideal sheaf.
* `Stacks.Chow.length_stalk_quotient_comap_eq` — the colength at `x` of the inverse image of an
  ideal sheaf along a closed immersion `g` equals the colength at `g x` of the sum of the kernel
  of the stalk map of `g` and the stalk of the ideal sheaf.
* `Stacks.Chow.cycleAssociatedToComap_apply_eq_length` — consequently the coefficient of the
  cycle of that inverse image, at the image of a generic point of relative dimension `k`, is that
  colength.
* `Stacks.Chow.exists_span_eq_ker_stalkMap_zeroSection` and
  `Stacks.Chow.exists_span_eq_ker_stalkMap_infinitySection` — the kernel of the stalk map of
  either distinguished section is a principal ideal, a local equation of that section.
* `Stacks.Chow.exists_localEquation_cycleAssociatedToZeroFiber_apply_eq_length` and
  `Stacks.Chow.exists_localEquation_cycleAssociatedToInfinityFiber_apply_eq_length` — the two
  statements the local identity consumes: the coefficient of `[Z₀]_k`, respectively `[Z_∞]_k`, at
  a point of relative dimension `k` is the colength of `(t, I)`.

## Implementation notes

The chain is three identities of lengths of one module. The coefficient of the cycle at the image
of a generic point is the multiplicity of that component
(`Stacks.Chow.cycleAssociatedToClosedSubscheme_apply`); the multiplicity is the length of the
stalk of the subscheme (`Stacks.Chow.componentMultiplicity_eq_length_stalk`), which is the
quotient of the local ring of `X` by the stalk of the inverse-image ideal sheaf
(`Stacks.Blowup.Colength.length_idealStalk_quotient_eq_subschemeStalk`); and that stalk is the
image of the stalk upstairs (`AlgebraicGeometry.idealStalk_comap_eq_map`), so the quotient is
`A/(ker φ + I)` for `φ : A → 𝒪_{X,x}` the stalk map. The last step is purely ring-theoretic —
for a surjection `φ : A → B` and an ideal `I ⊆ A`, the `A`-module `B/I.map φ` is `A/(ker φ + I)`,
since `(I.map φ).comap φ = I ⊔ ker φ` — and the change of base ring is
`Stacks.length_restrictScalars_eq_of_surjective`, the same device
`Stacks.Chow.componentMultiplicity_eq_length_stalk` uses.

The identification of `ker φ` with the stalk of `g.ker` is read on one affine open `U` of the
target and its preimage, which is affine because a closed immersion is an affine morphism. On
sections the statement is `Scheme.Hom.ker_apply` (available because a closed immersion is
quasi-compact) together with `Stacks.Flatness.ker_stalkMap_eq_map_germ`, whose surjectivity
hypothesis is `Scheme.Hom.app_surjective`.

Two declarations of other modules are reached with `import all` rather than re-ported:
`Stacks.Blowup.Colength.length_idealStalk_quotient_eq_subschemeStalk` and
`AlgebraicGeometry.idealStalk_comap_eq_map`. The stalk of an ideal sheaf on an affine open is
read off with the public `AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ`.

The two concluding statements are existential in the local equation `t` because local principality
supplies a generator only locally, and no canonical choice is available or needed: the local
identity holds for every element whose quotient has the right dimension, so the consumer may use
whichever generator it is handed.

### What Tag 02S5 takes from this file, and why nothing here bears its attribute

The source's proof of Tag 02S5 has two halves and this file serves only the first. Writing
`W_i` for the irreducible components of `Z` of delta-dimension `k + 1` and `n_i` for their
multiplicities, they are:

* the *claim* `[Z_0]_k = \sum n_i [(W_i)_0]_k`, whose local content is
  `Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`. The
  statements of this file supply its left-hand side, and those of
  `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/StalkDimension.lean` two of its three
  hypotheses. The index correspondence on the right — that the components of `Z` through `\xi`
  are the minimal primes of `IdealSheafData.stalk Z \xi`, with
  `Stacks.Chow.componentMultiplicity` at the component matching the length of the localisation
  of `A/I` there — is `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/StalkPrimes.lean`:
  `Stacks.Chow.bijOn_fromSpecStalk_minimalPrimes` and
  `Stacks.Chow.length_localizedModule_quotient_idealStalk_eq_componentMultiplicity`. It does use
  `AlgebraicGeometry.Scheme.fromSpecStalk` as an order embedding of `Spec 𝒪_{X,\xi}` onto the
  generalisations of `\xi`, and that embedding is available: `IsPreimmersion` of
  `X.fromSpecStalk \xi` gives injectivity and, through `Topology.IsInducing.specializes_iff`,
  order reflection, while `AlgebraicGeometry.Scheme.range_fromSpecStalk` gives the range. All
  three hypotheses of the local comparison are now discharged from the hypotheses of the tag
  itself, in `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/FibreCoefficientSum.lean`, and the
  assembly of the finsum over a global family of components is
  `Stacks.Chow.fibreCycleComponentDecompositionRule`
  (`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/ComponentDecomposition.lean`), so the claim
  is proved.
* Tag 02S4 part (3), which in library vocabulary reads: for `C : ChowSituation`, `f : X ⟶ C.S`
  locally of finite type, `k : ℤ` and a family `W : J → (projectiveLineProduct f).IdealSheafData`
  with each `(W j).subscheme` integral, each generic point of relative dimension `k + 1` for
  `Stacks.Chow.familyBase f (W j)`, each `Set.range (W j).subschemeι` contained in neither
  `Set.range (zeroSection f)` nor `Set.range (infinitySection f)`, and
  `LocallyFinite fun j ↦ ((W j).support : Set (projectiveLineProduct f))`, there is a cycle
  `α : CycleGroup C f k` with `IsRationallyEquivalentToZero C f k α` and
  `∀ x, α.1 x = familyFibreDifferenceCoefficient C f k W x`. The coefficient function is defined
  as `Stacks.Chow.familyFibreDifferenceCoefficient`; the statement is stated in library
  vocabulary as `Stacks.Chow.FamilyFibreDifferencesRationallyEquivalentToZero`
  (`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/FibreComparison.lean`),
  `StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/FibreFamilyReduction.lean` reduces it to the
  one-member statement `Stacks.Chow.FibreCyclesRationallyEquivalentWithin` — the existence of
  the cycle `α` being proved there as `Stacks.Chow.exists_familyFibreDifferenceSum` — and the
  one-member statement is discharged, with no hypothesis, by the dimension-drop branch of Tag
  02S2 in
  `StacksFrontier/AlgebraicGeometry/Chow/ProperPushforwardPrincipal/DimensionDropApplications.lean`.
  So the theorem is proved too, as
  `Stacks.Chow.familyFibreDifferencesRationallyEquivalentToZero`, and nothing here is circular.

So no declaration here carries `@[stacks 02S5]`, but the tag's own statement is proved:
`Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent`
(`StacksFrontier/AlgebraicGeometry/Chow/ProperPushforwardPrincipal/DimensionDropApplications.lean`),
and in the hypothesis shape of the source
`Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent_of_isEmbeddedPoint`
(`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/EmbeddedPointHypothesis.lean`).

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Order TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### A colength identity for a surjection of rings -/

/-- For a surjective ring map `φ : A →+* B` and an ideal `I` of `A`, the `A`-module `B ⧸ I.map φ`
has the same length as `A ⧸ (ker φ ⊔ I)`. -/
private theorem length_quotient_map_eq_length_quotient_sup_ker
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : Function.Surjective φ)
    (I : Ideal A) :
    letI : Module A (B ⧸ I.map φ) := Module.compHom _ φ
    Module.length A (B ⧸ I.map φ) = Module.length A (A ⧸ (RingHom.ker φ ⊔ I)) := by
  let _ : Module A (B ⧸ I.map φ) := Module.compHom _ φ
  let ψ : A →ₗ[A] (B ⧸ I.map φ) :=
    { toFun := fun a => Ideal.Quotient.mk (I.map φ) (φ a)
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        simp only [RingHom.id_apply]
        show Ideal.Quotient.mk (I.map φ) (φ (r * a)) = r • Ideal.Quotient.mk (I.map φ) (φ a)
        rw [map_mul]
        rfl }
  have hψsurj : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
  have hcm := Ideal.comap_map_of_surjective φ hφ I
  have hker : LinearMap.ker ψ = RingHom.ker φ ⊔ I := by
    rw [sup_comm]
    apply le_antisymm
    · intro a ha
      refine hcm ▸ Ideal.mem_comap.mpr ?_
      exact Ideal.Quotient.eq_zero_iff_mem.mp ha
    · intro a ha
      have h2 : a ∈ (I.map φ).comap φ := hcm ▸ ha
      show Ideal.Quotient.mk (I.map φ) (φ a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp h2)
  have e : (A ⧸ (RingHom.ker φ ⊔ I)) ≃ₗ[A] (B ⧸ I.map φ) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hψsurj)
  exact e.length_eq.symm

/-! ### The kernel of the stalk map of a closed immersion -/

/-- For a closed immersion, the kernel of the stalk map at a point is the stalk at the image of
the kernel ideal sheaf.

Both sides are read on one affine open of the target and its preimage, which is affine because a
closed immersion is an affine morphism; the section-level statement is then `Scheme.Hom.ker_apply`
together with `Stacks.Flatness.ker_stalkMap_eq_map_germ`, whose surjectivity hypothesis holds
because a closed immersion is surjective on sections over an affine open. -/
theorem ker_stalkMap_eq_idealStalk_ker {X Y : Scheme.{u}} (g : X ⟶ Y) [IsClosedImmersion g]
    (x : X) :
    RingHom.ker (g.stalkMap x).hom = IdealSheafData.stalk g.ker (g x) := by
  obtain ⟨U, hxU⟩ := Stacks.Divisors.exists_affineOpens_mem (g x)
  have hVaff : IsAffineOpen (g ⁻¹ᵁ (U : Y.Opens)) := U.2.preimage g
  have hxV : x ∈ g ⁻¹ᵁ (U : Y.Opens) := hxU
  have hsurj : Function.Surjective
      (g.appLE (U : Y.Opens) (g ⁻¹ᵁ (U : Y.Opens)) le_rfl).hom := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact g.app_surjective (U : Y.Opens) U.2
  rw [IdealSheafData.stalk_eq_map_germ g.ker (g x) U hxU, Scheme.Hom.ker_apply g U,
    Stacks.Flatness.ker_stalkMap_eq_map_germ g U.2 hVaff le_rfl hxV hxU hsurj,
    ← Scheme.Hom.app_eq_appLE]

/-! ### The colength of an inverse-image ideal sheaf -/

/-- The stalk at `x` of the inverse image of an ideal sheaf along a closed immersion `g` has the
same colength as the sum, in the local ring of the ambient scheme at `g x`, of the kernel of the
stalk map of `g` and the stalk of the ideal sheaf. -/
theorem length_stalk_quotient_comap_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsClosedImmersion g]
    (Z : Y.IdealSheafData) (x : X) :
    Module.length (X.presheaf.stalk x)
        (X.presheaf.stalk x ⧸ IdealSheafData.stalk (Z.comap g) x) =
      Module.length (Y.presheaf.stalk (g x))
        (Y.presheaf.stalk (g x) ⧸
          (RingHom.ker (g.stalkMap x).hom ⊔ IdealSheafData.stalk Z (g x))) := by
  have hsurj : Function.Surjective (g.stalkMap x).hom :=
    SurjectiveOnStalks.stalkMap_surjective g x
  rw [idealStalk_comap_eq_map g Z x,
    ← length_restrictScalars_eq_of_surjective (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)
      (g.stalkMap x).hom hsurj _,
    length_quotient_map_eq_length_quotient_sup_ker (g.stalkMap x).hom hsurj _]

/-- The coefficient, at the image of a generic point of relative dimension `k`, of the cycle
associated to the inverse image of `Z` along a closed immersion `g`, as a colength in the local
ring of the ambient scheme.

The coefficient is the multiplicity of the component, hence the length of the stalk of the
inverse image; that stalk is the quotient of the local ring of `X` by the stalk of the
inverse-image ideal sheaf, and `Stacks.Chow.length_stalk_quotient_comap_eq` reads the latter in
the local ring of `Y`. -/
theorem cycleAssociatedToComap_apply_eq_length
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (g : X ⟶ Y) [IsClosedImmersion g] (Z : Y.IdealSheafData) (k : ℤ)
    (ξ : genericPoints (Z.comap g).subscheme)
    (hξ : relativeDimension C.dimensionFunction p ((Z.comap g).subschemeι ξ.1) = k) :
    (cycleAssociatedToClosedSubscheme C p (Z.comap g).subschemeι k).1
        ((Z.comap g).subschemeι ξ.1) =
      ((Module.length (Y.presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)))
        (Y.presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)) ⧸
          (RingHom.ker (g.stalkMap ((Z.comap g).subschemeι ξ.1)).hom ⊔
            IdealSheafData.stalk Z (g ((Z.comap g).subschemeι ξ.1))))).toNat : ℤ) := by
  rw [cycleAssociatedToClosedSubscheme_apply C p (Z.comap g).subschemeι k ξ hξ,
    componentMultiplicity_eq_length_stalk,
    ← Stacks.Blowup.Colength.length_idealStalk_quotient_eq_subschemeStalk (Z.comap g) ξ.1,
    length_stalk_quotient_comap_eq g Z ((Z.comap g).subschemeι ξ.1)]

/-! ### Local equations for the two sections -/

/-- If the kernel ideal sheaf of a closed immersion is locally principal, the kernel of its stalk
map at every point is principal. -/
private theorem exists_span_eq_ker_stalkMap_of_isLocallyPrincipal {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsClosedImmersion g] (hg : Stacks.Divisors.IsLocallyPrincipal g.ker) (x : X) :
    ∃ t : Y.presheaf.stalk (g x), RingHom.ker (g.stalkMap x).hom = Ideal.span {t} := by
  obtain ⟨U, hxU, hprin⟩ := hg (g x)
  obtain ⟨t, ht⟩ := Submodule.IsPrincipal.principal (g.ker.ideal U)
  refine ⟨(Y.presheaf.germ (U : Y.Opens) (g x) hxU).hom t, ?_⟩
  rw [ker_stalkMap_eq_idealStalk_ker, IdealSheafData.stalk_eq_map_germ _ _ U hxU, ht,
    Ideal.map_span, Set.image_singleton]

/-- The kernel of the stalk map of the zero section is principal at every point: the ideal sheaf
cut out by the zero section is locally principal. -/
theorem exists_span_eq_ker_stalkMap_zeroSection {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk (zeroSection f x),
      RingHom.ker ((zeroSection f).stalkMap x).hom = Ideal.span {t} :=
  exists_span_eq_ker_stalkMap_of_isLocallyPrincipal _ (isLocallyPrincipal_ker_zeroSection f) x

/-- The kernel of the stalk map of the infinity section is principal at every point. -/
theorem exists_span_eq_ker_stalkMap_infinitySection {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk (infinitySection f x),
      RingHom.ker ((infinitySection f).stalkMap x).hom = Ideal.span {t} :=
  exists_span_eq_ker_stalkMap_of_isLocallyPrincipal _ (isLocallyPrincipal_ker_infinitySection f) x

/-! ### The coefficient of a fibre cycle as the colength of a local equation -/

/-- If the kernel of the stalk map of a closed immersion `g` is principal at every point, the
coefficient of the cycle of the inverse image of `Z` is the colength of a local equation of `g`
together with the stalk of `Z`. -/
private theorem exists_cycleAssociatedToComap_apply_eq_length_span
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (g : X ⟶ Y) [IsClosedImmersion g]
    (hg : ∀ x : X, ∃ t : Y.presheaf.stalk (g x),
      RingHom.ker (g.stalkMap x).hom = Ideal.span {t})
    (Z : Y.IdealSheafData) (k : ℤ) (ξ : genericPoints (Z.comap g).subscheme)
    (hξ : relativeDimension C.dimensionFunction p ((Z.comap g).subschemeι ξ.1) = k) :
    ∃ t : Y.presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)),
      (cycleAssociatedToClosedSubscheme C p (Z.comap g).subschemeι k).1
          ((Z.comap g).subschemeι ξ.1) =
        ((Module.length (Y.presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)))
          (Y.presheaf.stalk (g ((Z.comap g).subschemeι ξ.1)) ⧸
            (Ideal.span {t} ⊔
              IdealSheafData.stalk Z (g ((Z.comap g).subschemeι ξ.1))))).toNat : ℤ) := by
  obtain ⟨t, ht⟩ := hg ((Z.comap g).subschemeι ξ.1)
  refine ⟨t, ?_⟩
  have h := cycleAssociatedToComap_apply_eq_length C p g Z k ξ hξ
  rw [ht] at h
  exact h

/-- The coefficient of `[Z₀]_k` at a point of relative dimension `k` which is the image of a
generic point of the zero fibre is the colength, in the local ring of `X ×_S ℙ¹_S` at the
corresponding point of the zero section, of the ideal generated by a local equation of the zero
section together with the stalk of the ideal sheaf of `Z`.

This is the left-hand side of
`Stacks.Chow.length_quotient_span_sup_eq_sum_minimalPrimes_of_notMem_associatedPrimes`, read on
the geometry of Tag 02S5. -/
theorem exists_localEquation_cycleAssociatedToZeroFiber_apply_eq_length
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Z : (projectiveLineProduct f).IdealSheafData) (k : ℤ)
    (ξ : genericPoints (zeroFiber f Z).subscheme)
    (hξ : relativeDimension C.dimensionFunction f ((zeroFiber f Z).subschemeι ξ.1) = k) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (zeroSection f ((zeroFiber f Z).subschemeι ξ.1)),
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k).1
          ((zeroFiber f Z).subschemeι ξ.1) =
        ((Module.length
            ((projectiveLineProduct f).presheaf.stalk
              (zeroSection f ((zeroFiber f Z).subschemeι ξ.1)))
            ((projectiveLineProduct f).presheaf.stalk
                (zeroSection f ((zeroFiber f Z).subschemeι ξ.1)) ⧸
              (Ideal.span {t} ⊔
                IdealSheafData.stalk Z
                  (zeroSection f ((zeroFiber f Z).subschemeι ξ.1))))).toNat : ℤ) :=
  exists_cycleAssociatedToComap_apply_eq_length_span C f (zeroSection f)
    (exists_span_eq_ker_stalkMap_zeroSection f) Z k ξ hξ

/-- The coefficient of `[Z_∞]_k` at a point of relative dimension `k` which is the image of a
generic point of the infinity fibre, as the colength of a local equation of the infinity section
together with the stalk of the ideal sheaf of `Z`. -/
theorem exists_localEquation_cycleAssociatedToInfinityFiber_apply_eq_length
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (Z : (projectiveLineProduct f).IdealSheafData) (k : ℤ)
    (ξ : genericPoints (infinityFiber f Z).subscheme)
    (hξ : relativeDimension C.dimensionFunction f ((infinityFiber f Z).subschemeι ξ.1) = k) :
    ∃ t : (projectiveLineProduct f).presheaf.stalk
        (infinitySection f ((infinityFiber f Z).subschemeι ξ.1)),
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k).1
          ((infinityFiber f Z).subschemeι ξ.1) =
        ((Module.length
            ((projectiveLineProduct f).presheaf.stalk
              (infinitySection f ((infinityFiber f Z).subschemeι ξ.1)))
            ((projectiveLineProduct f).presheaf.stalk
                (infinitySection f ((infinityFiber f Z).subschemeι ξ.1)) ⧸
              (Ideal.span {t} ⊔
                IdealSheafData.stalk Z
                  (infinitySection f ((infinityFiber f Z).subschemeι ξ.1))))).toNat : ℤ) :=
  exists_cycleAssociatedToComap_apply_eq_length_span C f (infinitySection f)
    (exists_span_eq_ker_stalkMap_infinitySection f) Z k ξ hξ

end Stacks.Chow

end
