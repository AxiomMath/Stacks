module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.AffineComplement
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmpleFamily
public import StacksFrontier.AlgebraicGeometry.Properties.NormalCoproduct
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
import StacksCore.Tactic.StacksAttribute

/-!
# A quasi-compact regular scheme with affine diagonal has an ample family of invertible modules

Let `X` be a quasi-compact regular scheme whose diagonal `Δ : X ⟶ X ×  X` is affine. Then `X`
carries an ample family of invertible modules in the sense of
`AlgebraicGeometry.Scheme.IsAmpleFamily` (Stacks Tag 0FXR).

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_dense_mem_of_isNormal`: every point of a Noetherian
  normal scheme lies in a *dense* affine open.
* `AlgebraicGeometry.exists_isAmpleFamily_of_isRegular`: **Stacks Tag 0GML.**

## The argument

The source's proof is followed step for step.

*The dense affine open.* A Noetherian normal scheme is a finite disjoint union of integral
schemes (Tag 033M, `AlgebraicGeometry.isNormal_iff_exists_iso_finite_coproduct_integral_normal`),
and a regular scheme is normal (Tag 0569, `AlgebraicGeometry.isNormal_of_isRegular`). On an
integral scheme every nonempty open is dense, so choosing in each component an affine open — the
one containing the given point in the component that point lies in, an arbitrary one elsewhere —
and taking the union over components gives a dense open which is affine, being a *finite*
disjoint union of affines. This is `exists_isAffineOpen_dense_mem_of_isNormal`, and it replaces
the source's reduction to the integral case: rather than reducing the statement, the only thing
the integral case is used for — a dense affine neighbourhood of each point — is produced
directly.

*The divisor.* The local rings of a regular scheme are regular local, hence unique factorization
domains (`IsRegularLocalRing.uniqueFactorizationMonoid`, the source's More on Algebra, Lemma
15.123.2). Tag 0EGJ (`AlgebraicGeometry.exists_effectiveCartierDivisor_compl_affineOpen`) then
produces, for each point `x`, an effective Cartier divisor `D x` whose support is the complement
of the dense affine open `U x` around `x`. This is the step that consumes the affine diagonal.

*The family.* Take `𝒪_X(D x)` for `L x`, indexed by the points of `X`, and `1_{D x}` for the
section. The canonical section vanishes exactly along the divisor
(`Stacks.Divisors.nonvanishingLocus_canonicalSections`), so its nonvanishing locus is `U x`,
which is affine and contains `x`. Invertibility of `𝒪_X(D x)` is Tag 01WX (1)
(`Stacks.Divisors.stacksIsInvertible_invertibleSheaf`), and quasi-compactness is the hypothesis.
The first tensor power is the sheaf itself (`SheafOfModules.tensorPower_one` is a `rfl`), so no
tensor-power comparison is needed.

## Implementation notes

**Quasi-compactness is `CompactSpace X`**, an instance binder, and the affine diagonal is
`IsAffineHom (pullback.diagonal (terminal.from X))`, likewise. The latter is a condition on the
absolute diagonal and is strictly weaker than separatedness; it is the hypothesis Tag 0EGJ is
stated with.

**The index type is `X` itself.** `IsAmpleFamily` quantifies over an arbitrary index type and
asks only that *some* member of the family work at each point, so the family may be indexed by
the points of `X` with no finiteness condition; quasi-compactness enters only through the
`compactSpace` field. The source's "finite family" is recovered where it is needed, by
`AlgebraicGeometry.Scheme.exists_finite_affine_nonvanishing_cover`.

**Two spellings of `𝒪_X(D)`.** `Stacks.Divisors.invertibleSheaf` lives over
`structureSheafRing X.toRingedSpace` and
`Stacks.Divisors.invertibleSheaf'` over
`structureSheafRing X.toRingedSpace`. The two ring
sheaves are equal by `rfl`, and the former is the one
`Stacks.Divisors.nonvanishingLocus_canonicalSections` is stated for, so it is the one used here;
`X.Modules` accepts it without a cast.

## References

* [Stacks Project, Tag 0GML](https://stacks.math.columbia.edu/tag/0GML)
* [Stacks Project, Tag 0FXR](https://stacks.math.columbia.edu/tag/0FXR)
* [Stacks Project, Tag 0EGJ](https://stacks.math.columbia.edu/tag/0EGJ)
* [Stacks Project, Tag 033M](https://stacks.math.columbia.edu/tag/033M)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

section CoproductOpens

variable {X : Scheme.{u}} {ι : Type u}

/-- The image in `X` of a chosen open of the `i`-th component, along an isomorphism
`e : X ≅ ∐ Y`. -/
noncomputable def coproductComponentImage (Y : ι → Scheme.{u}) (e : X ≅ ∐ Y)
    (t : ∀ i, (Y i).Opens) (i : ι) : X.Opens :=
  ((t i).ι ≫ Sigma.ι Y i ≫ e.inv).opensRange

/-- The union, over the components of `X ≅ ∐ Y`, of the images of a chosen open in each
component. -/
noncomputable def coproductComponentUnion (Y : ι → Scheme.{u}) (e : X ≅ ∐ Y)
    (t : ∀ i, (Y i).Opens) : X.Opens :=
  ⨆ i, coproductComponentImage Y e t i

/-- A union over the components of `X ≅ ∐ Y` of affine opens, one per component, is affine when
there are finitely many components: the pieces are pairwise disjoint and a finite disjoint union
of affine schemes is affine. -/
@[ega "II 1.4.9" "more general"]
theorem coproductComponentUnion_isAffineOpen [Finite ι] (Y : ι → Scheme.{u}) (e : X ≅ ∐ Y)
    (t : ∀ i, (Y i).Opens) (hAff : ∀ i, IsAffineOpen (t i)) :
    IsAffineOpen (coproductComponentUnion Y e t) := by
  refine IsAffineOpen.iSup_of_disjoint (fun i => ?_) (fun i j hij => ?_)
  · have : IsAffine (t i).toScheme := hAff i
    exact isAffineOpen_opensRange _
  · refine disjoint_iff.mpr (Opens.ext ?_)
    rw [Opens.coe_inf, Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hsum : Sigma.ι Y i ((t i).ι a) = Sigma.ι Y j ((t j).ι b) := by
      simpa [coproductComponentImage, Scheme.Hom.comp_apply] using congrArg e.hom (ha.trans hb.symm)
    exact hij (congrArg Sigma.fst ((sigmaι_eq_iff Y i j _ _).mp hsum))

/-- Every point of `X ≅ ∐ Y` is the image of a point of some component. -/
private theorem exists_sigma_ι_inv_eq (Y : ι → Scheme.{u}) (e : X ≅ ∐ Y) (x : X) :
    ∃ (i : ι) (y : Y i), e.inv (Sigma.ι Y i y) = x := by
  obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Y).surjective (e.hom x)
  exact ⟨i, y, by simpa using congrArg e.inv hy⟩

/-- A union over the components of `X ≅ ∐ Y` of opens dense in their component is dense. -/
theorem coproductComponentUnion_dense (Y : ι → Scheme.{u}) (e : X ≅ ∐ Y)
    (t : ∀ i, (Y i).Opens) (hDense : ∀ i, Dense (t i : Set (Y i))) :
    Dense (coproductComponentUnion Y e t : Set X) := by
  refine dense_iff_inter_open.2 fun W hW ⟨x, hxW⟩ => ?_
  obtain ⟨i, y, hmap⟩ := exists_sigma_ι_inv_eq Y e x
  set f : Y i ⟶ X := Sigma.ι Y i ≫ e.inv with hf
  replace hmap : f y = x := hmap
  obtain ⟨y', hy'W, hy'U⟩ := (hDense i).inter_open_nonempty (f ⁻¹' W)
    (hW.preimage (Scheme.Hom.continuous f)) ⟨y, by rw [Set.mem_preimage, hmap]; exact hxW⟩
  exact ⟨f y', hy'W, Opens.mem_iSup.mpr ⟨i, ⟨⟨y', hy'U⟩, rfl⟩⟩⟩

end CoproductOpens

/-- **Every point of a Noetherian normal scheme lies in a dense affine open.**

A Noetherian normal scheme is a finite disjoint union of integral schemes (Tag 033M), on each of
which every nonempty open is dense. Choosing an affine open in each component — one containing
the given point in the component that point lies in — and taking the union over the finitely many
components gives an open which is dense, and affine because a finite disjoint union of affines
is affine.

This is the first step of the Stacks proof of Tag 0GML; it is what the reduction to the integral
case there is used for. -/
theorem exists_isAffineOpen_dense_mem_of_isNormal (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsNormal X) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ Dense (U : Set X) ∧ x ∈ U := by
  classical
  obtain ⟨ι, hfin, Y, -, hint, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_finite_coproduct_integral_normal X).mp hX
  have : Finite ι := hfin
  obtain ⟨i₀, y₀, hxi⟩ := exists_sigma_ι_inv_eq Y e x
  have hne : ∀ i, Nonempty (Y i) := fun i => have := hint i; IsIntegral.nonempty
  -- a point of every component, taken to be `y₀` in the component of `x`
  set z : ∀ i, Y i := Function.update (fun i => (hne i).some) i₀ y₀ with hz
  have hzi₀ : z i₀ = y₀ := by rw [hz]; exact Function.update_self ..
  -- an affine open around each of those points
  choose V hVmem using fun i => Stacks.Divisors.exists_affineOpens_mem (z i)
  refine ⟨coproductComponentUnion Y e (fun i => (V i).1),
    coproductComponentUnion_isAffineOpen Y e _ (fun i => (V i).2),
    coproductComponentUnion_dense Y e _ (fun i => ?_), Opens.mem_iSup.mpr ⟨i₀, ?_⟩⟩
  · have : IsIntegral (Y i) := hint i
    exact (V i).1.isOpen.dense ⟨z i, hVmem i⟩
  · exact ⟨⟨y₀, hzi₀ ▸ hVmem i₀⟩, hxi⟩

/-- **Stacks Project, Tag 0GML.** A quasi-compact regular scheme whose diagonal is affine has an
ample family of invertible modules.

The family is `{𝒪_X(D x)}` indexed by the points of `X`, where `D x` is the effective Cartier
divisor whose support is the complement of a dense affine open around `x`, supplied by Tag 0EGJ;
the required section of `𝒪_X(D x)` is the canonical section `1_{D x}`, whose nonvanishing locus
is exactly that affine open. -/
@[stacks 0GML, sga "6 II 2.2.7.1" "more general"]
theorem exists_isAmpleFamily_of_isRegular (X : Scheme.{u}) [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : IsRegular X) :
    ∃ (I : Type u) (L : I → X.Modules), X.IsAmpleFamily L := by
  classical
  have hreg := ((isRegular_tfae X).out 1 2).mp hX
  have : IsLocallyNoetherian X := hreg.1
  have : IsNoetherian X := ⟨⟩
  have hUFD : ∀ y : X, UniqueFactorizationMonoid (X.presheaf.stalk y) := fun y =>
    have := hreg.2 y
    IsRegularLocalRing.uniqueFactorizationMonoid _
  -- a dense affine open around each point, and the divisor cutting out its complement
  choose U hUaff hUdense hUmem using
    exists_isAffineOpen_dense_mem_of_isNormal X (isNormal_of_isRegular X hX)
  choose D hDeff hDsupp using fun x : X =>
    exists_effectiveCartierDivisor_compl_affineOpen X (U x) (hUaff x) (hUdense x)
      fun y _ => hUFD y
  have hUeq : ∀ x : X, (U x : Set X) = ((D x).support : Set X)ᶜ := fun x => by
    rw [hDsupp x, compl_compl]
  refine ⟨X, fun x => (Stacks.Divisors.invertibleSheaf (D x) : X.Modules), ?_, ?_, fun x => ?_⟩
  · intro x
    have := hDeff x
    exact Stacks.Divisors.stacksIsInvertible_invertibleSheaf (D x)
  · infer_instance
  · have := hDeff x
    refine ⟨x, 1, le_refl 1, Stacks.Divisors.canonicalSections (D x), U x, ?_, hUmem x, hUaff x⟩
    rw [hUeq x]
    exact (Stacks.Divisors.nonvanishingLocus_canonicalSections (D x)).symm

end AlgebraicGeometry

end
