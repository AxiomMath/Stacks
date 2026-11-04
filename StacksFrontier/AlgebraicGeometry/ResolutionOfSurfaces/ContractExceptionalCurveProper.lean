module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.NodalContraction.FiniteType
import all StacksFrontier.AlgebraicGeometry.NodalContraction.FiniteType

/-!
# The contraction of an exceptional curve is proper over an affine Noetherian base

Let `R` be a Noetherian ring, let `X` be proper over `S = Spec R`, and let `E ⊆ X` be an
exceptional curve of the first kind, presented by its ideal sheaf `D` together with an
isomorphism `e : 𝐏¹_k ≅ E`. If `b : X ⟶ X'` is a contraction of `E` in the sense of
`AlgebraicGeometry.IsContractionOfExceptionalCurve`, then the structure morphism of `X` factors
uniquely through `b` and the factorisation `X' ⟶ S` is proper. This is assertion (2) of
[Stacks, Tag 0C2M].

The factorisation itself is the universal property of the contraction ([Stacks, Tag 0C5J],
`AlgebraicGeometry.existsUnique_comp_eq_of_isContractionOfExceptionalCurve`): the exceptional
curve is sent to a single point of `S` because `Γ(E, 𝒪_E) = k` is a field. Properness of the
factorisation is then descent along `b`, which is proper and surjective:

* `UniversallyClosed` descends along a surjection
  (`AlgebraicGeometry.UniversallyClosed.of_comp_surjective`);
* `IsSeparated` descends along a surjective universally closed morphism
  ([Stacks, Tag 09MQ], `AlgebraicGeometry.isSeparated_of_surjective_universallyClosed`);
* `LocallyOfFiniteType` descends because the question is local on `X'` and a contraction is an
  isomorphism away from its centre, while on an affine neighbourhood of the centre the global
  sections of the target are a finite-type `R`-algebra
  (`AlgebraicGeometry.locallyOfFiniteType_of_contraction_of_isAffine`).

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_of_isContractionOfExceptionalCurve` — finite type over
  an affine Noetherian base descends along a contraction.
* `AlgebraicGeometry.isProper_of_isContractionOfExceptionalCurve` — properness over an affine
  Noetherian base descends along a contraction.
* `AlgebraicGeometry.exists_isProper_comp_eq_of_isContractionOfExceptionalCurve` — assertion (2)
  of [Stacks, Tag 0C2M]: the contracted scheme is proper over the base, through the unique
  factorisation of the structure morphism.

## Implementation notes

**Where Tag 0C2M is registered.** This file proves assertion (2) of [Stacks, Tag 0C2M] for an
arbitrary contraction. The tag itself, with all three assertions, is registered on
`AlgebraicGeometry.exists_contraction_isProper_isAmple` in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/ContractExceptionalCurveAmple.lean`, which
uses the results here for assertion (2).

The ampleness hypothesis on `L` is not stated below: assertion (2) does not use it. The source
needs it only to construct the morphism to `𝐏^{n+1}_S` whose Stein factorization gives (1), and
to run the ampleness bookkeeping of (3). Likewise the normal-sheaf clause
`AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` of the exceptional curve
is not needed: what the argument consumes is the presentation `e : 𝐏¹_k ≅ E`, which gives both
that `E` is nonempty and that `Γ(E, 𝒪_E)` is a field.

## References

* [Stacks Project, Tag 0C2M](https://stacks.math.columbia.edu/tag/0C2M)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Finite type over an affine Noetherian base descends along a contraction.** If
`b : X ⟶ X'` contracts an ideal sheaf on `X` and `X` is locally of finite type over `Spec R`
through `b`, then `X'` is locally of finite type over `Spec R`.

The question is local on `X'`. Away from the contracted point `z` the contraction is an
isomorphism, so the base morphism there is a composition of an open immersion with
`b ≫ f'`. On an affine open neighbourhood of `z` the restriction of `b` is again a contraction
(`AlgebraicGeometry.contraction_restrict`) and the affine case
`AlgebraicGeometry.locallyOfFiniteType_of_contraction_of_isAffine` applies. -/
public theorem locallyOfFiniteType_of_isContractionOfExceptionalCurve
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (.of R)) [LocallyOfFiniteType (b ≫ f')] :
    LocallyOfFiniteType f' := by
  have := hb.isNoetherian
  have : MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨z, hz, hreg, hdim, hD, ε, hε⟩ := hb.exists_blowUp_iso
  obtain ⟨U, hUaff, hzU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X') (U := ⊤) (x := z) trivial
  have : IsAffine U.toScheme := hUaff
  have hres : ∀ V : X'.Opens, LocallyOfFiniteType ((b ∣_ V) ≫ V.ι ≫ f') := fun V => by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  have := hres U
  have hU : LocallyOfFiniteType (U.ι ≫ f') :=
    locallyOfFiniteType_of_contraction_of_isAffine
      (contraction_restrict D b z hz hreg hdim hD ε hε U hzU) (U.ι ≫ f')
  let W : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
  have hW : LocallyOfFiniteType (W.ι ≫ f') := by
    have : IsIso (b ∣_ W) :=
      isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
        (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ε hε
    exact (MorphismProperty.cancel_left_of_respectsIso
      (@LocallyOfFiniteType.{u}) (b ∣_ W) (W.ι ≫ f')).mp (hres W)
  let C : Bool → X'.Opens := fun t => if t then U else W
  have hcover : iSup C = ⊤ := by
    refine top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ?_
    by_cases hy : y = z
    · exact ⟨true, hy ▸ hzU⟩
    · exact ⟨false, hy⟩
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType.{u}) C hcover fun
    | false => hW
    | true => hU

/-- **Properness over an affine Noetherian base descends along a contraction.** Let
`b : X ⟶ X'` contract an exceptional curve of the first kind presented by
`e : 𝐏¹_k ≅ E`, and let `f' : X' ⟶ Spec R` be a morphism with `R` Noetherian. If the composite
`b ≫ f'` is proper then so is `f'`.

A contraction is proper and, the exceptional curve being nonempty, surjective. So universal
closedness descends by `AlgebraicGeometry.UniversallyClosed.of_comp_surjective`, separatedness
by [Stacks, Tag 09MQ] and finite type by
`AlgebraicGeometry.locallyOfFiniteType_of_isContractionOfExceptionalCurve`. -/
public theorem isProper_of_isContractionOfExceptionalCurve
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X X' : Scheme.{u}}
    (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme)
    {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (.of R)) (hf : IsProper (b ≫ f')) :
    IsProper f' := by
  have := hf
  have := hb.isProper
  have : Surjective b := ⟨surjective_of_isContractionOfExceptionalCurve D k e b hb⟩
  have hUC : UniversallyClosed f' := UniversallyClosed.of_comp_surjective b f'
  have hsep : IsSeparated f' := by
    let g : (Over.mk (b ≫ f') : Over (Spec (.of R))) ⟶ Over.mk f' := Over.homMk b rfl
    have : Surjective g.left := inferInstanceAs (Surjective b)
    have : UniversallyClosed g.left := inferInstanceAs (UniversallyClosed b)
    have : IsSeparated (Over.mk (b ≫ f') : Over (Spec (.of R))).hom :=
      inferInstanceAs (IsSeparated (b ≫ f'))
    exact isSeparated_of_surjective_universallyClosed g
  exact (isProper_iff f').2
    ⟨hsep, hUC, locallyOfFiniteType_of_isContractionOfExceptionalCurve hb f'⟩

/-- **[Stacks, Tag 0C2M] assertion (2).** Let `R` be a Noetherian ring, let `f : X ⟶ Spec R` be
proper, and let `E ⊆ X` be an exceptional curve of the first kind presented by its ideal sheaf
`D` and an isomorphism `e : 𝐏¹_k ≅ E`. If `b : X ⟶ X'` is a contraction of `E`, then `X'` is
proper over `Spec R`: the structure morphism of `X` factors through `b`, and the factorisation
is proper.

The factorisation exists because `f` carries `E` to a single point of `Spec R`, the ring
`Γ(E, 𝒪_E) = k` being a field, so the universal property of the contraction ([Stacks, Tag
0C5J]) applies; it is unique by that same universal property. -/
public theorem exists_isProper_comp_eq_of_isContractionOfExceptionalCurve
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X X' : Scheme.{u}}
    (D : X.IdealSheafData) (k : Type u) [Field k]
    (e : projectiveLineProj k ≅ D.subscheme)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f : X ⟶ Spec (.of R)) (hf : IsProper f) :
    ∃ f' : X' ⟶ Spec (.of R), b ≫ f' = f ∧ IsProper f' := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  obtain ⟨d₀⟩ : Nonempty D.subscheme := inferInstance
  have : Nonempty (Spec (CommRingCat.of R)) := ⟨f (D.subschemeι d₀)⟩
  obtain ⟨f', hcomp, -⟩ := existsUnique_comp_eq_of_isContractionOfExceptionalCurve D b hb f
    (exists_const_on_exceptionalCurve D k e f)
  exact ⟨f', hcomp, isProper_of_isContractionOfExceptionalCurve D k e hb f' (by rwa [hcomp])⟩

end AlgebraicGeometry

end
