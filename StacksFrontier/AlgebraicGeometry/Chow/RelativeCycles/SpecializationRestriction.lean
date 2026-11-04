module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquareFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.RingTheory.ElementaryDivisorDomain.Bezout
public import StacksCore.Tactic.StacksAttribute
-- Private: this module defines a root-level `Spec` on its import path, which would otherwise
-- shadow `AlgebraicGeometry.Spec` in the importers of this file. Used only in proofs below.
import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GraphLineProjectionFlat

/-!
# Restriction of relative cycles to an open subscheme of the source

Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of finite type, and let `j : U ⟶ X`
be an open immersion with `j ≫ f = f_U`. On each fibre `j` induces an open immersion
`U_s ⟶ X_s` of scheme-theoretic fibres, so restricting coefficients along it is a homomorphism
`Z_r(X_s) ⟶ Z_r(U_s)`, and a family `α` of `r`-cycles on the fibres of `X/S` restricts to a
family `α|_U` of `r`-cycles on the fibres of `U/S`. This file proves that `α|_U` is a relative
`r`-cycle whenever `α` is: the restriction clause of Lemma 0H51 in the case where the open
subscheme of the base is the whole of `S`.

## Main definitions

* `Stacks.Chow.pullbackRestrict`: the base change of an open immersion of schemes over `S`.
* `Stacks.Chow.fiberRestrict`: the morphism `U_s ⟶ X_s` of scheme-theoretic fibres induced by
  an open immersion `j : U ⟶ X` over a fixed base.
* `Stacks.Chow.fiberCycleRestrict`: the induced homomorphism `Z_r(X_s) ⟶ Z_r(U_s)` on
  fibrewise cycle groups.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_comap_of_isOpenImmersion`: the cycle of a
  closed subscheme restricts to the cycle of its inverse image in an open subscheme.
* `Stacks.Chow.specializationClosure_eq_integralComponentAt`: the schematic closure of the
  integral closed subscheme of the generic fibre with generic point `ξ` is the integral closed
  subscheme of `X` with generic point the image of `ξ`.
* `Stacks.Chow.flat_subschemeι_specializationClosure_comp`: that schematic closure is flat over
  the discrete valuation ring.
* `Stacks.Chow.specializationCycle_fiberCycleRestrict`: over a discrete valuation ring,
  specialization commutes with restriction to an open subscheme of the source.
* `Stacks.Chow.baseChangeCycleCoeff_pullbackRestrict`,
  `Stacks.Chow.baseChangeFamily_fiberCycleRestrict`: base change of cycles, and of families of
  cycles on fibres, commutes with restriction to an open subscheme of the source.
* `Stacks.Chow.isRelativeCycle_fiberCycleRestrict`: the restriction of a relative `r`-cycle to an
  open subscheme of `X` is a relative `r`-cycle.

## References

* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Tag 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Restriction of the cycle of a closed subscheme to an open subscheme -/

/-- The cycle of a closed subscheme restricts, along an open immersion of the ambient scheme, to
the cycle of the inverse image of the subscheme. -/
theorem cycleAssociatedToClosedSubscheme_comap_of_isOpenImmersion (C : ChowSituation.{u})
    {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (jm : U ⟶ X) [IsOpenImmersion jm] (hjm : jm ≫ sX = sU)
    (I : X.IdealSheafData) (k : ℤ) (y : U) :
    (cycleAssociatedToClosedSubscheme C sU (I.comap jm).subschemeι k).1 y =
      (cycleAssociatedToClosedSubscheme C sX I.subschemeι k).1 (jm y) :=
  closedSubschemeCycleCoeff_comap_of_isOpenImmersion C sX sU jm hjm I k y

/-! ### Base change of an open immersion of schemes over a fixed base -/

/-- The morphism induced on base changes by an open immersion `j : U ⟶ X` of schemes over `S`:
the base change of `j` along a morphism `g : T ⟶ S`. -/
def pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    (h : j ≫ f = fU) (g : T ⟶ S) : (pullback fU g : Scheme.{u}) ⟶ pullback f g :=
  pullback.map fU g f g j (𝟙 _) (𝟙 _) (by simpa using h.symm) (by simp)

/-- The base change of an open immersion is compatible with the projections to the two
sources. -/
@[reassoc]
theorem pullbackRestrict_fst {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    (h : j ≫ f = fU) (g : T ⟶ S) :
    pullbackRestrict f fU j h g ≫ pullback.fst f g = pullback.fst fU g ≫ j := by
  dsimp only [pullbackRestrict, pullback.map]
  rw [pullback.lift_fst]

/-- The base change of an open immersion is a morphism over the new base. -/
@[reassoc]
theorem pullbackRestrict_snd {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    (h : j ≫ f = fU) (g : T ⟶ S) :
    pullbackRestrict f fU j h g ≫ pullback.snd f g = pullback.snd fU g := by
  dsimp only [pullbackRestrict, pullback.map]
  rw [pullback.lift_snd, Category.comp_id]

/-- The base change of an open immersion is an open immersion. -/
instance isOpenImmersion_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU) (g : T ⟶ S) :
    IsOpenImmersion (pullbackRestrict f fU j h g) := by
  change IsOpenImmersion (pullback.map fU g f g j (𝟙 _) (𝟙 _) (by simpa using h.symm) (by simp))
  infer_instance

/-! ### Restriction of fibrewise cycles along an open immersion of the source -/

/-- The morphism of scheme-theoretic fibres over a point `s` of the base induced by an open
immersion `j : U ⟶ X` of schemes over that base: the base change of `j` along the morphism from
the spectrum of the residue field at `s`. -/
@[ega "III 6.9.10", ega "IV 17.8.2"]
def fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    (h : j ≫ f = fU) (s : S) : fU.fiber s ⟶ f.fiber s :=
  pullbackRestrict f fU j h (S.fromSpecResidueField s)

/-- The fibre morphism induced by an open immersion is compatible with the inclusions of the
fibres into the total spaces. -/
@[reassoc]
theorem fiberRestrict_fiberι {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    (h : j ≫ f = fU) (s : S) :
    fiberRestrict f fU j h s ≫ f.fiberι s = fU.fiberι s ≫ j :=
  pullbackRestrict_fst f fU j h (S.fromSpecResidueField s)

/-- The fibre morphism induced by an open immersion lies over the residue field of the base
point. -/
@[reassoc]
theorem fiberRestrict_fiberToSpecResidueField {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) (h : j ≫ f = fU) (s : S) :
    fiberRestrict f fU j h s ≫ f.fiberToSpecResidueField s = fU.fiberToSpecResidueField s :=
  pullbackRestrict_snd f fU j h (S.fromSpecResidueField s)

/-- The fibre morphism induced by an open immersion is an open immersion. -/
instance isOpenImmersion_fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (s : S) :
    IsOpenImmersion (fiberRestrict f fU j h s) :=
  isOpenImmersion_pullbackRestrict f fU j h (S.fromSpecResidueField s)

/-- Equal composites of morphisms of schemes agree on points. -/
private theorem comp_apply_eq_of_comp_eq {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ W}
    {c : X ⟶ Z} {d : Z ⟶ W} (e : a ≫ b = c ≫ d) (x : X) : b (a x) = d (c x) := by
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : X ⟶ W => m x) e

/-- On points, the fibre morphism induced by an open immersion is determined by the inclusions of
the fibres: a point of the fibre of `X/S` over `s` whose image in `X` lies in `U` is the image of
a point of the fibre of `U/S` over `s`. -/
theorem exists_fiberRestrict_eq {X S U : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S) (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (u : U) :
    ∀ (s : S), fU u = s → ∀ ξ : f.fiber s, f.fiberι s ξ = j u →
      ∃ υ : fU.fiber s, fiberRestrict f fU j h s υ = ξ := by
  intro s hs ξ hξ
  subst hs
  refine ⟨fU.asFiber u, (f.fiberι (fU u)).isEmbedding.injective ?_⟩
  rw [comp_apply_eq_of_comp_eq (fiberRestrict_fiberι f fU j h (fU u)),
    Scheme.Hom.fiberι_asFiber, hξ]

/-- Restriction of fibrewise `r`-cycles along an open immersion of the source over a fixed base:
the coefficient at a point of `U_s` is the coefficient at its image in `X_s`. -/
def fiberCycleRestrict {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ S)
    [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU) (s : S) (r : ℕ) :
    FiberCycleGroup f s r →+ FiberCycleGroup fU s r :=
  let : IsOpenImmersion (fiberRestrict f fU j h s) := isOpenImmersion_fiberRestrict f fU j h s
  cycleGroupRestrict (fieldChowSituation (S.residueField s)) (f.fiberToSpecResidueField s)
    (fU.fiberToSpecResidueField s) (fiberRestrict f fU j h s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) (r : ℤ)

/-- The coefficient of a restricted fibrewise cycle. -/
@[simp]
theorem fiberCycleRestrict_apply {X S U : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU)
    (s : S) (r : ℕ) (c : FiberCycleGroup f s r) (y : fU.fiber s) :
    (fiberCycleRestrict f fU j h s r c : AlgebraicCycle (fU.fiber s) ℤ) y =
      (c : AlgebraicCycle (f.fiber s) ℤ) (fiberRestrict f fU j h s y) :=
  rfl

/-! ### Reindexing a locally finite sum along an injection -/

/-- A locally finite sum over the source of an injection is the sum over the target, provided
the summand vanishes off the image. -/
private theorem finsum_comp_of_eq_zero_of_notMem_range {A B : Type u} (i : A → B) (g : B → ℤ)
    (hi : Function.Injective i) (hz : ∀ b, (¬ ∃ a, i a = b) → g b = 0) :
    ∑ᶠ a, g (i a) = ∑ᶠ b, g b := by
  rw [← finsum_mem_range hi, ← finsum_mem_univ g]
  refine finsum_mem_inter_support_eq g _ _ ?_
  ext b
  refine ⟨fun hmem => ⟨trivial, hmem.2⟩, fun hmem => ⟨?_, hmem.2⟩⟩
  by_contra hk
  exact hmem.2 (hz b (by simpa [Set.mem_range] using hk))

/-! ### The schematic closure of an integral subscheme of the generic fibre -/

/-- The scheme-theoretic image of the integral closed subscheme of the generic fibre with generic
point `ξ` is the integral closed subscheme of `X` whose generic point is the image of `ξ`. -/
theorem specializationClosure_eq_integralComponentAt {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    specializationClosure f ξ =
      integralComponentAt (f.fiberι (genericPoint (Spec (.of R))) ξ) := by
  rw [specializationClosure, integralComponentAt, integralComponentAt,
    Scheme.IdealSheafData.map_vanishingIdeal]
  refine congrArg Scheme.IdealSheafData.vanishingIdeal (Closeds.ext ?_)
  rw [Closeds.coe_closure, Closeds.coe_closure, Closeds.coe_closure, ← Set.image_singleton]
  exact closure_image_closure (f.fiberι (genericPoint (Spec (.of R)))).continuous

/-! ### Specialization commutes with restriction to an open subscheme -/

/-- The closed subscheme of the special fibre of `U` entering the specialization map is the
inverse image, along the open immersion of special fibres, of the corresponding closed subscheme
of the special fibre of `X`. -/
theorem specializationSpecialFibre_comap_fiberRestrict {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X U : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (fU : U ⟶ Spec (.of R)) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (υ : fU.fiber (genericPoint (Spec (.of R)))) :
    specializationSpecialFibre fU υ =
      (specializationSpecialFibre f
          (fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ)).comap
        (fiberRestrict f fU j h (IsLocalRing.closedPoint R)) := by
  have hpoint : f.fiberι (genericPoint (Spec (.of R)))
      (fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ) =
      j (fU.fiberι (genericPoint (Spec (.of R))) υ) := by
    exact comp_apply_eq_of_comp_eq (fiberRestrict_fiberι f fU j h _) υ
  have hcomp : fiberRestrict f fU j h (IsLocalRing.closedPoint R) ≫
      f.fiberι (IsLocalRing.closedPoint R) =
      fU.fiberι (IsLocalRing.closedPoint R) ≫ j :=
    fiberRestrict_fiberι f fU j h (IsLocalRing.closedPoint R)
  rw [specializationSpecialFibre, specializationSpecialFibre,
    specializationClosure_eq_integralComponentAt, specializationClosure_eq_integralComponentAt,
    ← Scheme.IdealSheafData.comap_comp, hcomp, hpoint,
    Scheme.IdealSheafData.comap_comp, comap_integralComponentAt_of_isOpenImmersion]

/-- The `r`-cycle of a closed subscheme of a fibre of `X/S` restricts, along the open immersion
of fibres induced by an open immersion of the source, to the `r`-cycle of the inverse image of
that closed subscheme. -/
theorem fiberSubschemeCycle_comap_fiberRestrict {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (s : S) (r : ℕ)
    (W : (f.fiber s).IdealSheafData) (x : fU.fiber s) :
    (fiberSubschemeCycle fU s r (W.comap (fiberRestrict f fU j h s))).1 x =
      (fiberSubschemeCycle f s r W).1 (fiberRestrict f fU j h s x) :=
  cycleAssociatedToClosedSubscheme_comap_of_isOpenImmersion
    (fieldChowSituation (S.residueField s)) (f.fiberToSpecResidueField s)
    (fU.fiberToSpecResidueField s) (fiberRestrict f fU j h s)
    (fiberRestrict_fiberToSpecResidueField f fU j h s) W (r : ℤ) x

/-- The coefficient of the specialized fundamental cycle of an integral closed subscheme of the
generic fibre of `U`, at a point of the special fibre of `U`, is the corresponding coefficient
for `X`. -/
theorem specializationIntegralCycle_fiberRestrict {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X U : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (fU : U ⟶ Spec (.of R)) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (υ : fU.fiber (genericPoint (Spec (.of R))))
    (x : fU.fiber (IsLocalRing.closedPoint R)) :
    (specializationIntegralCycle fU r υ).1 x =
      (specializationIntegralCycle f r
          (fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ)).1
        (fiberRestrict f fU j h (IsLocalRing.closedPoint R) x) := by
  have hI := specializationSpecialFibre_comap_fiberRestrict f fU j h υ
  have key := fiberSubschemeCycle_comap_fiberRestrict f fU j h (IsLocalRing.closedPoint R) r
    (specializationSpecialFibre f (fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ)) x
  rwa [← hI] at key

/-- The specialization map commutes with restriction to an open subscheme of the source: for
`j : U ⟶ X` an open immersion of schemes locally of finite type over a discrete valuation ring
`R`, restricting an `r`-cycle on the generic fibre of `X` to the generic fibre of `U` and then
specializing is the same as specializing and then restricting to the special fibre of `U`. -/
@[stacks 0H4L "open immersions"]
theorem specializationCycle_fiberCycleRestrict {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X U : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (fU : U ⟶ Spec (.of R)) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ)
    (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r) :
    specializationCycle fU r
        (fiberCycleRestrict f fU j h (genericPoint (Spec (.of R))) r c) =
      fiberCycleRestrict f fU j h (IsLocalRing.closedPoint R) r (specializationCycle f r c) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hR : (fiberCycleRestrict f fU j h (IsLocalRing.closedPoint R) r
        (specializationCycle f r c)).1 x =
      ∑ᶠ ξ, c.1 ξ * (specializationIntegralCycle f r ξ).1
        (fiberRestrict f fU j h (IsLocalRing.closedPoint R) x) :=
    specializationCycle_apply f r c _
  have hterm : ∀ υ : fU.fiber (genericPoint (Spec (.of R))),
      (fiberCycleRestrict f fU j h (genericPoint (Spec (.of R))) r c).1 υ *
          (specializationIntegralCycle fU r υ).1 x =
        c.1 (fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ) *
          (specializationIntegralCycle f r
              (fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ)).1
            (fiberRestrict f fU j h (IsLocalRing.closedPoint R) x) := by
    intro υ
    rw [fiberCycleRestrict_apply, specializationIntegralCycle_fiberRestrict f fU j h r υ x]
  have hzero : ∀ ξ : f.fiber (genericPoint (Spec (.of R))),
      (¬ ∃ υ, fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ = ξ) →
        c.1 ξ * (specializationIntegralCycle f r ξ).1
          (fiberRestrict f fU j h (IsLocalRing.closedPoint R) x) = 0 := by
    intro ξ hξ
    by_contra hne
    have hjx : f.fiberι (IsLocalRing.closedPoint R)
        (fiberRestrict f fU j h (IsLocalRing.closedPoint R) x) =
        j (fU.fiberι (IsLocalRing.closedPoint R) x) := by
      exact comp_apply_eq_of_comp_eq (fiberRestrict_fiberι f fU j h _) x
    have hspec : f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
        f.fiberι (IsLocalRing.closedPoint R)
          (fiberRestrict f fU j h (IsLocalRing.closedPoint R) x) := by
      by_contra hns
      exact (mul_ne_zero_iff.mp hne).2
        (specializationIntegralCycle_apply_eq_zero_of_not_specializes f r ξ _ hns)
    obtain ⟨v, hv1, hv2⟩ := mem_closure_iff.mp (specializes_iff_mem_closure.mp hspec)
      (Set.range j.base) j.isOpenEmbedding.isOpen_range
      ⟨fU.fiberι (IsLocalRing.closedPoint R) x, hjx.symm⟩
    obtain ⟨u, hu⟩ : f.fiberι (genericPoint (Spec (.of R))) ξ ∈ Set.range j.base := by
      rwa [← Set.mem_singleton_iff.mp hv2]
    have hsu : fU u = genericPoint (Spec (.of R)) := by
      have hjf := congrArg (fun m : U ⟶ Spec (.of R) => m u) h
      change f (j u) = fU u at hjf
      rw [← hjf, hu]
      have hmem : f.fiberι (genericPoint (Spec (.of R))) ξ ∈
          f.base ⁻¹' {genericPoint (Spec (.of R))} := by
        rw [← f.range_fiberι]
        exact ⟨ξ, rfl⟩
      exact Set.mem_singleton_iff.mp hmem
    exact hξ (exists_fiberRestrict_eq f fU j h u _ hsu ξ hu.symm)
  rw [hR, specializationCycle_apply, finsum_congr hterm]
  exact finsum_comp_of_eq_zero_of_notMem_range
    (fun υ => fiberRestrict f fU j h (genericPoint (Spec (.of R))) υ)
    (fun ξ => c.1 ξ * (specializationIntegralCycle f r ξ).1
      (fiberRestrict f fU j h (IsLocalRing.closedPoint R) x))
    (fiberRestrict f fU j h (genericPoint (Spec (.of R)))).isOpenEmbedding.injective hzero

/-! ### Base change of cycles and restriction to an open subscheme of the source -/

/-- The canonical morphisms of fibres commute with the open immersions induced by an open
immersion of the source: the fibre of `U ×_S T` over `t` maps to the fibre of `U` over the image
of `t` in the same way whether one first restricts the base change or first takes fibres. -/
theorem restrictedFiberMap_fiberRestrict {X S U T : Scheme.{u}} (f : X ⟶ S) (fU : U ⟶ S)
    (j : U ⟶ X) (h : j ≫ f = fU) (g : T ⟶ S) (t : T) :
    fiberRestrict (pullback.snd f g) (pullback.snd fU g) (pullbackRestrict f fU j h g)
          (pullbackRestrict_snd f fU j h g) t ≫
        restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t =
      restrictedFiberMap fU (pullback.snd fU g) (pullback.fst fU g) g pullback.condition t ≫
        fiberRestrict f fU j h (g t) := by
  refine pullback.hom_ext (?_ : _ ≫ f.fiberι (g t) = _ ≫ f.fiberι (g t))
    (?_ : _ ≫ f.fiberToSpecResidueField (g t) = _ ≫ f.fiberToSpecResidueField (g t))
  · simp only [Category.assoc, restrictedFiberMap_fiberι, fiberRestrict_fiberι,
      fiberRestrict_fiberι_assoc, pullbackRestrict_fst]
    rw [← Category.assoc, ← Category.assoc, restrictedFiberMap_fiberι]
  · simp only [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField,
      fiberRestrict_fiberToSpecResidueField, fiberRestrict_fiberToSpecResidueField_assoc]

/-- The canonical identification of the fibre of a base change with the residue field base change
of a fibre is compatible with restriction to an open subscheme of the source. -/
theorem fibreBaseChangeIso_hom_pullbackRestrict {X S U T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X) (h : j ≫ f = fU)
    (g : T ⟶ S) (t : T) :
    fiberRestrict (pullback.snd f g) (pullback.snd fU g) (pullbackRestrict f fU j h g)
          (pullbackRestrict_snd f fU j h g) t ≫ (fibreBaseChangeIso f g t).hom =
      (fibreBaseChangeIso fU g t).hom ≫
        pullbackRestrict (f.fiberToSpecResidueField (g t)) (fU.fiberToSpecResidueField (g t))
          (fiberRestrict f fU j h (g t)) (fiberRestrict_fiberToSpecResidueField f fU j h (g t))
          (residueFieldBaseChangeSituation g t).g := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, fibreBaseChangeIso_hom_fst, Category.assoc, pullbackRestrict_fst,
      ← Category.assoc, fibreBaseChangeIso_hom_fst]
    exact restrictedFiberMap_fiberRestrict f fU j h g t
  · rw [Category.assoc, fibreBaseChangeIso_hom_snd, Category.assoc, pullbackRestrict_snd,
      fibreBaseChangeIso_hom_snd]
    exact fiberRestrict_fiberToSpecResidueField (pullback.snd f g) (pullback.snd fU g)
      (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) t

/-- The multiplicity entering the base change of a cycle is unchanged by restriction to an open
subscheme of the source. -/
theorem flatPullbackWeight_pullbackRestrict (B : FlatBaseChangeSituation.{u}) {X U : Scheme.{u}}
    (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX] (sU : U ⟶ B.base.S) [LocallyOfFiniteType sU]
    (w : U ⟶ X) [IsOpenImmersion w] (hw : w ≫ sX = sU) (k : ℤ)
    (y : (pullback sU B.g : Scheme.{u})) :
    flatPullbackWeight B.baseChange (pullback.snd sU B.g) (pullback.fst sU B.g) k y =
      flatPullbackWeight B.baseChange (pullback.snd sX B.g) (pullback.fst sX B.g) k
        (pullbackRestrict sX sU w hw B.g y) := by
  have hpt : pullback.fst sX B.g (pullbackRestrict sX sU w hw B.g y) =
      w (pullback.fst sU B.g y) :=
    comp_apply_eq_of_comp_eq (pullbackRestrict_fst sX sU w hw B.g) y
  have hideal : ((integralComponentAt (pullback.fst sX B.g
          (pullbackRestrict sX sU w hw B.g y))).comap (pullback.fst sX B.g)).comap
        (pullbackRestrict sX sU w hw B.g) =
      (integralComponentAt (pullback.fst sU B.g y)).comap (pullback.fst sU B.g) := by
    rw [← Scheme.IdealSheafData.comap_comp, pullbackRestrict_fst, hpt,
      Scheme.IdealSheafData.comap_comp, comap_integralComponentAt_of_isOpenImmersion]
  have key := closedSubschemeCycleCoeff_comap_of_isOpenImmersion B.baseChange
    (pullback.snd sX B.g) (pullback.snd sU B.g) (pullbackRestrict sX sU w hw B.g)
    (pullbackRestrict_snd sX sU w hw B.g)
    ((integralComponentAt (pullback.fst sX B.g
      (pullbackRestrict sX sU w hw B.g y))).comap (pullback.fst sX B.g)) k y
  rwa [hideal] at key

/-- Base change of a cycle along a flat change of the base scheme commutes with restriction to an
open subscheme of the source. -/
theorem baseChangeCycleCoeff_pullbackRestrict (B : FlatBaseChangeSituation.{u})
    {X U : Scheme.{u}} (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX] (sU : U ⟶ B.base.S)
    [LocallyOfFiniteType sU] (w : U ⟶ X) [IsOpenImmersion w] (hw : w ≫ sX = sU) (k : ℤ)
    (z : CycleGroup B.base sX k) (y : (pullback sU B.g : Scheme.{u})) :
    baseChangeCycleCoeff B sU k (cycleGroupRestrict B.base sX sU w hw k z) y =
      baseChangeCycleCoeff B sX k z (pullbackRestrict sX sU w hw B.g y) := by
  have hpt : pullback.fst sX B.g (pullbackRestrict sX sU w hw B.g y) =
      w (pullback.fst sU B.g y) :=
    comp_apply_eq_of_comp_eq (pullbackRestrict_fst sX sU w hw B.g) y
  show (cycleGroupRestrict B.base sX sU w hw k z).1 (pullback.fst sU B.g y) *
      flatPullbackWeight B.baseChange (pullback.snd sU B.g) (pullback.fst sU B.g) (k + B.c) y =
    z.1 (pullback.fst sX B.g (pullbackRestrict sX sU w hw B.g y)) *
      flatPullbackWeight B.baseChange (pullback.snd sX B.g) (pullback.fst sX B.g) (k + B.c)
        (pullbackRestrict sX sU w hw B.g y)
  rw [cycleGroupRestrict_apply, hpt,
    flatPullbackWeight_pullbackRestrict B sX sU w hw (k + B.c) y]

/-- Base change of a family of cycles on fibres commutes with restriction to an open subscheme of
the source. -/
theorem baseChangeFamily_fiberCycleRestrict {X S U T : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ S) [LocallyOfFiniteType fU] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ f = fU) (g : T ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : T) :
    baseChangeFamily fU g r (fun s => fiberCycleRestrict f fU j h s r (α s)) t =
      fiberCycleRestrict (pullback.snd f g) (pullback.snd fU g) (pullbackRestrict f fU j h g)
        (pullbackRestrict_snd f fU j h g) t r (baseChangeFamily f g r α t) := by
  rw [baseChangeFamily_eq_baseChangeFiberCycle, baseChangeFamily_eq_baseChangeFiberCycle]
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  have hpt : pullbackRestrict (f.fiberToSpecResidueField (g t))
        (fU.fiberToSpecResidueField (g t)) (fiberRestrict f fU j h (g t))
        (fiberRestrict_fiberToSpecResidueField f fU j h (g t))
        (residueFieldBaseChangeSituation g t).g ((fibreBaseChangeIso fU g t).hom z) =
      (fibreBaseChangeIso f g t).hom
        (fiberRestrict (pullback.snd f g) (pullback.snd fU g) (pullbackRestrict f fU j h g)
          (pullbackRestrict_snd f fU j h g) t z) := by
    exact (comp_apply_eq_of_comp_eq (fibreBaseChangeIso_hom_pullbackRestrict f fU j h g t) z).symm
  have key := baseChangeCycleCoeff_pullbackRestrict (residueFieldBaseChangeSituation g t)
    (f.fiberToSpecResidueField (g t)) (fU.fiberToSpecResidueField (g t))
    (fiberRestrict f fU j h (g t)) (fiberRestrict_fiberToSpecResidueField f fU j h (g t))
    (r : ℤ) (α (g t)) ((fibreBaseChangeIso fU g t).hom z)
  rwa [hpt] at key

/-- The restriction of a relative `r`-cycle on `X/S` to an open subscheme `U ⊆ X`, taken over the
same base, is a relative `r`-cycle on `U/S`. -/
@[stacks 0H51 "restriction along an open immersion of the source"]
theorem isRelativeCycle_fiberCycleRestrict {X S U : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (fU : U ⟶ S) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (h : j ≫ f = fU) (r : ℕ) {α : FamilyOfCycles f r}
    (hα : IsRelativeCycle f r α) :
    IsRelativeCycle fU r (fun s => fiberCycleRestrict f fU j h s r (α s)) := by
  intro R _ _ _ g
  rw [baseChangeFamily_fiberCycleRestrict f fU j h g r α (genericPoint (Spec (.of R))),
    baseChangeFamily_fiberCycleRestrict f fU j h g r α (IsLocalRing.closedPoint R),
    specializationCycle_fiberCycleRestrict (pullback.snd f g) (pullback.snd fU g)
      (pullbackRestrict f fU j h g) (pullbackRestrict_snd f fU j h g) r
      (baseChangeFamily f g r α (genericPoint (Spec (.of R)))),
    hα R g]

/-! ### The schematic closure is flat over the base -/

/-- The local rings of the spectrum of a discrete valuation ring are Bézout domains. -/
theorem isBezout_stalk_spec_of_isDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (y : Spec (.of R)) :
    IsBezout ((Spec (.of R)).presheaf.stalk y) := by
  have hp : y.asIdeal.IsPrime := y.isPrime
  have hval : ValuationRing (Localization.AtPrime y.asIdeal) :=
    (isBezout_localization_and_valuationRing_atPrime_and_iff
      (R := R) (Rₘ := Localization.AtPrime y.asIdeal)
      (A := Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl y.asIdeal).2.1
  exact isBezout_of_ringEquiv
    (AlgebraicGeometry.Spec.stalkIso (.of R) y).commRingCatIsoToRingEquiv.symm

/-- The scheme-theoretic image in `X` of the integral closed subscheme of the generic fibre with
generic point `ξ` is flat over `Spec R`. -/
@[ega "IV 2.8.5" "partial", sga "7 I 4.1" "special case"]
theorem flat_subschemeι_specializationClosure_comp {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    Flat ((specializationClosure f ξ).subschemeι ≫ f) := by
  rw [specializationClosure_eq_integralComponentAt]
  set x₀ := f.fiberι (genericPoint (Spec (.of R))) ξ with hx₀
  have hbase : f.base x₀ = genericPoint (Spec (.of R)) :=
    (f.fiberHomeo (genericPoint (Spec (.of R))) ξ).property
  have _ : IsIntegral (integralComponentAt x₀).subscheme := isIntegral_integralComponentAt x₀
  have hdom : IsDominant ((integralComponentAt x₀).subschemeι ≫ f) := by
    rw [isDominant_iff, denseRange_iff_closure_range]
    have hrange : Set.range ((integralComponentAt x₀).subschemeι ≫ f).base =
        f.base '' (closure {x₀}) := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    rw [hrange]
    refine Set.eq_univ_of_univ_subset ?_
    have h1 : closure {genericPoint (Spec (.of R))} = Set.univ :=
      (genericPoint_spec (Spec (.of R))).def
    rw [← h1, ← hbase]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨x₀, subset_closure rfl, rfl⟩)
  exact flat_of_isDominant_of_isBezout_stalk _ (isBezout_stalk_spec_of_isDiscreteValuationRing R)

end Stacks.Chow

end
