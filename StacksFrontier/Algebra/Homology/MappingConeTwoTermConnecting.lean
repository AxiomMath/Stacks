module

public import StacksFrontier.Algebra.Homology.MappingConeTwoTermHomology

/-!
# The connecting morphism of the cone of a map of two-term complexes, as a zig-zag

Let `g : L ⟶ M` be a morphism of cochain complexes in an abelian category with `L` zero in
degree `1`, `M` zero in degree `-2` and `g` invertible in degree `0`, and let
`c : P ⟶ C(g)[-1]` be a morphism out of a complex `P` vanishing in degree `1` which is an
isomorphism on degree `0` cohomology.  The composite

`∂ : H^{-1}(M) --connecting--> H⁰(C(g)[-1]) --H⁰(c)⁻¹--> H⁰(P)`

is the shape of the connecting morphism of the six-term exact sequence of
[Stacks Project, Tag 0E1Y]: there `L = NL_{C/A}`, `M = NL_{C/B}`, `P = NL_{B/A} ⊗_B C` and `c`
is the canonical map of that tag, whose invertibility on `H⁰` is
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`.

This file computes `∂` **elementwise**, by a zig-zag: a cycle `ξ` of `M` in degree `-1` whose
inclusion into `M^{-1}` can be written as

`ω ≫ (the degree 0 component of c against the second projection of the cone) + ζ ≫ g^{-1}`

has `∂ ξ = ω` read in `H⁰(P)`.  For the canonical map of [Stacks Project, Tag 0E1Y] the first
morphism is the degree `-1` component of the null homotopy of [Stacks Project, Tag 07VC]
(`CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone`), so the statement
reads: *if `ξ = h(ω)` modulo the image of `g` in degree `-1`, then `∂ ξ = [ω]`* — which is
the usual recipe for a connecting morphism, with no sign.

That is the handle any comparison of `∂` with a differently constructed morphism has to go
through: a distinguished triangle pins its maps only up to automorphisms of their sources and
targets, so `∂` has to be computed, and this is the computation with the cone, the shift and the
inverse of `H⁰(c)` all discharged.

## Main results

* `mappingCone.homologyπ_comp_coneHomologyConnecting_comp_shiftedHomologyZeroIsoCokernel`:
  **the connecting morphism of the cone, read through the identification
  `H⁰(C(g)[-1]) ≅ coker (g^{-1})`, is the inclusion of the cycles followed by the projection onto
  the cokernel.**  No cone and no shift are left in the statement.
* `CochainComplex.mappingCone.homologyπ_comp_connecting_comp_cokernelDesc`: the same with
  `H⁰(c)⁻¹` folded in, so that the target is read as `coker (d_P^{-1})`.
* `CochainComplex.mappingCone.cycle_comp_connecting`: **the zig-zag computation of `∂`.**
* `CochainComplex.mappingCone.cycle_connecting_apply`: the same elementwise, under an arbitrary
  zero-preserving functor to abelian groups — which is the form a germwise or sectionwise
  zig-zag can be fed into, the zig-zag of [Stacks Project, Tag 0E1Y] not being natural.

## Implementation notes

The connecting morphism is `CochainComplex.coneHomologyConnecting`, which is the map induced by
`CochainComplex.mappingCone.inr` read through the identification of the shift — in particular it
carries no sign, and neither does the identification
`CochainComplex.mappingCone.shiftedHomologyZeroIsoCokernel` of `H⁰(C(g)[-1])` with
`coker (g^{-1})`, which is given by the second projection of the cone.  So the whole of the
sign bookkeeping of the long exact sequence of the cone has already been discharged in
`StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit` and
`StacksFrontier.Algebra.Homology.MappingConeTwoTermHomology`, and the equations below hold on the
nose.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the six-term sequence
  and its connecting morphism.
* [Stacks Project, Tag 08RI](https://stacks.math.columbia.edu/tag/08RI), part (2), the
  factorisation through the shifted cone.
* [Stacks Project, Tag 07VC](https://stacks.math.columbia.edu/tag/07VC), the explicit null
  homotopy of a tower of rings, which is the morphism the zig-zag is written against.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open CategoryTheory.Preadditive

universe w v u

noncomputable section

namespace CochainComplex.mappingCone

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {L M : CochainComplex 𝒜 ℤ} (g : L ⟶ M)

section TwoTerm

variable [IsIso (g.f 0)]

/-- Degree `-1` is the shift by `-1` of degree `0`. -/
theorem rel_shift : (-1 : ℤ) + 0 = -1 := by omega

/-- The cycles of `M` in degree `-1`, included into `M^{-1}` and then into the cone, are a cycle
of the cone in degree `-1`. -/
theorem iCycles_comp_inr_comp_d :
    (M.iCycles (-1) ≫ (inr g).f (-1)) ≫ (mappingCone g).d (-1) 0 = 0 := by
  rw [Category.assoc, inr_f_d, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

/-- The map induced by the right inclusion of the cone on cycles in degree `-1` is the lift of
the inclusion of the cycles of `M`. -/
theorem cyclesMap_inr :
    HomologicalComplex.cyclesMap (inr g) (-1) =
      (mappingCone g).liftCycles (M.iCycles (-1) ≫ (inr g).f (-1)) 0
        (by rw [CochainComplex.next]; omega) (iCycles_comp_inr_comp_d g) := by
  rw [← cancel_mono ((mappingCone g).iCycles (-1)), HomologicalComplex.cyclesMap_i,
    HomologicalComplex.liftCycles_i]

/-- **The connecting morphism of the cone, read through the identification
`H⁰(C(g)[-1]) ≅ coker (g^{-1})`.**  On the canonical epimorphism `Z^{-1}(M) ⟶ H^{-1}(M)` it is
the inclusion of the cycles followed by the projection onto the cokernel: no cone, no shift and
no connecting morphism are left.

Since `HomologicalComplex.homologyπ` is an epimorphism this determines the connecting morphism
read through the identification. -/
theorem homologyπ_comp_coneHomologyConnecting_comp_shiftedHomologyZeroIsoCokernel
    (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2))) :
    M.homologyπ (-1) ≫ CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
        (shiftedHomologyZeroIsoCokernel g hL hM).hom =
      M.iCycles (-1) ≫ cokernel.π (g.f (-1)) := by
  have h1 : CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
      (shiftedHomologyZeroIsoCokernel g hL hM).hom =
      HomologicalComplex.homologyMap (inr g) (-1) ≫
        (homologyNegOneIsoCokernel g hL hM).hom := by
    rw [CochainComplex.coneHomologyConnecting, shiftedHomologyZeroIsoCokernel, Iso.trans_hom,
      Category.assoc, Iso.inv_hom_id_assoc]
  rw [h1, HomologicalComplex.homologyπ_naturality_assoc, cyclesMap_inr,
    liftCycles_homologyπ_comp_homologyNegOneIsoCokernel g hL hM _
      (iCycles_comp_inr_comp_d g),
    Category.assoc (HomologicalComplex.iCycles M (-1)) ((inr g).f (-1)), inr_f_snd_v,
    Category.comp_id]

variable {P : CochainComplex 𝒜 ℤ}
  (c : P ⟶ (CategoryTheory.shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)).obj (mappingCone g))

/-- The morphism of cokernels `coker (d_P^{-1}) ⟶ coker (g^{-1})` induced by the degree `0`
component of `c` read against the second projection of the cone.  For the canonical map of
[Stacks Project, Tag 0E1Y] it is the map induced by the degree `-1` component of the null
homotopy of [Stacks Project, Tag 07VC]. -/
abbrev cokernelDescShiftedSndZero (hM : IsZero (M.X (-2))) :
    cokernel (P.d (-1) 0) ⟶ cokernel (g.f (-1)) :=
  cokernel.desc (P.d (-1) 0) (shiftedSndZero g c ≫ cokernel.π (g.f (-1)))
    (d_comp_shiftedSndZero_comp_π g c hM)

/-- The morphism of cokernels is the map on `H⁰` induced by `c`, up to the identifications. -/
private theorem cokernelDescShiftedSndZero_eq (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2)))
    (hP : IsZero (P.X 1)) :
    cokernelDescShiftedSndZero g c hM =
      (P.homologyZeroIsoCokernel hP).inv ≫ HomologicalComplex.homologyMap c 0 ≫
        (shiftedHomologyZeroIsoCokernel g hL hM).hom :=
  (homologyMap_zero_eq_cokernelDesc g c hL hM hP).symm

/-- The morphism of cokernels is invertible as soon as `c` is invertible on `H⁰`. -/
theorem isIso_cokernelDescShiftedSndZero (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2)))
    (hP : IsZero (P.X 1)) [IsIso (HomologicalComplex.homologyMap c 0)] :
    IsIso (cokernelDescShiftedSndZero g c hM) := by
  rw [cokernelDescShiftedSndZero_eq g c hL hM hP]
  infer_instance

/-- **The connecting morphism of [Stacks Project, Tag 0E1Y] read against the two cokernels.**
The composite `H^{-1}(M) --∂--> H⁰(C(g)[-1]) --H⁰(c)⁻¹--> H⁰(P) ≅ coker (d_P^{-1})`, followed by
the morphism of cokernels induced by the degree `0` component of `c`, is the inclusion of the
cycles followed by the projection onto `coker (g^{-1})`.

This is
`mappingCone.homologyπ_comp_coneHomologyConnecting_comp_shiftedHomologyZeroIsoCokernel`
with `H⁰(c)` replaced by the morphism of cokernels it is
(`CochainComplex.mappingCone.homologyMap_zero_eq_cokernelDesc`). -/
theorem homologyπ_comp_connecting_comp_cokernelDesc (hL : IsZero (L.X 1))
    (hM : IsZero (M.X (-2))) (hP : IsZero (P.X 1))
    [IsIso (HomologicalComplex.homologyMap c 0)] :
    M.homologyπ (-1) ≫ CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
          inv (HomologicalComplex.homologyMap c 0) ≫ (P.homologyZeroIsoCokernel hP).hom ≫
        cokernelDescShiftedSndZero g c hM =
      M.iCycles (-1) ≫ cokernel.π (g.f (-1)) := by
  have h : inv (HomologicalComplex.homologyMap c 0) ≫ (P.homologyZeroIsoCokernel hP).hom ≫
      cokernelDescShiftedSndZero g c hM = (shiftedHomologyZeroIsoCokernel g hL hM).hom := by
    rw [cokernelDescShiftedSndZero_eq g c hL hM hP, Iso.hom_inv_id_assoc,
      IsIso.inv_hom_id_assoc]
  rw [h, homologyπ_comp_coneHomologyConnecting_comp_shiftedHomologyZeroIsoCokernel g hL hM]

/-- **The zig-zag computation of the connecting morphism of [Stacks Project, Tag 0E1Y].**  Let
`ξ` be a cycle of `M` in degree `-1`, and suppose its inclusion into `M^{-1}` is

`ω ≫ (the degree 0 component of c against the second projection of the cone) + ζ ≫ g^{-1}`.

Then the connecting morphism carries the class of `ξ` to the class of `ω` in `H⁰(P)`.

For the canonical map of the tag the first morphism is the degree `-1` component of the null
homotopy of [Stacks Project, Tag 07VC]
(`CochainComplex.mappingCone.shiftedSndZero_factorThroughShiftedMappingCone`), so the hypothesis
reads `ξ = h ω` modulo the image of `g` in degree `-1`, and the conclusion `∂ ξ = [ω]`.  There
is no sign. -/
theorem cycle_comp_connecting (hL : IsZero (L.X 1)) (hM : IsZero (M.X (-2)))
    (hP : IsZero (P.X 1)) [IsIso (HomologicalComplex.homologyMap c 0)]
    {A : 𝒜} (ξ : A ⟶ M.cycles (-1)) (ω : A ⟶ P.X 0) (ζ : A ⟶ L.X (-1))
    (hrel : ξ ≫ M.iCycles (-1) = ω ≫ shiftedSndZero g c + ζ ≫ g.f (-1)) :
    ξ ≫ M.homologyπ (-1) ≫ CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
        inv (HomologicalComplex.homologyMap c 0) =
      ω ≫ P.toHomologyZero hP := by
  have := isIso_cokernelDescShiftedSndZero g c hL hM hP
  rw [← cancel_mono ((P.homologyZeroIsoCokernel hP).hom ≫ cokernelDescShiftedSndZero g c hM)]
  calc (ξ ≫ M.homologyπ (-1) ≫ CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
          inv (HomologicalComplex.homologyMap c 0)) ≫
        (P.homologyZeroIsoCokernel hP).hom ≫ cokernelDescShiftedSndZero g c hM
      = ξ ≫ (M.homologyπ (-1) ≫ CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
            inv (HomologicalComplex.homologyMap c 0) ≫
              (P.homologyZeroIsoCokernel hP).hom ≫ cokernelDescShiftedSndZero g c hM) := by
        simp only [Category.assoc]
    _ = (ξ ≫ M.iCycles (-1)) ≫ cokernel.π (g.f (-1)) := by
        rw [homologyπ_comp_connecting_comp_cokernelDesc g c hL hM hP, Category.assoc]
    _ = ω ≫ shiftedSndZero g c ≫ cokernel.π (g.f (-1)) := by
        rw [hrel, add_comp, Category.assoc, Category.assoc, cokernel.condition, comp_zero,
          add_zero]
    _ = (ω ≫ P.toHomologyZero hP) ≫
        (P.homologyZeroIsoCokernel hP).hom ≫ cokernelDescShiftedSndZero g c hM := by
        rw [Category.assoc, CochainComplex.toHomologyZero_comp_homologyZeroIsoCokernel_assoc,
          cokernel.π_desc]

/-- **The zig-zag computation of the connecting morphism, elementwise under an additive
functor.**  The hypothesis and the conclusion of
`CochainComplex.mappingCone.cycle_comp_connecting` are equations between morphisms, so using it
requires the zig-zag datum to be natural; but the datum of the proof of
[Stacks Project, Tag 0E1Y] is *not* natural — the element `ω` is obtained by choosing a variable
indexed by the element `ξ`, which is a map of sheaves of sets and not of modules.

This version is therefore stated under an arbitrary zero-preserving functor to abelian groups,
with
`ξ`, `ω` and `ζ` **elements**: taking the functor to be the stalk at a point, or the sections
over an open, makes the zig-zag a germwise, respectively sectionwise, choice. -/
theorem cycle_connecting_apply
    (F : 𝒜 ⥤ AddCommGrpCat.{w}) [F.PreservesZeroMorphisms] (hL : IsZero (L.X 1))
    (hM : IsZero (M.X (-2))) (hP : IsZero (P.X 1))
    [IsIso (HomologicalComplex.homologyMap c 0)]
    (ξ : F.obj (M.cycles (-1))) (ω : F.obj (P.X 0)) (ζ : F.obj (L.X (-1)))
    (hrel : F.map (M.iCycles (-1)) ξ =
      F.map (shiftedSndZero g c) ω + F.map (g.f (-1)) ζ) :
    F.map (M.homologyπ (-1) ≫ CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
        inv (HomologicalComplex.homologyMap c 0)) ξ =
      F.map (P.toHomologyZero hP) ω := by
  have := isIso_cokernelDescShiftedSndZero g c hL hM hP
  have hcomp : ∀ {U V W : 𝒜} (φ : U ⟶ V) (ψ : V ⟶ W) (u : F.obj U),
      F.map (φ ≫ ψ) u = F.map ψ (F.map φ u) := fun φ ψ u => by simp
  have hA : (M.homologyπ (-1) ≫ CochainComplex.coneHomologyConnecting g (-1) 0 rel_shift ≫
        inv (HomologicalComplex.homologyMap c 0)) ≫
          (P.homologyZeroIsoCokernel hP).hom ≫ cokernelDescShiftedSndZero g c hM =
      M.iCycles (-1) ≫ cokernel.π (g.f (-1)) := by
    simpa only [Category.assoc] using homologyπ_comp_connecting_comp_cokernelDesc g c hL hM hP
  have hB : P.toHomologyZero hP ≫
        (P.homologyZeroIsoCokernel hP).hom ≫ cokernelDescShiftedSndZero g c hM =
      shiftedSndZero g c ≫ cokernel.π (g.f (-1)) := by
    rw [← Category.assoc, CochainComplex.toHomologyZero_comp_homologyZeroIsoCokernel,
      cokernel.π_desc]
  have hinj : Function.Injective
      (F.map ((P.homologyZeroIsoCokernel hP).hom ≫ cokernelDescShiftedSndZero g c hM)) := by
    refine Function.LeftInverse.injective
      (g := F.map (inv ((P.homologyZeroIsoCokernel hP).hom ≫
        cokernelDescShiftedSndZero g c hM))) fun u => ?_
    rw [← hcomp, IsIso.hom_inv_id, F.map_id]
    rfl
  have hz : F.map (cokernel.π (g.f (-1))) (F.map (g.f (-1)) ζ) = 0 := by
    rw [← hcomp, cokernel.condition, F.map_zero]
    rfl
  refine hinj ?_
  rw [← hcomp, ← hcomp, hA, hB, hcomp, hcomp, hrel, map_add, hz, add_zero]

end TwoTerm

end CochainComplex.mappingCone

end

end
