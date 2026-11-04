module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.MappingConeDegreewiseIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowFlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatModuleOfTorAmplitude
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# The bottom cocycles of a bounded complex of flat modules are flat

Let `(C, O)` be a ringed site, let `T` be a derived tensor product on `D(O)` and let `P` be a
complex of flat `O`-modules concentrated in degrees `[n, b]`. If the canonical truncation
`τ_{≥ n+1}P` has Tor amplitude in `[n + 1, b]`, then the degree-`(n + 1)` *opcycles* of `P` —
the cokernel `Coker(P^n ⟶ P^{n+1})`, which is the lowest term of `τ_{≥ n+1}P` — are a flat
`O`-module.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_opcycles_of_hasTorAmplitude_truncGE`: the
  statement above.

## Implementation notes

This is the sentence "it follows that `Tor_1(E', F) = 0` where `E' = Coker(E^{a-1} ⟶ E^a)`,
hence `E'` is flat" of the source's proof of Stacks 08G7, with `a = n + 1`. The input is the
companion statement
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cycles_of_hasTorAmplitude_truncGE`, which
makes `K = Z^n(P)` flat.

The flat-cokernel criterion of Stacks 08G0 as it is available here,
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitudeGE`, produces the
flatness of `Coker(d^{a-1})` for a *K-flat complex of flat modules* whose image in `D(O)` has
Tor amplitude in `[a, ∞]`. None of the complexes already at hand satisfies all three conditions
at once: `P` itself has the right terms but the wrong Tor amplitude (its cohomology in degree `n`
does not vanish after tensoring), while `τ_{≥ n+1}P` has the right Tor amplitude and the term
whose flatness is in question, so applying the criterion to it would be circular.

The complex that does work is the mapping cone of `P.ιTruncLE n`. Its terms are `Z^n(P)` in
degree `n - 1`, flat by the companion statement, and `P^m` in every degree `m ≥ n`, by
`CochainComplex.mappingCone.isIso_inl_v` and `CochainComplex.mappingCone.isIso_inr_f` — the two
summands `(τ_{≤ n}P)^{m+1}` and `P^m` of the degree-`m` term of the cone vanish for `m ≠ n - 1`
and `m < n` respectively, because `P` is concentrated in degrees `≥ n`. So the cone is a bounded
complex of flat modules, hence K-flat by Stacks 06YQ, and
`CategoryTheory.DerivedCategory.triangleOfSESIso` identifies it in `D(O)` with the third term of
the cokernel sequence of `P.ιTruncLE n`, that is with `τ_{≥ n+1}P`, which is where the
Tor-amplitude hypothesis is. Finally `mappingCone.inr` is an isomorphism in the two degrees `n`
and `n + 1`, so the two differentials `P^n ⟶ P^{n+1}` and `Cone^n ⟶ Cone^{n+1}` have isomorphic
cokernels.

## References

* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max u v} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
      Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The opcycles in the bottom degree of the canonical truncation of a bounded complex of flat
`O`-modules are flat, as soon as that truncation has Tor amplitude starting there.**

Let `P` be a complex of flat `O`-modules concentrated in degrees `[n, b]` and suppose that
`τ_{≥ n+1}P` has Tor amplitude in `[n + 1, b]`. Then `Coker(P^n ⟶ P^{n+1})` is a flat
`O`-module.

This is the step which makes the lowest term of the complex
`Coker(E^{a-1} ⟶ E^a) ⟶ E^{a+1} ⟶ … ⟶ E^b` of the source's proof of Stacks 08G7 flat, with
`n = a - 1`. -/
theorem isFlat_opcycles_of_hasTorAmplitude_truncGE
    (T : DerivedTensorProduct.{u, v, max u v, d} Y)
    (P : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ) (n b : ℤ)
    [P.IsStrictlyGE n] [P.IsStrictlyLE b]
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) (P.X i))
    (hamp : HasTorAmplitude T (DerivedCategory.Q.obj (P.truncGE (n + 1))) (n + 1) b) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
      (P.opcycles (n + 1)) := by
  have hcyc := isFlat_cycles_of_hasTorAmplitude_truncGE T P n b hflat hamp
  have hSE := P.shortComplexTruncLE_shortExact n
  -- the truncation `τ_{≤ n}P` is concentrated in the single degree `n`
  have hFzero : ∀ i : ℤ, i ≠ n → IsZero ((P.truncLE n).X i) := by
    intro i hi
    rcases lt_or_gt_of_ne hi with h | h
    · exact (P.isZero_of_isStrictlyGE n i h).of_iso (P.truncLEXIso n i h)
    · exact (P.truncLE n).isZero_of_isStrictlyLE n i h
  -- away from degree `n - 1` the cone is the complex `P` itself
  let einr : ∀ m : ℤ, m ≠ n - 1 → (P.X m ≅ (CochainComplex.mappingCone (P.ιTruncLE n)).X m) :=
    fun m hm =>
    haveI := CochainComplex.mappingCone.isIso_inr_f (P.ιTruncLE n) m (hFzero (m + 1) (by omega))
    asIso ((CochainComplex.mappingCone.inr (P.ιTruncLE n)).f m)
  -- the cone has flat terms
  have hpq : n + (-1) = n - 1 := by omega
  have hextflat : ∀ m : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
        ((CochainComplex.mappingCone (P.ιTruncLE n)).X m) := by
    intro m
    by_cases hm : m = n - 1
    · subst hm
      have hiso : IsIso ((CochainComplex.mappingCone.inl (P.ιTruncLE n)).v n (n - 1) hpq) :=
        CochainComplex.mappingCone.isIso_inl_v _ n (n - 1) hpq
          (P.isZero_of_isStrictlyGE n (n - 1) (by omega))
      exact FlatRetract.isFlat_of_iso Y.O
        ((P.truncLEXIsoCycles n).symm ≪≫ @asIso _ _ _ _ _ hiso) hcyc
    · exact FlatRetract.isFlat_of_iso Y.O (einr m hm) (hflat m)
  -- the cone is bounded above, hence K-flat by Stacks 06YQ
  have hextLE : (CochainComplex.mappingCone (P.ιTruncLE n)).IsStrictlyLE (max b n) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro m hm
    rw [max_lt_iff] at hm
    exact (P.isZero_of_isStrictlyLE b m (by omega)).of_iso (einr m (by omega)).symm
  have hKflat : IsKFlat Y.O (CochainComplex.mappingCone (P.ιTruncLE n)) :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat Y.O _ ⟨max b n, hextLE⟩ hextflat
  -- in `D(O)` the cone is the canonical truncation, which carries the Tor-amplitude hypothesis
  have hampGE : HasTorAmplitudeGE T
      (DerivedCategory.Q.obj (CochainComplex.mappingCone (P.ιTruncLE n))) (n + 1) := by
    refine (hasTorAmplitudeGE_of_hasTorAmplitude T _ (n + 1) b hamp).of_iso ?_
    have e₃ : DerivedCategory.Q.obj (P.shortComplexTruncLE n).X₃ ≅
        DerivedCategory.Q.obj (CochainComplex.mappingCone (P.ιTruncLE n)) :=
      Triangle.π₃.mapIso (DerivedCategory.triangleOfSESIso hSE)
    have hφ : IsIso (DerivedCategory.Q.map (P.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso
        (C := RingedSite.Modules.{u, v, max u v} Y) _).2 inferInstance
    exact e₃.symm ≪≫ @asIso _ _ _ _ _ hφ
  have hcoker := isFlat_cokernel_of_hasTorAmplitudeGE T
    (CochainComplex.mappingCone (P.ιTruncLE n)) (n + 1) hKflat hextflat hampGE
  rw [show n + 1 - 1 = n from by omega] at hcoker
  -- the two differentials out of degree `n` have isomorphic cokernels
  have ecoker : cokernel (P.d n (n + 1)) ≅
      cokernel ((CochainComplex.mappingCone (P.ιTruncLE n)).d n (n + 1)) :=
    cokernel.mapIso (f := P.d n (n + 1))
      (f' := (CochainComplex.mappingCone (P.ιTruncLE n)).d n (n + 1))
      (p := einr n (by omega))
      (q := einr (n + 1) (by omega))
      (w := ((CochainComplex.mappingCone.inr (P.ιTruncLE n)).comm n (n + 1)).symm)
  have eop : P.opcycles (n + 1) ≅ cokernel (P.d n (n + 1)) :=
    IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel n (n + 1) (by simp))
      (colimit.isColimit _)
  exact FlatRetract.isFlat_of_iso Y.O (ecoker.symm ≪≫ eop.symm) hcoker

end Stacks.SheafOfModules.DerivedTensorProduct

end
