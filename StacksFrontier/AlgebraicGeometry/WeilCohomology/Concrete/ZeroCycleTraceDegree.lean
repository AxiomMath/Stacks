module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionDegree
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RationalPointIndivisibility
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionBasePoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The trace of the cycle class of a zero cycle is its degree (Stacks 0FHR)

Assume given data (D0)–(D3) satisfying (A), (B), (C) over the actual category of smooth
projective schemes over `k` (`Stacks.WeilCohomology.WeilData`), and let `X` be a nonempty smooth
projective scheme over `k`, equidimensional of dimension `d`. Stacks 0FHR: the diagram

`CH^d(X) --γ--> H^{2d}(X)(d) --∫_X--> F`, `CH^d(X) = CH_0(X) --deg--> 𝐙`

commutes, `deg` being the degree of zero cycles of Chow Homology, Section 0AZ0, on
`CH^d(X) = CH_0(X)` (`Stacks.WeilCohomology.codimensionDegree`, the degree `Stacks.Chow.chowDegree`
of Stacks 0AZ1 on the part `X_d = X` of `X` of dimension `d`).

Every `β ∈ CH^d(X)` is the image `zeroCycleToCodimension α` of a zero cycle class `α ∈ CH_0(X)` of
the same degree (`Stacks.WeilCohomology.exists_zeroCycleToCodimension_eq`), so it suffices to show
`∫_X γ(α) = deg(α)` for zero cycle classes on `X`.

The proof is the source's. By Stacks 0FH5
(`Stacks.Chow.mem_closure_separablePointClasses_of_isProjectiveMorphism`) `CH_0(X)` is generated
by the classes `[x]` of closed points `x` with residue field separable over `k`, so it suffices to
treat one of them. View `x` as the smooth projective `k`-scheme `Spec κ(x)` of dimension zero
(`Stacks.WeilCohomology.closedPointObj`) with its closed immersion `i : x ⟶ X`. Then
`γ([x]) = γ(i_*[x]) = i_*γ'([x]) = i_*1` (axiom (C)(b) and Stacks 0FHF, in the form of Stacks
0FHG), so `∫_X γ([x]) = ∫_x 1` by the definition of `i_*` on cohomology; by Stacks 0FHQ (4) the
trace `∫_x` is the trace of the finite `F`-algebra `H^0(x)`, so `∫_x 1 = dim_F H^0(x)`, which is
`[κ(x) : k] = deg(x → Spec k)` by Stacks 0FHQ (3)
(`Stacks.WeilCohomology.WeilData.h0Pairing_cycleClass_closedSubschemeClass`,
`Stacks.WeilCohomology.WeilData.traceZero_eq_trace`,
`Stacks.WeilCohomology.WeilData.finrank_H0_of_dimension_zero`). On the other side the degree of
`[x]` is the residue degree `[κ(x) : k]` (`Stacks.Chow.cycleDegree_single`).

## Main results

* `Stacks.WeilCohomology.WeilData.trace_cycleClass_eq_codimensionDegree`: **Stacks 0FHR**,
  `∫_X γ(β) = deg(β)` for `β ∈ CH^d(X)`.
* `Stacks.WeilCohomology.WeilData.trace_cycleClass_zeroCycleToCodimension`: the same for a zero
  cycle class `α ∈ CH_0(X)` read in `CH^d(X)`.
* `Stacks.WeilCohomology.exists_zeroCycleToCodimension_eq`: every class of `CH^d(X)` is a zero
  cycle class of the same degree.
* `Stacks.WeilCohomology.WeilData.trace_cycleClass_closedPoint`: `∫_X γ([x]) = [κ(x) : k]` for a
  closed point `x` with separable residue field.
* `Stacks.WeilCohomology.finrank_globalSections_closedPointObj`:
  `dim_k Γ(Spec κ(x), 𝒪) = [κ(x) : k]`.

## References

* [Stacks Project, Tag 0FHR](https://stacks.math.columbia.edu/tag/0FHR)
* [Stacks Project, Section 0AZ0](https://stacks.math.columbia.edu/tag/0AZ0)
* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 0FHQ](https://stacks.math.columbia.edu/tag/0FHQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

open SmoothProjectiveScheme

/-! ### The degree of a closed point -/

section ClosedPoint

variable {Y : (SmoothProjectiveScheme k).FullSubcategory} {y : Y.obj.left}
  (hy : IsClosed ({y} : Set Y.obj.left))
  (hsep : HasSeparableResidueField k Y.obj.hom y)

/-- `Γ(Spec κ(y), 𝒪) = κ(y)` as `k`-algebras, the `k`-algebra structure on the left coming from
the structure morphism of `Spec κ(y)` over `k`. -/
def globalSectionsClosedPointObjEquiv :
    letI := residueFieldAlgebra y
    globalSections (closedPointObj hy hsep) ≃ₐ[k] Y.obj.left.residueField y :=
  letI := residueFieldAlgebra y
  AlgEquiv.ofRingEquiv
    (f := (Scheme.ΓSpecIso (.of (Y.obj.left.residueField y))).commRingCatIsoToRingEquiv)
    fun c ↦ by
      change ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Y.obj.left.fromSpecResidueField y ≫ Y.obj.hom).appTop ≫
          (Scheme.ΓSpecIso (.of (Y.obj.left.residueField y))).hom).hom c = _
      rw [fromSpecResidueField_comp_hom, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
      rfl

/-- The residue field of `y`, with the `k`-algebra structure through the structure morphism,
has dimension `[κ(y) : k]` over `k`, the residue degree of `y` over `Spec k`. -/
theorem finrank_residueField_eq_residueDegree :
    letI := residueFieldAlgebra y
    Module.finrank k (Y.obj.left.residueField y) = Y.obj.hom.residueDegree y := by
  rw [residueDegree_eq_finrank_residueField k Y.obj.hom y]
  rfl

/-- **`dim_k Γ(Spec κ(y), 𝒪) = [κ(y) : k]`**: the global sections of the closed point `y`, viewed
as the smooth projective `k`-scheme `Spec κ(y)`, have dimension over `k` the residue degree of
`y`. -/
theorem finrank_globalSections_closedPointObj :
    Module.finrank k (globalSections (closedPointObj hy hsep)) = Y.obj.hom.residueDegree y := by
  let := residueFieldAlgebra y
  rw [(globalSectionsClosedPointObjEquiv hy hsep).toLinearEquiv.finrank_eq]
  exact finrank_residueField_eq_residueDegree

/-- **The degree of the class of a closed point is its residue degree**: for `y` closed with
separable residue field, the cycle of `Spec κ(y) ⟶ Y` is the prime cycle `[y]`, of degree
`[κ(y) : k]`. -/
theorem chowDegree_closedPointHom (s : (fieldChowSituation k).S) :
    chowDegree (fieldChowSituation k) (fun _ ↦ rfl) Y.obj.hom s
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Y.obj.hom
          (closedPointHom hy hsep).hom.left 0)) =
      (Y.obj.hom.residueDegree y : ℤ) := by
  have : IsIntegral (closedPointObj hy hsep).obj.left :=
    inferInstanceAs (IsIntegral (Spec (.of (Y.obj.left.residueField y))))
  have hgen : (closedPointHom hy hsep).hom.left (genericPoint (closedPointObj hy hsep).obj.left) =
      y :=
    Scheme.fromSpecResidueField_apply (X := Y.obj.left) y _
  have hsingle := cycleAssociatedToClosedSubscheme_eq_single (fieldChowSituation k) Y.obj.hom
    (closedPointHom hy hsep).hom.left 0 (by
      rw [hgen]
      exact relativeDimension_eq_zero_of_isClosed (fieldChowSituation k) (fun _ _ ↦ rfl) Y.obj.hom
        y hy)
  rw [hgen] at hsingle
  rw [Subsingleton.elim s (Y.obj.hom.base y)]
  exact (chowDegree_mk _ _ _ _ _).trans
    (cycleDegree_single (fieldChowSituation k) (fun _ ↦ rfl) Y.obj.hom y _ hsingle)

end ClosedPoint

/-! ### `CH_0(X) = CH^d(X)` -/

/-- **Every class of `CH^d(X)` is a zero cycle class of the same degree**, for `X` smooth
projective over `k` and equidimensional of dimension `d`: `β ∈ CH^d(X) = ∏_e CH_{e-d}(X_e)` is
`zeroCycleToCodimension α` for `α ∈ CH_0(X)` the pushforward of its component on `X_d`, the
other components living on the empty parts `X_e`, `e ≠ d`, and
`deg(α) = Stacks.WeilCohomology.codimensionDegree X d β`. -/
theorem exists_zeroCycleToCodimension_eq {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : AlgebraicGeometry.RelativeDimension X.obj.hom d) (s : (fieldChowSituation k).S)
    (β : codimensionChowGroup k X.obj.hom d) :
    ∃ α : chowGroup (fieldChowSituation k) X.obj.hom 0,
      zeroCycleToCodimension X.obj.hom d α = β ∧
        chowDegree (fieldChowSituation k) (fun _ ↦ rfl) X.obj.hom s α =
          codimensionDegree X d β := by
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  let β₀ : chowGroup (fieldChowSituation k) (partBase X.obj.hom d) 0 :=
    chowGroupDegreeEquiv _ _ (sub_self (d : ℤ)) (β d)
  refine ⟨properChowPushforward (fieldChowSituation k) (partBase X.obj.hom d) X.obj.hom
    (dimPart X.obj.hom d).ι rfl 0
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ _) β₀, ?_, ?_⟩
  · funext e
    by_cases h : (0 : ℤ) = e - d
    · obtain rfl : e = d := by omega
      simp only [zeroCycleToCodimension, AddMonoidHom.pi_apply, dif_pos h,
        AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
      rw [chowGroupRestrict_properChowPushforward_opens_self]
      exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _))
    · have := isEmpty_dimPart_of_ne X.obj.hom hX (e := e) (by omega)
      exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _
  · rw [codimensionDegree_apply, Subsingleton.elim s (IsLocalRing.closedPoint k),
      Subsingleton.elim (genericPoint (fieldChowSituation k).S) (IsLocalRing.closedPoint k)]
    exact (chowDegree_properChowPushforward k X.obj.hom (partBase X.obj.hom d)
      (dimPart X.obj.hom d).ι rfl β₀).symm

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-- The pairing of `1 ∈ H^0(X)` with `b ∈ H^{2d}(X)(d)` is `∫_X b`. -/
theorem h0Pairing_one (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) (b : W.Tw X (2 * d) d) :
    W.h0Pairing X d hX 1 b = W.trace X d hX b := by
  simp only [h0Pairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply]
  rw [pairingTw_apply, W.cupTw_eq_self_of_coe_twCoord_eq_one X _ _ _ _ _ _ _
    (by rw [twCoord_h0TwEquiv]; rfl)]

variable {W} [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
  (hC : W.CycleClassAxiom hA.perfectPairing)

include hA hB hC

/-- **`∫_X γ([y]) = [κ(y) : k]`** for a closed point `y` of `X` with residue field separable over
`k`, `X` nonempty and equidimensional of dimension `d`: with `i : Spec κ(y) ⟶ X`,
`∫_X γ([y]) = ∫_X 1 ∪ i_*1 = ∫_{κ(y)} 1 = dim_F H^0(κ(y)) = [κ(y) : k]` (Stacks 0FHG, 0FHQ). -/
theorem trace_cycleClass_closedPoint {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) {y : X.obj.left} (hy : IsClosed ({y} : Set X.obj.left))
    (hsep : HasSeparableResidueField k X.obj.hom y) :
    W.trace X d hX (W.cycleClass X d
        (closedSubschemeClass X.obj.hom (closedPointHom hy hsep).hom.left d)) =
      (X.obj.hom.residueDegree y : F) := by
  have hZ := isNonemptyEquidimensional_closedPointObj hy hsep
  have hZ0 := topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional hZ
  have := finiteDimensional_H0_of_dimension_zero hA hB hC hZ0
  have h := W.h0Pairing_cycleClass_closedSubschemeClass hA hB hC (closedPointHom hy hsep) hX hZ
    (fun c ↦ traceZero_eq_trace hA hB hC hZ0 c) 1
  rw [map_one (H0.pullHom W (closedPointHom hy hsep)),
    ← map_one (algebraMap F (W.H0 (closedPointObj hy hsep))),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one, finrank_H0_of_dimension_zero hA hB hC hZ0,
    finrank_globalSections_closedPointObj, h0Pairing_one] at h
  exact h

/-- **`∫_X γ(α) = deg(α)` for a zero cycle class** `α ∈ CH_0(X)`, read in `CH^d(X)` through
`Stacks.WeilCohomology.zeroCycleToCodimension`, `X` nonempty and equidimensional of dimension
`d`. By Stacks 0FH5 it suffices to take `α = [y]` for a closed point `y` with separable residue
field, which is `Stacks.WeilCohomology.WeilData.trace_cycleClass_closedPoint`. -/
theorem trace_cycleClass_zeroCycleToCodimension
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (s : (fieldChowSituation k).S)
    (α : chowGroup (fieldChowSituation k) X.obj.hom 0) :
    W.trace X d hX (W.cycleClass X d (zeroCycleToCodimension X.obj.hom d α)) =
      (chowDegree (fieldChowSituation k) (fun _ ↦ rfl) X.obj.hom s α : F) := by
  let φ : chowGroup (fieldChowSituation k) X.obj.hom 0 →+ F :=
    (W.trace X d hX).toAddMonoidHom.comp
      ((W.cycleClass X d).comp (zeroCycleToCodimension X.obj.hom d))
  let ψ : chowGroup (fieldChowSituation k) X.obj.hom 0 →+ F :=
    (Int.castAddHom F).comp (chowDegree (fieldChowSituation k) (fun _ ↦ rfl) X.obj.hom s)
  have hgen : Set.EqOn φ ψ (separablePointClasses k X.obj.hom) := by
    rintro _ ⟨y, hy, hsep, rfl⟩
    rw [mk_integralComponentAt_eq hy hsep]
    show W.trace X d hX (W.cycleClass X d (zeroCycleToCodimension X.obj.hom d _)) =
      ((chowDegree (fieldChowSituation k) (fun _ ↦ rfl) X.obj.hom s _ : ℤ) : F)
    rw [zeroCycleToCodimension_mk_cycleAssociatedToClosedSubscheme X.obj.hom _
        (relativeDimension_closedPointHom hy hsep) d,
      trace_cycleClass_closedPoint hA hB hC hX hy hsep, chowDegree_closedPointHom hy hsep s,
      Int.cast_natCast]
  have htop : AddSubgroup.closure (separablePointClasses k X.obj.hom) = ⊤ :=
    eq_top_iff.mpr fun α _ ↦ mem_closure_separablePointClasses_of_isProjectiveMorphism k
      X.obj.hom ((AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine _).1
        (SmoothProjectiveScheme.isProjective X)) α
  exact DFunLike.congr_fun (AddMonoidHom.eq_of_eqOn_dense htop hgen) α

/-- **Stacks 0FHR.** Assume given data (D0)–(D3) satisfying (A), (B) and (C), and let `X` be a
nonempty smooth projective scheme over `k`, equidimensional of dimension `d`. Then the diagram
`CH^d(X) --γ--> H^{2d}(X)(d) --∫_X--> F`, `CH^d(X) = CH_0(X) --deg--> 𝐙 → F` commutes:
`∫_X γ(β) = deg(β)` for every `β ∈ CH^d(X)`, where `deg` is the degree of zero cycles of Chow
Homology, Section 0AZ0 (Stacks 0AZ1), on `CH^d(X) = CH_0(X)`
(`Stacks.WeilCohomology.codimensionDegree`). -/
@[stacks 0FHR]
theorem trace_cycleClass_eq_codimensionDegree
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) (β : codimensionChowGroup k X.obj.hom d) :
    W.trace X d hX (W.cycleClass X d β) = (codimensionDegree X d β : F) := by
  obtain ⟨α, rfl, hα⟩ := exists_zeroCycleToCodimension_eq hX.relativeDimension
    (IsLocalRing.closedPoint k) β
  rw [trace_cycleClass_zeroCycleToCodimension hA hB hC hX (IsLocalRing.closedPoint k), hα]

end WeilData

end Stacks.WeilCohomology

end
