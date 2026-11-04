module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSection
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 part (1)(b) at an arbitrary closed point of the projective line

Part (1)(b) of Tag 0B07 reads the cycle `[W_a]_k` of part (1)(a) on `X` rather than on
`X ×_S ℙ¹_S`: the fibre `W_a`, viewed as a closed subscheme of `X` through the section, has
cycle the proper pushforward of `W · (X × a)` along the projection `pr : X ×_S ℙ¹_S ⟶ X`. The
repository had this at the two distinguished points `a = 0` and `a = ∞`; this file reads it at
an arbitrary point of the affine chart of `ℙ¹_S`, that is at an arbitrary element of
`Γ(S, ⊤)` — for `S = Spec k` with `k` algebraically closed, at an arbitrary closed point of
`ℙ¹_k` other than `∞`.

## Main definitions

* `Stacks.Chow.pointFiber`: the fibre `W_a` of a closed subscheme `W ⊆ X ×_S ℙ¹_S` at the point
  `a` attached to `t : Γ(S, ⊤)`, its scheme-theoretic preimage along the section, as a closed
  subscheme of `X`. This is how Section 43.8 views `W_a`.
* `Stacks.Chow.pointDivisor`: the closed subscheme of `W` cut out by the image of that section.

## Main results

* `Stacks.Chow.isIso_sectionKer_over`: the image of *any* section of `ℙ¹_S ⟶ S` which is a
  closed immersion is isomorphic to `S` over `S`. This is
  `Stacks.Chow.isIso_lineConstantSection_ker_over` with the integral point replaced by an
  arbitrary section.
* `Stacks.Chow.ker_pointDivisor_subschemeι_comp`: **the divisor of `W` at `a` and the fibre of
  `W` at `a` are the same closed subscheme of `X`.** No reducedness of `W` is needed, because
  the divisor is defined here by the kernel ideal sheaf of the section rather than by the
  reduced structure on its image.
* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_pointSection`: the
  pushforward identity for the cycle of the scheme-theoretic intersection.
* `Stacks.Chow.properPushforward_intersectionProductCycle_eq_pointFiberCycle`: **Tag 0B07 part
  (1)(b) at an arbitrary point**, over an arbitrary Chow situation.
* `Stacks.Chow.properPushforward_intersectionProductCycle_eq_pointFiberCycle_of_isRegular`: the
  same for a nonsingular variety over an algebraically closed field, with nothing assumed about
  the ambient family.

## Implementation notes

The distinguished-section versions are built on `Stacks.Chow.zeroDivisor`, the *reduced*
structure on the image of the section intersected with `W`, and they therefore carry
`IsReduced W.subscheme` through the comparison
`Stacks.Chow.zeroDivisor_eq_comap_ker` of the two structures. Here `Stacks.Chow.pointDivisor` is
the inverse image of the kernel ideal sheaf from the start, so that comparison never arises and
no reducedness hypothesis appears; in the application `W` is integral anyway.

Part (3), the converse, is carried at an arbitrary pair of points of the affine chart by
`Stacks.Chow.PointCycle.isPointFibreIntersectionDifference_of_mem_rationalEquivalences`, but
not at a pair with one point at infinity.
Part (2) at an arbitrary pair is carried in
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSectionRationalEquivalence`:
`Stacks.Chow.fibreDifferences`, the generating set of Tag 0AZG, does have the zero and the
infinity fibre hard-coded, but it never has to be unfolded, because rational equivalence itself
(Tag 02RW) is defined by an *arbitrary* principal divisor, and the difference of the two fibre
cycles at an arbitrary pair is the pushforward of one. Tag 0B2U, the 2-transitivity of the
automorphism group of the projective line, is not invoked here or anywhere in the repository's
Chow chapter.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

/-! ### The image of an arbitrary section of the projective line -/

section GeneralSection

variable {S : Scheme.{u}} (σ : S ⟶ relativeProjectiveLine S) [IsClosedImmersion σ]

/-- **The image of a section of `ℙ¹_S ⟶ S` is isomorphic to `S` over `S`.** A closed immersion
factors through its scheme-theoretic image by an isomorphism, and the section composed with the
structure morphism is the identity. -/
theorem isIso_sectionKer_over (hσ : σ ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S) :
    IsIso (σ.ker.subschemeι ≫ (relativeProjectiveLine S ↘ S)) := by
  have h : IsIso σ.toImage := inferInstance
  have hfac : σ.toImage ≫ (σ.imageι ≫ (relativeProjectiveLine S ↘ S)) = 𝟙 S := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hσ]
  have : IsIso (σ.toImage ≫ (σ.imageι ≫ (relativeProjectiveLine S ↘ S))) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_left σ.toImage _

variable {X : Scheme.{u}} (f : X ⟶ S)

/-- Cutting `X ×_S ℙ¹_S` with the image of a section of `ℙ¹_S ⟶ S` gives a closed subscheme of
`X`: that image is isomorphic to `S`, so the intersection is `X ×_S S = X`. -/
theorem isClosedImmersion_comap_sectionKer_comp_fst
    (hσ : σ ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S) :
    IsClosedImmersion
      ((σ.ker.comap (pullback.snd f (relativeProjectiveLine S ↘ S))).subschemeι ≫
        pullback.fst f (relativeProjectiveLine S ↘ S)) := by
  have hiso := isIso_sectionKer_over σ hσ
  have hci : IsClosedImmersion (σ.ker.subschemeι ≫ (relativeProjectiveLine S ↘ S)) :=
    inferInstance
  have hbase : IsClosedImmersion
      (pullback.fst (pullback.snd f (relativeProjectiveLine S ↘ S)) σ.ker.subschemeι ≫
        pullback.fst f (relativeProjectiveLine S ↘ S)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
      ((IsPullback.of_hasPullback (pullback.snd f (relativeProjectiveLine S ↘ S))
        σ.ker.subschemeι).paste_horiz
        (IsPullback.of_hasPullback f (relativeProjectiveLine S ↘ S))).flip hci
  rw [← Scheme.IdealSheafData.comapIso_hom_fst σ.ker
    (pullback.snd f (relativeProjectiveLine S ↘ S)), Category.assoc]
  infer_instance

/-- Cutting a closed subscheme of `X ×_S ℙ¹_S` with the image of a section of `ℙ¹_S ⟶ S` gives
a closed subscheme of `X`. -/
theorem isClosedImmersion_comap_sectionKer_comp
    (hσ : σ ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S) {Z : Scheme.{u}}
    (i : Z ⟶ projectiveLineProduct f) [IsClosedImmersion i] :
    IsClosedImmersion
      ((σ.ker.comap (i ≫ pullback.snd f (relativeProjectiveLine S ↘ S))).subschemeι ≫
        i ≫ pullback.fst f (relativeProjectiveLine S ↘ S)) := by
  have hA := isClosedImmersion_comap_sectionKer_comp_fst σ f hσ
  rw [Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comapIso_hom_fst
      (σ.ker.comap (pullback.snd f (relativeProjectiveLine S ↘ S))) i,
    Category.assoc, ← Category.assoc (pullback.fst i _) i, pullback.condition, Category.assoc]
  infer_instance

end GeneralSection

/-! ### The fibre of a closed subscheme at an arbitrary point -/

section Fibre

variable {X S : Scheme.{u}} (f : X ⟶ S) (t : Γ(S, ⊤))
  (W : (projectiveLineProduct f).IdealSheafData)

/-- **The fibre `W_a` of a closed subscheme of `X ×_S ℙ¹_S` at the point `a` attached to
`t : Γ(S, ⊤)`**: its scheme-theoretic preimage along the section at `t`, as a closed subscheme
of `X`. This is how Section 43.8 views `W_a`. -/
def pointFiber : X.IdealSheafData := W.comap (pointSection f t)

/-- The closed subscheme of `W` cut out by the image of the section at `t`. -/
def pointDivisor : W.subscheme.IdealSheafData :=
  (pointSection f t).ker.comap W.subschemeι

/-- At `t = 0` the fibre at `t` is the zero fibre, so the statements below specialize to the
existing distinguished-section ones and nothing is lost against them. -/
theorem pointFiber_zero : pointFiber f (0 : Γ(S, ⊤)) W = zeroFiber f W := by
  rw [pointFiber, pointSection_zero, zeroFiber]

/-- The divisor of `W` at `t`, pushed forward into `X ×_S ℙ¹_S`, is the intersection of `W` with
the image of the section at `t`. -/
private theorem map_pointDivisor_subschemeι :
    (pointDivisor f t W).map W.subschemeι = (pointSection f t).ker ⊔ W := by
  rw [pointDivisor, Stacks.IdealSheaf.map_comap_of_isClosedImmersion W.subschemeι
    (pointSection f t).ker, Scheme.IdealSheafData.ker_subschemeι]

/-- The scheme-theoretic intersection of `W` with the image of the section at `t`, presented
through the divisor of `W` at `t`. -/
theorem ker_pointDivisor_subschemeι_comp_subschemeι :
    ((pointDivisor f t W).subschemeι ≫ W.subschemeι).ker = W ⊔ (pointSection f t).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    map_pointDivisor_subschemeι, sup_comm]

/-- The divisor of `W` at `t`, included into `X`, is a closed subscheme of `X`. -/
instance isClosedImmersion_pointDivisor_subschemeι_comp :
    IsClosedImmersion ((pointDivisor f t W).subschemeι ≫ fibreBaseProjection f W) := by
  rw [pointDivisor, ker_pointSection, ← Scheme.IdealSheafData.comap_comp,
    fibreBaseProjection_def]
  exact isClosedImmersion_comap_sectionKer_comp (lineSection S t) f (lineSection_comp S t)
    W.subschemeι

/-- **The divisor of `W` at `t` and the fibre of `W` at `t` are the same closed subscheme of
`X`.** The divisor pushes forward from `W` to `(pointSection f t).ker ⊔ W` by the ideal
correspondence for the closed immersion `W ⟶ X ×_S ℙ¹_S`; that ideal sheaf is in turn the
pushforward along the section of `W.comap (pointSection f t)`, again by the ideal
correspondence; and the section is a section of the first projection, so pushing forward along
the first projection undoes it. -/
theorem ker_pointDivisor_subschemeι_comp :
    ((pointDivisor f t W).subschemeι ≫ fibreBaseProjection f W).ker = pointFiber f t W := by
  have hsplit : (pointSection f t).ker ⊔ W = (pointFiber f t W).map (pointSection f t) := by
    rw [pointFiber, Stacks.IdealSheaf.map_comap_of_isClosedImmersion (pointSection f t) W,
      sup_comm]
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    fibreBaseProjection_def, Scheme.IdealSheafData.map_comp, map_pointDivisor_subschemeι,
    hsplit, ← Scheme.IdealSheafData.map_comp,
    pointSection_comp_fst, Scheme.IdealSheafData.map_id]

end Fibre

/-! ### Pushing the fibre cycle at an arbitrary point down to `X` -/

section Push

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (t : Γ(C.S, ⊤)) (W : (projectiveLineProduct p).IdealSheafData) (k : ℤ)

/-- **Stacks 0B07, the pushforward of part (1)(b), at an arbitrary point.** The cycle on
`X ×_S ℙ¹_S` of the scheme-theoretic intersection of `W` with the image of the section at `t` is
carried by the proper pushforward along the first projection to the cycle of the fibre of `W` at
`t` on `X`. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_pointSection :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        (cycleAssociatedToClosedSubscheme C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          (W ⊔ (pointSection p t).ker).subschemeι k) =
      cycleAssociatedToClosedSubscheme C p (pointFiber p t W).subschemeι k := by
  have hci : IsClosedImmersion
      (((pointDivisor p t W).subschemeι ≫ W.subschemeι) ≫
        pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) := by
    rw [Category.assoc]
    exact isClosedImmersion_pointDivisor_subschemeι_comp p t W
  rw [← ker_pointDivisor_subschemeι_comp_subschemeι p t W,
    ← cycleAssociatedToClosedSubscheme_ker C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      ((pointDivisor p t W).subschemeι ≫ W.subschemeι) k,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl
      ((pointDivisor p t W).subschemeι ≫ W.subschemeι) k,
    cycleAssociatedToClosedSubscheme_ker C p
      (((pointDivisor p t W).subschemeι ≫ W.subschemeι) ≫
        pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) k,
    Category.assoc, ← fibreBaseProjection_def p W, ker_pointDivisor_subschemeι_comp p t W]

/-- **Stacks 0B07, part (1)(b), at an arbitrary point of the projective line.** The cycle
`[W_a]_k` of the fibre of `W` at the point `a` attached to `t`, viewed as a closed subscheme of
`X`, is the proper pushforward along `pr : X ×_S ℙ¹_S ⟶ X` of the Section 43.14 intersection
product `W · (X × a)`.

Nothing pointwise is assumed: `W` is a closed subvariety of delta-dimension `k + 1` meeting the
image of the section properly, and `Stacks.Chow.localConditions_ker_pointSection` derives the
local conditions of part (1)(a) from that. -/
theorem properPushforward_intersectionProductCycle_eq_pointFiberCycle
    [IsIntegral W.subscheme] (d : ℕ) (hY : IsRegular (projectiveLineProduct p))
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
              (pointSection p t).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
            (pointSection p t).ker k hWD⟩ =
      cycleAssociatedToClosedSubscheme C p (pointFiber p t W).subschemeι k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have hbundle : (⟨_, intersectionProductCycle_mem_cyclesOfDimension C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W
      (pointSection p t).ker k hWD⟩ :
      CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
      cycleAssociatedToClosedSubscheme C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ (pointSection p t).ker).subschemeι k :=
    Subtype.ext (cycleAssociatedToClosedSubscheme_sup_pointSection_eq_intersectionProductCycle
      C p t W hY k d hd hDim hWD).symm
  rw [hbundle]
  exact properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_pointSection C p t W k

end Push

/-! ### Part (1)(b) at an arbitrary point for a nonsingular variety -/

section NonsingularVariety

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (Kf : Type u) [Field Kf] [IsAlgClosed Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
  (hX : IsRegular X) (t : Γ(C.S, ⊤)) (k : ℤ)

/-- **Stacks 0B07, part (1)(b), at an arbitrary point, for a nonsingular variety.** The cycle
`[W_a]_k` of the fibre of `W` at an arbitrary point `a` of the affine chart of `ℙ¹_S` is the
proper pushforward along `pr : X ×_S ℙ¹_S ⟶ X` of the Section 43.14 intersection product
`W · (X × a)`. Nothing is assumed about the ambient family. -/
theorem properPushforward_intersectionProductCycle_eq_pointFiberCycle_of_isRegular
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (pointSection p t).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (pointSection p t).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W
            (pointSection p t).ker k hWD⟩ =
      cycleAssociatedToClosedSubscheme C p (pointFiber p t W).subschemeι k := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact properPushforward_intersectionProductCycle_eq_pointFiberCycle C p t W k d
    (isRegular_projectiveLineProduct_of_eq p hC hX) hd hDim hWD

end NonsingularVariety

end Stacks.Chow

end
