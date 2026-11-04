module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProjectionFormulaFlat.ZeroFibreDegeneration
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectiveLineBridge
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.ClosedPointSection
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.SectionRange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TorsionPoints
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DominanceCases

/-!
# The points `0` and `∞` of the projective line over a field, and fibres of integral families

Over an algebraically closed field `k` the zero and infinity sections of `X × ℙ¹ ⟶ X` are the
sections `Stacks.Chow.closedPointSection` at the closed points `0` and `∞` of `ℙ¹_k`; and an
integral closed subscheme `W ⊆ X × ℙ¹` either dominates `ℙ¹` or lies over a single closed point, so
that if it is contained in neither of the two sections, its fibre over `0` (or `∞`) is empty unless
it dominates `ℙ¹`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The point `0` of `ℙ¹_k`. -/
def zeroLinePoint : relativeProjectiveLine (Spec (.of k)) :=
  lineZeroSection (Spec (.of k)) (IsLocalRing.closedPoint k)

/-- The point `∞` of `ℙ¹_k`. -/
def infinityLinePoint : relativeProjectiveLine (Spec (.of k)) :=
  lineInfinitySection (Spec (.of k)) (IsLocalRing.closedPoint k)

omit [IsAlgClosed k] in
/-- The point `0` of `ℙ¹_k` is closed. -/
theorem isClosed_zeroLinePoint : IsClosed ({zeroLinePoint k} : Set _) :=
  ProjectiveLineBridge.isClosed_singleton_of_isClosedImmersion k _

omit [IsAlgClosed k] in
/-- The point `∞` of `ℙ¹_k` is closed. -/
theorem isClosed_infinityLinePoint : IsClosed ({infinityLinePoint k} : Set _) :=
  ProjectiveLineBridge.isClosed_singleton_of_isClosedImmersion k _

/-- The `k`-point of `ℙ¹_k` at `0` is the zero section. -/
theorem closedPointLineSection_zeroLinePoint :
    closedPointLineSection k rfl (zeroLinePoint k) (isClosed_zeroLinePoint k) =
      lineZeroSection (Spec (.of k)) := by
  refine ext_of_apply_closedPoint_eq_of_comp_eq
    (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) (isClosed_zeroLinePoint k)
    (closedPointLineSection_apply k rfl _ _ _) rfl ?_
  rw [closedPointLineSection_comp, lineZeroSection_comp]

/-- The `k`-point of `ℙ¹_k` at `∞` is the infinity section. -/
theorem closedPointLineSection_infinityLinePoint :
    closedPointLineSection k rfl (infinityLinePoint k) (isClosed_infinityLinePoint k) =
      lineInfinitySection (Spec (.of k)) := by
  refine ext_of_apply_closedPoint_eq_of_comp_eq
    (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) (isClosed_infinityLinePoint k)
    (closedPointLineSection_apply k rfl _ _ _) rfl ?_
  rw [closedPointLineSection_comp, lineInfinitySection_comp]

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- **The section of `X × ℙ¹` at `0` is the zero section.** -/
theorem closedPointSection_zeroLinePoint :
    closedPointSection k rfl (zeroLinePoint k) (isClosed_zeroLinePoint k) p = zeroSection p := by
  refine pullback.hom_ext ?_ ?_
  · rw [closedPointSection_comp_fst, zeroSection_comp_fst]
  · rw [closedPointSection_comp_snd, zeroSection_comp_snd, closedPointLineSection_zeroLinePoint]

/-- **The section of `X × ℙ¹` at `∞` is the infinity section.** -/
theorem closedPointSection_infinityLinePoint :
    closedPointSection k rfl (infinityLinePoint k) (isClosed_infinityLinePoint k) p =
      infinitySection p := by
  refine pullback.hom_ext ?_ ?_
  · rw [closedPointSection_comp_fst, infinitySection_comp_fst]
  · rw [closedPointSection_comp_snd, infinitySection_comp_snd,
      closedPointLineSection_infinityLinePoint]

/-! ### Fibres of an integral family which does not dominate the line -/

omit [IsAlgClosed k] in
/-- A point of `X × ℙ¹` over `0` lies on the zero section. -/
theorem mem_range_zeroSection_of_snd_eq {y : projectiveLineProduct p}
    (hy : (pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base y =
      zeroLinePoint k) :
    y ∈ Set.range (zeroSection p).base := by
  have h := range_constantSection p integralZeroSection
  change Set.range (zeroSection p).base = _ at h
  have key : ∀ a : Spec (.of k), (pullback.snd (terminal.from (Spec (.of k)))
      (terminal.from (projectiveLine (ULift.{u} ℤ)))).base
        ((lineZeroSection (Spec (.of k))).base a) ∈
      Set.range integralZeroSection.base := fun a => by
    rw [← Scheme.Hom.comp_apply, lineZeroSection, lineConstantSection, pullback.lift_snd,
      Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  rw [h, Set.mem_preimage, projectiveLineProjection, Scheme.Hom.comp_apply, hy, zeroLinePoint]
  exact key _

omit [IsAlgClosed k] in
/-- A point of `X × ℙ¹` over `∞` lies on the infinity section. -/
theorem mem_range_infinitySection_of_snd_eq {y : projectiveLineProduct p}
    (hy : (pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base y =
      infinityLinePoint k) :
    y ∈ Set.range (infinitySection p).base := by
  have h := range_constantSection p integralInfinitySection
  change Set.range (infinitySection p).base = _ at h
  have key : ∀ a : Spec (.of k), (pullback.snd (terminal.from (Spec (.of k)))
      (terminal.from (projectiveLine (ULift.{u} ℤ)))).base
        ((lineInfinitySection (Spec (.of k))).base a) ∈
      Set.range integralInfinitySection.base := fun a => by
    rw [← Scheme.Hom.comp_apply, lineInfinitySection, lineConstantSection, pullback.lift_snd,
      Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  rw [h, Set.mem_preimage, projectiveLineProjection, Scheme.Hom.comp_apply, hy, infinityLinePoint]
  exact key _

omit [IsAlgClosed k] in
/-- The zero section lies over `0`. -/
theorem snd_zeroSection_apply (x : X) :
    (pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base
      ((zeroSection p).base x) = zeroLinePoint k := by
  rw [← Scheme.Hom.comp_apply, zeroSection_comp_snd, Scheme.Hom.comp_apply, zeroLinePoint]
  congr 1
  exact Subsingleton.elim _ _

omit [IsAlgClosed k] in
/-- The infinity section lies over `∞`. -/
theorem snd_infinitySection_apply (x : X) :
    (pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base
      ((infinitySection p).base x) = infinityLinePoint k := by
  rw [← Scheme.Hom.comp_apply, infinitySection_comp_snd, Scheme.Hom.comp_apply, infinityLinePoint]
  congr 1
  exact Subsingleton.elim _ _

variable (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]

omit [IsAlgClosed k] in
/-- The second projection out of an integral family which does not dominate the line is
constant. -/
theorem snd_eq_of_not_isDominant
    (hnd : ¬ IsDominant (W.subschemeι ≫
      pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)))) (w : W.subscheme) :
    (W.subschemeι ≫ pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base w =
      (W.subschemeι ≫ pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base
        (genericPoint W.subscheme) := by
  have : IsIntegral (relativeProjectiveLine (fieldChowSituation k).S) :=
    isIntegral_relativeProjectiveLine _
  exact constant_of_not_isDominant (fieldChowSituation k) (fun _ => rfl)
    (relativeProjectiveLine (fieldChowSituation k).S ↘ (fieldChowSituation k).S)
    (schemeDeltaDimension_relativeProjectiveLine_eq_one k (fieldChowSituation k) rfl
      (fun _ => rfl)) _ hnd w

/-- An integral family which meets a section `s` over a point `q` of the line, and is not
contained in `s`, dominates the line, provided the fibre of `X × ℙ¹` over `q` is `s`. -/
private theorem isDominant_of_meets_section {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (W : (projectiveLineProduct p).IdealSheafData)
    [IsIntegral W.subscheme] (q : relativeProjectiveLine (Spec (.of k)))
    (s : X ⟶ projectiveLineProduct p)
    (hs : ∀ y, (pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base y = q ↔
      y ∈ Set.range s.base)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range s) (w : W.subscheme)
    (hw : W.subschemeι.base w ∈ Set.range s.base) :
    IsDominant (W.subschemeι ≫
      pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) := by
  by_contra hnd
  refine h₀ ?_
  rintro _ ⟨w', rfl⟩
  exact (hs _).1 <| (snd_eq_of_not_isDominant _ p W hnd w').trans <|
    (snd_eq_of_not_isDominant _ p W hnd w).symm.trans <| (hs _).2 hw

omit [IsAlgClosed k] in
/-- **An integral family with a nonempty zero fibre, contained in neither section, dominates the
line.** -/
theorem isDominant_of_zeroFiber_nonempty
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection p))
    (hne : ((zeroFiber p W).support : Set X).Nonempty) :
    IsDominant (W.subschemeι ≫
      pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) := by
  obtain ⟨x, hx⟩ := hne
  rw [coe_support_zeroFiber, Set.mem_preimage, ← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨w, hw⟩ := hx
  exact isDominant_of_meets_section p W _ _
    (fun y => ⟨mem_range_zeroSection_of_snd_eq k p, by
      rintro ⟨x, rfl⟩; exact snd_zeroSection_apply k p x⟩) h₀ w ⟨x, hw.symm⟩

omit [IsAlgClosed k] in
/-- **An integral family with a nonempty infinity fibre, contained in neither section, dominates
the line.** -/
theorem isDominant_of_infinityFiber_nonempty
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    (hne : ((infinityFiber p W).support : Set X).Nonempty) :
    IsDominant (W.subschemeι ≫
      pullback.snd p (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))) := by
  obtain ⟨x, hx⟩ := hne
  rw [coe_support_infinityFiber, Set.mem_preimage, ← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨w, hw⟩ := hx
  exact isDominant_of_meets_section p W _ _
    (fun y => ⟨mem_range_infinitySection_of_snd_eq k p, by
      rintro ⟨x, rfl⟩; exact snd_infinitySection_apply k p x⟩) hInf w ⟨x, hw.symm⟩

end Stacks.Intersection.RationalEquivalenceProduct

end
