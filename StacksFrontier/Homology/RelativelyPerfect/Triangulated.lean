module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.RelativelyPerfect
public import StacksFrontier.Homology.TorAmplitude.Summand
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Relatively perfect objects form a saturated triangulated subcategory

Let `R → A` be a flat ring map of finite presentation. The objects of `D(A)` that are perfect
relative to `R` (Stacks 0DHS) form a strictly full, saturated, triangulated subcategory of
`D(A)`: the property is closed under isomorphisms, it contains the zero object and is closed
under shifts and extensions, and it passes to direct summands.

## Main definitions

* `PseudoCoherence.relativelyPerfect`: relative perfectness packaged as an object property.

## Main results

* `PseudoCoherence.isClosedUnderIsomorphisms_relativelyPerfect`,
  `PseudoCoherence.isTriangulated_relativelyPerfect` and
  `PseudoCoherence.isSaturated_relativelyPerfect` (Stacks 0DHT): the three assertions whose
  conjunction says that the relatively perfect objects form a strictly full saturated
  triangulated subcategory.

## Implementation notes

Strict fullness is `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`, the
triangulated-subcategory condition is `CategoryTheory.ObjectProperty.IsTriangulated` and
saturation is `CategoryTheory.ObjectProperty.IsSaturated` (Stacks 05RB).

Pseudo-coherence over `A` contributes through its own providers: it is preserved by isomorphisms
(`StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso`), holds for a zero object
(`StacksDraft.PseudoCoherence.pseudoCoherent_of_isZero`), satisfies two-out-of-three in a
distinguished triangle (Stacks 064V) and passes to direct summands (Stacks 064X).

Finite Tor dimension over `R` contributes through Stacks 066G for summands, and through the
propagation of Tor amplitude along a distinguished triangle (Stacks 0655), proved here for the
derived tensor product of `StacksFrontier.Homology.TorAmplitude.Defs` with independent ring and
module universes.

The derived tensor product is supplied as data, in the shape used by Stacks 0DHS: the bifunctor,
its comparison with termwise tensoring and the universal property making each `- ⊗ᴸ M[0]` a total
left derived functor. Closure under shifts and extensions needs each `- ⊗ᴸ M[0]` to be exact, so
its shift compatibility and triangulatedness are supplied too.

## References

* [The Stacks Project, Lemma 15.85.2 (0DHT)](https://stacks.math.columbia.edu/tag/0DHT)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

namespace PseudoCoherence

universe u v w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

open StacksDraft.PseudoCoherence StacksDraft.TorAmplitude

section Triangle

variable {R : Type u} [CommRing R]
  (derivedTensor :
    DerivedCategory (ModuleCat.{v} R) ⥤
      DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R))
  (comparison : ∀ M : ModuleCat.{v} R,
    DerivedCategory.Q ⋙
        derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ M : ModuleCat.{v} R,
    (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
      (comparison M) (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)))

/-- Widening the interval weakens Tor amplitude. -/
private lemma hasTorAmplitude_mono (K : DerivedCategory (ModuleCat.{v} R)) {a b a' b' : ℤ}
    (ha : a' ≤ a) (hb : b ≤ b')
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived K a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived K a' b' := by
  intro M i hi
  refine h M i ?_
  simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
  omega

/-- Tor amplitude only depends on the isomorphism class of the object. -/
private lemma hasTorAmplitude_of_iso {X Y : DerivedCategory (ModuleCat.{v} R)} (e : X ≅ Y)
    {a b : ℤ} (h : HasTorAmplitude derivedTensor comparison isLeftDerived X a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived Y a b := fun M i hi ↦
  (h M i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso
      ((derivedTensor.mapIso e).app
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M))).symm

/-- Finite Tor dimension only depends on the isomorphism class of the object. -/
private lemma hasFiniteTorDimension_of_iso {X Y : DerivedCategory (ModuleCat.{v} R)} (e : X ≅ Y)
    (h : HasFiniteTorDimension derivedTensor comparison isLeftDerived X) :
    HasFiniteTorDimension derivedTensor comparison isLeftDerived Y := by
  obtain ⟨a, b, h⟩ := h
  exact ⟨a, b, hasTorAmplitude_of_iso derivedTensor comparison isLeftDerived e h⟩

variable
  (commShift : ∀ M : ModuleCat.{v} R,
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).CommShift ℤ)
  (triangulated : ∀ M : ModuleCat.{v} R, letI := commShift M;
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsTriangulated)

include commShift triangulated in
/-- The three propagation rules of Stacks 0655 for the certified derived tensor product: in a
distinguished triangle, Tor amplitude of two of the vertices in the displayed ranges forces Tor
amplitude of the third. Each `- ⊗ᴸ M[0]` is exact, so it carries the triangle to a distinguished
triangle, and the claim is read off the long exact cohomology sequence. -/
private lemma hasTorAmplitude_of_distinguished
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distinguishedTriangles)
    (a b : ℤ) :
    (HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₁ (a + 1) (b + 1) →
        HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₂ a b →
        HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₃ a b) ∧
      (HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₁ a b →
        HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₃ a b →
        HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₂ a b) ∧
      (HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₂ (a + 1) (b + 1) →
        HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₃ a b →
        HasTorAmplitude derivedTensor comparison isLeftDerived T.obj₁ (a + 1) (b + 1)) := by
  have key (M : ModuleCat.{v} R) :
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).mapTriangle.obj T ∈
          distinguishedTriangles := by
    let _ := commShift M
    let _ := triangulated M
    exact Functor.map_distinguished _ T hT
  refine ⟨fun h₁ h₂ M i hi ↦ ?_, fun h₁ h₃ M i hi ↦ ?_, fun h₂ h₃ M i hi ↦ ?_⟩
  · have hex := DerivedCategory.HomologySequence.exact₃ _ (key M) i (i + 1) rfl
    refine hex.isZero_of_both_zeros ((h₂ M i hi).eq_zero_of_src _)
      ((h₁ M (i + 1) ?_).eq_zero_of_tgt _)
    simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
    omega
  · have hex := DerivedCategory.HomologySequence.exact₂ _ (key M) i
    exact hex.isZero_of_both_zeros ((h₁ M i hi).eq_zero_of_src _)
      ((h₃ M i hi).eq_zero_of_tgt _)
  · have hex := DerivedCategory.HomologySequence.exact₁ _ (key M) (i - 1) i (by omega)
    refine hex.isZero_of_both_zeros ((h₃ M (i - 1) ?_).eq_zero_of_src _)
      ((h₂ M i hi).eq_zero_of_tgt _)
    simp only [Set.mem_Icc, not_and, not_le] at hi ⊢
    omega

include commShift triangulated in
/-- Two-out-of-three for finite Tor dimension in a distinguished triangle: the intervals are
widened to a common one and the propagation rules of Stacks 0655 apply. -/
private lemma hasFiniteTorDimension_of_distinguished
    (T : Triangle (DerivedCategory (ModuleCat.{v} R))) (hT : T ∈ distinguishedTriangles) :
    (HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₁ →
        HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₂ →
        HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₃) ∧
      (HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₁ →
        HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₃ →
        HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₂) ∧
      (HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₂ →
        HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₃ →
        HasFiniteTorDimension derivedTensor comparison isLeftDerived T.obj₁) := by
  have key := hasTorAmplitude_of_distinguished derivedTensor comparison isLeftDerived commShift
    triangulated T hT
  have mono := hasTorAmplitude_mono derivedTensor comparison isLeftDerived
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩
    exact ⟨min (a₁ - 1) a₂, max (b₁ - 1) b₂,
      (key _ _).1 (mono _ (by omega) (by omega) h₁) (mono _ (by omega) (by omega) h₂)⟩
  · rintro ⟨a₁, b₁, h₁⟩ ⟨a₃, b₃, h₃⟩
    exact ⟨min a₁ a₃, max b₁ b₃,
      (key _ _).2.1 (mono _ (by omega) (by omega) h₁) (mono _ (by omega) (by omega) h₃)⟩
  · rintro ⟨a₂, b₂, h₂⟩ ⟨a₃, b₃, h₃⟩
    exact ⟨min (a₂ - 1) a₃ + 1, max (b₂ - 1) b₃ + 1,
      (key _ _).2.2 (mono _ (by omega) (by omega) h₂) (mono _ (by omega) (by omega) h₃)⟩

include commShift triangulated in
/-- A zero object has finite Tor dimension: each `- ⊗ᴸ M[0]` is additive, hence sends a zero
object to a zero object. -/
private lemma hasFiniteTorDimension_zero :
    HasFiniteTorDimension derivedTensor comparison isLeftDerived
      (0 : DerivedCategory (ModuleCat.{v} R)) := by
  refine ⟨0, 0, fun M i _ ↦ ?_⟩
  let _ := commShift M
  let _ := triangulated M
  exact (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_isZero
    ((derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).map_isZero (isZero_zero _))

end Triangle

/-- An object property of a pretriangulated category that contains the zero object, is closed
under isomorphisms and satisfies the first and third two-out-of-three rules in a distinguished
triangle is stable under all integer shifts: a shift by `n` is reached from the contractible
triangles by induction on `n`. -/
private lemma isStableUnderShift_of_twoOutOfThree {C : Type*} [Category* C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (h₁ : ∀ T : Triangle C, T ∈ distinguishedTriangles → P T.obj₂ → P T.obj₃ → P T.obj₁)
    (h₃ : ∀ T : Triangle C, T ∈ distinguishedTriangles → P T.obj₁ → P T.obj₂ → P T.obj₃) :
    P.IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro X hX
    induction n using Int.induction_on with
    | zero => exact P.prop_of_iso ((shiftFunctorZero C ℤ).symm.app X) hX
    | succ n hn =>
        exact P.prop_of_iso ((shiftFunctorAdd C (n : ℤ) 1).symm.app X)
          (h₃ _ (contractible_distinguished₂ (X⟦(n : ℤ)⟧)) hn P.prop_zero)
    | pred n hn =>
        apply h₁ (Triangle.mk (0 : X⟦-(n : ℤ) - 1⟧ ⟶ (0 : C)) 0
            (𝟙 ((X⟦-(n : ℤ) - 1⟧)⟦(1 : ℤ)⟧)))
          (contractible_distinguished₂ (X⟦-(n : ℤ) - 1⟧)) P.prop_zero
        exact P.prop_of_iso
          ((shiftFunctorAdd' C (-(n : ℤ) - 1) 1 (-(n : ℤ)) (by omega)).app X) hn⟩

section Subcategory

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Flat R A] [Algebra.FinitePresentation R A]
  (derivedTensor :
    DerivedCategory (ModuleCat.{max u v w} R) ⥤
      DerivedCategory (ModuleCat.{max u v w} R) ⥤ DerivedCategory (ModuleCat.{max u v w} R))
  (comparison : ∀ M : ModuleCat.{max u v w} R,
    DerivedCategory.Q ⋙
        derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ M : ModuleCat.{max u v w} R,
    (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor
          (ModuleCat.{max u v w} R) 0).obj M)).IsLeftDerivedFunctor
      (comparison M)
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R) (ComplexShape.up ℤ)))
  (commShift : ∀ M : ModuleCat.{max u v w} R,
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M)).CommShift ℤ)
  (triangulated : ∀ M : ModuleCat.{max u v w} R, letI := commShift M;
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj M)).IsTriangulated)

/-- The objects of `D(A)` that are perfect relative to `R` (Stacks 0DHS), viewed as a property
of the objects of `D(A)`. -/
def relativelyPerfect : ObjectProperty (DerivedCategory (ModuleCat.{max u v w} A)) :=
  IsRelativelyPerfect derivedTensor comparison isLeftDerived

/-- An object of `D(A)` lies in `relativelyPerfect` exactly when it is perfect relative to
`R`. -/
theorem relativelyPerfect_iff (K : DerivedCategory (ModuleCat.{max u v w} A)) :
    relativelyPerfect derivedTensor comparison isLeftDerived K ↔
      IsRelativelyPerfect derivedTensor comparison isLeftDerived K :=
  Iff.rfl

/-- For a flat, finitely presented ring map `R → A`, the objects of `D(A)` perfect relative to
`R` form a *strictly full* subcategory: relative perfectness is invariant under isomorphism in
`D(A)`. -/
@[stacks 0DHT]
theorem isClosedUnderIsomorphisms_relativelyPerfect :
    (relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison
      isLeftDerived).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ ⟨h.1.ofIso e,
    hasFiniteTorDimension_of_iso derivedTensor comparison isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.mapIso e) h.2⟩⟩

include commShift triangulated in
/-- Two out of three for relative perfectness in a distinguished triangle of `D(A)`: restriction
of scalars to `R` is exact, so it carries the triangle to a distinguished triangle of `D(R)`,
where finite Tor dimension propagates; pseudo-coherence propagates by Stacks 064V. -/
private lemma relativelyPerfect_of_distinguished
    (T : Triangle (DerivedCategory (ModuleCat.{max u v w} A)))
    (hT : T ∈ distinguishedTriangles) :
    let P := relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison isLeftDerived
    (P T.obj₁ → P T.obj₂ → P T.obj₃) ∧ (P T.obj₁ → P T.obj₃ → P T.obj₂) ∧
      (P T.obj₂ → P T.obj₃ → P T.obj₁) := by
  have hTF : ((ModuleCat.restrictScalars
      (algebraMap R A)).mapDerivedCategory.mapTriangle.obj T) ∈ distinguishedTriangles :=
    Functor.map_distinguished _ T hT
  have hpc := isPseudoCoherent_of_distinguished T hT
  have htor := hasFiniteTorDimension_of_distinguished derivedTensor comparison isLeftDerived
    commShift triangulated _ hTF
  exact ⟨fun h₁ h₂ ↦ ⟨hpc.1 h₁.1 h₂.1, htor.1 h₁.2 h₂.2⟩,
    fun h₁ h₃ ↦ ⟨hpc.2.1 h₁.1 h₃.1, htor.2.1 h₁.2 h₃.2⟩,
    fun h₂ h₃ ↦ ⟨hpc.2.2 h₂.1 h₃.1, htor.2.2 h₂.2 h₃.2⟩⟩

include commShift triangulated in
/-- For a flat, finitely presented ring map `R → A`, the objects of `D(A)` perfect relative to
`R` form a *triangulated* subcategory: the property contains the zero object, is stable under all
shifts, and is closed under extensions. -/
@[stacks 0DHT, sga "6 III 4.2" "affine case, flat f.p."]
theorem isTriangulated_relativelyPerfect :
    (relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison
      isLeftDerived).IsTriangulated := by
  let _ := isClosedUnderIsomorphisms_relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison
    isLeftDerived
  let _ : (relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison
      isLeftDerived).ContainsZero :=
    ⟨⟨0, isZero_zero _,
      ⟨(pseudoCoherent_of_isZero (0 : DerivedCategory (ModuleCat.{max u v w} A))
          (isZero_zero _)).1,
        hasFiniteTorDimension_of_iso derivedTensor comparison isLeftDerived
          (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map_isZero
            (isZero_zero _)).iso (isZero_zero _)).symm
          (hasFiniteTorDimension_zero derivedTensor comparison isLeftDerived commShift
            triangulated)⟩⟩⟩
  have htri := relativelyPerfect_of_distinguished (A := A) derivedTensor comparison
    isLeftDerived commShift triangulated
  let _ := isStableUnderShift_of_twoOutOfThree
    (relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison isLeftDerived)
    (fun T hT ↦ (htri T hT).2.2) (fun T hT ↦ (htri T hT).1)
  exact { ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ ((htri T hT).2.1 h₁ h₃) }

/-- For a flat, finitely presented ring map `R → A`, the objects of `D(A)` perfect relative to
`R` form a *saturated* (thick) subcategory: a direct summand of a relatively perfect object is
relatively perfect. -/
@[stacks 0DHT]
theorem isSaturated_relativelyPerfect :
    (relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison
      isLeftDerived).IsSaturated := by
  let _ := isClosedUnderIsomorphisms_relativelyPerfect.{u, v, w} (A := A) derivedTensor comparison
    isLeftDerived
  have key (X Y : DerivedCategory (ModuleCat.{max u v w} A))
      (h : IsRelativelyPerfect derivedTensor comparison isLeftDerived (X ⊞ Y)) :
      IsRelativelyPerfect derivedTensor comparison isLeftDerived X ∧
        IsRelativelyPerfect derivedTensor comparison isLeftDerived Y := by
    obtain ⟨hp, a, b, hab⟩ := h
    have hab' : HasTorAmplitude derivedTensor comparison isLeftDerived
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj X ⊞
          (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj Y) a b :=
      hasTorAmplitude_of_iso derivedTensor comparison isLeftDerived
        (Functor.mapBiprod _ X Y) hab
    have hsplit := hasTorAmplitude_of_biprod derivedTensor comparison isLeftDerived _ _ a b hab'
    have hpc := (isPseudoCoherentFrom_and_pseudoCoherent_of_biproduct X Y 0).2 hp
    exact ⟨⟨hpc.1, a, b, hsplit.1⟩, ⟨hpc.2, a, b, hsplit.2⟩⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    rw [ObjectProperty.isoClosure_eq_self] at h ⊢
  · exact (key _ _ h).1
  · exact (key _ _ h).2

end Subcategory

end PseudoCoherence
