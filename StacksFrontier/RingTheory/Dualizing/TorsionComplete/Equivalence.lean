module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Basic
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletionAfterLocalCohomology

/-!
# Torsion versus complete modules

Let `I` be a finitely generated ideal of a commutative ring `A` and `Z = V(I)`. Derived
`I`-completion and local cohomology with support in `Z` are quasi-inverse equivalences between
the full subcategory of `D(A)` of complexes with `I`-power-torsion cohomology and the full
subcategory of derived `I`-complete complexes.

The composite adjunction of the two coreflections has invertible counit by Stacks 0A6W, which is
the half of the statement saying that completing the local cohomology of a complex gives its
completion. Invertibility of the unit reduces, by the triangle identity, to the statement that a
complex with `I`-power-torsion cohomology whose completion vanishes is zero. That in turn follows
from the derived Nakayama argument: dividing by a generating family produces a complex on which
each generator acts nilpotently, hence a complex that is both torsion and left orthogonal to all
derived complete objects — and such a complex is derived complete itself, so it vanishes.

## Main definitions

* `Dualizing.derivedCompletionReflection` — derived completion as a reflection onto the derived
  `I`-complete objects, together with its adjunction.
* `Dualizing.derivedCompletion` — derived completion valued in that subcategory.

## Main results

* `Dualizing.torsionCompleteEquivalence` — Stacks 0A6X, the equivalence, with its functor
  identified as derived completion and its inverse as local cohomology.

## References

* [Stacks Project, Tag 0A6X](https://stacks.math.columbia.edu/tag/0A6X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u v

namespace Dualizing

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Having `I`-power-torsion cohomology is invariant under isomorphism in `D(A)`. -/
instance derivedPowerTorsionProperty_isClosedUnderIsomorphisms (hI : I.FG) :
    (derivedPowerTorsionProperty.{u, v} A I hI).IsClosedUnderIsomorphisms where
  of_iso e h i := (powerTorsionModuleProperty A I hI).prop_of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e) (h i)

/-- The complexes with `I`-power-torsion cohomology form a triangulated subcategory of `D(A)`:
they contain zero and are stable under shifts and extensions. -/
instance derivedPowerTorsionProperty_isTriangulated (hI : I.FG) :
    (derivedPowerTorsionProperty.{u, v} A I hI).IsTriangulated := by
  let P := derivedPowerTorsionProperty.{u, v} A I hI
  let S := powerTorsionModuleProperty.{u, v} A I hI
  have : P.ContainsZero := ⟨⟨0, isZero_zero _, fun i =>
    S.prop_of_isZero ((DerivedCategory.homologyFunctor _ i).map_isZero (isZero_zero _))⟩⟩
  have : P.IsStableUnderShift ℤ := ⟨fun n => ⟨fun X h i =>
    S.prop_of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).shiftIso
      n i (n + i) rfl).app X).symm (h (n + i))⟩⟩
  have : P.IsTriangulatedClosed₂ := .mk' fun T hT h₁ h₃ i =>
    S.prop_X₂_of_exact (DerivedCategory.HomologySequence.exact₂ T hT i) (h₁ i) (h₃ i)
  exact {}

/-- **Derived completion as a reflection.** A finitely generated ideal admits a finite generating
family, and the derived limit of the Koszul powers of such a family is left adjoint to the
inclusion of the derived `I`-complete objects. -/
def derivedCompletionReflection (hI : I.FG) :
    Σ C : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCompleteDerivedCategory A I,
      C ⊣ (derivedCompleteProperty A I).ι := by
  let hfg := Submodule.fg_iff_exists_fin_generating_family.mp hI
  let f := Classical.choose (Classical.choose_spec hfg)
  have hf := Classical.choose_spec (Classical.choose_spec hfg)
  rw [← hf]
  let h := AdicKoszulAdjunction.koszulPowerDerivedLimit_isLeftAdjoint A f
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{v} A))
  exact ⟨Classical.choose h, Classical.choice (Classical.choose_spec h).1⟩

/-- Derived `I`-completion, valued in the full subcategory of derived `I`-complete complexes. -/
def derivedCompletion (hI : I.FG) :
    DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCompleteDerivedCategory A I :=
  (derivedCompletionReflection.{u, v} A I hI).1

variable {A I}

/-- If an element kills the two outer maps of a distinguished triangle whose first vertex carries
it as a scalar, its square kills the third vertex: the identity of the third vertex factors
through the first map. -/
private theorem smul_sq_id_eq_zero_of_distTriang
    {X Z : DerivedCategory (ModuleCat.{v} A)} {f : X ⟶ X} {g : X ⟶ Z} {h : Z ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang _) (a : A) (h₁ : (a • 𝟙 X) ≫ g = 0)
    (h₂ : h ≫ (shiftFunctor _ (1 : ℤ)).map (a • 𝟙 X) = 0) : a ^ 2 • 𝟙 Z = 0 := by
  rw [Functor.Linear.map_smul, (shiftFunctor _ (1 : ℤ)).map_id X] at h₂
  obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₃ _ hT (a • 𝟙 Z)
    (by simpa [Linear.smul_comp, Linear.comp_smul] using h₂)
  dsimp only [Triangle.mk_obj₂, Triangle.mk_mor₂] at k hk
  calc
    a ^ 2 • 𝟙 Z = (a • 𝟙 Z) ≫ (a • 𝟙 Z) := by
      simp [pow_two, Linear.comp_smul, smul_smul]
    _ = (k ≫ g) ≫ (a • 𝟙 Z) := congrArg (fun q => q ≫ (a • 𝟙 Z)) hk
    _ = k ≫ (a • 𝟙 X) ≫ g := by simp [Linear.smul_comp, Linear.comp_smul]
    _ = 0 := by rw [h₁, comp_zero]

/-- A complex with `I`-power-torsion cohomology on which an element of `I` acts invertibly is
zero: every cohomology class is killed by a power of that element, which also acts invertibly. -/
private theorem isZero_of_derivedPowerTorsion_of_isIso_smul (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{v} A)) (hX : derivedPowerTorsionProperty A I hI X)
    (a : A) (ha : a ∈ I) [IsIso (a • 𝟙 X)] : IsZero X := by
  apply (IsZero.iff_id_eq_zero X).2
  have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj X) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro x
    let : Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i) :=
      derivedHomologyFunctorLinear i
    have hpow (n : ℕ) : IsIso (a ^ n • 𝟙 X) := by
      induction n with
      | zero => simpa using (inferInstance : IsIso (𝟙 X))
      | succ n ih =>
        have hsucc : a ^ (n + 1) • 𝟙 X = (a ^ n • 𝟙 X) ≫ (a • 𝟙 X) := by
          simp [pow_succ, Linear.comp_smul, smul_smul, mul_comm]
        rw [hsucc]
        infer_instance
    obtain ⟨n, -, hn⟩ := hX i x
    have := hpow n
    have hi : IsIso (a ^ n •
        𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj X)) := by
      have hi' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
          (a ^ n • 𝟙 X)) := inferInstance
      rwa [Functor.Linear.map_smul,
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map_id X] at hi'
    apply (ModuleCat.mono_iff_injective
      (a ^ n • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj X))).mp
      inferInstance
    simpa using hn (a ^ n) (Ideal.pow_mem_pow ha n)
  have hi : IsIso (0 : X ⟶ X) := (DerivedCategory.isIso_iff _ _).2 fun i => by
    rw [Functor.map_zero]
    exact (hz i).isIso (hz i) _
  exact isIsoZeroSelfEquiv X hi

/-- Dividing successively by the elements of a finite subset of `I` replaces a torsion complex
left orthogonal to the derived complete objects by one on which every element of that subset
acts nilpotently, without leaving either class and without creating a nonzero object out of a
zero one. -/
private theorem exists_nilpotent_of_derivedPowerTorsion_of_leftOrthogonal (hI : I.FG)
    (s : Finset A) (hs : ∀ a ∈ s, a ∈ I) (X : DerivedCategory (ModuleCat.{v} A))
    (hX : derivedPowerTorsionProperty A I hI X)
    (hO : (derivedCompleteProperty A I).leftOrthogonal X) :
    ∃ Y : DerivedCategory (ModuleCat.{v} A),
      derivedPowerTorsionProperty A I hI Y ∧
      (derivedCompleteProperty A I).leftOrthogonal Y ∧
      (∀ a ∈ s, ∃ n : ℕ, a ^ n • 𝟙 Y = 0) ∧ (IsZero Y → IsZero X) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨X, hX, hO, by simp, id⟩
  | @insert a s ha ih =>
    obtain ⟨Y, hY, hOY, hnil, hzero⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (a • 𝟙 Y)
    let T := Triangle.mk (a • 𝟙 Y) g h
    refine ⟨Z,
      (derivedPowerTorsionProperty A I hI).ext_of_isTriangulatedClosed₃ T hT hY hY,
      (derivedCompleteProperty A I).leftOrthogonal.ext_of_isTriangulatedClosed₃ T hT hOY hOY,
      ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with hb | hb
      · subst b
        exact ⟨2, smul_sq_id_eq_zero_of_distTriang hT a (comp_distTriang_mor_zero₁₂ T hT)
          (comp_distTriang_mor_zero₃₁ T hT)⟩
      · obtain ⟨n, hn⟩ := hnil b hb
        refine ⟨n * 2, ?_⟩
        rw [pow_mul]
        apply smul_sq_id_eq_zero_of_distTriang hT (b ^ n)
        · rw [hn, zero_comp]
        · rw [hn, Functor.map_zero, comp_zero]
    · intro hz
      have : IsIso (a • 𝟙 Y) := (Triangle.isZero₃_iff_isIso₁ T hT).1 hz
      exact hzero (isZero_of_derivedPowerTorsion_of_isIso_smul hI Y hY a
        (hs a (Finset.mem_insert_self _ _)))

/-- **A torsion complex left orthogonal to every derived complete complex is zero.** After
dividing by a generating family the ideal acts nilpotently, so the complex is itself derived
complete, hence orthogonal to itself. -/
private theorem isZero_of_derivedPowerTorsion_of_leftOrthogonal (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{v} A)) (hX : derivedPowerTorsionProperty A I hI X)
    (hO : (derivedCompleteProperty A I).leftOrthogonal X) : IsZero X := by
  obtain ⟨s, hs⟩ := hI
  obtain ⟨Y, -, hOY, hnil, hzero⟩ := exists_nilpotent_of_derivedPowerTorsion_of_leftOrthogonal
    ⟨s, hs⟩ s (fun a ha => hs ▸ Ideal.subset_span ha) X hX hO
  refine hzero ((IsZero.iff_id_eq_zero Y).2 (hOY (𝟙 Y) fun a ha => ?_))
  let J : Ideal A := RingHom.ker (algebraMap A (End Y))
  have hj : I ≤ J.radical := by
    rw [← hs, Ideal.span_le]
    intro b hb
    obtain ⟨n, hn⟩ := hnil b hb
    refine ⟨n, ?_⟩
    rw [RingHom.mem_ker, Algebra.algebraMap_eq_smul_one]
    ext
    simpa using hn
  obtain ⟨n, hn⟩ := hj ha
  exact isDerivedCompleteAt_of_isNilpotent ⟨n, by
    rw [← Algebra.algebraMap_eq_smul_one, ← map_pow]; exact hn⟩

/-- A torsion complex whose derived completion vanishes is zero. -/
private theorem isZero_of_derivedCompletion_isZero (hI : I.FG)
    (C : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCompleteDerivedCategory A I)
    (adj : C ⊣ (derivedCompleteProperty A I).ι) (X : DerivedCategory (ModuleCat.{v} A))
    (hX : derivedPowerTorsionProperty A I hI X) (hz : IsZero (C.obj X)) : IsZero X := by
  apply isZero_of_derivedPowerTorsion_of_leftOrthogonal hI X hX
  intro Y g hY
  have h : (adj.homEquiv X ⟨Y, hY⟩).symm g = 0 := hz.eq_of_src _ _
  rw [← (adj.homEquiv X ⟨Y, hY⟩).apply_symm_apply g, h, adj.homEquiv_unit]
  simp

/-- A map of torsion complexes inverted by derived completion is itself invertible: its cone is
torsion and has vanishing completion. -/
private theorem isIso_of_derivedCompletion_map_isIso (hI : I.FG)
    (C : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCompleteDerivedCategory A I)
    (adj : C ⊣ (derivedCompleteProperty A I).ι)
    {X Y : DerivedCategory (ModuleCat.{v} A)} (g : X ⟶ Y)
    (hX : derivedPowerTorsionProperty A I hI X) (hY : derivedPowerTorsionProperty A I hI Y)
    [IsIso (C.map g)] : IsIso g := by
  let := adj.leftAdjointCommShift ℤ
  let := adj.commShift_of_rightAdjoint ℤ
  have : C.IsTriangulated := adj.isTriangulated_leftAdjoint
  obtain ⟨Z, p, q, hT⟩ := distinguished_cocone_triangle g
  let T := Triangle.mk g p q
  have hZ := (derivedPowerTorsionProperty A I hI).ext_of_isTriangulatedClosed₃ T hT hX hY
  have hz : IsZero (C.obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ (C.mapTriangle.obj T) (C.map_distinguished T hT)).2
      (show IsIso (C.map g) from inferInstance)
  exact (Triangle.isZero₃_iff_isIso₁ T hT).1
    (isZero_of_derivedCompletion_isZero hI C adj Z hZ hz)

/-- **The equivalence of Stacks 0A6X exists.** The composite of the two coreflections is an
adjoint equivalence: its counit is invertible by Stacks 0A6W, and its unit then follows from the
triangle identity together with the vanishing of a torsion complex with zero completion. -/
theorem nonempty_torsionCompleteEquivalence (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) :
    Nonempty (Σ E : PowerTorsionDerivedCategory.{u, v} A I hI ≌
        DerivedCompleteDerivedCategory A I,
      (E.functor ≅ ((derivedPowerTorsionProperty A I hI).ι ⋙ derivedCompletion A I hI)) ×
      (E.inverse ≅ ((derivedCompleteProperty A I).ι ⋙ localCohomologyFunctor A I hI))) := by
  let P := derivedPowerTorsionProperty.{u, v} A I hI
  let Q := derivedCompleteProperty.{u, v} A I
  let C := derivedCompletion.{u, v} A I hI
  let adjG := localCohomologyAdjunction.{u, v} A I hI
  let adjC := (derivedCompletionReflection.{u, v} A I hI).2
  let adj := adjG.comp adjC
  have hcounit (Y : Q.FullSubcategory) : IsIso (adj.counit.app Y) := by
    rw [Adjunction.comp_counit_app]
    have : IsIso (Q.ι.map (C.map (adjG.counit.app (Q.ι.obj Y)))) := by
      change IsIso ((C ⋙ Q.ι).map (adjG.counit.app (Q.ι.obj Y)))
      exact isIso_derivedCompletion_map_localCohomologyCounit A I hI C adjC (Q.ι.obj Y)
    have h₁ : IsIso (C.map (adjG.counit.app (Q.ι.obj Y))) := isIso_of_reflects_iso _ Q.ι
    let := Q.fullyFaithfulι
    exact IsIso.comp_isIso' h₁ inferInstance
  have hunit (X : P.FullSubcategory) : IsIso (adj.unit.app X) := by
    have h : IsIso ((P.ι ⋙ C).map (adj.unit.app X) ≫ adj.counit.app ((P.ι ⋙ C).obj X)) := by
      rw [show (P.ι ⋙ C).map (adj.unit.app X) ≫
        adj.counit.app ((P.ι ⋙ C).obj X) = 𝟙 _ from adj.left_triangle_components X]
      infer_instance
    have hm : IsIso (C.map (P.ι.map (adj.unit.app X))) := by
      change IsIso ((P.ι ⋙ C).map (adj.unit.app X))
      exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (hcounit _) h
    have : IsIso (P.ι.map (adj.unit.app X)) :=
      isIso_of_derivedCompletion_map_isIso hI C adjC _ X.property
        ((Q.ι ⋙ localCohomologyFunctor A I hI).obj ((P.ι ⋙ C).obj X)).property
    exact isIso_of_reflects_iso _ P.ι
  have : ∀ X, IsIso (adj.unit.app X) := hunit
  have : ∀ Y, IsIso (adj.counit.app Y) := hcounit
  exact ⟨⟨adj.toEquivalence, Iso.refl _, Iso.refl _⟩⟩

/-- **Stacks 0A6X.** For a finitely generated ideal `I` of a commutative ring `A` and `Z = V(I)`,
derived `I`-completion and local cohomology with support in `Z` are quasi-inverse equivalences
between the full subcategory of `D(A)` of complexes with `I`-power-torsion cohomology and the
full subcategory of derived `I`-complete complexes. The two functors of the equivalence are
identified with derived completion and local cohomology by natural isomorphisms, not merely
objectwise. -/
@[stacks 0A6X]
def torsionCompleteEquivalence (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Σ E : PowerTorsionDerivedCategory.{u, v} A I hI ≌ DerivedCompleteDerivedCategory A I,
      (E.functor ≅ ((derivedPowerTorsionProperty A I hI).ι ⋙ derivedCompletion A I hI)) ×
      (E.inverse ≅ ((derivedCompleteProperty A I).ι ⋙ localCohomologyFunctor A I hI)) :=
  Classical.choice (nonempty_torsionCompleteEquivalence A I hI)

end Dualizing

end
