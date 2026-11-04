module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummandsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEIsoOfCohomologyIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMapGeneral

/-!
# The lowest term of a complex quasi-isomorphic to a bounded flat complex

Let `(C, O)` be a ringed site and let `β : P ⟶ T` be a quasi-isomorphism of bounded complexes of
`O`-modules. Suppose that every term of `P` is flat, that `P` and `T` vanish below degree `a`, and
that every term of `T` above degree `a` is flat. Then the remaining term `T^a` is flat as well.

This is the step which, in the proof that a perfect object is detected after a flat pullback,
replaces the Tor-amplitude argument of Stacks 08G7: if a complex `T = [N ⟶ T^{a+1} ⟶ ⋯]` with
flat terms above `a` represents, locally, an object which is also represented by a strictly
perfect complex living in degrees `≥ a`, then `N` is flat.

## Main results

* `HomologicalComplex.shortExact_iCycles_toCycles`: for an acyclic complex, the cycles, a term
  and the next cycles form a short exact sequence.
* `CochainComplex.prop_X_of_acyclic`: in a bounded above acyclic complex, a property of objects
  which contains the zero objects, is invariant under isomorphism and satisfies the two halves
  of a two-out-of-three condition for short exact sequences, holds at the term in degree `n` as
  soon as it holds above `n` and at `n - 1`, and the term in degree `n - 2` vanishes.
* `Stacks.SheafOfModules.isFlat_X_of_quasiIso`: the statement above.
* `Stacks.SheafOfModules.exists_coveringSieve_isFlat_X_of_derivedIso`: its local form, for a
  strictly perfect `P` and an isomorphism `P ≅ T` of the derived category, through Stacks 08FR.

## Implementation notes

The argument is the cone of `β`: it is an acyclic bounded complex whose terms
`P^{i+1} ⊕ T^i` are flat in every degree except possibly `a`, and which vanishes below `a - 1`.
Descending through the short exact sequences `0 ⟶ Z^i ⟶ C^i ⟶ Z^{i+1} ⟶ 0`, the cycles are flat
above `a` by Stacks 03EY (2); in degree `a` the cycles are `C^{a-1} = P^a`, so Stacks 03EY (1)
makes `C^a` flat, and `T^a` is a direct summand of it. No derived tensor product occurs, so the
universes of the site are free, which is what the small étale site of a scheme needs.

## References

* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

section Abstract

variable {A : Type*} [Category A] [Abelian A]

/-- **The cycles, a term and the next cycles of an acyclic complex form a short exact
sequence**: `0 ⟶ Z^i ⟶ K^i ⟶ Z^{i+1} ⟶ 0`, as soon as `K` is exact in degree `i + 1`. -/
theorem HomologicalComplex.shortExact_iCycles_toCycles (K : CochainComplex A ℤ) (i : ℤ)
    (hK : K.ExactAt (i + 1)) :
    (ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1))
      (by rw [← cancel_mono (K.iCycles (i + 1))]; simp)).ShortExact := by
  have hexact : (ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1))).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (K.cyclesIsKernel i (i + 1) (by simp))
  have hepi : Epi (K.toCycles i (i + 1)) :=
    Preadditive.epi_of_isZero_cokernel' _ (K.homologyIsCokernel i (i + 1) (by simp))
      hK.isZero_homology
  refine { exact := ?_, mono_f := inferInstance, epi_g := hepi }
  refine (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := K.iCycles (i + 1) } (S₁ := ShortComplex.mk (K.iCycles i)
      (K.toCycles i (i + 1)) (by rw [← cancel_mono (K.iCycles (i + 1))]; simp))
      (S₂ := ShortComplex.mk (K.iCycles i) (K.d i (i + 1)) (K.iCycles_d i (i + 1)))).2 hexact

variable (p : A → Prop)

/-- **A property descends through the cycles of a bounded above acyclic complex.** If `p`
contains the zero objects and satisfies Stacks 03EY (2) — in a short exact sequence whose middle
and right terms have `p`, so has the left one — then in an acyclic complex which vanishes above
`b` and has `p` in every degree above `n`, the cycles have `p` in every degree above `n`. -/
theorem CochainComplex.prop_cycles_of_acyclic
    (hzero : ∀ X : A, IsZero X → p X)
    (hleft : ∀ S : ShortComplex A, S.ShortExact → p S.X₂ → p S.X₃ → p S.X₁)
    (K : CochainComplex A ℤ) (hK : ∀ i, K.ExactAt i) (n b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hp : ∀ i, n < i → p (K.X i)) :
    ∀ i, n < i → p (K.cycles i) := by
  have key : ∀ k : ℕ, ∀ i, n < i → b + 1 - k ≤ i → p (K.cycles i) := by
    intro k
    induction k with
    | zero =>
      intro i _ hi
      refine hzero _ ?_
      have hz : IsZero (K.X i) := hb i (by omega)
      exact IsZero.of_mono (K.iCycles i) hz
    | succ k ih =>
      intro i hni hi
      by_cases h : b + 1 - k ≤ i
      · exact ih i hni h
      · have hS := HomologicalComplex.shortExact_iCycles_toCycles K i (hK (i + 1))
        exact hleft _ hS (hp i hni) (ih (i + 1) (by omega) (by omega))
  intro i hi
  exact key (Int.toNat (b + 1 - i)) i hi (by omega)

/-- **A property of the middle term of a bounded above acyclic complex.** If `p` contains the
zero objects, is invariant under isomorphism and satisfies both halves of Stacks 03EY, then in
an acyclic complex which vanishes above `b` and in degree `n - 2`, and has `p` in degree `n - 1`
and in every degree above `n`, the term in degree `n` has `p`. -/
theorem CochainComplex.prop_X_of_acyclic
    (hiso : ∀ {X Y : A}, (X ≅ Y) → p X → p Y)
    (hzero : ∀ X : A, IsZero X → p X)
    (hleft : ∀ S : ShortComplex A, S.ShortExact → p S.X₂ → p S.X₃ → p S.X₁)
    (hmid : ∀ S : ShortComplex A, S.ShortExact → p S.X₁ → p S.X₃ → p S.X₂)
    (K : CochainComplex A ℤ) (hK : ∀ i, K.ExactAt i) (n b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hp : ∀ i, n < i → p (K.X i))
    (hn₁ : p (K.X (n - 1))) (hn₂ : IsZero (K.X (n - 2))) :
    p (K.X n) := by
  have hZ : p (K.cycles (n + 1)) :=
    CochainComplex.prop_cycles_of_acyclic p hzero hleft K hK n b hb hp (n + 1) (by omega)
  -- The cycles in degree `n - 1` vanish: they are the image of `K^{n-2} = 0`.
  have hS₂ := HomologicalComplex.shortExact_iCycles_toCycles K (n - 2) (hK (n - 2 + 1))
  have hz₁ : IsZero (K.cycles (n - 1)) := by
    have := hS₂.epi_g
    have : IsZero (K.cycles (n - 2 + 1)) :=
      IsZero.of_epi (K.toCycles (n - 2) (n - 2 + 1)) hn₂
    simpa [show n - 2 + 1 = n - 1 by omega] using this
  -- Hence `K^{n-1} ⟶ Z^n` is an isomorphism.
  have hS₁ := HomologicalComplex.shortExact_iCycles_toCycles K (n - 1) (hK (n - 1 + 1))
  have hmono : Mono (K.toCycles (n - 1) (n - 1 + 1)) :=
    hS₁.exact.mono_g (hz₁.eq_of_src _ _)
  have : IsIso (K.toCycles (n - 1) (n - 1 + 1)) := by
    have := hS₁.epi_g
    exact isIso_of_mono_of_epi _
  have hZn : p (K.cycles (n - 1 + 1)) := hiso (asIso (K.toCycles (n - 1) (n - 1 + 1))) hn₁
  have hZn' : p (K.cycles n) := by simpa [show n - 1 + 1 = n by omega] using hZn
  exact hmid _ (HomologicalComplex.shortExact_iCycles_toCycles K n (hK (n + 1))) hZn' hZ

end Abstract

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A binary biproduct of flat `O`-modules is flat, by Stacks 03EY (1). -/
theorem isFlat_biprod {M N : AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y}
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) N) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) (M ⊞ N) :=
  FlatTwoOutOfThree.isFlat_middle_of_shortExact Y.O
    (ShortComplex.mk (biprod.inl : M ⟶ M ⊞ N) (biprod.snd : M ⊞ N ⟶ N) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct M N).shortExact hM hN

/-- The mapping cone of a quasi-isomorphism is acyclic. -/
private theorem exactAt_mappingCone {P T : CochainComplex
    (AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y) ℤ} (β : P ⟶ T) [QuasiIso β] (i : ℤ) :
    (CochainComplex.mappingCone β).ExactAt i := by
  have h : QuasiIso β ↔ ∀ n : ℤ, (CochainComplex.mappingCone β).ExactAt n := by
    rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
      HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic _).trW_iff_of_distinguished _
        (HomotopyCategory.mappingCone_triangleh_distinguished β)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt _)
  exact h.1 inferInstance i

/-- **The lowest term of a complex quasi-isomorphic to a bounded flat complex is flat.** Let
`β : P ⟶ T` be a quasi-isomorphism of complexes of `O`-modules, both vanishing below `a` and
above `b`, with every term of `P` flat and every term of `T` above degree `a` flat. Then `T^a` is
flat. -/
theorem isFlat_X_of_quasiIso {P T : CochainComplex
    (AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y) ℤ} (β : P ⟶ T) (hβ : QuasiIso β) (a b : ℤ)
    (hP : ∀ i, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) (P.X i))
    (hPa : ∀ i, i < a → IsZero (P.X i)) (hTa : ∀ i, i < a → IsZero (T.X i))
    (hT : ∀ i, a < i → AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) (T.X i))
    (hPb : ∀ i, b < i → IsZero (P.X i)) (hTb : ∀ i, b < i → IsZero (T.X i)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) (T.X a) := by
  let K := CochainComplex.mappingCone β
  let e : ∀ i, K.X i ≅ P.X (i + 1) ⊞ T.X i := fun i =>
    HomologicalComplex.homotopyCofiber.XIsoBiprod β i (i + 1) rfl
  let Flat : AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y → Prop := fun M =>
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := Y.O) M
  have hiso : ∀ {M N : AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y}, (M ≅ N) → Flat M →
      Flat N := fun e h => FlatRetract.isFlat_of_iso Y.O e h
  have hzero : ∀ M : AlgebraicGeometry.RingedSite.Modules.{u, v, w} Y, IsZero M → Flat M :=
    fun M hM => DerivedTensorProduct.isFlat_of_isZero M hM
  have hKa : Flat (K.X a) :=
    CochainComplex.prop_X_of_acyclic Flat hiso hzero
      (fun S hS h₂ h₃ => FlatTwoOutOfThree.isFlat_left_of_shortExact Y.O S hS h₂ h₃)
      (fun S hS h₁ h₃ => FlatTwoOutOfThree.isFlat_middle_of_shortExact Y.O S hS h₁ h₃)
      K (fun i => (have := hβ; exactAt_mappingCone β i)) a b
      (fun i hi => (CochainComplex.mappingCone.isZero_X_iff β i).2 ⟨hPb _ (by omega), hTb _ hi⟩)
      (fun i hi => hiso (e i).symm (isFlat_biprod (hP _) (hT i hi)))
      (hiso (e (a - 1)).symm (isFlat_biprod (hP _) (hzero _ (hTa _ (by omega)))))
      ((CochainComplex.mappingCone.isZero_X_iff β (a - 2)).2 ⟨hPa _ (by omega), hTa _ (by omega)⟩)
  exact FlatRetract.isFlat_of_retract Y.O (biprod.inr ≫ (e a).inv) ((e a).hom ≫ biprod.snd)
    (by simp) hKa

/-- A strictly perfect complex vanishes above some degree. -/
theorem exists_isZero_X_gt_of_isStrictlyPerfect {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    {P : CochainComplex (_root_.SheafOfModules.{w} R) ℤ} (hP : IsStrictlyPerfect R P) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i) := by
  obtain ⟨r, hr⟩ := hP.bounded.bddAbove
  refine ⟨r, fun i hi => ?_⟩
  by_contra h
  exact absurd (hr (by simpa only [Set.mem_ofPred_eq] using h)) (by omega)

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Sheafification on a slice, at the spelling of the localized ringed site. -/
local instance flatLowestTermSliceHasSheafify (W : X.C) :
    HasSheafify (X.over W).J AddCommGrpCat.{w} :=
  (inferInstance : ∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{w}) W

/-- Local bijectivity of the weak equivalences on a slice, at the localized spelling. -/
local instance flatLowestTermSliceWEqualsLocallyBijective (W : X.C) :
    (X.over W).J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  (inferInstance : ∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}) W

/-- **The local form: a complex isomorphic in the derived category to a strictly perfect complex
living in degrees `≥ a` has, locally, a flat term in degree `a`.** Let `Z` be an object of the
site and let `P`, `T` be complexes of `O|_Z`-modules with `P` strictly perfect, an isomorphism
`P ≅ T` in `D(O|_Z)`, both vanishing below `a`, `T` vanishing above `b` and with every term of
`T` above degree `a` a direct summand of a finite free module. Then over the members of a covering
sieve of `Z` the restriction of `T^a` is flat.

Stacks 08FR turns the derived isomorphism into a quasi-isomorphism of complexes over a covering,
and `isFlat_X_of_quasiIso` applies there. -/
theorem exists_coveringSieve_isFlat_X_of_derivedIso (Z : X.C)
    [HasDerivedCategory.{d} (_root_.SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z))]
    {P T : CochainComplex (_root_.SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z) P)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj T) (a b : ℤ)
    (hPa : ∀ i, i < a → IsZero (P.X i)) (hTa : ∀ i, i < a → IsZero (T.X i))
    (hTb : ∀ i, b < i → IsZero (T.X i))
    (hT : ∀ i, a < i →
      IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z) (T.X i)) :
    ∃ S : Sieve Z, S ∈ X.J Z ∧ ∀ ⦃Z' : X.C⦄ (f : Z' ⟶ Z), S f →
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, max u v, w, w} (O := (X.over Z').O)
        ((_root_.SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).obj
          (T.X a)) := by
  obtain ⟨S, hS, hβ⟩ :=
    AlgebraicGeometry.RingedSite.exists_coveringSieve_quasiIso_of_derivedIso_general X Z hP e
  refine ⟨S, hS, fun Z' f hf => ?_⟩
  obtain ⟨β, hβ⟩ := hβ f hf
  obtain ⟨c, hc⟩ := exists_isZero_X_gt_of_isStrictlyPerfect hP
  let H := _root_.SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  exact isFlat_X_of_quasiIso (Y := X.over Z') β hβ a (max b c)
    (isFlat_X_of_isStrictlyPerfect_general (Y := X.over Z')
      (isStrictlyPerfect_restrictComplexAlong_general _ f hP))
    (fun i hi => H.map_isZero (hPa i hi)) (fun i hi => H.map_isZero (hTa i hi))
    (fun i hi => isFlat_of_isDirectSummandOfFiniteFree_general (Y := X.over Z') _
      (isDirectSummandOfFiniteFree_overMap_general _ f (hT i hi)))
    (fun i hi => H.map_isZero (hc i (by omega))) (fun i hi => H.map_isZero (hTb i (by omega)))

/-- **The lowest opcycles of a strictly perfect approximation are locally flat.** Let `Z` be an
object of the site, `β : Y ⟶ Y'` a morphism of complexes of `O|_Z`-modules with `Y` strictly
perfect, invertible on cohomology in degrees `≥ a`, with `Y'` acyclic below `a`, and suppose `Y'`
is isomorphic in `D(O|_Z)` to a strictly perfect complex `P` vanishing below `a`. Then over the
members of a covering sieve of `Z` the restriction of the opcycles `Coker(Y^{a-1} ⟶ Y^a)` is flat.

The canonical truncation `τ_{≥ a}Y` represents `Y'` (`exists_iso_Q_truncGE_of_isIso_homologyMap`)
and has the opcycles as its term in degree `a`, so `exists_coveringSieve_isFlat_X_of_derivedIso`
applies to it. -/
theorem exists_coveringSieve_isFlat_opcycles (Z : X.C)
    [HasDerivedCategory.{d} (_root_.SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z))]
    {P Y Y' : CochainComplex (_root_.SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z) P)
    (hY : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z) Y)
    (β : Y ⟶ Y') (a : ℤ) (hβ : ∀ i, a ≤ i → IsIso (HomologicalComplex.homologyMap β i))
    (hY' : ∀ i, i < a → IsZero (Y'.homology i))
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Y')
    (hPa : ∀ i, i < a → IsZero (P.X i)) :
    ∃ S : Sieve Z, S ∈ X.J Z ∧ ∀ ⦃Z' : X.C⦄ (f : Z' ⟶ Z), S f →
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, max u v, w, w} (O := (X.over Z').O)
        ((_root_.SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).obj
          (Y.opcycles a)) := by
  have : (DerivedCategory.Q.obj Y').IsGE a := (DerivedCategory.isGE_iff _ _).2 fun i hi =>
    (hY' i hi).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app Y')
  obtain ⟨e'⟩ := CochainComplex.exists_iso_Q_truncGE_of_isIso_homologyMap a β hβ
  obtain ⟨b, hb⟩ := exists_isZero_X_gt_of_isStrictlyPerfect hY
  obtain ⟨S, hS, h⟩ := exists_coveringSieve_isFlat_X_of_derivedIso X Z hP (e ≪≫ e'.symm) a
    (max a b) hPa (fun i hi => (Y.truncGE a).isZero_of_isStrictlyGE a i hi)
    (fun i hi => (hb i (by omega)).of_iso (Y.truncGEXIso a i (by omega)))
    (fun i hi => IsDirectSummandOfFiniteFree.of_iso _ (Y.truncGEXIso a i hi)
      (hY.termDirectSummand i))
  refine ⟨S, hS, fun Z' f hf => ?_⟩
  exact FlatRetract.isFlat_of_iso (X.over Z').O
    ((_root_.SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapIso
      (Y.truncGEXIsoOpcycles a)) (h f hf)

end Stacks.SheafOfModules

end
