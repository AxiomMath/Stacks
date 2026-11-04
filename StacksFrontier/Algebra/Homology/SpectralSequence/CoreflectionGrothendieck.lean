module

public import StacksFrontier.Algebra.Homology.SpectralSequence.WeakSerreDescent
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Coreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.AbelianSheafSpectralSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Grothendieck spectral sequence read through two coreflections

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories with enough
injectives, `F` carrying injectives to `G`-acyclic objects, so that the Grothendieck spectral
sequence `R^pG(R^qF M) ⟹ R^{p+q}(G ∘ F) M` exists ([Stacks, Tag 015N]). Suppose given on `ℬ`
and on `𝒞` the data of a coreflection onto a full subcategory through a weak Serre class, as in
`StacksFrontier/CategoryTheory/Abelian/DeltaFunctor/Coreflection.lean`:

* `i_ℬ : 𝒬 ⥤ ℬ`, fully faithful, with right adjoint `Q_ℬ`, landing in a weak Serre class `L_ℬ`
  on which `Q_ℬ` is right exact, and likewise `(i_𝒞, Q_𝒞, L_𝒞)` on `𝒞`.

This is the shape of `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳) ⊆ Mod(𝒪_𝒳)` with the coherator `Q` of an
algebraic stack ([Stacks, Tag 0771], [Stacks, Tag 0778], [Stacks, Tag 0779]). If `R^qF M` lies in
`L_ℬ`, `R^pG` carries `L_ℬ` into `L_𝒞`, and `Q_𝒞 ∘ R^pG` kills the objects of `L_ℬ` killed by
`Q_ℬ`, then there is a spectral sequence of `𝒬_𝒞` with

`E_2^{p,q} = Q_𝒞(R^pG(i_ℬ(Q_ℬ(R^qF M))))  ⟹  Q_𝒞(R^{p+q}(G ∘ F) M)`.

This is the proof of [Stacks, Tag 0783] for abstract categories: apply the exact functor `Q_𝒞`
to the Grothendieck spectral sequence, which is possible from the second page on because every
term of the second page lies in `L_𝒞`
(`CategoryTheory.SpectralSequence.exists_map_abutsTo_of_isWeakSerreClass'`), and identify the
second page through the counit `i_ℬ(Q_ℬ X) ⟶ X`, whose kernel and cokernel are killed by `Q_ℬ`
and hence by `Q_𝒞 ∘ R^pG`
(`CategoryTheory.DeltaFunctor.isIso_map_map_of_isIso_map`, applied to the δ-functor of the right
derived functors of `G`).

## Main definitions

* `CategoryTheory.Limits.extendNatByZero`: an `ℕ`-graded object read as a `ℤ`-graded one, zero in
  negative degrees.

## Main results

* `CategoryTheory.Functor.exists_spectralSequence_rightDerived_comp_coreflection`: the spectral
  sequence above, with its second page and its abutment stated with Mathlib's `ℕ`-indexed right
  derived functors `CategoryTheory.Functor.rightDerived`.

## Implementation notes

The Grothendieck spectral sequence is
`CategoryTheory.Functor.exists_abutsTo_homology_rightDerivedFunctorPlus_comp`, whose second page
lies in `L_𝒞` only from page `2` on, so it is read from page `2`
(`CategoryTheory.SpectralSequence.shiftStart`) before being pushed along `Q_𝒞`. The derived
categories it needs are the standard ones, chosen inside the proof, so that the statement does
not depend on them. The hypothesis that `F` preserves injectives (rather than that `F(I)` be
`G`-acyclic) is the one available for the direct image along a 1-morphism of algebraic stacks,
whose inverse image is exact.

## References

* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 0783](https://stacks.math.columbia.edu/tag/0783)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open ZeroObject

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜]
  {ℬ : Type u₂} [Category.{v₂} ℬ] [Abelian ℬ]
  {𝒞 : Type u₃} [Category.{v₃} 𝒞] [Abelian 𝒞]
  [EnoughInjectives 𝒜] [EnoughInjectives ℬ]
  {𝒬 : Type u₄} [Category.{v₄} 𝒬] [Preadditive 𝒬]
  {ℛ : Type u₅} [Category.{v₅} ℛ] [Abelian ℛ]
  {iB : 𝒬 ⥤ ℬ} {QB : ℬ ⥤ 𝒬} (adjB : iB ⊣ QB) [iB.Full] [iB.Faithful] [QB.Additive]
  (LB : ObjectProperty ℬ) [LB.IsWeakSerreClass] (hiB : ∀ X, LB (iB.obj X))
  [PreservesFiniteColimits (LB.ι ⋙ QB)]
  {iC : ℛ ⥤ 𝒞} {QC : 𝒞 ⥤ ℛ} (adjC : iC ⊣ QC) [iC.Full] [iC.Faithful] [QC.Additive]
  (LC : ObjectProperty 𝒞) [LC.IsWeakSerreClass] (hiC : ∀ X, LC (iC.obj X))
  [PreservesFiniteColimits (LC.ι ⋙ QC)]

/-- The `ℤ`-graded object of an `ℕ`-graded one, zero in negative degrees: the abutment of a
first quadrant spectral sequence converging to an `ℕ`-graded object. -/
def _root_.CategoryTheory.Limits.extendNatByZero {𝒟 : Type*} [Category 𝒟] [HasZeroObject 𝒟]
    (H : ℕ → 𝒟) : ℤ → 𝒟
  | (n : ℕ) => H n
  | .negSucc _ => 0

/-- In a degree `n : ℕ`, `extendNatByZero H` is `H n`. -/
@[simp]
lemma _root_.CategoryTheory.Limits.extendNatByZero_natCast {𝒟 : Type*} [Category 𝒟]
    [HasZeroObject 𝒟] (H : ℕ → 𝒟) (n : ℕ) : extendNatByZero H n = H n :=
  rfl

/-- In every negative degree, `extendNatByZero H` is a zero object. -/
lemma _root_.CategoryTheory.Limits.isZero_extendNatByZero_negSucc {𝒟 : Type*} [Category 𝒟]
    [HasZeroObject 𝒟] (H : ℕ → 𝒟) (n : ℕ) : IsZero (extendNatByZero H (.negSucc n)) :=
  isZero_zero 𝒟

/-- A weak Serre class containing the `ℕ`-indexed `R^mF X` contains all the `ℤ`-indexed
`R^qF X`, since these vanish in negative degrees. -/
private theorem prop_rightDerivedPlus_obj {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [EnoughInjectives C] [HasDerivedCategory C]
    [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] (P : ObjectProperty D) [P.IsWeakSerreClass]
    (X : C) (h : ∀ m : ℕ, P ((F.rightDerived m).obj X)) (q : ℤ) :
    P ((F.rightDerivedPlus q).obj X) := by
  rcases lt_or_ge q 0 with hq | hq
  · exact P.prop_of_isZero (isZero_rightDerivedPlus_of_neg F X q hq)
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact P.prop_of_iso ((Stacks.DerivedIndexing.rightDerivedIso F m).app X) (h m)

variable (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ 𝒞) (H : 𝒜 ⥤ 𝒞) [F.Additive] [G.Additive] [H.Additive]

include adjB hiB adjC hiC in
/-- **The Grothendieck spectral sequence read through two coreflections.** Let `F : 𝒜 ⥤ ℬ` and
`G : ℬ ⥤ 𝒞` be additive functors between abelian categories with enough injectives, with
`F` carrying injectives to injectives, and let `H ≅ F ⋙ G`. Let `(i_ℬ, Q_ℬ, L_ℬ)` and
`(i_𝒞, Q_𝒞, L_𝒞)` be coreflections of `ℬ` and `𝒞` onto full subcategories `𝒬` and `ℛ` through
weak Serre classes, `Q` being right exact on `L`. Let `X` be an object of `𝒜` such that

* `R^qF X` lies in `L_ℬ` for every `q` (`hX`),
* `R^pG` carries `L_ℬ` into `L_𝒞` (`hG`), and
* `Q_𝒞 ∘ R^pG` kills every object of `L_ℬ` killed by `Q_ℬ` (`hGQ`).

Then there is a spectral sequence of `ℛ` with second page

`E_2^{p,q} = Q_𝒞(R^pG(i_ℬ(Q_ℬ(R^qF X))))`, zero outside the first quadrant,

converging to `Q_𝒞(R^n H X)` (`n ≥ 0`, zero for `n < 0`).

For algebraic stacks this is [Stacks, Tag 0783]: `F = f_*`, `G = g_*`, `H = (g ∘ f)_*`,
`Q = Q_𝒴, Q_𝒵` the coherators and `L = LQCoh^fbc`. -/
@[sga "4 V 5.4" "more general",
  sga "4½ Arcata 2.3.3" "more general",
  sga "4½ Arcata 2.3.4" "more general"]
theorem exists_spectralSequence_rightDerived_comp_coreflection
    (hinj : ∀ I : 𝒜, Injective I → Injective (F.obj I)) (e : F ⋙ G ≅ H) (X : 𝒜)
    (hX : ∀ q : ℕ, LB ((F.rightDerived q).obj X))
    (hG : ∀ Y, LB Y → ∀ p : ℕ, LC ((G.rightDerived p).obj Y))
    (hGQ : ∀ Y, LB Y → IsZero (QB.obj Y) → ∀ p : ℕ, IsZero (QC.obj ((G.rightDerived p).obj Y))) :
    ∃ E : CohomologicalSpectralSequence ℛ 2,
      (∀ p q : ℕ, Nonempty ((E.page 2 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
        QC.obj ((G.rightDerived p).obj (iB.obj (QB.obj ((F.rightDerived q).obj X)))))) ∧
      (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((E.page 2 le_rfl).X (p, q))) ∧
      SpectralSequence.AbutsTo E
        (extendNatByZero fun n => QC.obj ((H.rightDerived n).obj X)) := by
  let := HasDerivedCategory.standard 𝒜
  let := HasDerivedCategory.standard ℬ
  let := HasDerivedCategory.standard 𝒞
  -- the Grothendieck spectral sequence, read from the second page
  obtain ⟨K, hK⟩ := exists_abutsTo_homology_rightDerivedFunctorPlus_comp F G
    (fun I hI => Stacks.Cohomology.Leray.rightAcyclic_of_injective G (F.obj I) (hinj I hI))
    ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X)
  obtain ⟨E₀, -, hE₂, habuts₀⟩ := hK _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  let E := E₀.shiftStart (show (0 : ℤ) ≤ 2 by omega)
  have habuts : SpectralSequence.AbutsTo E _ := habuts₀.shiftStart (show (0 : ℤ) ≤ 2 by omega)
  -- the `ℤ`-indexed and `ℕ`-indexed derived functors
  have hXplus : ∀ q : ℤ, LB ((F.rightDerivedPlus q).obj X) :=
    prop_rightDerivedPlus_obj F LB X hX
  have hGplus : ∀ Y, LB Y → ∀ p : ℤ, LC ((G.rightDerivedPlus p).obj Y) := fun Y hY =>
    prop_rightDerivedPlus_obj G LC Y (hG Y hY)
  -- the second page lies in `L_𝒞`
  have hpage : ∀ pq : ℤ × ℤ, LC ((E.page 2 le_rfl).X pq) := fun ⟨p, q⟩ =>
    LC.prop_of_iso (hE₂ p q).some.symm (hGplus _ (hXplus q) p)
  -- transport along the coherator of `𝒞`, exact on `L_𝒞`
  have := DeltaFunctor.preservesFiniteLimits_ι_comp adjC LC
  have : (LC.ι ⋙ QC).PreservesMonomorphisms := inferInstance
  obtain ⟨E', hE', habuts'⟩ :=
    SpectralSequence.exists_map_abutsTo_of_isWeakSerreClass' LC QC hpage habuts
  -- the δ-functor of the right derived functors of `G`
  let D : DeltaFunctor ℬ 𝒞 := Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor G
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure G) _ (fun _ _ => rfl)
  have hD : ∀ Y, LB Y → ∀ n, LC ((D.functor n).obj Y) := fun Y hY n => hGplus Y hY n
  have hDQ : ∀ Y, LB Y → IsZero (QB.obj Y) → ∀ n, IsZero (QC.obj ((D.functor n).obj Y)) :=
    fun Y hY hQ n => (hGQ Y hY hQ n).of_iso
      (QC.mapIso ((Stacks.DerivedIndexing.rightDerivedIso G n).app Y).symm)
  refine ⟨E', fun p q => ?_, fun p q hpq => ?_, ?_⟩
  · -- the second page, through the counit of the coreflection of `ℬ`
    let Y := (F.rightDerivedPlus q).obj X
    have : IsIso (QB.map (adjB.counit.app Y)) := by
      have : IsIso (adjB.unit.app (QB.obj Y) ≫ QB.map (adjB.counit.app Y)) := by
        rw [adjB.right_triangle_components Y]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (adjB.unit.app (QB.obj Y)) _
    have hk : IsIso (QC.map ((D.functor p).map (adjB.counit.app Y))) :=
      DeltaFunctor.isIso_map_map_of_isIso_map adjB LB hiB adjC LC hiC D hD hDQ
        (adjB.counit.app Y) (hiB _) (hXplus q) p
    exact ⟨(hE' 2 le_rfl (p, q)).some ≪≫ QC.mapIso (hE₂ p q).some ≪≫
      (asIso (QC.map ((D.functor p).map (adjB.counit.app Y)))).symm ≪≫
      QC.mapIso (((Stacks.DerivedIndexing.rightDerivedIso G p).app _).symm ≪≫
        (G.rightDerived p).mapIso (iB.mapIso (QB.mapIso
          ((Stacks.DerivedIndexing.rightDerivedIso F q).app X).symm)))⟩
  · refine (QC.map_isZero (IsZero.of_iso ?_ (hE₂ p q).some)).of_iso (hE' 2 le_rfl (p, q)).some
    rcases lt_or_ge p 0 with hp | hp
    · exact isZero_rightDerivedPlus_of_neg G _ p hp
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      have hq : q < 0 := hpq.resolve_left (by omega)
      have := D.additive m
      exact (D.functor m).map_isZero (isZero_rightDerivedPlus_of_neg F X q hq)
  · refine habuts'.of_nonempty_iso fun n => ?_
    cases n with
    | ofNat m =>
      exact ⟨QC.mapIso ((DerivedCategory.Plus.homologyFunctor 𝒞 m).mapIso
        ((rightDerivedFunctorPlusNatIso e).app _) ≪≫
          ((Stacks.DerivedIndexing.rightDerivedIso H m).app X).symm)⟩
    | negSucc m =>
      exact ⟨(QC.map_isZero (isZero_rightDerivedPlus_of_neg (F ⋙ G) X _
        (Int.negSucc_lt_zero m))).iso (isZero_extendNatByZero_negSucc _ m)⟩

end CategoryTheory.Functor

end
