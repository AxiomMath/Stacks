module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.IndependenceKTheory
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassIntegral
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplexBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.PerfectHomomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IrreducibleCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability

/-!
# The total Chern class of a complex depends only on its derived object

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `Y` be locally of
finite type over `S`. **Stacks 0ESZ** says that the total Chern class `c(ℰ^•)` of a locally
bounded complex `ℰ^•` of finite locally free `𝒪_Y`-modules depends only on the object of `D(𝒪_Y)`
that the complex represents.

## Main results

* `Stacks.Chow.op_id_complexChernBounded_eq_of_iso` — the last two paragraphs of the source's
  proof: on an integral scheme, two bounded complexes of finite locally free modules of constant
  ranks representing the same object of `D(𝒪_W)`, whose cohomology modules are perfect of Tor
  dimension at most one, have the same total Chern class operation on the Chow groups of `W`.
* `Stacks.Chow.exists_isBirational_op_complexChern_eq_of_iso` — the modification of the source's
  proof: over an integral `T`, the admissible blowup of Stacks 0ESR after which the cohomology of
  the pulled-back object is perfect of Tor dimension at most one.
* `Stacks.Chow.complexChern_eq_of_iso` — **Stacks 0ESZ** for the total Chern class: two locally
  bounded complexes of finite locally free `𝒪_Y`-modules, of arbitrary ranks, isomorphic in
  `D(𝒪_Y)`, have equal total Chern classes `Stacks.Chow.complexChern`, with `Y` not assumed
  quasi-compact. The cases of `P_p` and `ch` are in
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PowerSumIndependence`.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

/-! ### Admissible blowups of an integral scheme -/

namespace Stacks.Blowup.IsAdmissibleBlowup

variable {X X' : Scheme.{u}} {U : X.Opens} {b : X' ⟶ X}

/-- The centre of a `U`-admissible blowup of an integral scheme with `U` nonempty is not the zero
ideal: its support misses `U`, while the zero ideal is supported everywhere. -/
theorem exists_ne_bot [IsIntegral X] (h : IsAdmissibleBlowup U b) (hU : (U : Set X).Nonempty) :
    ∃ I : X.IdealSheafData, I ≠ ⊥ ∧
      ∃ e : X' ≅ AlgebraicGeometry.blowUp I, e.hom ≫ AlgebraicGeometry.blowUpToBase I = b := by
  obtain ⟨I, -, hdisj, e, he⟩ := (isAdmissibleBlowup_iff U b).mp h
  refine ⟨I, fun hI ↦ ?_, e, he⟩
  obtain ⟨x, hx⟩ := hU
  have htop : I.support = ⊤ := Scheme.IdealSheafData.support_eq_top_iff.mpr hI
  exact Set.disjoint_left.mp hdisj hx (by rw [htop]; trivial)

/-- **A `U`-admissible blowup of an integral scheme, with `U` nonempty, is integral** (Stacks
02ND). -/
theorem isIntegral [IsIntegral X] (h : IsAdmissibleBlowup U b) (hU : (U : Set X).Nonempty) :
    IsIntegral X' := by
  obtain ⟨I, hI, e, -⟩ := h.exists_ne_bot hU
  have := isIntegral_blowUp I hI
  exact IsIntegral.of_isIso e.inv

/-- **A `U`-admissible blowup of an integral scheme, with `U` nonempty, is birational.** -/
theorem isBirational [IsIntegral X] (h : IsAdmissibleBlowup U b) (hU : (U : Set X).Nonempty) :
    IsBirational b := by
  obtain ⟨I, hI, e, he⟩ := h.exists_ne_bot hU
  have := isIntegral_blowUp I hI
  have := h.isIntegral hU
  rw [← he]
  exact (isBirational_of_isIso_stalkMap_genericPoint e.hom).comp (isBirational_blowUpToBase I hI)

end Stacks.Blowup.IsAdmissibleBlowup

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard


section Integral

variable (C : ChowSituation.{u}) {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]

/-- A finite set of degrees outside of which two finitely supported rank functions vanish, in the
form of a window `a, …, a + k`. -/
theorem exists_window_of_finsupp (ρ σ : ℤ →₀ ℕ) :
    ∃ (a : ℤ) (k : ℕ), (∀ n, (n < a ∨ a + (k : ℤ) < n) → ρ n = 0) ∧
      ∀ n, (n < a ∨ a + (k : ℤ) < n) → σ n = 0 := by
  classical
  set N : ℕ := (ρ.support ∪ σ.support).sup Int.natAbs
  have hN : ∀ n, (n < -(N : ℤ) ∨ -(N : ℤ) + ((2 * N : ℕ) : ℤ) < n) →
      n ∉ ρ.support ∪ σ.support := fun n hn hmem ↦ by
    have h := Finset.le_sup (f := Int.natAbs) hmem
    omega
  refine ⟨-(N : ℤ), 2 * N, fun n hn ↦ ?_, fun n hn ↦ ?_⟩
  · by_contra h
    exact hN n hn (Finset.mem_union_left _ (Finsupp.mem_support_iff.2 h))
  · by_contra h
    exact hN n hn (Finset.mem_union_right _ (Finsupp.mem_support_iff.2 h))

/-- The operation on the Chow groups of `W` of a factor `c(P^n)^{(-1)^n}` is the corresponding
power of the total Chern class `c(P^n)` of Stacks 02U6. -/
theorem units_map_opRingHom_complexChernFactor (P : CochainComplex W.Modules ℤ) (ρ : ℤ → ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (n : ℤ) :
    Units.map (TotalChowClass.opRingHom (C := C) (sY := sW) (𝟙 W)).toMonoidHom
        (complexChernFactor C sW P ρ hP n) =
      (haveI := hP n; GenuineChern.chernFamilyUnit C (𝟙 W ≫ sW) (P.X n) (ρ n)) ^
        ((n.negOnePow : ℤˣ) : ℤ) := by
  let := hP n
  rw [complexChernFactor, map_zpow]
  congr 1
  refine Units.ext ?_
  rw [Units.coe_map, GenuineChern.val_chernFamilyUnit]
  change (totalChern C sW (P.X n) (ρ n)).op (𝟙 W) = _
  rw [op_totalChern]
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (P.X n) (ρ n) (𝟙 W)
  exact GenuineChern.chernFamily_congr C (𝟙 W ≫ sW) (P.X n) (ρ n)
    ((Scheme.Modules.pullbackId W).app (P.X n)) rfl

/-- The operation on the Chow groups of `W` of the total Chern class of a bounded complex of
constant ranks is the ordered alternating product of the total Chern classes of its terms, over
any window outside of which the ranks vanish. -/
theorem op_id_complexChernBounded (P : CochainComplex W.Modules ℤ) (ρ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (a : ℤ) (k : ℕ) (hρ : ∀ n, (n < a ∨ a + (k : ℤ) < n) → ρ n = 0) :
    (complexChernBounded C sW P ρ hP).op (𝟙 W) =
      ((((Finset.Icc a (a + (k : ℤ))).sort (· ≤ ·)).map fun n ↦
        (haveI := hP n; GenuineChern.chernFamilyUnit C (𝟙 W ≫ sW) (P.X n) (ρ n)) ^
          ((n.negOnePow : ℤˣ) : ℤ)).prod : (GradedCapFamily (chowGroup C (𝟙 W ≫ sW)))ˣ) := by
  rw [complexChernBounded_eq_prod C sW P ρ hP (Finset.Icc a (a + (k : ℤ))) fun n hn ↦
    hρ n (by rw [Finset.mem_Icc] at hn; omega), complexChernProd]
  change (TotalChowClass.opRingHom (𝟙 W)).toMonoidHom _ = _
  rw [← Units.coe_map, map_list_prod, List.map_map]
  congr 2
  exact List.map_congr_left fun n _ ↦ units_map_opRingHom_complexChernFactor C sW P ρ hP n

/-- **Stacks 0ESZ on an integral scheme whose cohomology is perfect of Tor dimension at most
one.** Let `W` be integral and locally Noetherian and let `P`, `Q` be bounded complexes of finite
locally free `𝒪_W`-modules of constant ranks `ρ`, `σ` representing the same object of `D(𝒪_W)`,
whose cohomology modules are perfect of Tor dimension at most one. Then `c(P)` and `c(Q)` operate
in the same way on the Chow groups of `W`.

This is the last two paragraphs of the source's proof: by Stacks 0F8J the kernels and images of
the differentials are finite locally free, Schanuel's lemma compares the two presentations of
each cohomology module, so the alternating classes in `K_0(Vect(W))` agree
(`Stacks.Chow.alternatingKClass_eq_of_iso_derivedCategory`), and on `W` the total Chern class
factors through `K_0(Vect(W))` by the Whitney sum formula
(`Stacks.Chow.GenuineChern.prod_Icc_chernFamilyUnit_eq_of_iso`). -/
theorem op_id_complexChernBounded_eq_of_iso [IsIntegral W] [IsLocallyNoetherian W]
    (P Q : CochainComplex W.Modules ℤ) (ρ σ : ℤ →₀ ℕ)
    (hP : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n) (ρ n))
    (hQ : ∀ n, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Q.X n) (σ n))
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q)
    (hE : ∀ i : ℤ,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj (DerivedCategory.Q.obj P))) ∧
      HasTorAmplitude W.toRingedSpace ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj (DerivedCategory.Q.obj P))) (-1) 0) :
    (complexChernBounded C sW P ρ hP).op (𝟙 W) = (complexChernBounded C sW Q σ hQ).op (𝟙 W) := by
  obtain ⟨a, k, hρ, hσ⟩ := exists_window_of_finsupp ρ σ
  rw [op_id_complexChernBounded C sW P ρ hP a k hρ, op_id_complexChernBounded C sW Q σ hQ a k hσ,
    GenuineChern.prod_Icc_chernFamilyUnit_eq_of_iso C (𝟙 W ≫ sW) P Q ρ σ hP hQ a k hρ hσ e hE]

end Integral

section Pullback

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  {P P' : CochainComplex Y.Modules ℤ} (hP : IsLocallyBoundedFiniteLocallyFree P)
  (hP' : IsLocallyBoundedFiniteLocallyFree P')

/-- **Termwise pullback computes derived pullback on locally bounded complexes**, so two such
complexes representing the same object of `D(𝒪_Y)` pull back to complexes representing the same
object of `D(𝒪_T)`: `Q(f^*P) ≅ Lf^*Q(P) ≅ Lf^*Q(P') ≅ Q(f^*P')`. -/
def pullbackComplexQIso {T : Scheme.{u}} (f : T ⟶ Y)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    DerivedCategory.Q.obj (pullbackComplex f P) ≅ DerivedCategory.Q.obj (pullbackComplex f P') :=
  (Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom P
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree P hP)).symm ≪≫
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom).mapIso e ≪≫
    Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom P'
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree P' hP')

include hP in
/-- On an integral scheme the terms of a locally bounded complex of finite locally free modules
have constant ranks: the fibre ranks at any point. -/
theorem isFiniteLocallyFreeOfRank_complexRank [IsIntegral Y] (x : Y) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (P.X n)
      (complexRank hP x n) := by
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (P.X n) := hP.1 n
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq (P.X n) _ x
    (complexRank_apply hP x n).symm

/-- **Stacks 0ESZ along a morphism from an integral scheme over which the cohomology is perfect of
Tor dimension at most one.** Let `f : W ⟶ Y` be locally of finite type with `W` integral, and let
`P`, `P'` be locally bounded complexes of finite locally free `𝒪_Y`-modules representing the same
object of `D(𝒪_Y)`. If the cohomology modules of `Lf^*P` are perfect of Tor dimension at most
one, then `c(P)` and `c(P')` operate in the same way on the Chow groups of `W`. -/
theorem op_complexChern_eq_of_iso_of_isIntegral {W : Scheme.{u}} [IsIntegral W] (f : W ⟶ Y)
    [LocallyOfFiniteType f] (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P')
    (hE : ∀ i : ℤ,
      IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj
          (DerivedCategory.Q.obj (pullbackComplex f P)))) ∧
      HasTorAmplitude W.toRingedSpace ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((DerivedCategory.homologyFunctor W.Modules i).obj
          (DerivedCategory.Q.obj (pullbackComplex f P)))) (-1) 0) :
    (complexChern C sY hP).op f = (complexChern C sY hP').op f := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sY)
  obtain ⟨x⟩ : Nonempty W := inferInstance
  have hσ := isFiniteLocallyFreeOfRank_complexRank
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback f P hP) x
  have hσ' := isFiniteLocallyFreeOfRank_complexRank
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback f P' hP') x
  have h : (TotalChowClass.res f rfl (complexChern C sY hP)).op (𝟙 W) =
      (TotalChowClass.res f rfl (complexChern C sY hP')).op (𝟙 W) := by
    rw [res_complexChern_eq_complexChernBounded C sY hP f rfl _ hσ,
      res_complexChern_eq_complexChernBounded C sY hP' f rfl _ hσ']
    exact op_id_complexChernBounded_eq_of_iso C (f ≫ sY) _ _ _ _ hσ hσ'
      (pullbackComplexQIso hP hP' f e) hE
  exact eq_of_heq ((((TotalChowClass.op_heq_congr _ (Category.id_comp f)).symm.trans
    (TotalChowClass.op_res f rfl _ (𝟙 W)).symm).trans (heq_of_eq h)).trans
    ((TotalChowClass.op_res f rfl _ (𝟙 W)).trans
      (TotalChowClass.op_heq_congr _ (Category.id_comp f))))

/-- **The proper birational modification of the proof of Stacks 0ESZ.** Let `g : T ⟶ Y` be locally
of finite type with `T` integral, and let `P`, `P'` be locally bounded complexes of finite
locally free `𝒪_Y`-modules representing the same object of `D(𝒪_Y)`. There is a proper
birational `π : T' ⟶ T` such that `c(P)` and `c(P')` operate in the same way on the Chow groups
of `T'`: namely the admissible blowup of Stacks 0ESR applied to the perfect object `Lg^*P`, after
which its cohomology modules are perfect of Tor dimension at most one. -/
theorem exists_isBirational_op_complexChern_eq_of_iso {T : Scheme.{u}} [IsIntegral T]
    (g : T ⟶ Y) [LocallyOfFiniteType g] (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    ∃ (T' : Scheme.{u}) (π : T' ⟶ T) (_ : IsProper π), AlgebraicGeometry.IsBirational π ∧
      (complexChern C sY hP).op (π ≫ g) = (complexChern C sY hP').op (π ≫ g) := by
  have hPg := Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback g P hP
  have hperf : IsPerfect.{u, u, u + 1} (X := T.toRingedSpace)
      (DerivedCategory.Q.obj (pullbackComplex g P)) :=
    ⟨pullbackComplex g P,
      Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree _ hPg,
      ⟨Iso.refl _⟩⟩
  obtain ⟨U, -, hU, -, T', b, hb, hE⟩ :=
    exists_nonempty_open_admissibleBlowup_forall_isHomologyPerfectTorLEOne T
      (DerivedCategory.Q.obj (pullbackComplex g P)) hperf
  have := hb.isProper
  have := hb.isIntegral hU
  refine ⟨T', b, inferInstance, hb.isBirational hU,
    op_complexChern_eq_of_iso_of_isIntegral C sY hP hP' (b ≫ g) e fun i ↦ ?_⟩
  let ε : DerivedCategory.Q.obj (pullbackComplex (b ≫ g) P) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback b.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj (pullbackComplex g P)) :=
    (DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Scheme.Modules.pullbackComp b g)
        (ComplexShape.up ℤ)).app P)).symm ≪≫
      (Cohomology.derivedPullbackIsoPullbackOfKFlat b.toLRSHom.toShHom (pullbackComplex g P)
        (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree _ hPg)).symm
  exact AlgebraicGeometry.IsPerfectTorLEOne.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso ε.symm) (hE i)

/-- **Stacks 0ESZ for the total Chern class.** Let `Y` be locally of finite type over the base of
chapter 42 and let `P`, `P'` be locally bounded complexes of finite locally free `𝒪_Y`-modules
representing the same object of `D(𝒪_Y)`. Then their total Chern classes
`c(P), c(P') ∈ ∏_{p ≥ 0} A^p(Y)` are equal.

The proof is the source's. By Stacks 02UC it suffices to compare the operations of the two
classes on the fundamental class of a proper birational modification of every integral scheme `T`
locally of finite type over `Y` (`Stacks.Chow.TotalChowClass.eq_of_op_fundamentalChowClass_eq`).
Over `T` the pulled-back complexes are bounded with constant ranks, after the admissible blowup of
Stacks 0ESR the cohomology of the pulled-back object is perfect of Tor dimension at most one, and
there the two classes agree by Stacks 0F8J, Schanuel's lemma and the Whitney sum formula
(`Stacks.Chow.exists_isBirational_op_complexChern_eq_of_iso`). -/
@[stacks 0ESZ "the independence of the choice of the complex for c(E^bullet), at the hypotheses \
of the source: two locally bounded complexes of finite locally free modules representing one \
object of D(O_Y), no rank assumed constant and Y not assumed quasi-compact"]
theorem complexChern_eq_of_iso (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj P') :
    complexChern C sY hP = complexChern C sY hP' :=
  TotalChowClass.eq_of_op_fundamentalChowClass_eq fun g _ _ ↦ by
    obtain ⟨T', π, hπ, hbir, h⟩ := exists_isBirational_op_complexChern_eq_of_iso C sY hP hP' g e
    exact ⟨T', π, hπ, hbir, fun k p ↦ by rw [h]⟩

end Pullback

end Stacks.Chow

end
