module

public import Mathlib.Algebra.Category.Grp.AB
import StacksFrontier.Homology.HomologyColimit
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes.PCellularComplexes
public import StacksFrontier.CategoryTheory.Functor.Derived.Computing

/-!
# The left derived functor of a right exact functor on the unbounded derived category

`F` sends quasi-isomorphisms between `P`-cellular complexes to quasi-isomorphisms, hence the
`P`-cellular complexes derive `F`, which gives **Stacks 0794**: `LF` is defined on all of `D(A)`
in the sense of Tags 05S9 and 05SV, i.e. at every object the pro-object `(s : K' ⟶ K) ↦ F(K')`
is essentially constant (`isLeftDerivable_of_acyclic_mapHomologicalComplex`, through
Stacks 06XN(2)). The file also records that the pointwise left derived functor exists in
Mathlib's sense, and that it is absolute.
-/

@[expose] public section

open CategoryTheory Limits

namespace StacksDraft.UnboundedLeftDerivedFunctor

open CategoryTheory Limits Functor LocalizerMorphism
open CategoryTheory.LeftDerivedByResolutions

universe v₁ v₂ v₃ u₁ u₂ u₃

section Concrete

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]

/-- The cocone on `ofSequence g` with point `S` and legs `σ n`, for compatible legs. -/
private def sequenceCocone {C : Type*} [Category C] {Q : ℕ → C} {g : ∀ n, Q n ⟶ Q (n + 1)}
    {S : C} (σ : ∀ n, Q n ⟶ S) (hσ : ∀ n, g n ≫ σ (n + 1) = σ n) :
    Cocone (Functor.ofSequence g) where
  pt := S
  ι := NatTrans.ofSequence σ (fun n => by
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact (hσ n).trans (Category.comp_id _).symm)

/-- Transporting a colimit cocone of an `ℕ`-sequence along an isomorphism of its point gives
compatible legs `σ n` forming a colimit cocone. -/
private theorem exists_sequenceCocone {C : Type*} [Category C] {Q : ℕ → C}
    {g : ∀ n, Q n ⟶ Q (n + 1)} {S : C} (c : Cocone (Functor.ofSequence g)) (hc : IsColimit c)
    (e : c.pt ≅ S) :
    ∃ (σ : ∀ n, Q n ⟶ S) (hσ : ∀ n, g n ≫ σ (n + 1) = σ n),
      (∀ n, σ n = c.ι.app n ≫ e.hom) ∧ Nonempty (IsColimit (sequenceCocone σ hσ)) := by
  refine ⟨fun n => c.ι.app n ≫ e.hom, fun n => ?_, fun _ => rfl,
    ⟨IsColimit.ofIsoColimit hc (Cocone.ext e fun _ => rfl)⟩⟩
  rw [← Functor.ofSequence_map_homOfLE_succ g n]
  exact (c.extend e.hom).w _

/-- **The second paragraph of the source's proof.** `F` sends a quasi-isomorphism between
`P`-cellular complexes to a quasi-isomorphism.

Fix `i : ℤ` and write `Φ = H^i (F (·))` (`homF`). Given cellular presentations `S = colim Q n`,
`T = colim R n` with structural maps `σ n : Q n ⟶ S`, `ρ n : R n ⟶ T`, and a quasi-isomorphism
`α : S ⟶ T`, the stages are compared as follows.

* `exists_common_resolution` produces, for each `n`, a strictly `≤ n` complex `V n` with terms
  satisfying `P` together with quasi-isomorphisms `a n : V n ⟶ Q n` and `b n : V n ⟶ R n` such
  that `a n ≫ σ n ≫ α` and `b n ≫ ρ n` agree in `D (A)`. Since `Φ` inverts quasi-isomorphisms
  between such complexes (`isIso_homF_map`), this transports `Φ (b n)` along the isomorphism
  `Φ (a n)` to a comparison isomorphism `w n : Φ (Q n) ≅ Φ (R n)`.
* `exists_refinement` produces, for each `n`, a further resolution `u n : U n ⟶ V n` and a
  morphism `k n : U n ⟶ V (n + 1)` lying over `a n ≫ g n` in `D (A)`; combining the two
  compatibilities and the injectivity of `∘ Q ρ (n + 1)` on morphisms out of a `≤ n` object
  (`eq_of_comp_Q_map`) shows `k n` lies over `b n ≫ g' n` as well. Because `Φ` descends to
  `D (A)` on bounded above complexes with terms satisfying `P` (`homF_map_eq_of_Q_map_eq`),
  `comm_of_comm` then makes `w` a natural transformation of the two `ℕ`-diagrams, and likewise
  compatible with the two cocones.
* `Φ` preserves colimits of shape `ℕ` — `F` does, colimits of complexes are computed degreewise,
  and `H^i` does by `Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor` — so
  `Φ (α)` is the morphism of
  colimit points induced by the natural isomorphism `w`, hence an isomorphism.

This is where `[HasDerivedCategory A]` is used, and the only place `Stacks 05T7`
(`CochainComplex.exists_quasiIso_prop`) enters. -/
public lemma quasiIso_mapHomologicalComplex_of_isPCellular (F : A ⥤ B) [F.Additive]
    [PreservesFiniteColimits F] (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasDerivedCategory A]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F]
    {S T : CochainComplex A ℤ} (hS : IsPCellular P S) (hT : IsPCellular P T)
    (α : S ⟶ T) (hα : QuasiIso α) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
  obtain ⟨Qc, g, c, hc, e, hle, hQP, hstage⟩ := hS
  obtain ⟨Rc, g', c', hc', e', hle', hRP, hstage'⟩ := hT
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- the structural maps of the two presentations, and the colimit cocones they form
  obtain ⟨σ, hσw, hσdef, ⟨hcS⟩⟩ := exists_sequenceCocone c hc e
  obtain ⟨ρ, hρw, hρdef, ⟨hcT⟩⟩ := exists_sequenceCocone c' hc' e'
  have hσq : ∀ (n : ℕ) (j : ℤ), j ≤ (n : ℤ) → QuasiIsoAt (σ n) j := by
    intro n j hj; rw [hσdef]; exact hstage n j hj
  have hρq : ∀ (n : ℕ) (j : ℤ), j ≤ (n : ℤ) → QuasiIsoAt (ρ n) j := by
    intro n j hj; rw [hρdef]; exact hstage' n j hj
  -- one common resolution of the two presentations at each stage
  have hstages : ∀ n : ℕ, ∃ (V : CochainComplex A ℤ) (_ : V.IsStrictlyLE (n : ℤ))
      (_ : ∀ j, P (V.X j)) (a : V ⟶ Qc n) (_ : QuasiIso a) (b : V ⟶ Rc n) (_ : QuasiIso b),
      DerivedCategory.Q.map (a ≫ σ n ≫ α) = DerivedCategory.Q.map (b ≫ ρ n) := fun n =>
    exists_common_resolution P hP α hα (n : ℤ) (hle n) (hle' n) (σ n) (hσq n) (ρ n) (hρq n)
  choose V hVLE hVP av hav bv hbv hstageComp using hstages
  -- and a refinement comparing consecutive stages
  have hrefines : ∀ n : ℕ, ∃ (U : CochainComplex A ℤ) (_ : U.IsStrictlyLE (n : ℤ))
      (_ : ∀ j, P (U.X j)) (u : U ⟶ V n) (_ : QuasiIso u) (k : U ⟶ V (n + 1)),
      DerivedCategory.Q.map (k ≫ av (n + 1)) =
        DerivedCategory.Q.map (u ≫ av n ≫ g n) := fun n =>
    exists_refinement P hP (n : ℤ) (hVLE n) (av n ≫ g n) (av (n + 1)) (hav (n + 1))
  choose U hULE hUP u hu k hk using hrefines
  -- the three families of isomorphisms `H^i (F (·))` produces
  have hisoav : ∀ n : ℕ, IsIso ((homF F i).map (av n)) := fun n =>
    isIso_homF_map F P hsum hFP i (n : ℤ) (hVLE n) (hle n) (hVP n) (hQP n) (av n) (hav n)
  have hisobv : ∀ n : ℕ, IsIso ((homF F i).map (bv n)) := fun n =>
    isIso_homF_map F P hsum hFP i (n : ℤ) (hVLE n) (hle' n) (hVP n) (hRP n) (bv n) (hbv n)
  have hisou : ∀ n : ℕ, IsIso ((homF F i).map (u n)) := fun n =>
    isIso_homF_map F P hsum hFP i (n : ℤ) (hULE n) (hVLE n) (hUP n) (hVP n) (u n) (hu n)
  -- the refinement is also compatible with the second presentation: both sides agree after
  -- composing with `ρ (n + 1)`, which is injective on morphisms out of `U n`
  have hkb : ∀ n : ℕ, DerivedCategory.Q.map (k n ≫ bv (n + 1)) =
      DerivedCategory.Q.map (u n ≫ bv n ≫ g' n) := by
    intro n
    have hUle : CochainComplex.IsLE (U n) ((n : ℕ) : ℤ) := by
      have := hULE n; infer_instance
    have hXle : (DerivedCategory.Q.obj (U n)).IsLE ((n : ℕ) : ℤ) := by
      have := hUle; infer_instance
    refine eq_of_comp_Q_map (X := DerivedCategory.Q.obj (U n)) (n := ((n : ℕ) : ℤ))
      (m := (((n + 1 : ℕ)) : ℤ)) (by push_cast; lia) hXle (hle' (n + 1)) (ρ (n + 1))
      (hρq (n + 1)) ?_
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    calc DerivedCategory.Q.map ((k n ≫ bv (n + 1)) ≫ ρ (n + 1))
        = DerivedCategory.Q.map (k n) ≫ DerivedCategory.Q.map (bv (n + 1) ≫ ρ (n + 1)) := by
          rw [← DerivedCategory.Q.map_comp, Category.assoc]
      _ = DerivedCategory.Q.map (k n) ≫
            DerivedCategory.Q.map (av (n + 1) ≫ σ (n + 1) ≫ α) := by
          rw [hstageComp (n + 1)]
      _ = DerivedCategory.Q.map (k n ≫ av (n + 1)) ≫ DerivedCategory.Q.map (σ (n + 1) ≫ α) := by
          rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
          congr 1
          exact (Category.assoc _ _ _).symm
      _ = DerivedCategory.Q.map (u n ≫ av n ≫ g n) ≫
            DerivedCategory.Q.map (σ (n + 1) ≫ α) := by rw [hk n]
      _ = DerivedCategory.Q.map (u n) ≫ DerivedCategory.Q.map (av n ≫ σ n ≫ α) := by
          rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
          congr 1
          simp only [Category.assoc]
          rw [reassoc_of% (hσw n)]
      _ = DerivedCategory.Q.map (u n) ≫ DerivedCategory.Q.map (bv n ≫ ρ n) := by
          rw [hstageComp n]
      _ = DerivedCategory.Q.map ((u n ≫ bv n ≫ g' n) ≫ ρ (n + 1)) := by
          rw [← DerivedCategory.Q.map_comp]
          congr 1
          simp only [Category.assoc]
          rw [hρw n]
  -- the stagewise comparison isomorphisms `H^i (F (Q n)) ≅ H^i (F (R n))`
  have hex : ∀ n : ℕ, ∃ wn : (homF F i).obj (Qc n) ⟶ (homF F i).obj (Rc n),
      (homF F i).map (av n) ≫ wn = (homF F i).map (bv n) ∧ IsIso wn := by
    intro n
    have hia : IsIso ((homF F i).map (av n)) := hisoav n
    have hib : IsIso ((homF F i).map (bv n)) := hisobv n
    exact ⟨CategoryTheory.inv ((homF F i).map (av n)) ≫ (homF F i).map (bv n),
      IsIso.hom_inv_id_assoc _ _, inferInstance⟩
  choose wc hwc hwciso using hex
  -- the comparison commutes with the transition maps of the two systems
  have hnatclean : ∀ n : ℕ,
      (homF F i).map (g n) ≫ wc (n + 1) = wc n ≫ (homF F i).map (g' n) := by
    intro n
    have h₁ : (homF F i).map (k n) ≫ (homF F i).map (av (n + 1))
        = (homF F i).map (u n) ≫ (homF F i).map (av n) ≫ (homF F i).map (g n) := by
      rw [← (homF F i).map_comp, ← (homF F i).map_comp, ← (homF F i).map_comp]
      exact homF_map_eq_of_Q_map_eq F P hsum hP hFP i (n : ℤ) (hULE n) (hUP n) (hk n)
    have h₂ : (homF F i).map (k n) ≫ (homF F i).map (bv (n + 1))
        = (homF F i).map (u n) ≫ (homF F i).map (bv n) ≫ (homF F i).map (g' n) := by
      rw [← (homF F i).map_comp, ← (homF F i).map_comp, ← (homF F i).map_comp]
      exact homF_map_eq_of_Q_map_eq F P hsum hP hFP i (n : ℤ) (hULE n) (hUP n) (hkb n)
    have hia : IsIso ((homF F i).map (av n)) := hisoav n
    have hiu : IsIso ((homF F i).map (u n)) := hisou n
    exact comm_of_comm (hwc n) (hwc (n + 1)) h₁ h₂
  -- hence a natural transformation of the two `ℕ`-diagrams, which is an isomorphism
  have hnat : ∀ n : ℕ,
      (Functor.ofSequence g ⋙ homF F i).map (homOfLE (Nat.le_add_right n 1)) ≫ wc (n + 1)
        = wc n ≫ (Functor.ofSequence g' ⋙ homF F i).map (homOfLE (Nat.le_add_right n 1)) := by
    intro n
    have hga : (Functor.ofSequence g ⋙ homF F i).map (homOfLE (Nat.le_add_right n 1))
        = (homF F i).map (g n) :=
      congrArg (homF F i).map (Functor.ofSequence_map_homOfLE_succ g n)
    have hgb : (Functor.ofSequence g' ⋙ homF F i).map (homOfLE (Nat.le_add_right n 1))
        = (homF F i).map (g' n) :=
      congrArg (homF F i).map (Functor.ofSequence_map_homOfLE_succ g' n)
    rw [hga, hgb]
    exact hnatclean n
  have hwiso : IsIso (NatTrans.ofSequence
      (F := Functor.ofSequence g ⋙ homF F i) (G := Functor.ofSequence g' ⋙ homF F i) wc hnat) := by
    have happ : ∀ n : ℕ, IsIso ((NatTrans.ofSequence
        (F := Functor.ofSequence g ⋙ homF F i) (G := Functor.ofSequence g' ⋙ homF F i)
        wc hnat).app n) := fun n => hwciso n
    exact NatIso.isIso_of_isIso_app _
  -- the comparison is compatible with the two cocones
  have hlegclean : ∀ n : ℕ, (homF F i).map (σ n) ≫ (homF F i).map α
      = wc n ≫ (homF F i).map (ρ n) := by
    intro n
    have hia : IsIso ((homF F i).map (av n)) := hisoav n
    refine (cancel_epi ((homF F i).map (av n))).1 ?_
    calc (homF F i).map (av n) ≫ (homF F i).map (σ n) ≫ (homF F i).map α
        = (homF F i).map (av n ≫ σ n ≫ α) := by
          rw [(homF F i).map_comp, (homF F i).map_comp]
      _ = (homF F i).map (bv n ≫ ρ n) :=
        homF_map_eq_of_Q_map_eq F P hsum hP hFP i (n : ℤ) (hVLE n) (hVP n) (hstageComp n)
      _ = (homF F i).map (bv n) ≫ (homF F i).map (ρ n) := (homF F i).map_comp _ _
      _ = ((homF F i).map (av n) ≫ wc n) ≫ (homF F i).map (ρ n) := by rw [hwc n]
      _ = (homF F i).map (av n) ≫ wc n ≫ (homF F i).map (ρ n) := Category.assoc _ _ _
  -- `H^i (F (·))` preserves the two colimits, so `H^i (F α)` is a colimit of isomorphisms
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := B) (J := ℕ) (ComplexShape.up ℤ) i
  have hSc := isColimitOfPreserves (homF F i) hcS
  have hTc := isColimitOfPreserves (homF F i) hcT
  have hfin : IsIso ((homF F i).map α) := by
    rw [show (homF F i).map α = (IsColimit.coconePointsIsoOfNatIso hSc hTc
        (asIso (NatTrans.ofSequence
          (F := Functor.ofSequence g ⋙ homF F i) (G := Functor.ofSequence g' ⋙ homF F i)
          wc hnat))).hom from
      hSc.hom_ext (fun n => by
        erw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
        exact hlegclean n)]
    exact Iso.isIso_hom _
  exact hfin

/-- `F` sends a quasi-isomorphism between `P`-cellular complexes to a quasi-isomorphism.

This is the mathematical content of Stacks 0794. For bounded above complexes with terms
satisfying `P` it is the hypothesis `hFP` applied to the mapping cone of the quasi-isomorphism;
in general, a quasi-isomorphism `α : colim Q n ⟶ colim R n` between `P`-cellular complexes is
compared, for each `n`, with a common bounded above `P`-resolution of `Q n` and `R n` obtained
from the right calculus of fractions, which produces compatible isomorphisms
`H^i (F (Q n)) ≅ H^i (F (R n))`; exactness of `ℕ`-colimits in `B` and the fact that `F` commutes
with them identify `H^i (F (colim Q n))` with `colim H^i (F (Q n))`, whence `H^i (F α)` is an
isomorphism. -/
public lemma derives_cellularLocalizerMorphism (F : A ⥤ B) [F.Additive]
    [PreservesFiniteColimits F] (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F] :
    (cellularLocalizerMorphism P).Derives
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
  intro X Y f hf
  obtain ⟨S, hS, ⟨eS⟩⟩ := X.property
  obtain ⟨T, hT, ⟨eT⟩⟩ := Y.property
  -- the morphism of `K(A)` underlying `f`, transported to a morphism between the two
  -- `P`-cellular complexes, and lifted to a morphism of complexes
  obtain ⟨α, hαeq⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective
    (eS.inv ≫ (cellular P).ι.map f ≫ eT.hom)
  have hquot : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α) := by
    rw [hαeq]
    exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk eS eT (by
      change eS.hom ≫ eS.inv ≫ (cellular P).ι.map f ≫ eT.hom
        = (cellular P).ι.map f ≫ eT.hom
      simp))).1 hf
  have hqα : QuasiIso α := (HomotopyCategory.quotient_map_mem_quasiIso_iff α).1 hquot
  have hqFα : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) :=
    quasiIso_mapHomologicalComplex_of_isPCellular F P hsum hP hFP hS hT α hqα
  -- so `F` of the transported morphism is a quasi-isomorphism, hence so is `F(f)`
  have hFquot : HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map
        (eS.inv ≫ (cellular P).ι.map f ≫ eT.hom)) := by
    rw [← hαeq, Functor.mapHomotopyCategory_map]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hqFα
  have hFf : HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map ((cellular P).ι.map f)) := by
    refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).mapIso eS)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).mapIso eT) ?_)).2 hFquot
    change (F.mapHomotopyCategory (ComplexShape.up ℤ)).map eS.hom ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map
          (eS.inv ≫ (cellular P).ι.map f ≫ eT.hom)
      = (F.mapHomotopyCategory (ComplexShape.up ℤ)).map ((cellular P).ι.map f) ≫
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map eT.hom
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp
  exact (DerivedCategory.isIso_Qh_map_iff _).2 hFf

variable [HasDerivedCategory A] [HasDerivedCategory B]

private theorem solution
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have := isLeftDerivabilityStructure_cellularLocalizerMorphism P
    (hasLeftResolutions_cellularLocalizerMorphism P hsum hP)
  exact hasPointwiseLeftDerivedFunctor_of_derives _ _
    (derives_cellularLocalizerMorphism F P hsum hP hFP)

/-- The left derived functor of Stacks 0794 is absolute. The `P`-cellular objects of `K(A)`
resolve every object and `F` inverts the quasi-isomorphisms between them, so this is the
instance of `CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions`
at that resolving class. -/
private theorem solution_postcomp
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F]
    {D : Type*} [Category D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (LF : D ⥤ DerivedCategory B)
    (α : L ⋙ LF ⟶ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {E : Type*} [Category E] (G : DerivedCategory B ⥤ E) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hres := hasLeftResolutions_cellularLocalizerMorphism P hsum hP
  have hder := derives_cellularLocalizerMorphism F P hsum hP hFP
  refine CategoryTheory.LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (cellular P) (fun X => ?_) _
    (fun s hs hX hY => ?_) L LF α G
  · obtain ⟨R⟩ := hres X
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  · exact hder (ObjectProperty.homMk (P := cellular P) (X := ⟨_, hX⟩) (Y := ⟨_, hY⟩) s) hs

end Concrete

end StacksDraft.UnboundedLeftDerivedFunctor

namespace CategoryTheory.Functor

variable {A : Type*} [Category A] {B : Type*} [Category B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- Under the hypotheses of Stacks 0794, the functor `K(𝒜) ⥤ D(ℬ)`, `K ↦ F(K)`, has a
pointwise left derived functor along the localization `Qh : K(𝒜) ⥤ D(𝒜)` at
quasi-isomorphisms, in Mathlib's sense (`Functor.HasPointwiseLeftDerivedFunctor`: a pointwise
right Kan extension exists at every object).

This is Mathlib's form of the conclusion; the Stacks conclusion, that `LF` is defined on all of
`D(𝒜)` in the sense of Tags 05S9/05SV (essential constancy of the pro-object at every object),
is `isLeftDerivable_of_acyclic_mapHomologicalComplex`. The hypotheses are those of Stacks 0794:
`F` is right exact, `P` contains a zero object, is closed under finite direct sums, and every
object of `𝒜` is a quotient of an object satisfying `P`; `F` turns every bounded above acyclic
complex with all terms satisfying `P` into an acyclic complex; `𝒜` and `ℬ` have exact colimits
of systems indexed by `ℕ`, and `F` commutes with them. -/
public theorem hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  StacksDraft.UnboundedLeftDerivedFunctor.solution F P hsum hP hFP

/-- The quasi-isomorphisms of `K(𝒜)` are multiplicative and satisfy the saturation condition
MS4: if `f ≫ g` and `g ≫ h` are quasi-isomorphisms then so is `g`, since on each
cohomology object `H^n(g)` is then both a monomorphism and an epimorphism. -/
theorem _root_.HomotopyCategory.isSaturatedMultiplicative_quasiIso (C : Type*) [Category C]
    [Abelian C] :
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).IsSaturatedMultiplicative := by
  refine { toIsMultiplicative := inferInstance, mem_of_comp_mem_comp := ?_ }
  intro X Y Z T f g h hfg hgh n
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n
  have h₁ : IsIso (H.map f ≫ H.map g) := by
    rw [← H.map_comp]
    exact hfg n
  have h₂ : IsIso (H.map g ≫ H.map h) := by
    rw [← H.map_comp]
    exact hgh n
  have : Mono (H.map g) := mono_of_mono _ (H.map h)
  have : Epi (H.map g) := epi_of_epi (H.map f) _
  exact isIso_of_mono_of_epi (H.map g)

/-- **Stacks 0794.** Let `F : 𝒜 ⥤ ℬ` be a right exact functor of abelian categories and let `P`
be a class of objects of `𝒜`. Assume

1. `P` contains a zero object, is closed under finite direct sums, and every object of `𝒜` is a
   quotient of an object satisfying `P`,
2. `F` turns every bounded above acyclic complex with all terms satisfying `P` into an acyclic
   complex,
3. `𝒜` and `ℬ` have colimits of systems indexed by `ℕ`,
4. those colimits are exact in both `𝒜` and `ℬ`, and
5. `F` commutes with them.

Then `LF` is defined on all of `D(𝒜)`: the functor `K(𝒜) ⥤ D(ℬ)`, `K ↦ F(K)`, is left
derivable with respect to the quasi-isomorphisms (Tag 05SV), i.e. for every complex `K` the
pro-object `(s : K' ⟶ K) ↦ F(K')` over quasi-isomorphisms `s` is essentially constant (Tag 05S9).

The proof is the source's: every object of `K(𝒜)` receives a quasi-isomorphism from a
`P`-cellular complex (the colimit of the ladder of Tag 06XX), `F` sends quasi-isomorphisms
between `P`-cellular complexes to quasi-isomorphisms (the claim of the source's proof,
`StacksDraft.UnboundedLeftDerivedFunctor.derives_cellularLocalizerMorphism`), and Tag 06XN(2)
then makes `LF` everywhere defined. -/
@[stacks 0794]
public theorem isLeftDerivable_of_acyclic_mapHomologicalComplex
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).IsLeftDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have hres :=
    StacksDraft.UnboundedLeftDerivedFunctor.hasLeftResolutions_cellularLocalizerMorphism P hsum hP
  have hder :=
    StacksDraft.UnboundedLeftDerivedFunctor.derives_cellularLocalizerMorphism F P hsum hP hFP
  refine (Stacks.DerivedFunctor.Computing.leftDerived_everywhereDefined_and_computes _
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (HomotopyCategory.isSaturatedMultiplicative_quasiIso A)
    {X | StacksDraft.UnboundedLeftDerivedFunctor.cellular P X} (fun X => ?_)
    (fun X Y s hs hX hY => ?_)).1
  · obtain ⟨R⟩ := hres X
    exact ⟨R.X₁.obj, R.w, R.hw, R.X₁.property⟩
  · exact hder (ObjectProperty.homMk
      (P := StacksDraft.UnboundedLeftDerivedFunctor.cellular P) (X := ⟨_, hX⟩) (Y := ⟨_, hY⟩) s) hs

/-- **The left derived functor of Stacks 0794 is absolute.** Under the hypotheses of
`hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex`, if `α` exhibits `LF` as the
left derived functor of `K ↦ F(K)` along a localization `L` of `K(𝒜)` at the
quasi-isomorphisms, then for *every* functor `G` out of `D(ℬ)` the composite `LF ⋙ G` is the
left derived functor of `K ↦ G(F(K))`, with the whiskered comparison.

This is the hypothesis that a derived adjunction imposes on its left derived functor —
`CategoryTheory.Adjunction.derived`, i.e. Stacks 09T5, asks for absoluteness of both derived
functors, and for the right one over a Grothendieck abelian category it is automatic
(`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp`). It holds here because the
functor of Stacks 0794 is derived by resolutions: the `P`-cellular objects of `K(𝒜)` resolve
every object and `F` inverts the quasi-isomorphisms between them, so the comparison of
`K ↦ G(F(K))` is invertible on that class because the comparison of `K ↦ F(K)` is. -/
public theorem isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F]
    {D : Type*} [Category D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (LF : D ⥤ DerivedCategory B)
    (α : L ⋙ LF ⟶ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {E : Type*} [Category E] (G : DerivedCategory B ⥤ E) :
    (LF ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator L LF G).inv ≫ Functor.whiskerRight α G)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  StacksDraft.UnboundedLeftDerivedFunctor.solution_postcomp F P hsum hP hFP L LF α G

end CategoryTheory.Functor

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace CochainComplex

/-- The canonical map from an upper truncation of a cochain complex of an abelian category is a
monomorphism. Mathlib proves this for `HomologicalComplex.ιTruncLE` at an arbitrary embedding of
complex shapes; `CochainComplex.ιTruncLE` is a definition wrapping that at `embeddingUpIntLE`, so
the instance does not fire through it and is restated here. -/
instance mono_ιTruncLE {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (n : ℤ) : Mono (K.ιTruncLE n) := by
  unfold CochainComplex.ιTruncLE
  infer_instance

/-- **A quasi-isomorphism of cochain complexes becomes an isomorphism in the derived category.**
The localization functor `DerivedCategory.Q` inverts exactly the quasi-isomorphisms, by
`DerivedCategory.isIso_Q_map_iff_quasiIso`; this packages the invertibility it provides as the
isomorphism itself. -/
noncomputable def derivedIsoOfQuasiIso {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {S T : CochainComplex A ℤ} (φ : S ⟶ T) (hφ : QuasiIso φ) :
    DerivedCategory.Q.obj S ≅ DerivedCategory.Q.obj T :=
  @asIso _ _ _ _ _ ((DerivedCategory.isIso_Q_map_iff_quasiIso A φ).mpr hφ)

end CochainComplex

end
