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
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes.TruncLEResolutions

/-!
# `P`-cellular complexes and the comparison of their resolutions

`P`-cellular complexes, the left derivability structure they give on the homotopy category,
the acyclicity of `F` on them, and the comparison of two cellular presentations through common
resolutions in the derived category, used to show that `F` preserves quasi-isomorphisms between
`P`-cellular complexes.
-/

@[expose] public section

open CategoryTheory Limits

/-! ### The left derived functor of a right exact functor on the whole derived category

That a resolving class of objects, for a class of morphisms with a right calculus of fractions,
is a left derivability structure is `CategoryTheory.LeftDerivedByResolutions`; it is applied here
to the `P`-cellular complexes.
-/

namespace StacksDraft.UnboundedLeftDerivedFunctor

open CategoryTheory Limits Functor LocalizerMorphism
open CategoryTheory.LeftDerivedByResolutions

universe v₁ v₂ v₃ u₁ u₂ u₃

section Concrete

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]

/-- A cochain complex `S` in an abelian category is *`P`-cellular* if it is the colimit of an
`ℕ`-indexed system of complexes `Q n` such that `Q n` is bounded above by `n` with all terms
satisfying `P`, and such that the structural map `Q n ⟶ S` is an isomorphism on `H^i` for every
`i ≤ n`.

This is the class of complexes produced by the ladder of resolutions of the canonical
truncations of an arbitrary complex (Stacks 06XX): there `Q n ⟶ τ_{≤ n} K` is a
quasi-isomorphism, and `τ_{≤ n} K ⟶ K` is one in degrees `≤ n`, so `Q n ⟶ colim Q` is an
isomorphism on `H^i` for `i ≤ n`. It is the class of complexes which compute the left derived
functor in Stacks 0794.

The condition on `H^i` is what makes the class useful, and it is not implied by the mere
existence of the colimit: it says that `Q n` is a resolution of `τ_{≤ n} S`, which is the only
property of the ladder the source's argument uses. In particular a `P`-cellular complex which is
acyclic is the colimit of a system of bounded above *acyclic* complexes with terms satisfying
`P`, which is what `acyclic_mapHomologicalComplex_of_isPCellular` needs. -/
public def IsPCellular (P : ObjectProperty A) : ObjectProperty (CochainComplex A ℤ) :=
  fun S => ∃ (Q : ℕ → CochainComplex A ℤ) (g : ∀ n : ℕ, Q n ⟶ Q (n + 1))
    (c : Cocone (Functor.ofSequence g)) (_ : IsColimit c) (e : c.pt ≅ S),
      (∀ n : ℕ, (Q n).IsStrictlyLE (n : ℤ)) ∧ (∀ (n : ℕ) (i : ℤ), P ((Q n).X i)) ∧
        ∀ (n : ℕ) (i : ℤ), i ≤ (n : ℤ) → QuasiIsoAt (c.ι.app n ≫ e.hom) i

/-- The objects of the homotopy category `K(A)` which are isomorphic to a `P`-cellular complex. -/
public def cellular (P : ObjectProperty A) :
    ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
  fun X => ∃ S : CochainComplex A ℤ, IsPCellular P S ∧
    Nonempty (X ≅ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj S)

/-- The inclusion of the `P`-cellular objects of `K(A)`, as a localizer morphism for the
quasi-isomorphisms. -/
public abbrev cellularLocalizerMorphism (P : ObjectProperty A) :=
  inclusionLocalizerMorphism (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (cellular P)

/-- **Stacks 06XX**: the resolutions of the canonical truncations `τ_{≤ n} K` can be chosen
compatibly with the maps `τ_{≤ n} K ⟶ τ_{≤ n + 1} K`, forming a ladder whose stages are bounded
above with terms satisfying `P` and whose transition maps are degreewise split injections with
cokernel satisfying `P`.

This is the statement of Stacks Tag 06XX, verbatim except for the clause that each `f n` is
degreewise epimorphic, which this proof does not use. -/
@[sga "4½ Etat_0 3.1.9" "special case"]
public lemma exists_sequence_quasiIso_truncLE (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p) (K : CochainComplex A ℤ) :
    ∃ (Q : ℕ → CochainComplex A ℤ) (f : ∀ n : ℕ, Q n ⟶ K.truncLE (n : ℤ))
      (g : ∀ n : ℕ, Q n ⟶ Q (n + 1)),
      (∀ n, QuasiIso (f n)) ∧ (∀ n : ℕ, (Q n).IsStrictlyLE (n : ℤ)) ∧
        (∀ (n : ℕ) (i : ℤ), P ((Q n).X i)) ∧
        (∀ (n : ℕ) (i : ℤ), ∃ (C : A) (_ : P C) (e : (Q (n + 1)).X i ≅ (Q n).X i ⊞ C),
          (g n).f i ≫ e.hom = biprod.inl) ∧
        (∀ n : ℕ, g n ≫ f (n + 1) ≫ K.ιTruncLE ((n + 1 : ℕ) : ℤ)
          = f n ≫ K.ιTruncLE ((n : ℕ) : ℤ)) := by
  obtain ⟨Q, f, g, hf, -, hle, hQ, hsplit, hladder⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncLE P hsum hP K
  exact ⟨Q, f, g, hf, hle, hQ, hsplit, hladder⟩

/-- If `ι ≫ α = f ≫ K.ιTruncLE n` with `f` a quasi-isomorphism, then `ι ≫ α` is an isomorphism
on `H^i` for `i ≤ n`. -/
private lemma quasiIsoAt_comp_of_eq_ιTruncLE {K Q C : CochainComplex A ℤ} {n : ℤ}
    (f : Q ⟶ K.truncLE n) [QuasiIso f] (ι : Q ⟶ C) (α : C ⟶ K)
    (hα : ι ≫ α = f ≫ K.ιTruncLE n) (i : ℤ) (hi : i ≤ n) : QuasiIsoAt (ι ≫ α) i := by
  have := CochainComplex.quasiIsoAt_ιTruncLE K n i hi
  rw [hα]
  infer_instance

/-- The colimit of a ladder of resolutions of the canonical truncations of `K` is a resolution
of `K`.

Exactness of `ℕ`-colimits in `A` identifies `H^i (colim Q n)` with `colim H^i (Q n)`, and for
`i ≤ n` the map `H^i (Q n) ⟶ H^i (K)` is an isomorphism because `f n` is a quasi-isomorphism
and `τ_{≤ n} K ⟶ K` is a quasi-isomorphism in degrees `≤ n`
(`CochainComplex.quasiIsoAt_ιTruncLE`); the system `H^i (Q n)` is therefore eventually constant
with value `H^i (K)`. -/
public lemma quasiIso_of_isColimit_of_quasiIso_truncLE
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
    {K : CochainComplex A ℤ} {Q : ℕ → CochainComplex A ℤ} {g : ∀ n : ℕ, Q n ⟶ Q (n + 1)}
    (f : ∀ n : ℕ, Q n ⟶ K.truncLE (n : ℤ)) (hf : ∀ n, QuasiIso (f n))
    {c : Cocone (Functor.ofSequence g)} (hc : IsColimit c) (α : c.pt ⟶ K)
    (hα : ∀ n : ℕ, c.ι.app n ≫ α = f n ≫ K.ιTruncLE (n : ℤ)) :
    QuasiIso α := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  set H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := A) (J := ℕ) (ComplexShape.up ℤ) i
  -- each stage of the ladder computes `H^i K` as soon as `i ≤ n`
  have hiso : ∀ n : ℕ, i ≤ (n : ℤ) → IsIso (H.map (c.ι.app n ≫ α)) := fun n hn => by
    have := hf n
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).1
      (quasiIsoAt_comp_of_eq_ιTruncLE (f n) (c.ι.app n) α (hα n) i hn)
  set n₀ := i.toNat
  have hn₀le : i ≤ (n₀ : ℤ) := Int.self_le_toNat i
  -- the system `n ↦ H^i (Q n)` is constant from `n₀` on
  have hev : (Functor.ofSequence g ⋙ H).IsEventuallyConstantFrom n₀ := by
    intro j φ
    have hj : i ≤ (j : ℤ) := hn₀le.trans (by exact_mod_cast leOfHom φ)
    have h₁ : IsIso (H.map (c.ι.app j ≫ α)) := hiso j hj
    have h₂ : IsIso (H.map (c.ι.app n₀ ≫ α)) := hiso n₀ hn₀le
    have w : (Functor.ofSequence g ⋙ H).map φ ≫ H.map (c.ι.app j ≫ α)
        = H.map (c.ι.app n₀ ≫ α) := by
      rw [Functor.comp_map, ← H.map_comp, ← Category.assoc, c.w φ]
    exact IsIso.of_isIso_fac_right w
  -- hence `H^i K` is the colimit of that system
  let u : Cocone (Functor.ofSequence g ⋙ H) :=
    Cocone.mk (H.obj K)
      { app := fun n => H.map (c.ι.app n ≫ α)
        naturality := fun j j' φ => by
          dsimp
          rw [Category.comp_id, ← H.map_comp, ← Category.assoc, c.w φ] }
  have hu₀ : IsIso (u.ι.app n₀) := hiso n₀ hn₀le
  have hu : IsColimit u := hev.isColimitOfIsIso u
  have hHc : IsColimit (H.mapCocone c) := isColimitOfPreserves H hc
  have heq : H.map α = (hHc.coconePointUniqueUpToIso hu).hom := by
    refine hHc.hom_ext (fun n => ?_)
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (H.map_comp _ _).symm
  show IsIso (H.map α)
  rw [heq]
  infer_instance

/-- Every object of `K(A)` receives a quasi-isomorphism from a `P`-cellular complex: it is the
colimit of the ladder of resolutions of the canonical truncations. -/
public lemma hasLeftResolutions_cellularLocalizerMorphism (P : ObjectProperty A)
    [P.ContainsZero] (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] :
    (cellularLocalizerMorphism P).HasLeftResolutions := by
  intro X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Q, f, g, hf, hle, hQ, -, hladder⟩ :=
    exists_sequence_quasiIso_truncLE P hsum hP K
  let c := colimit.cocone (Functor.ofSequence g)
  have hc : IsColimit c := colimit.isColimit _
  let s : Cocone (Functor.ofSequence g) :=
    Cocone.mk K (NatTrans.ofSequence (fun n => f n ≫ CochainComplex.ιTruncLE K (n : ℤ))
      (fun n => by
        rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
        exact (hladder n).trans (Category.comp_id _).symm))
  have hα : ∀ n : ℕ, (c.ι.app n : Q n ⟶ c.pt) ≫ hc.desc s
      = f n ≫ CochainComplex.ιTruncLE K (n : ℤ) :=
    fun n => hc.fac s n
  have hqi : QuasiIso (hc.desc s) :=
    quasiIso_of_isColimit_of_quasiIso_truncLE f hf hc _ hα
  -- each stage of the ladder is a resolution of `τ_{≤ n}` of the colimit
  have hstage : ∀ (n : ℕ) (i : ℤ), i ≤ (n : ℤ) →
      QuasiIsoAt (c.ι.app n ≫ (Iso.refl c.pt).hom) i := by
    intro n i hi
    have := hqi
    have := hf n
    have := quasiIsoAt_comp_of_eq_ιTruncLE (f n) (c.ι.app n) (hc.desc s) (hα n) i hi
    simpa using quasiIsoAt_of_comp_right (c.ι.app n) (hc.desc s) i (hφφ' := this)
  exact ⟨{ X₁ := ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj c.pt,
             ⟨c.pt, ⟨Q, g, c, hc, Iso.refl _, hle, hQ, hstage⟩, ⟨Iso.refl _⟩⟩⟩
           w := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (hc.desc s)
           hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hqi }⟩

/-- The inclusion of the `P`-cellular objects of `K(A)` is a left derivability structure for the
quasi-isomorphisms.

Given the existence of left resolutions, this is the formal part of the source's argument: the
quasi-isomorphisms of `K(A)` have a right calculus of fractions (Stacks 05RT), so the categories
of `P`-cellular resolutions of an object and of an arrow of `K(A)` are connected and nonempty,
and the inclusion is a localized equivalence. -/
public lemma isLeftDerivabilityStructure_cellularLocalizerMorphism (P : ObjectProperty A)
    (hres : (cellularLocalizerMorphism P).HasLeftResolutions) :
    (cellularLocalizerMorphism P).IsLeftDerivabilityStructure := by
  have h₁ := hres
  exact isLeftDerivabilityStructure_inclusionLocalizerMorphism _ _

/-- `F` sends a `P`-cellular acyclic complex to an acyclic complex.

Each stage `Q n` of a cellular presentation of an acyclic `S` is itself acyclic: in degrees
`i ≤ n` because `Q n ⟶ S` is an isomorphism on `H^i`, and in degrees `i > n` because `Q n` is
bounded above by `n`. So `F (Q n)` is acyclic by hypothesis, and `F (S)` is the colimit of the
`F (Q n)`, because `F` commutes with colimits over `ℕ` and colimits of complexes are computed
degreewise; exactness of `ℕ`-colimits in `B` then gives
`H^i (F S) = colim H^i (F (Q n)) = 0`. -/
public lemma acyclic_mapHomologicalComplex_of_isPCellular (F : A ⥤ B) [F.Additive]
    (P : ObjectProperty A)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F]
    {S : CochainComplex A ℤ} (hS : IsPCellular P S) (hac : S.Acyclic) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj S).Acyclic := by
  obtain ⟨Q, g, c, hc, e, hle, hQ, hstage⟩ := hS
  have hQac : ∀ n : ℕ, (Q n).Acyclic := by
    intro n
    have := hle n
    rw [HomologicalComplex.acyclic_iff]
    intro i
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    by_cases hi : i ≤ (n : ℤ)
    · have hiso : IsIso (HomologicalComplex.homologyMap (c.ι.app n ≫ e.hom) i) := by
        rw [← quasiIsoAt_iff_isIso_homologyMap]
        exact hstage n i hi
      exact IsZero.of_iso (hac i).isZero_homology (@asIso _ _ _ _ _ hiso)
    · rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact HomologicalComplex.ExactAt.of_isZero
        ((Q n).isZero_of_isStrictlyLE (n : ℤ) i (by omega))
  have hFQac : ∀ n : ℕ, ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Q n)).Acyclic :=
    fun n => hFP (n : ℤ) (Q n) (hle n) (hQ n) (hQac n)
  rw [HomologicalComplex.acyclic_iff]
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := B) (J := ℕ) (ComplexShape.up ℤ) i
  have hFc : IsColimit ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapCocone c) :=
    isColimitOfPreserves _ hc
  have hHc : IsColimit ((HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i).mapCocone
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapCocone c)) :=
    isColimitOfPreserves _ hFc
  have hz : IsZero ((HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj c.pt)) := by
    rw [IsZero.iff_id_eq_zero]
    exact hHc.hom_ext (fun n => ((hFQac n i).isZero_homology).eq_of_src _ _)
  exact IsZero.of_iso hz (((HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i).mapIso
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e)).symm)

/-- The mapping cone of a quasi-isomorphism is acyclic: it is the third object of the
distinguished triangle of `φ` in the homotopy category, and the acyclic complexes are the
triangulated subcategory whose associated class of morphisms is the quasi-isomorphisms. -/
public lemma acyclic_mappingCone {X Y : CochainComplex A ℤ} (φ : X ⟶ Y) (h : QuasiIso φ) :
    (CochainComplex.mappingCone φ).Acyclic := by
  have h1 : HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map φ) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact h
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at h1
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)).1 h1

/-- Conversely, a morphism whose mapping cone is acyclic is a quasi-isomorphism: the same
triangle, read in the other direction. -/
public lemma quasiIso_of_acyclic_mappingCone {X Y : CochainComplex A ℤ} (φ : X ⟶ Y)
    (h : (CochainComplex.mappingCone φ).Acyclic) : QuasiIso φ := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact (ObjectProperty.trW_iff_of_distinguished _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)).2
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 h)

/-- **The bounded above case: the first paragraph of the source's proof.** `F` sends a
quasi-isomorphism between complexes bounded above by `a` with all terms satisfying `P` to a
quasi-isomorphism.

The mapping cone of the quasi-isomorphism is acyclic (`acyclic_mappingCone`), is again bounded
above by `a` — its term in degree `i` vanishes as soon as both `X ^ {i + 1}` and `Y ^ i` do — and
its terms are the biproducts `X ^ {i + 1} ⊕ Y ^ i`, which satisfy `P` by `hsum`; note that this
last step uses the *equality* of objects underlying `homotopyCofiber.XIsoBiprod`, because `P` is
not assumed closed under isomorphisms anywhere in this file. So `hFP` applies and `F` of the cone
is acyclic. Since `F` is additive it commutes with the formation of mapping cones
(`CochainComplex.mappingCone.mapHomologicalComplexIso`), so the cone of `F (φ)` is acyclic, which
by `quasiIso_of_acyclic_mappingCone` is the assertion. -/
public lemma quasiIso_mapHomologicalComplex_of_isStrictlyLE (F : A ⥤ B) [F.Additive]
    (P : ObjectProperty A) (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    (a : ℤ) {X Y : CochainComplex A ℤ} (hX : X.IsStrictlyLE a) (hY : Y.IsStrictlyLE a)
    (hXP : ∀ i, P (X.X i)) (hYP : ∀ i, P (Y.X i)) (φ : X ⟶ Y) (hφ : QuasiIso φ) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have := hX
  have := hY
  have hle : (CochainComplex.mappingCone φ).IsStrictlyLE a := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨X.isZero_of_isStrictlyLE a (i + 1) (by omega), Y.isZero_of_isStrictlyLE a i hi⟩
  have hr : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i ((ComplexShape.up ℤ).next i) := fun i => by simp
  have hXeq : ∀ i : ℤ, (CochainComplex.mappingCone φ).X i =
      (X.X ((ComplexShape.up ℤ).next i) ⊞ Y.X i) := fun i => dite_eq_left (hr i)
  have hconeP : ∀ i, P ((CochainComplex.mappingCone φ).X i) := fun i => by
    rw [hXeq i]
    exact hsum _ _ (hXP _) (hYP i)
  have hcone := hFP a (CochainComplex.mappingCone φ) hle hconeP (acyclic_mappingCone φ hφ)
  refine quasiIso_of_acyclic_mappingCone _ ((HomologicalComplex.acyclic_iff _).2 (fun i => ?_))
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i).mapIso
    (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)).symm
  exact (hcone i).isZero_homology

section Comparison

/-- The commutation of two comparison morphisms. Suppose `wn` and `wn'` are transported from `β`
and `β'` along the isomorphisms `α` and `α'`, and that `α`, `β` and `α'`, `β'` become compatible
with `γ` and `δ` after pulling back along an isomorphism `uu` and a morphism `kk`. Then `wn` and
`wn'` form a commuting square with `γ` and `δ`. -/
public lemma comm_of_comm {D : Type*} [Category D] {U V V' X X' Y Y' : D}
    {α : V ⟶ X} {β : V ⟶ Y} {α' : V' ⟶ X'} {β' : V' ⟶ Y'} {γ : X ⟶ X'} {δ : Y ⟶ Y'}
    {wn : X ⟶ Y} {wn' : X' ⟶ Y'} {uu : U ⟶ V} {kk : U ⟶ V'} [IsIso α] [IsIso uu]
    (hw : α ≫ wn = β) (hw' : α' ≫ wn' = β')
    (h₁ : kk ≫ α' = uu ≫ α ≫ γ) (h₂ : kk ≫ β' = uu ≫ β ≫ δ) :
    γ ≫ wn' = wn ≫ δ := by
  rw [← cancel_epi α, ← cancel_epi uu, reassoc_of% hw, ← h₂, ← hw', reassoc_of% h₁]

/-- The functor `K ↦ H^i (F (K))` on cochain complexes of `A`: the functor along which the two
cellular presentations of a quasi-isomorphism are compared. -/
public noncomputable abbrev homF (F : A ⥤ B) [F.Additive] (i : ℤ) :
    CochainComplex A ℤ ⥤ B :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i

/-- `H^i (F (·))` is homotopy invariant: it identifies two morphisms of complexes which become
equal in the homotopy category. -/
public lemma homF_map_eq_of_quotient_map_eq (F : A ⥤ B) [F.Additive] (i : ℤ)
    {X Y : CochainComplex A ℤ} {u v : X ⟶ Y}
    (h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map v) :
    (homF F i).map u = (homF F i).map v := by
  have e := F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)
  have key : (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map u) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map v) := by
    have n₁ := e.hom.naturality u
    have n₂ := e.hom.naturality v
    dsimp only [Functor.comp_map] at n₁ n₂
    rw [← cancel_epi (e.hom.app X), ← n₁, ← n₂, h]
  exact (HomotopyCategory.homotopyOfEq _ _ key).homologyMap_eq i

/-- `H^i (F (·))` inverts quasi-isomorphisms between bounded above complexes with terms
satisfying `P`: this is `quasiIso_mapHomologicalComplex_of_isStrictlyLE`. -/
public lemma isIso_homF_map (F : A ⥤ B) [F.Additive] (P : ObjectProperty A)
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    (i a : ℤ) {X Y : CochainComplex A ℤ} (hX : X.IsStrictlyLE a) (hY : Y.IsStrictlyLE a)
    (hXP : ∀ j, P (X.X j)) (hYP : ∀ j, P (Y.X j)) (β : X ⟶ Y) (hβ : QuasiIso β) :
    IsIso ((homF F i).map β) := by
  have h := quasiIso_mapHomologicalComplex_of_isStrictlyLE F P hsum hFP a hX hY hXP hYP β hβ
  have h' := (quasiIso_iff _).1 h i
  rwa [quasiIsoAt_iff_isIso_homologyMap] at h'

/-- **`H^i (F (·))` descends to the derived category on bounded above complexes with terms
satisfying `P`.** Two morphisms out of such a complex which agree in `D (A)` have the same image
under `H^i (F (·))`: they agree after a quasi-isomorphism from some complex, which may be
resolved by a bounded above complex with terms satisfying `P` (Stacks 05T7(2)), on which
`H^i (F (·))` inverts quasi-isomorphisms. -/
public lemma homF_map_eq_of_Q_map_eq [HasDerivedCategory A] (F : A ⥤ B) [F.Additive]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    (i a : ℤ) {X Y : CochainComplex A ℤ} (hX : X.IsStrictlyLE a) (hXP : ∀ j, P (X.X j))
    {u v : X ⟶ Y} (h : DerivedCategory.Q.map u = DerivedCategory.Q.map v) :
    (homF F i).map u = (homF F i).map v := by
  have e := DerivedCategory.quotientCompQhIso A
  have hQh : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map v) := by
    have n₁ := e.hom.naturality u
    have n₂ := e.hom.naturality v
    dsimp only [Functor.comp_map] at n₁ n₂
    rw [← cancel_mono (e.hom.app Y), n₁, n₂, h]
  rw [MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] at hQh
  obtain ⟨Z, s, hs, hfac⟩ := hQh
  obtain ⟨Z, rfl⟩ := HomotopyCategory.quotient_obj_surjective Z
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective s
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hs
  have hs' : QuasiIso s := hs
  have hX' : X.IsStrictlyLE a := hX
  have hZ : CochainComplex.IsLE Z a := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have h1 : IsIso (HomologicalComplex.homologyMap s j) := by
      have := (quasiIso_iff s).1 hs j
      rwa [quasiIsoAt_iff_isIso_homologyMap] at this
    refine IsZero.of_iso ?_ (asIso (HomologicalComplex.homologyMap s j))
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact HomologicalComplex.ExactAt.of_isZero (X.isZero_of_isStrictlyLE a j hj)
  obtain ⟨Z', r, hr, hZ'P, hZ'LE⟩ := (CochainComplex.exists_quasiIso_prop P hP a).2 Z
  have hr' : QuasiIso r := hr
  have hrs : QuasiIso (r ≫ s) := quasiIso_comp r s
  have hiso := isIso_homF_map F P hsum hFP i a hZ'LE hX hZ'P hXP (r ≫ s) hrs
  have hquot : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ((r ≫ s) ≫ u) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map ((r ≫ s) ≫ v) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hfac]
  have key := homF_map_eq_of_quotient_map_eq F i hquot
  have key2 : (homF F i).map (r ≫ s) ≫ (homF F i).map u =
      (homF F i).map (r ≫ s) ≫ (homF F i).map v := by
    rw [← (homF F i).map_comp, ← (homF F i).map_comp]
    exact key
  exact (cancel_epi _).1 key2

/-- Composition with the canonical morphism `Q (T.truncLE m) ⟶ Q T` is injective on morphisms out
of an object of `D (A)` which is `≤ n` for some `n ≤ m`: the cokernel of `T.truncLE m ⟶ T` is
`T.truncGE (m + 1)`, so the third object of the corresponding distinguished triangle, shifted by
`-1`, is `≥ m + 2`, and there are no nonzero morphisms from an object which is `≤ m`. -/
public lemma eq_of_comp_Q_map_ιTruncLE [HasDerivedCategory A]
    {X : DerivedCategory A} {n m : ℤ} (hnm : n ≤ m) (hX : X.IsLE n)
    (T : CochainComplex A ℤ) {h₁ h₂ : X ⟶ DerivedCategory.Q.obj (T.truncLE m)}
    (h : h₁ ≫ DerivedCategory.Q.map (T.ιTruncLE m) =
      h₂ ≫ DerivedCategory.Q.map (T.ιTruncLE m)) :
    h₁ = h₂ := by
  have := hX
  have : X.IsLE m := DerivedCategory.TStructure.t.isLE_of_le X n m hnm
  suffices hz : h₁ - h₂ = 0 by rwa [sub_eq_zero] at hz
  have hSE := T.shortComplexTruncLE_shortExact m
  have hd : (h₁ - h₂) ≫ DerivedCategory.Q.map (T.ιTruncLE m) = 0 := by
    rw [Preadditive.sub_comp, h, sub_self]
  obtain ⟨w, hw⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _
    (Pretriangulated.inv_rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished hSE))
    (h₁ - h₂) hd
  have hGE : DerivedCategory.TStructure.t.IsGE
      (DerivedCategory.Q.obj ((T.shortComplexTruncLE m).X₃)) (m + 1) :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (asIso (DerivedCategory.Q.map
        (T.shortComplexTruncLEX₃ToTruncGE m (m + 1) (by lia)))).symm (m + 1)
  have hGE' : DerivedCategory.TStructure.t.IsGE (Pretriangulated.Triangle.invRotate
      (DerivedCategory.triangleOfSES hSE)).obj₁ (m + 2) :=
    DerivedCategory.TStructure.t.isGE_shift
      (DerivedCategory.Q.obj ((T.shortComplexTruncLE m).X₃)) (m + 1) (-1) (m + 2) (by lia)
  rw [hw, DerivedCategory.TStructure.t.zero w m (m + 2) (by lia)]
  exact zero_comp

/-- A morphism `ρ : R ⟶ T` which is an isomorphism on `H^i` for `i ≤ m`, with `R` strictly `≤ m`,
factors in `D (A)` as an isomorphism `Q R ≅ Q (T.truncLE m)` followed by `Q T.ιTruncLE m`. -/
private lemma exists_isIso_comp_Q_map_ιTruncLE [HasDerivedCategory A] {m : ℤ}
    {R T : CochainComplex A ℤ} (hR : R.IsStrictlyLE m) (ρ : R ⟶ T)
    (hρ : ∀ i : ℤ, i ≤ m → QuasiIsoAt ρ i) :
    ∃ σ : DerivedCategory.Q.obj R ⟶ DerivedCategory.Q.obj (T.truncLE m),
      IsIso σ ∧ σ ≫ DerivedCategory.Q.map (T.ιTruncLE m) = DerivedCategory.Q.map ρ := by
  have hq : QuasiIso (CochainComplex.truncLEMap ρ m) := by
    rw [CochainComplex.quasiIso_truncLEMap_iff]
    exact hρ
  have : IsIso (DerivedCategory.Q.map (R.ιTruncLE m)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have : IsIso (DerivedCategory.Q.map (CochainComplex.truncLEMap ρ m)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  refine ⟨inv (DerivedCategory.Q.map (R.ιTruncLE m)) ≫
    DerivedCategory.Q.map (CochainComplex.truncLEMap ρ m), inferInstance, ?_⟩
  rw [Category.assoc, ← DerivedCategory.Q.map_comp,
    CochainComplex.ιTruncLE_naturality, DerivedCategory.Q.map_comp, IsIso.inv_hom_id_assoc]

/-- Composition with `Q ρ` is injective on morphisms out of an object of `D (A)` which is `≤ n`,
when `ρ : R ⟶ T` is an isomorphism on `H^i` for all `i ≤ m`, `R` is strictly `≤ m` and `n ≤ m`:
such a `ρ` factors as a quasi-isomorphism `R ⟶ T.truncLE m` followed by the canonical
`T.truncLE m ⟶ T`. -/
public lemma eq_of_comp_Q_map [HasDerivedCategory A]
    {X : DerivedCategory A} {n m : ℤ} (hnm : n ≤ m) (hX : X.IsLE n)
    {R T : CochainComplex A ℤ} (hR : R.IsStrictlyLE m) (ρ : R ⟶ T)
    (hρ : ∀ i : ℤ, i ≤ m → QuasiIsoAt ρ i)
    {h₁ h₂ : X ⟶ DerivedCategory.Q.obj R}
    (h : h₁ ≫ DerivedCategory.Q.map ρ = h₂ ≫ DerivedCategory.Q.map ρ) :
    h₁ = h₂ := by
  obtain ⟨σ, hσiso, hσι⟩ := exists_isIso_comp_Q_map_ιTruncLE hR ρ hρ
  have := hσiso
  refine (cancel_mono σ).1 (eq_of_comp_Q_map_ιTruncLE hnm hX T ?_)
  rw [Category.assoc, Category.assoc, hσι]
  exact h

/-- A morphism `φ : Q X ⟶ Q Y` in `D (A)` with `X` strictly `≤ m` becomes, after precomposing with
a quasi-isomorphism `a` from a strictly `≤ m` complex `V` with terms satisfying `P`, the image
of a morphism of complexes `b`. -/
private lemma exists_quasiIso_comp_eq_Q_map [HasDerivedCategory A]
    (P : ObjectProperty A) [P.ContainsZero]
    (hP : ∀ Z : A, ∃ (W : A) (_ : P W) (p : W ⟶ Z), Epi p) (m : ℤ)
    {X Y : CochainComplex A ℤ} (hX : X.IsStrictlyLE m)
    (φ : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y) :
    ∃ (V : CochainComplex A ℤ) (_ : V.IsStrictlyLE m) (_ : ∀ j, P (V.X j))
      (a : V ⟶ X) (_ : QuasiIso a) (b : V ⟶ Y),
      DerivedCategory.Q.map a ≫ φ = DerivedCategory.Q.map b := by
  obtain ⟨X', hX'LE, s, hs, g, hfac⟩ := DerivedCategory.right_fac_of_isStrictlyLE φ m
  obtain ⟨V, r, -, hr, hVP, hVLE⟩ := (CochainComplex.exists_quasiIso_prop P hP m).1 X'
  have : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hs
  refine ⟨V, hVLE, hVP, r ≫ s, inferInstance, r ≫ g, ?_⟩
  rw [hfac]
  simp

/-- **One stage of the comparison of two cellular presentations.** Let `α : S ⟶ T` be a
quasi-isomorphism, let `X` and `Y` be strictly `≤ m` and let `σ : X ⟶ S` and `ρ : Y ⟶ T` be
isomorphisms on `H^j` for every `j ≤ m`. Then `X` and `Y` receive quasi-isomorphisms `a`, `b` from
a common complex `V` which is strictly `≤ m` with all terms satisfying `P`, in such a way that the
square formed with `α` commutes in `D (A)`.

Indeed `σ ≫ α` and `ρ` both factor through `T.truncLE m` by quasi-isomorphisms
(`CochainComplex.quasiIso_truncLEMap_iff`), which produces an isomorphism
`Q X ≅ Q Y` in `D (A)` over `Q T`; presenting it as a right fraction with strictly `≤ m` apex
(`DerivedCategory.right_fac_of_isStrictlyLE`) and resolving that apex by Stacks 05T7(1) gives
`V`. -/
@[sga "4½ Etat_0 3.1.9" "special case"]
public lemma exists_common_resolution [HasDerivedCategory A]
    (P : ObjectProperty A) [P.ContainsZero]
    (hP : ∀ Z : A, ∃ (W : A) (_ : P W) (p : W ⟶ Z), Epi p)
    {S T : CochainComplex A ℤ} (α : S ⟶ T) (hα : QuasiIso α) (m : ℤ)
    {X Y : CochainComplex A ℤ} (hX : X.IsStrictlyLE m) (hY : Y.IsStrictlyLE m)
    (σ : X ⟶ S) (hσ : ∀ j : ℤ, j ≤ m → QuasiIsoAt σ j)
    (ρ : Y ⟶ T) (hρ : ∀ j : ℤ, j ≤ m → QuasiIsoAt ρ j) :
    ∃ (V : CochainComplex A ℤ) (_ : V.IsStrictlyLE m) (_ : ∀ j, P (V.X j))
      (a : V ⟶ X) (_ : QuasiIso a) (b : V ⟶ Y) (_ : QuasiIso b),
      DerivedCategory.Q.map (a ≫ σ ≫ α) = DerivedCategory.Q.map (b ≫ ρ) := by
  obtain ⟨σ₁, hσ₁, hσ₁ι⟩ := exists_isIso_comp_Q_map_ιTruncLE hX (σ ≫ α) fun j hj =>
    have := hσ j hj
    have := hα.quasiIsoAt j
    inferInstance
  obtain ⟨σ₂, hσ₂, hσ₂ι⟩ := exists_isIso_comp_Q_map_ιTruncLE hY ρ hρ
  have := hσ₂
  obtain ⟨V, hVLE, hVP, a, ha, b, hab⟩ := exists_quasiIso_comp_eq_Q_map P hP m hX (σ₁ ≫ inv σ₂)
  have : IsIso (DerivedCategory.Q.map b) := by
    rw [← hab]
    infer_instance
  refine ⟨V, hVLE, hVP, a, ha, b, (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 this, ?_⟩
  rw [DerivedCategory.Q.map_comp a, ← hσ₁ι, DerivedCategory.Q.map_comp b, ← hσ₂ι, ← hab]
  simp

/-- **Comparison of two consecutive stages.** If `a' : V' ⟶ W` is a quasi-isomorphism and
`a : V ⟶ W` is any morphism with `V` strictly `≤ m`, then `V` receives a quasi-isomorphism from a
complex `U` which is strictly `≤ m` with terms satisfying `P` and which maps to `V'` over `W`,
the square commuting in `D (A)`. -/
public lemma exists_refinement [HasDerivedCategory A]
    (P : ObjectProperty A) [P.ContainsZero]
    (hP : ∀ Z : A, ∃ (W : A) (_ : P W) (p : W ⟶ Z), Epi p)
    (m : ℤ) {V V' W : CochainComplex A ℤ} (hV : V.IsStrictlyLE m)
    (a : V ⟶ W) (a' : V' ⟶ W) (ha' : QuasiIso a') :
    ∃ (U : CochainComplex A ℤ) (_ : U.IsStrictlyLE m) (_ : ∀ j, P (U.X j))
      (u : U ⟶ V) (_ : QuasiIso u) (k : U ⟶ V'),
      DerivedCategory.Q.map (k ≫ a') = DerivedCategory.Q.map (u ≫ a) := by
  have : IsIso (DerivedCategory.Q.map a') := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 ha'
  obtain ⟨U, hULE, hUP, u, hu, k, hk⟩ := exists_quasiIso_comp_eq_Q_map P hP m hV
    (DerivedCategory.Q.map a ≫ inv (DerivedCategory.Q.map a'))
  refine ⟨U, hULE, hUP, u, hu, k, ?_⟩
  rw [DerivedCategory.Q.map_comp, ← hk]
  simp

end Comparison

end Concrete

end StacksDraft.UnboundedLeftDerivedFunctor
