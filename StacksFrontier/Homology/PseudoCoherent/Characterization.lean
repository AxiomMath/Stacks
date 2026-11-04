module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Ring.Shrink
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.PseudoCoherent.Homology
public import StacksFrontier.Homology.PseudoCoherent.Triangle
import StacksCore.Tactic.EgaSgaAttribute
import Mathlib

@[expose] public section

/-!
# Characterizations of pseudo-coherent objects of the derived category of a ring

Let `R` be a ring and let `D(R)` be the derived category of `R`-modules. An object of `D(R)` is
pseudo-coherent when it is represented by a bounded-above complex of finite free modules. This
module proves that pseudo-coherence is equivalent to `m`-pseudo-coherence for every integer `m`,
and to admitting a bounded-above representative by finite *projective* modules; when the
cohomology vanishes above a degree `b`, the finite free representative may be chosen to vanish
above `b` as well. The characterizations are then used to show that pseudo-coherence passes from
a binary biproduct to each of its summands.

## Main definitions

* `PseudoCoherence.IsBoundedAboveFiniteFree`: a cochain complex vanishes in all sufficiently
  large degrees and has finite free terms.
* `PseudoCoherence.IsPseudoCoherent`: pseudo-coherence of an object of `D(R)`.

## Main results

* `PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective`: the three
  equivalent forms of pseudo-coherence, together with the prescribed upper bound for the
  finite free representative.
* `PseudoCoherence.pseudoCoherent_iff_all`: the all-degree characterization, valid also when the
  module carriers are smaller than the coefficient ring.
* `PseudoCoherence.isPseudoCoherentFrom_and_pseudoCoherent_of_biproduct`: both forms of
  pseudo-coherence pass from a binary biproduct to its two summands.

## Implementation notes

Complexes are represented by objects of the derived category, so a quasi-isomorphism of complexes
appears as an isomorphism in `D(R)` and the vanishing of a cohomology module as that module being
a zero object. The main equivalence is proved in a common ambient universe containing both the
ring and the module carriers, where finite free complements fit; the all-degree and
prescribed-bound statements are then transported to an arbitrary carrier universe along a
coefficient ring equivalence when the ring is small, and derived from vanishing otherwise.

The successive finite free approximations of an object are assembled into a sequence indexed by
`ℕ` whose colimit is the required finite free representative; the sequence is eventually constant
in every fixed degree, which is what makes the colimit termwise finite free.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StacksDraft.PseudoCoherence
open scoped ZeroObject

-- The finite free approximation tower below identifies mapping-cone terms with biproducts and
-- reads instances through those identifications; this needs the pre-4.x defeq transparency.
set_option backward.isDefEq.respectTransparency false


attribute [local instance] HasDerivedCategory.standard

namespace PseudoCoherence

universe u v u' w

/-! ### Pseudo-coherence

The results below concern `StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree` and
`StacksDraft.PseudoCoherence.IsPseudoCoherent`. -/
export StacksDraft.PseudoCoherence (IsBoundedAboveFiniteFree IsPseudoCoherent
  mapDerivedCategoryHomologyIso
  pseudoCoherent_iff_of_ringEquiv
  pseudoCoherent_of_isZero
  finiteProjectiveRepresentative_of_pseudoCoherent
  isBoundedFiniteFree_single
  pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
  pseudoCoherent_iff_all
  exists_finiteFree_representative_le
  isPseudoCoherentFrom_of_homology_isZero)

/-- If `K ≅ L` in the derived category, then `L` is `m`-pseudo-coherent whenever `K` is, for every
`m`, and `L` is pseudo-coherent whenever `K` is. -/
theorem pseudoCoherent_iso {R : Type u} [Ring R]
    {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L) :
    (∀ m, IsPseudoCoherentFrom K m → IsPseudoCoherentFrom L m) ∧
    (IsPseudoCoherent K → IsPseudoCoherent L) :=
  ⟨fun _ h ↦ h.ofIso e, fun h ↦ h.ofIso e⟩

/-- **Stacks 064X.** Each summand of an `m`-pseudo-coherent binary biproduct is
`m`-pseudo-coherent, and each summand of a pseudo-coherent binary biproduct is
pseudo-coherent. -/
@[stacks 064X, sga "6 I 2.12" "necessity"]
theorem isPseudoCoherentFrom_and_pseudoCoherent_of_biproduct
    {R : Type u} [Ring R] (K L : DerivedCategory (ModuleCat.{v} R)) (m : ℤ) :
    (IsPseudoCoherentFrom (K ⊞ L) m →
      IsPseudoCoherentFrom K m ∧ IsPseudoCoherentFrom L m) ∧
    (IsPseudoCoherent (K ⊞ L) → IsPseudoCoherent K ∧ IsPseudoCoherent L) := by
  have fixed (n : ℤ) (h : IsPseudoCoherentFrom (K ⊞ L) n) :
      IsPseudoCoherentFrom K n ∧ IsPseudoCoherentFrom L n := by
    have ofIso {X Y : DerivedCategory (ModuleCat.{v} R)} {j : ℤ}
        (hX : IsPseudoCoherentFrom X j) (e : X ≅ Y) : IsPseudoCoherentFrom Y j := by
      obtain ⟨F, hF, β, hβ, eβ⟩ := hX
      refine ⟨F, hF, β ≫ e.hom, ?_, ?_⟩
      · intro i hi
        rw [Functor.map_comp]
        have := hβ i hi
        exact IsIso.comp_isIso
      · rw [Functor.map_comp]
        have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) j).map e.hom) :=
          IsIso.epi_of_iso _
        exact epi_comp _ _
    have hsum0 := h
    obtain ⟨E, hE, α, hα, -⟩ := h
    obtain ⟨b, hb⟩ := hE.upperBound
    let : E.IsStrictlyLE b := hb
    let N := max n b + 1
    have hnN : n ≤ N := by simp only [N]; omega
    have vanish (i : ℤ) (hi : N ≤ i) :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj (K ⊞ L)) := by
      have hEi : IsZero
          ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
            (ComplexShape.up ℤ) i).obj E) :=
        ShortComplex.isZero_homology_of_isZero_X₂ (E.sc i)
          (E.isZero_of_isStrictlyLE b i (by omega))
      have hQEi : IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
            (DerivedCategory.Q.obj E)) :=
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app E).isZero_iff.mpr hEi
      have := hα i (by omega)
      exact hQEi.of_iso (asIso ((DerivedCategory.homologyFunctor
        (ModuleCat.{v} R) i).map α)).symm
    have vanishK (i : ℤ) (hi : N ≤ i) :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K) := by
      rw [IsZero.iff_id_eq_zero,
        ← (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_id,
        show 𝟙 K = biprod.inl ≫ biprod.fst by simp,
        Functor.map_comp, (vanish i hi).eq_of_src
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map biprod.fst) 0, comp_zero]
    have vanishL (i : ℤ) (hi : N ≤ i) :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj L) := by
      rw [IsZero.iff_id_eq_zero,
        ← (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map_id,
        show 𝟙 L = biprod.inr ≫ biprod.snd by simp,
        Functor.map_comp, (vanish i hi).eq_of_src
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map biprod.snd) 0, comp_zero]
    have hKN : IsPseudoCoherentFrom K N :=
      isPseudoCoherentFrom_of_homology_isZero K N vanishK
    have hLN : IsPseudoCoherentFrom L N :=
      isPseudoCoherentFrom_of_homology_isZero L N vanishL
    have hsum (i : ℤ) (hi : n ≤ i) : IsPseudoCoherentFrom (K ⊞ L) i := by
      rcases hi.eq_or_lt with rfl | hi
      · exact hsum0
      obtain ⟨E, hE, α, hα, eα⟩ := hsum0
      refine ⟨E, hE, α, fun j hj ↦ hα j (by omega), ?_⟩
      have := hα i hi
      infer_instance
    let descend : ∀ (i : ℤ) (_ : i ≤ N),
        n ≤ i → IsPseudoCoherentFrom K i ∧ IsPseudoCoherentFrom L i :=
      Int.leInductionDown (m := N) (fun _ ↦ ⟨hKN, hLN⟩) (fun i hiN ih hni ↦ by
          have hs := hsum (i - 1) hni
          have hKi : IsPseudoCoherentFrom K (i - 1 + 1) := by
            simpa only [sub_add_cancel] using (ih (by omega)).1
          have hLi : IsPseudoCoherentFrom L (i - 1 + 1) := by
            simpa only [sub_add_cancel] using (ih (by omega)).2
          have hL' := PseudoCoherence.isPseudoCoherent_of_distinguished_one (i - 1)
            (binaryBiproductTriangle K L)
            (binaryBiproductTriangle_distinguished K L) hKi hs
          have hK' := PseudoCoherence.isPseudoCoherent_of_distinguished_one (i - 1)
            (binaryBiproductTriangle L K)
            (binaryBiproductTriangle_distinguished L K) hLi
            (ofIso hs (biprod.braiding K L))
          exact ⟨hK', hL'⟩)
    exact descend n hnN le_rfl
  refine ⟨fixed m, ?_⟩
  intro h
  have hall := (pseudoCoherent_iff_all
    (K ⊞ L)).1 h
  constructor
  · exact (pseudoCoherent_iff_all
      K).2 (fun n ↦ (fixed n (hall n)).1)
  · exact (pseudoCoherent_iff_all
      L).2 (fun n ↦ (fixed n (hall n)).2)

end PseudoCoherence
