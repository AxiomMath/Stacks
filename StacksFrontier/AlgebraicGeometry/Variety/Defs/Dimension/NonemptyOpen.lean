module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Dimension of a nonempty open subscheme

Let `X` be an irreducible scheme locally of finite type over a field. Every nonempty open subset
of `X` has the same Krull dimension as `X`, and consequently the dimension of `X` is also its
dimension at every one of its points.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen` identifies the dimension of `X` with that
  of any nonempty open subset.
* `AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible` identifies the
  dimension of `X` with its dimension at any point.

## Implementation notes

A locally algebraic `k`-scheme is represented by its structure morphism to `Spec k`, equipped
with Mathlib's `LocallyOfFiniteType` instance. An open subset is viewed with its subspace
topology when it occurs as the type argument of `topologicalKrullDim`. Both the global and the
pointwise dimension are Krull dimensions of the underlying topological space.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Local Krull dimension is preserved by open embeddings. -/
private theorem localKrullDim_eq_of_isOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {g : X → Y} (hg : Topology.IsOpenEmbedding g) (x : X) :
    TopologicalSpace.localKrullDim X x = TopologicalSpace.localKrullDim Y (g x) := by
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
    ← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  exact (hg.topologicalKrullDimAt_eq x).symm

/-- On an irreducible scheme locally of finite type over a field, the local dimension at a point
of an affine open is the dimension of that affine open. -/
@[sga "3 VIB 1.5" "partial"]
private theorem localKrullDim_eq_dim_affineOpen
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] (V : X.affineOpens) (x : V.1) :
    TopologicalSpace.localKrullDim X x.1 = topologicalKrullDim (V.1 : Set X) := by
  let e := V.2.isoSpec.hom.homeomorph
  let q : PrimeSpectrum Γ(X, V.1) := e x
  let g := (f.appLE ⊤ V.1 (by simp)).hom
  let : Algebra k Γ(X, V.1) :=
    (g.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  let : Algebra.FiniteType k Γ(X, V.1) := by
    apply RingHom.FiniteType.comp
      (f.finiteType_appLE (isAffineOpen_top (Spec (.of k))) V.2 (by simp))
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective
  let : Nonempty (V : Set X) := ⟨x⟩
  let : IrreducibleSpace (V : Set X) :=
    V.1.isOpen.isOpenEmbedding_subtypeVal.irreducibleSpace
  let : IrreducibleSpace V.1 := by
    change IrreducibleSpace (V : Set X)
    infer_instance
  let : IrreducibleSpace (PrimeSpectrum Γ(X, V.1)) :=
    e.irreducibleSpace_iff.mp inferInstance
  have hdim :
      TopologicalSpace.localKrullDim (PrimeSpectrum Γ(X, V.1)) q =
        topologicalKrullDim (PrimeSpectrum Γ(X, V.1)) := by
    have h := PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height k q
    rw [h.1, irreducibleComponents_eq_singleton]
    have hUniv :
        topologicalKrullDim (Set.univ : Set (PrimeSpectrum Γ(X, V.1))) =
          topologicalKrullDim (PrimeSpectrum Γ(X, V.1)) :=
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph
    calc
      (⨆ Z, ⨆ (_ : Z = Set.univ ∧ q ∈ Z), topologicalKrullDim Z) =
          topologicalKrullDim (Set.univ : Set (PrimeSpectrum Γ(X, V.1))) := by
        apply le_antisymm
        · refine iSup_le fun Z => iSup_le fun hZ => ?_
          rcases hZ with ⟨rfl, _⟩
          exact le_rfl
        · refine le_iSup_of_le Set.univ ?_
          exact le_iSup_of_le ⟨rfl, Set.mem_univ q⟩ le_rfl
      _ = topologicalKrullDim (PrimeSpectrum Γ(X, V.1)) := hUniv
  calc
    TopologicalSpace.localKrullDim X x.1 =
        TopologicalSpace.localKrullDim (V.1 : Set X) x :=
      (localKrullDim_eq_of_isOpenEmbedding V.1.isOpen.isOpenEmbedding_subtypeVal x).symm
    _ = TopologicalSpace.localKrullDim (PrimeSpectrum Γ(X, V.1)) q :=
      localKrullDim_eq_of_isOpenEmbedding e.isOpenEmbedding x
    _ = topologicalKrullDim (PrimeSpectrum Γ(X, V.1)) := hdim
    _ = topologicalKrullDim (V.1 : Set X) :=
      (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm

/-- Any two nonempty affine opens of an irreducible scheme locally of finite type over a field
have the same dimension. -/
@[sga "3 VIB 1.5" "special case"]
private theorem dim_affineOpen_eq_of_nonempty
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X]
    (V W : X.affineOpens) (hV : (V : Set X).Nonempty) (hW : (W : Set X).Nonempty) :
    topologicalKrullDim (V.1 : Set X) = topologicalKrullDim (W.1 : Set X) := by
  have hint : ((V.1 : Set X) ∩ (W.1 : Set X)).Nonempty := by
    have hV' : (Set.univ ∩ (V : Set X)).Nonempty := by simpa using hV
    have hW' : (Set.univ ∩ (W : Set X)).Nonempty := by simpa using hW
    have hI := (IrreducibleSpace.isIrreducible_univ X).2
      (V : Set X) (W : Set X) V.1.isOpen W.1.isOpen hV' hW'
    simpa using hI
  obtain ⟨x, hx⟩ := hint
  calc
    topologicalKrullDim (V.1 : Set X) = TopologicalSpace.localKrullDim X x :=
      (localKrullDim_eq_dim_affineOpen k X f V ⟨x, hx.1⟩).symm
    _ = topologicalKrullDim (W.1 : Set X) :=
      localKrullDim_eq_dim_affineOpen k X f W ⟨x, hx.2⟩

/-- A nonempty open subset of an irreducible scheme locally of finite type over a field has the
same Krull dimension as the whole scheme. -/
@[stacks 0A21 "dimension_nonempty_open", sga "3 VIB 1.5" "more general"]
theorem topologicalKrullDim_eq_of_isOpen
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] (U : Set X) (hU : IsOpen U)
    (hne : U.Nonempty) :
    topologicalKrullDim X = topologicalKrullDim U := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨_, ⟨V₀, hV₀aff, rfl⟩, hxV₀, hV₀U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx₀ hU
  let V₀ : X.affineOpens := ⟨V₀, hV₀aff⟩
  have hV₀ : (V₀.1 : Set X).Nonempty := ⟨x₀, hxV₀⟩
  let d := topologicalKrullDim (V₀.1 : Set X)
  have hlocalX : ∀ x : X, TopologicalSpace.localKrullDim X x = d := by
    intro x
    obtain ⟨_, ⟨Vopen, hVopen, rfl⟩, hxV, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let V : X.affineOpens := ⟨Vopen, hVopen⟩
    have hVne : (V.1 : Set X).Nonempty := ⟨x, hxV⟩
    calc
      TopologicalSpace.localKrullDim X x = topologicalKrullDim (V.1 : Set X) :=
        localKrullDim_eq_dim_affineOpen k X f V ⟨x, hxV⟩
      _ = d := dim_affineOpen_eq_of_nonempty k X f V V₀ hVne hV₀
  have hlocalU : ∀ y : U, TopologicalSpace.localKrullDim U y = d := by
    intro y
    calc
      TopologicalSpace.localKrullDim U y = TopologicalSpace.localKrullDim X y.1 :=
        localKrullDim_eq_of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal y
      _ = d := hlocalX y.1
  have : Nonempty X := ⟨x₀⟩
  have : Nonempty U := ⟨⟨x₀, hx₀⟩⟩
  calc
    topologicalKrullDim X = ⨆ x : X, TopologicalSpace.localKrullDim X x :=
      TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim X
    _ = d := by rw [iSup_congr hlocalX, iSup_const]
    _ = ⨆ y : U, TopologicalSpace.localKrullDim U y := by
      rw [iSup_congr hlocalU, iSup_const]
    _ = topologicalKrullDim U :=
      (TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim U).symm

/-- The dimension of an irreducible scheme locally of finite type over a field equals its
dimension at every point. -/
@[stacks 0A21 "dimension_at_point_irreducible"]
theorem topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] (x : X) :
    topologicalKrullDim X = topologicalKrullDimAt X x := by
  obtain ⟨⟨U, hxU, hU, hdim⟩, _⟩ := topologicalKrullDimAt_isLeast X x
  exact (topologicalKrullDim_eq_of_isOpen k X f U hU ⟨x, hxU⟩).trans hdim.symm

end AlgebraicGeometry

end
