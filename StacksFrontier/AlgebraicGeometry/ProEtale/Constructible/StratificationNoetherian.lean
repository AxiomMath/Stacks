module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Stratification
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.StratificationSupplement
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# Constructible stratifications of Noetherian schemes

On a Noetherian scheme a finite partition of the whole scheme into locally closed subschemes
restricts to every open subscheme, and every such partition is refined by one whose strata are
connected: each stratum is Noetherian, so it has finitely many connected components, each of
them open in it.

## Main definitions

* `AlgebraicGeometry.Scheme.ConstructibleStratification.restrict`: the restriction of a
  stratification of `X` to an open subscheme.

## Main results

* `AlgebraicGeometry.Scheme.ConstructibleStratification.exists_connectedSpace_refines`: a
  stratification is refined by one with connected strata, each an open subscheme of a stratum.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.ConstructibleStratification

variable {X : Scheme.{u}} {U : X.Opens}

private noncomputable def connectedComponentRepresentative
    (Y : Type*) [TopologicalSpace Y] [Finite (ConnectedComponents Y)]
    (c : _root_.ConnectedComponents Y) : Y :=
  Classical.choose (ConnectedComponents.surjective_coe c)

private theorem connectedComponentRepresentative_spec
    (Y : Type*) [TopologicalSpace Y] [Finite (ConnectedComponents Y)]
    (c : _root_.ConnectedComponents Y) :
    _root_.ConnectedComponents.mk (connectedComponentRepresentative Y c) = c :=
  Classical.choose_spec (ConnectedComponents.surjective_coe c)

private noncomputable def connectedComponentOpen
    (Y : Type*) [TopologicalSpace Y] [Finite (_root_.ConnectedComponents Y)]
    (c : _root_.ConnectedComponents Y) : TopologicalSpace.Opens Y :=
  ⟨connectedComponent (connectedComponentRepresentative Y c),
    (isClopen_connectedComponent_of_finite_connectedComponents _).2⟩

private theorem connectedSpace_connectedComponentOpen
    (Y : Type*) [TopologicalSpace Y] [Finite (_root_.ConnectedComponents Y)]
    (c : _root_.ConnectedComponents Y) : ConnectedSpace (connectedComponentOpen Y c) := by
  unfold connectedComponentOpen
  change ConnectedSpace (↑(connectedComponent (connectedComponentRepresentative Y c)))
  exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- Every point of the chosen open component `c` lies in the connected component `c`. -/
private theorem mk_eq_of_mem_connectedComponentOpen
    (Y : Type*) [TopologicalSpace Y] [Finite (_root_.ConnectedComponents Y)]
    (c : _root_.ConnectedComponents Y) (z : connectedComponentOpen Y c) :
    _root_.ConnectedComponents.mk z.1 = c :=
  (ConnectedComponents.coe_eq_coe'.mpr z.2).trans (connectedComponentRepresentative_spec Y c)

/-- **A stratification is refined by one with connected strata.** On a Noetherian scheme, each
stratum has finitely many connected components, which are open in it; they form a stratification
each of whose strata is an open subscheme of a stratum of the given one. -/
theorem exists_connectedSpace_refines [IsNoetherian X] (s : ConstructibleStratification X U) :
    ∃ t : ConstructibleStratification X U,
      (∀ j : Fin t.n, ConnectedSpace (t.piece j)) ∧
      ∀ j : Fin t.n, ∃ i : Fin s.n, ∃ q : t.piece j ⟶ s.piece i,
        IsOpenImmersion q ∧ q ≫ s.inclusion i = t.inclusion j := by
  let (i : Fin s.n) : IsImmersion (s.inclusion i) := s.isImmersion i
  let (i : Fin s.n) : TopologicalSpace.NoetherianSpace (s.piece i) :=
    (s.inclusion i).isEmbedding.noetherianSpace
  let : ∀ i : Fin s.n, Finite (_root_.ConnectedComponents (s.piece i)) := fun i =>
    NoetherianSpace.finite_connectedComponents (s.piece i)
  let J := Σ i : Fin s.n, _root_.ConnectedComponents (s.piece i)
  let : Finite J := inferInstance
  let : Fintype J := Fintype.ofFinite J
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let g (j : J) : (s.piece j.1).Opens := connectedComponentOpen _ j.2
  let f (j : J) : (g j).toScheme ⟶ X := (g j).ι ≫ s.inclusion j.1
  have hsub (j : J) : Set.range (f j).base ⊆ Set.range (s.inclusion j.1).base := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(g j).ι.base y, rfl⟩
  let t : ConstructibleStratification X U := {
    n := Fintype.card J
    piece := fun j => (g (e.symm j)).toScheme
    inclusion := fun j => f (e.symm j)
    isImmersion := fun _ => IsImmersion.comp _ _
    contained := fun j => (hsub (e.symm j)).trans (s.contained _)
    constructible := by
      intro j
      let : TopologicalSpace.NoetherianSpace U := Topology.IsInducing.subtypeVal.noetherianSpace
      exact AlgebraicGeometry.isConstructible_of_isLocallyClosed
        ((f (e.symm j)).isLocallyClosed_range.preimage (Scheme.Hom.continuous U.ι))
    pairwise_disjoint := by
      intro j k hjk
      have hpair : ∀ a b : J, a ≠ b → Disjoint
          (Set.range (f a).base) (Set.range (f b).base) := by
        rintro ⟨i, c⟩ ⟨i', d⟩ hab
        by_cases hii : i = i'
        · subst i'
          refine Set.disjoint_left.mpr ?_
          rintro x ⟨y, rfl⟩ ⟨z, hz⟩
          have hEq : (g ⟨i, c⟩).ι.base y = (g ⟨i, d⟩).ι.base z :=
            (s.inclusion i).isEmbedding.injective hz.symm
          exact hab (congrArg (Sigma.mk i) <|
            (mk_eq_of_mem_connectedComponentOpen _ c y).symm.trans <|
              (congrArg _ hEq).trans (mk_eq_of_mem_connectedComponentOpen _ d z))
        · exact (s.pairwise_disjoint i i' hii).mono (hsub ⟨i, c⟩) (hsub ⟨i', d⟩)
      exact hpair (e.symm j) (e.symm k) (fun h => hjk (by simpa using congrArg e h))
    covers := by
      rw [Set.Subset.antisymm_iff]
      constructor
      · intro x hx
        rw [s.covers] at hx
        rcases Set.mem_iUnion.mp hx with ⟨i, y, hxy⟩
        let c := _root_.ConnectedComponents.mk y
        have hyc : y ∈ connectedComponent (connectedComponentRepresentative _ c) :=
          (ConnectedComponents.coe_eq_coe').mp (connectedComponentRepresentative_spec _ c).symm
        refine Set.mem_iUnion.mpr ⟨e ⟨i, c⟩, ?_⟩
        rw [e.symm_apply_apply]
        exact ⟨⟨y, hyc⟩, hxy⟩
      · exact Set.iUnion_subset fun j => (hsub (e.symm j)).trans (s.contained _)
  }
  refine ⟨t, fun j => ?_, fun j => ⟨(e.symm j).1, (g (e.symm j)).ι, inferInstance, rfl⟩⟩
  change ConnectedSpace (g (e.symm j)).toScheme
  exact connectedSpace_connectedComponentOpen _ (e.symm j).2

/-- The restriction of a stratification of a Noetherian scheme `X` to an open subscheme `U`: the
strata are the preimages of `U` in the strata of `X`. -/
def restrict [IsNoetherian X] (s : ConstructibleStratification X ⊤) (U : X.Opens) :
    ConstructibleStratification X U := by
  let V (i : Fin s.n) : (s.piece i).Opens := (s.inclusion i) ⁻¹ᵁ U
  let f (i : Fin s.n) : (V i).toScheme ⟶ X := (V i).ι ≫ s.inclusion i
  have (i : Fin s.n) : IsImmersion (s.inclusion i) := s.isImmersion i
  exact {
    n := s.n
    piece := fun i => (V i).toScheme
    inclusion := f
    isImmersion := fun _ => IsImmersion.comp _ _
    contained := by
      rintro i _ ⟨y, rfl⟩
      change (s.inclusion i).base ((V i).ι.base y) ∈ U
      exact y.2
    constructible := by
      intro i
      let : TopologicalSpace.NoetherianSpace U := Topology.IsInducing.subtypeVal.noetherianSpace
      exact AlgebraicGeometry.isConstructible_of_isLocallyClosed
        ((f i).isLocallyClosed_range.preimage (Scheme.Hom.continuous U.ι))
    pairwise_disjoint := fun i j hij => by
      refine Set.disjoint_left.mpr fun x hx hx' => ?_
      have hxI : x ∈ Set.range (s.inclusion i).base := by
        rcases hx with ⟨y, rfl⟩
        exact ⟨(V i).ι.base y, rfl⟩
      have hxJ : x ∈ Set.range (s.inclusion j).base := by
        rcases hx' with ⟨y, rfl⟩
        exact ⟨(V j).ι.base y, rfl⟩
      exact (Set.disjoint_left.mp (s.pairwise_disjoint i j hij)) hxI hxJ
    covers := by
      rw [Set.Subset.antisymm_iff]
      constructor
      · intro x hx
        have hxTop : x ∈ (↑(⊤ : X.Opens) : Set X) := by simp
        rw [s.covers] at hxTop
        rcases Set.mem_iUnion.mp hxTop with ⟨i, y, hxy⟩
        have hy : y ∈ V i := by
          change (s.inclusion i).base y ∈ U
          rwa [hxy]
        exact Set.mem_iUnion.mpr ⟨i, ⟨y, hy⟩, hxy⟩
      · intro x hx
        rcases Set.mem_iUnion.mp hx with ⟨i, y, rfl⟩
        change (s.inclusion i).base ((V i).ι.base y) ∈ U
        exact y.2
  }

end AlgebraicGeometry.Scheme.ConstructibleStratification

end
