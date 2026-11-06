module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleLimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Open subgroups of the étale fundamental group

Let `X` be a connected scheme with a geometric point `x`. Every finite étale cover `Y ⟶ X` and
every point `y` of its geometric fibre `F_x(Y)` give a subgroup of `π₁(X, x)`, namely the
stabilizer of `y` for the action of `π₁(X, x)` on that fibre. Such a subgroup is called open,
and this file proves part (1) of Stacks 03VF: these subgroups are open for the canonical
topology of Stacks 0BMR, and they form a fundamental system of neighbourhoods of the identity.

## Main definitions

* `AlgebraicGeometry.EtaleFundamentalGroup.IsOpenSubgroup` — the property of being the stabilizer
  of a point of the geometric fibre of some finite étale cover.

## Main results

* `AlgebraicGeometry.EtaleFundamentalGroup.isOpen_coe_of_isOpenSubgroup` — an open subgroup is an
  open subset of `π₁(X, x)`.
* `AlgebraicGeometry.EtaleFundamentalGroup.isOpenSubgroup_iInf` — a finite intersection of open
  subgroups is open, because the geometric fibre functor turns a product of covers into the
  product of their fibres.
* `AlgebraicGeometry.EtaleFundamentalGroup.nhds_one_hasBasis_isOpenSubgroup` — **Stacks 03VF (1)**:
  the open subgroups are a neighbourhood basis of the identity.

## Implementation notes

The predicate records equality with a point stabilizer, rather than topological openness; that
the two agree in the direction needed for 03VF (1) is `isOpen_coe_of_isOpenSubgroup`. Stating it
transparently as an existential lets consumers use the description directly.

The action of the fundamental group on a geometric fibre is
`AlgebraicGeometry.etaleFundamentalGroupMulAction`, by evaluating a natural automorphism at the
cover. The canonical topology is induced by `CategoryTheory.componentEmbedding` from the product
of the pointwise-convergence topologies, so a neighbourhood of the identity is cut out by finitely
many covers, and the stabilizers meeting it are produced by one product of covers.

## References

* [Stacks Project, Tag 03VE](https://stacks.math.columbia.edu/tag/03VE)
* [Stacks Project, Tag 03VF](https://stacks.math.columbia.edu/tag/03VF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.EtaleFundamentalGroup

/-- **Stacks Project, Tag 03VE.** A subgroup of the étale fundamental group is open if it is
the stabilizer of a point of the geometric fibre of some finite étale cover. -/
@[stacks 03VE]
public abbrev IsOpenSubgroup {X : Scheme.{u}} [ConnectedSpace X]
    (x : GeometricPoint X) (H : Subgroup (EtaleFundamentalGroup X x)) : Prop :=
  ∃ (Y : FiniteEtaleOver X) (y : (finiteEtaleFiberFunctor x).obj Y),
    H = MulAction.stabilizer (EtaleFundamentalGroup X x) y

variable {X : Scheme.{u}} [ConnectedSpace X] {x : GeometricPoint X}

/-- The stabilizer of a point of a geometric fibre is an open subset of `π₁(X, x)`: it is the
preimage of a point of a discrete space under a continuous evaluation map. -/
private lemma isOpen_stabilizer (Y : FiniteEtaleOver X)
    (y : (finiteEtaleFiberFunctor x).obj Y) :
    IsOpen ((MulAction.stabilizer (EtaleFundamentalGroup X x) y :
      Subgroup (EtaleFundamentalGroup X x)) : Set (EtaleFundamentalGroup X x)) := by
  let (Z : FiniteEtaleOver X) : TopologicalSpace ((finiteEtaleFiberFunctor x).obj Z) := ⊥
  let (Z : FiniteEtaleOver X) : DiscreteTopology ((finiteEtaleFiberFunctor x).obj Z) := ⟨rfl⟩
  have h1 : Continuous fun σ : EtaleFundamentalGroup X x ↦
      componentEmbedding (finiteEtaleFiberFunctor x) σ := continuous_induced_dom
  have h2 : Continuous fun σ : EtaleFundamentalGroup X x ↦
      componentEmbedding (finiteEtaleFiberFunctor x) σ Y := (continuous_apply Y).comp h1
  have h3 : Continuous fun σ : EtaleFundamentalGroup X x ↦
      ((componentEmbedding (finiteEtaleFiberFunctor x) σ Y :
        Equiv.Perm ((finiteEtaleFiberFunctor x).obj Y)) :
        (finiteEtaleFiberFunctor x).obj Y → (finiteEtaleFiberFunctor x).obj Y) :=
    continuous_induced_dom.comp h2
  have hcont : Continuous fun σ : EtaleFundamentalGroup X x ↦ (σ.asIso.app Y).hom y :=
    (continuous_apply y).comp h3
  exact hcont.isOpen_preimage {y} (isOpen_discrete _)

/-- **Stacks Project, Tag 03VF (1), openness.** An open subgroup of the étale fundamental group
is an open subset for the canonical topology. -/
@[stacks 03VF "(1) the open subgroups are open subsets; that they are a neighbourhood basis of \
the identity is `nhds_one_hasBasis_isOpenSubgroup`, and (2) and (3) are not covered here"]
theorem isOpen_coe_of_isOpenSubgroup {H : Subgroup (EtaleFundamentalGroup X x)}
    (hH : IsOpenSubgroup x H) : IsOpen (H : Set (EtaleFundamentalGroup X x)) := by
  obtain ⟨Y, y, rfl⟩ := hH
  exact isOpen_stabilizer Y y

/-- A finite family of point stabilizers meets in the stabilizer of a point of the product of the
covers, because the geometric fibre functor preserves finite products. -/
private lemma exists_stabilizer_eq_iInf_fin {n : ℕ} (Y : Fin n → FiniteEtaleOver X)
    (y : ∀ j, (finiteEtaleFiberFunctor x).obj (Y j)) :
    ∃ (W : FiniteEtaleOver X) (z : (finiteEtaleFiberFunctor x).obj W),
      MulAction.stabilizer (EtaleFundamentalGroup X x) z =
        ⨅ j, MulAction.stabilizer (EtaleFundamentalGroup X x) (y j) := by
  have := preservesFiniteLimits_finiteEtaleFiberFunctor x
  have : IsIso (piComparison (finiteEtaleFiberFunctor x) Y) := by
    rw [← PreservesProduct.iso_hom]
    infer_instance
  obtain ⟨hcinj, hcsurj⟩ :=
    (isIso_iff_bijective (piComparison (finiteEtaleFiberFunctor x) Y)).mp inferInstance
  obtain ⟨hpinj, hpsurj⟩ := (isIso_iff_bijective
    (Types.productIso fun j ↦ (finiteEtaleFiberFunctor x).obj (Y j)).hom).mp inferInstance
  have hPi : ∀ (c : ∏ᶜ fun j ↦ (finiteEtaleFiberFunctor x).obj (Y j)) (j : Fin n),
      ConcreteCategory.hom
          (Types.productIso fun j ↦ (finiteEtaleFiberFunctor x).obj (Y j)).hom c j =
        ConcreteCategory.hom (Pi.π (fun j ↦ (finiteEtaleFiberFunctor x).obj (Y j)) j) c :=
    fun _ _ ↦ rfl
  have hjoint : ∀ t t' : (finiteEtaleFiberFunctor x).obj (∏ᶜ Y),
      (∀ j, (finiteEtaleFiberFunctor x).map (Pi.π Y j) t =
          (finiteEtaleFiberFunctor x).map (Pi.π Y j) t') → t = t' := by
    intro t t' h
    refine hcinj (hpinj (funext fun j ↦ ?_))
    rw [hPi, hPi, ← types_comp_apply, ← types_comp_apply, piComparison_comp_π, h j]
  obtain ⟨z, hz⟩ : ∃ z : (finiteEtaleFiberFunctor x).obj (∏ᶜ Y),
      ∀ j, (finiteEtaleFiberFunctor x).map (Pi.π Y j) z = y j := by
    obtain ⟨c, hc⟩ := hpsurj y
    obtain ⟨z, hzc⟩ := hcsurj c
    refine ⟨z, fun j ↦ ?_⟩
    rw [← piComparison_comp_π (finiteEtaleFiberFunctor x) Y j, types_comp_apply, hzc, ← hPi, hc]
  have hnat : ∀ (σ : EtaleFundamentalGroup X x) (j : Fin n),
      (finiteEtaleFiberFunctor x).map (Pi.π Y j) (σ • z) = σ • y j := by
    intro σ j
    have h := ConcreteCategory.congr_hom (σ.asIso.hom.naturality (Pi.π Y j)) z
    rw [types_comp_apply, types_comp_apply] at h
    rw [← hz j]
    exact h.symm
  refine ⟨∏ᶜ Y, z, ?_⟩
  ext σ
  rw [Subgroup.mem_iInf]
  simp only [MulAction.mem_stabilizer_iff]
  refine ⟨fun hσ j ↦ ?_, fun hσ ↦ hjoint _ _ fun j ↦ ?_⟩
  · rw [← hnat, hσ, hz]
  · rw [hnat, hσ, hz]

/-- A finite intersection of open subgroups of the étale fundamental group is open. -/
theorem isOpenSubgroup_iInf {ι : Type*} [Finite ι]
    {H : ι → Subgroup (EtaleFundamentalGroup X x)} (hH : ∀ i, IsOpenSubgroup x (H i)) :
    IsOpenSubgroup x (⨅ i, H i) := by
  choose Y y hy using hH
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  obtain ⟨W, z, hz⟩ := exists_stabilizer_eq_iInf_fin (fun j : Fin n ↦ Y (e.symm j))
    (fun j ↦ y (e.symm j))
  have hcomp : (⨅ j : Fin n, MulAction.stabilizer (EtaleFundamentalGroup X x) (y (e.symm j))) =
      ⨅ i, MulAction.stabilizer (EtaleFundamentalGroup X x) (y i) :=
    e.symm.surjective.iInf_comp fun i ↦ MulAction.stabilizer (EtaleFundamentalGroup X x) (y i)
  exact ⟨W, z, by rw [hz, hcomp]; exact iInf_congr hy⟩

/-- **Stacks Project, Tag 03VF (1).** For the canonical topology on the étale fundamental group
of a connected scheme, the open subgroups — the stabilizers of points of geometric fibres — form
a fundamental system of neighbourhoods of the identity. -/
@[stacks 03VF "(1) the open subgroups are a neighbourhood basis of the identity; that each of \
them is an open subset is `isOpen_coe_of_isOpenSubgroup`, and (2) and (3) are not covered here"]
theorem nhds_one_hasBasis_isOpenSubgroup (X : Scheme.{u}) [ConnectedSpace X]
    (x : GeometricPoint X) :
    (nhds (1 : EtaleFundamentalGroup X x)).HasBasis (IsOpenSubgroup x)
      fun H ↦ (H : Set (EtaleFundamentalGroup X x)) := by
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  let (Z : FiniteEtaleOver X) : TopologicalSpace ((finiteEtaleFiberFunctor x).obj Z) := ⊥
  let (Z : FiniteEtaleOver X) : DiscreteTopology ((finiteEtaleFiberFunctor x).obj Z) := ⟨rfl⟩
  refine Filter.hasBasis_iff.mpr fun V ↦ ⟨fun hV ↦ ?_, ?_⟩
  · obtain ⟨U, hU, hUV⟩ :=
      (mem_nhds_induced (componentEmbedding (finiteEtaleFiberFunctor x)) 1 V).mp hV
    rw [map_one, nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hIfin, t, ht, hIt⟩ := hU
    have : Finite ↥I := hIfin.to_subtype
    refine ⟨⨅ p : (Z : ↥I) × (finiteEtaleFiberFunctor x).obj (Z : FiniteEtaleOver X),
      MulAction.stabilizer (EtaleFundamentalGroup X x) p.2,
      isOpenSubgroup_iInf fun p ↦ ⟨_, p.2, rfl⟩, fun σ hσ ↦ ?_⟩
    refine hUV (hIt fun Z hZ ↦ ?_)
    have hone : componentEmbedding (finiteEtaleFiberFunctor x) σ Z = 1 := by
      ext s
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_iInf.mp hσ ⟨⟨Z, hZ⟩, s⟩)
    rw [hone]
    exact mem_of_mem_nhds (ht Z)
  · rintro ⟨H, hH, hHV⟩
    exact Filter.mem_of_superset ((isOpen_coe_of_isOpenSubgroup hH).mem_nhds H.one_mem) hHV

end AlgebraicGeometry.EtaleFundamentalGroup

end
