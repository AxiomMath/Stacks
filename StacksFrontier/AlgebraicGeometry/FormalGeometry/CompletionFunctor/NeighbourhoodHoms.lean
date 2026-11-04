module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithful
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of completions come from morphisms near the formal locus

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, put `U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the
set of open subschemes of `U` containing `U ∩ V(I)`, ordered by reverse inclusion. Stacks 0EIV
asserts that for `V ∈ 𝒱` and coherent `𝒪_V`-modules `ℱ`, `𝒢` the canonical map

`colim_{V' ≥ V} Hom_{V'}(𝒢|_{V'}, ℱ|_{V'}) ⟶ Hom_{Coh(U, I𝒪_U)}(𝒢^∧, ℱ^∧)`

is bijective as soon as `A` is `I`-adically complete with a dualizing complex and the
associated points of `ℱ` satisfy the dimension bound of Stacks 0EG2. Stacks 0EKU is the
corresponding statement for the completion functor on the full subcategory of finite locally
free objects.

This file constructs the comparison map of Stacks 0EIV at the neighbourhood `V = U` — the
member of `𝒱` to which the source reduces the general case in the first paragraph of its proof,
and over which the colimit runs over the whole of `𝒱` — and identifies its source with that
colimit. Its bijectivity at `V = U` is
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison_bijective_of_dimensionBound`, and the
statement for a general `V ∈ 𝒱` is `Stacks.Algebraization.nbhdHomComparisonOn_bijective`.

## Main definitions

* `Stacks.Algebraization.NeighbourhoodHoms.towerIso` — the `n`-th term of the completion of a
  coherent module is the `(n+1)`-st term of its tower of ideal-power quotients.
* `Stacks.Algebraization.NeighbourhoodHoms.adicCompletionLimitIso` — shifting the tower does
  not change its limit.
* `Stacks.Algebraization.NeighbourhoodHoms.sectionsAb` and
  `Stacks.Algebraization.NeighbourhoodHoms.sectionsAbLimitIso` — global sections as a functor
  to abelian groups, and its commutation with the limit of a tower.
* `Stacks.Algebraization.NeighbourhoodHoms.internalHomNear` — the internal hom of two coherent
  modules on `U`, as a coherent module.
* `Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison` — **the map of Stacks 0EIV**: the
  comparison of Stacks 0EG2 for the internal hom, followed by the shift of the tower and by the
  identification of Stacks 0882.

## Main results

* `Stacks.Algebraization.NeighbourhoodHoms.sectionsNearVanishing_internalHomNear` — the source
  of the comparison is the colimit over `𝒱` of the morphisms of the restrictions, so the
  comparison is the map of Stacks 0EIV.

## Implementation notes

`Stacks.Algebraization.completionFunctor` is `no_expose`, so the identification of its `n`-th
term with `H / J^(n+1) H` is available only as the propositional
`Stacks.Algebraization.completionFunctor_obj`; `towerIso` packages it as an isomorphism and
`towerIso_naturality` transports the transition maps across it, proved by cancelling the
epimorphism `Stacks.Algebraization.completionProjection`.

The two presentations `X.Modules` and `SheafOfModules X.ringCatSheaf` of one category make the
rewrite motives of this subtree ill-typed at `implicit` transparency, so the computations are
`Category.assoc`/`congrArg`/`Eq.trans` chains in term mode rather than `rw` calls, as elsewhere
in `CompletionFunctor`.

The comparison of Stacks 0EG2 lands in a limit of abelian groups while Stacks 0882 starts from
a limit of modules over `Γ(U, 𝒪_U)`; `sectionsAb` is the global sections functor read in
abelian groups, for which `Stacks.Algebraization.formalSections` is literally the composite
with the ideal-power tower, and `sectionsAbLimitIso` is the resulting commutation.

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
* [Stacks Project, Tag 0EKU](https://stacks.math.columbia.edu/tag/0EKU)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization.NeighbourhoodHoms

open Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance] HasDerivedCategory.standard

/-! ### Shifting the ideal-power tower -/

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (J : X.IdealSheafData)
  (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The `n`-th term of the completion of `H` is the `(n+1)`-st term of the tower of
ideal-power quotients of `H`. -/
public def towerIso (n : ℕ) :
    ((completionFunctor X J).obj H).obj.obj (op n) ≅
      (adicQuotientSystem J H.obj).obj (op (n + 1)) :=
  eqToIso (completionFunctor_obj X J H n)

/-- Under the identification of the terms, the projection onto the `n`-th term of the
completion is the quotient map onto `H / J^(n+1) H`. -/
public theorem completionProjection_comp_towerIso (n : ℕ) :
    completionProjection X J H n ≫ (towerIso J H n).hom =
      cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) H.obj).ι :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => cokernel.π (C := X.Modules) (idealPowerMultiple J (n + 1) H.obj).ι ≫ k)
        (towerIso J H n).inv_hom_id).trans (Category.comp_id _))

/-- The identification of the terms carries the transition maps of the completion to the
transition maps of the ideal-power tower, shifted by one. -/
public theorem towerIso_naturality {n m : ℕ} (h : n ≤ m) :
    ((completionFunctor X J).obj H).obj.map (homOfLE h).op ≫ (towerIso J H n).hom =
      (towerIso J H m).hom ≫
        (adicQuotientSystem J H.obj).map (homOfLE (Nat.add_le_add_right h 1)).op := by
  have hepi : Epi (completionProjection X J H m) := epi_completionProjection X J H m
  refine (cancel_epi (completionProjection X J H m)).1 ?_
  erw [← Category.assoc, completionProjection_map, completionProjection_comp_towerIso,
    ← Category.assoc, completionProjection_comp_towerIso]
  exact ((adicQuotientCone J H.obj).w (homOfLE (Nat.add_le_add_right h 1)).op).symm

/-- The inverse form of `towerIso_naturality`. -/
public theorem towerIso_inv_naturality {n m : ℕ} (h : n ≤ m) :
    (towerIso J H m).inv ≫ ((completionFunctor X J).obj H).obj.map (homOfLE h).op =
      (adicQuotientSystem J H.obj).map (homOfLE (Nat.add_le_add_right h 1)).op ≫
        (towerIso J H n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact towerIso_naturality J H h

/-- `towerIso_naturality` for an arbitrary morphism of the index category. -/
public theorem towerIso_naturality_hom {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((completionFunctor X J).obj H).obj.map f ≫ (towerIso J H j.unop).hom =
      (towerIso J H i.unop).hom ≫ (adicQuotientSystem J H.obj).map
        (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op :=
  (congrArg (fun g => ((completionFunctor X J).obj H).obj.map g ≫ (towerIso J H j.unop).hom)
      (Subsingleton.elim f (homOfLE (leOfHom f.unop)).op)).trans
    (towerIso_naturality J H (leOfHom f.unop))

/-- `towerIso_inv_naturality` for an arbitrary morphism of the index category. -/
public theorem towerIso_naturality_inv {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (towerIso J H i.unop).inv ≫ ((completionFunctor X J).obj H).obj.map f =
      (adicQuotientSystem J H.obj).map
          (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op ≫ (towerIso J H j.unop).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact towerIso_naturality_hom J H f

/-- The limit of the tower of ideal-power quotients, as a cone over the completion tower:
its component at `n` is the projection at `n + 1`. -/
public def adicLimitCone : Cone ((completionFunctor X J).obj H).obj where
  pt := limit (C := X.Modules) (adicQuotientSystem J H.obj)
  π :=
  { app := fun n =>
      limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫ (towerIso J H n.unop).inv
    naturality := fun i j f =>
      (Category.id_comp _).trans
        ((congrArg (fun k => k ≫ (towerIso J H j.unop).inv)
            (limit.w (adicQuotientSystem J H.obj)
              (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op)).symm.trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => limit.π (adicQuotientSystem J H.obj) (op (i.unop + 1)) ≫ k)
                (towerIso_naturality_inv J H f).symm).trans
              (Category.assoc _ _ _).symm))) }

/-- The limit of the completion tower, as a cone over the tower of ideal-power quotients:
its component at `n` is the projection at `n`, followed by the transition to `n`. -/
public def completionLimitCone : Cone (adicQuotientSystem J H.obj) where
  pt := limit (C := X.Modules) ((completionFunctor X J).obj H).obj
  π :=
  { app := fun n => limit.π ((completionFunctor X J).obj H).obj (op n.unop) ≫
      (towerIso J H n.unop).hom ≫
        (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op
    naturality := fun i j f => by
      refine (Category.id_comp _).trans ?_
      have hw := limit.w ((completionFunctor X J).obj H).obj (f := f)
      have h1 : limit.π ((completionFunctor X J).obj H).obj (op j.unop) ≫
            ((towerIso J H j.unop).hom ≫
              (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op) =
          (limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
            ((completionFunctor X J).obj H).obj.map f) ≫
            ((towerIso J H j.unop).hom ≫
              (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op) :=
        congrArg (fun k => k ≫ ((towerIso J H j.unop).hom ≫
          (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op)) hw.symm
      refine h1.trans ?_
      have h2 : (((completionFunctor X J).obj H).obj.map f ≫ (towerIso J H j.unop).hom) ≫
            (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op =
          ((towerIso J H i.unop).hom ≫ (adicQuotientSystem J H.obj).map
            (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op) ≫
            (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op :=
        congrArg (fun k => k ≫ (adicQuotientSystem J H.obj).map
          (homOfLE (Nat.le_succ j.unop)).op) (towerIso_naturality_hom J H f)
      have h3 : (adicQuotientSystem J H.obj).map
            (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op ≫
            (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op =
          (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ i.unop)).op ≫
            (adicQuotientSystem J H.obj).map (homOfLE (leOfHom f.unop)).op := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (adicQuotientSystem J H.obj).map (Subsingleton.elim _ _)
      calc (limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              ((completionFunctor X J).obj H).obj.map f) ≫
              ((towerIso J H j.unop).hom ≫
                (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op)
          = limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              ((((completionFunctor X J).obj H).obj.map f ≫ (towerIso J H j.unop).hom) ≫
                (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op) := by
            simp only [Category.assoc]
        _ = limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              (((towerIso J H i.unop).hom ≫ (adicQuotientSystem J H.obj).map
                (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op) ≫
                (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op) :=
            congrArg (fun k => limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫ k) h2
        _ = limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              ((towerIso J H i.unop).hom ≫
                ((adicQuotientSystem J H.obj).map
                    (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op ≫
                  (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ j.unop)).op)) := by
            simp only [Category.assoc]
        _ = limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              ((towerIso J H i.unop).hom ≫
                ((adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ i.unop)).op ≫
                  (adicQuotientSystem J H.obj).map (homOfLE (leOfHom f.unop)).op)) :=
            congrArg (fun k => limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              ((towerIso J H i.unop).hom ≫ k)) h3
        _ = (limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              ((towerIso J H i.unop).hom ≫
                (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ i.unop)).op)) ≫
              (adicQuotientSystem J H.obj).map (homOfLE (leOfHom f.unop)).op := by
            simp only [Category.assoc]
        _ = _ := congrArg (fun g => (limit.π ((completionFunctor X J).obj H).obj (op i.unop) ≫
              ((towerIso J H i.unop).hom ≫
                (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ i.unop)).op)) ≫
              (adicQuotientSystem J H.obj).map g) (Subsingleton.elim _ _) }

/-- The canonical map from the limit of the ideal-power tower to the limit of the completion. -/
public def adicLimitToCompletionLimit :
    limit (C := X.Modules) (adicQuotientSystem J H.obj) ⟶
      limit (C := X.Modules) ((completionFunctor X J).obj H).obj :=
  limit.lift _ (adicLimitCone J H)

/-- The canonical map from the limit of the completion to the limit of the ideal-power tower. -/
public def completionLimitToAdicLimit :
    limit (C := X.Modules) ((completionFunctor X J).obj H).obj ⟶
      limit (C := X.Modules) (adicQuotientSystem J H.obj) :=
  limit.lift _ (completionLimitCone J H)

/-- **Shifting the tower does not change its limit.** The limit of the tower `n ↦ H / Jⁿ H`
agrees with the limit of the completion `n ↦ H / J^(n+1) H`. -/
public def adicCompletionLimitIso :
    limit (C := X.Modules) (adicQuotientSystem J H.obj) ≅
      limit (C := X.Modules) ((completionFunctor X J).obj H).obj where
  hom := adicLimitToCompletionLimit J H
  inv := completionLimitToAdicLimit J H
  hom_inv_id := by
    refine limit.hom_ext fun n => ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    have h1 : completionLimitToAdicLimit J H ≫ limit.π (adicQuotientSystem J H.obj) n =
        limit.π ((completionFunctor X J).obj H).obj (op n.unop) ≫
          ((towerIso J H n.unop).hom ≫
            (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op) :=
      limit.lift_π (completionLimitCone J H) n
    have h2 : adicLimitToCompletionLimit J H ≫
          limit.π ((completionFunctor X J).obj H).obj (op n.unop) =
        limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫ (towerIso J H n.unop).inv :=
      limit.lift_π (adicLimitCone J H) (op n.unop)
    have h3 : (towerIso J H n.unop).inv ≫ ((towerIso J H n.unop).hom ≫
          (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op) =
        (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (adicQuotientSystem J H.obj).map
            (homOfLE (Nat.le_succ n.unop)).op) (towerIso J H n.unop).inv_hom_id).trans
          (Category.id_comp _))
    calc (adicLimitToCompletionLimit J H ≫ completionLimitToAdicLimit J H) ≫
            limit.π (adicQuotientSystem J H.obj) n
        = adicLimitToCompletionLimit J H ≫
            (completionLimitToAdicLimit J H ≫ limit.π (adicQuotientSystem J H.obj) n) :=
          Category.assoc _ _ _
      _ = (adicLimitToCompletionLimit J H ≫
            limit.π ((completionFunctor X J).obj H).obj (op n.unop)) ≫
              ((towerIso J H n.unop).hom ≫
                (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op) :=
          (congrArg (fun k => adicLimitToCompletionLimit J H ≫ k) h1).trans
            (Category.assoc _ _ _).symm
      _ = limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫
            ((towerIso J H n.unop).inv ≫ ((towerIso J H n.unop).hom ≫
              (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op)) :=
          (congrArg (fun k => k ≫ ((towerIso J H n.unop).hom ≫
            (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op)) h2).trans
              (Category.assoc _ _ _)
      _ = limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫
            (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ n.unop)).op :=
          congrArg (fun k => limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫ k) h3
      _ = limit.π (adicQuotientSystem J H.obj) n :=
          limit.w (adicQuotientSystem J H.obj) (homOfLE (Nat.le_succ n.unop)).op
  inv_hom_id := by
    refine limit.hom_ext fun n => ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    have h1 : adicLimitToCompletionLimit J H ≫
          limit.π ((completionFunctor X J).obj H).obj n =
        limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) ≫ (towerIso J H n.unop).inv :=
      limit.lift_π (adicLimitCone J H) n
    have h2 : completionLimitToAdicLimit J H ≫
          limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1)) =
        limit.π ((completionFunctor X J).obj H).obj (op (n.unop + 1)) ≫
          ((towerIso J H (n.unop + 1)).hom ≫
            (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ (n.unop + 1))).op) :=
      limit.lift_π (completionLimitCone J H) (op (n.unop + 1))
    have h3 : (towerIso J H (n.unop + 1)).hom ≫
          ((adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ (n.unop + 1))).op ≫
            (towerIso J H n.unop).inv) =
        ((completionFunctor X J).obj H).obj.map (homOfLE (Nat.le_succ n.unop)).op := by
      have hnat := towerIso_naturality J H (Nat.le_succ n.unop)
      have hsub : (adicQuotientSystem J H.obj).map
            (homOfLE (Nat.add_le_add_right (Nat.le_succ n.unop) 1)).op =
          (adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ (n.unop + 1))).op :=
        congrArg (adicQuotientSystem J H.obj).map (Subsingleton.elim _ _)
      calc (towerIso J H (n.unop + 1)).hom ≫
              ((adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ (n.unop + 1))).op ≫
                (towerIso J H n.unop).inv)
          = ((towerIso J H (n.unop + 1)).hom ≫ (adicQuotientSystem J H.obj).map
              (homOfLE (Nat.add_le_add_right (Nat.le_succ n.unop) 1)).op) ≫
                (towerIso J H n.unop).inv :=
            (congrArg (fun k => (towerIso J H (n.unop + 1)).hom ≫ (k ≫
              (towerIso J H n.unop).inv)) hsub.symm).trans (Category.assoc _ _ _).symm
        _ = (((completionFunctor X J).obj H).obj.map (homOfLE (Nat.le_succ n.unop)).op ≫
              (towerIso J H n.unop).hom) ≫ (towerIso J H n.unop).inv :=
            congrArg (fun k => k ≫ (towerIso J H n.unop).inv) hnat.symm
        _ = ((completionFunctor X J).obj H).obj.map (homOfLE (Nat.le_succ n.unop)).op :=
            (Category.assoc _ _ _).trans
              ((congrArg (fun k => ((completionFunctor X J).obj H).obj.map
                  (homOfLE (Nat.le_succ n.unop)).op ≫ k)
                (towerIso J H n.unop).hom_inv_id).trans (Category.comp_id _))
    calc (completionLimitToAdicLimit J H ≫ adicLimitToCompletionLimit J H) ≫
            limit.π ((completionFunctor X J).obj H).obj n
        = completionLimitToAdicLimit J H ≫ (adicLimitToCompletionLimit J H ≫
            limit.π ((completionFunctor X J).obj H).obj n) := Category.assoc _ _ _
      _ = (completionLimitToAdicLimit J H ≫
            limit.π (adicQuotientSystem J H.obj) (op (n.unop + 1))) ≫
              (towerIso J H n.unop).inv :=
          (congrArg (fun k => completionLimitToAdicLimit J H ≫ k) h1).trans
            (Category.assoc _ _ _).symm
      _ = limit.π ((completionFunctor X J).obj H).obj (op (n.unop + 1)) ≫
            ((towerIso J H (n.unop + 1)).hom ≫
              ((adicQuotientSystem J H.obj).map (homOfLE (Nat.le_succ (n.unop + 1))).op ≫
                (towerIso J H n.unop).inv)) := by
          rw [h2]; simp only [Category.assoc]
      _ = limit.π ((completionFunctor X J).obj H).obj (op (n.unop + 1)) ≫
            ((completionFunctor X J).obj H).obj.map (homOfLE (Nat.le_succ n.unop)).op :=
          congrArg (fun k => limit.π ((completionFunctor X J).obj H).obj
            (op (n.unop + 1)) ≫ k) h3
      _ = limit.π ((completionFunctor X J).obj H).obj n :=
          limit.w ((completionFunctor X J).obj H).obj (homOfLE (Nat.le_succ n.unop)).op

/-! ### Global sections of a limit, in abelian groups -/

/-- Global sections of a module on `X`, as a functor to abelian groups. -/
public abbrev sectionsAb (X : Scheme.{u}) : X.Modules ⥤ Ab.{u} :=
  _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)) ⋙
    forget₂ (ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) Ab.{u}

/-- Global sections commute with the inverse limit of a tower of modules. -/
public def sectionsLimitIso (D : ℕᵒᵖ ⥤ X.Modules) :
    (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
        (limit (C := X.Modules) D) ≅
      limit (C := ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
        (D ⋙ _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))) :=
  IsLimit.conePointUniqueUpToIso
    (@isLimitOfPreserves _ _ _ _ _ _ _
      (_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens)))
      (limit.cone D) (limit.isLimit D)
      (_root_.SheafOfModules.evaluationPreservesLimit _ (op (⊤ : X.Opens))))
    (limit.isLimit _)

/-- Global sections commute with the inverse limit of a tower of modules, in abelian groups. -/
public def sectionsAbLimitIso (D : ℕᵒᵖ ⥤ X.Modules) :
    (sectionsAb X).obj (limit (C := X.Modules) D) ≅ limit (C := Ab.{u}) (D ⋙ sectionsAb X) :=
  ((forget₂ (ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens)))) Ab.{u}).mapIso
      (sectionsLimitIso D)).trans
    (preservesLimitIso (forget₂ (ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))))
      Ab.{u}) (D ⋙ _root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))))

/-! ### The comparison of Stacks 0EIV -/

section Neighbourhood

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
    (complementZeroLocus A a : Scheme).ringCatSheaf)

/-- The internal hom of two coherent modules on `U = Spec(A) ∖ V(𝔞)`, as a coherent module. -/
public abbrev internalHomNear : AlgebraicGeometry.SheafOfModules.CoherentModules
    (complementZeroLocus A a : Scheme).ringCatSheaf :=
  internalHomCoherent (complementZeroLocus A a : Scheme) G F

/-- **The source of the comparison of Stacks 0EIV is the colimit of the morphisms of the
restrictions.** A section of the internal hom `SheafHom(𝒢, ℱ)` over an open neighbourhood `V`
of the formal locus is, on the nose, a morphism `𝒢|_V ⟶ ℱ|_V` of modules on the site of opens
below `V`. So the source of `nbhdHomComparison` is `colim_{V ∈ 𝒱} Hom_V(𝒢|_V, ℱ|_V)`. -/
@[stacks 0EIV "at the member V = U: the source is the colimit over the whole family"]
public theorem sectionsNearVanishing_internalHomNear
    (V : OpensNearVanishing A I a) :
    ToType ((sectionsNearVanishing A I a (internalHomNear A a G F).obj).obj V) =
      ((_root_.restrFun (complementZeroLocus A a : Scheme).sheaf.obj V.openSet).obj
          G.obj.val ⟶
        (_root_.restrFun (complementZeroLocus A a : Scheme).sheaf.obj V.openSet).obj
          F.obj.val) := rfl

variable [IsNoetherianRing A]

/-- **The map of Stacks 0EIV.** The canonical map from the morphisms `𝒢|_{V'} ⟶ ℱ|_{V'}`
defined on arbitrarily small open neighbourhoods `V'` of the formal locus `U ∩ V(I)` to the
morphisms of the completions `𝒢^∧ ⟶ ℱ^∧` in `Coh(U, I𝒪_U)`.

It is the composite of three canonical maps: the comparison of Stacks 0EG2 for the internal
hom `H = SheafHom(𝒢, ℱ)`, which lands in the compatible families of sections of `H / Iⁿ H` on
`U`; the identification of that limit with the limit of the global sections of the completion
of `H`, which is `adicCompletionLimitIso` on the tower and `sectionsAbLimitIso` on sections;
and the identification of Stacks 0882 of the latter with the morphisms of the completions. -/
@[stacks 0EIV "at V = U: the canonical map from germs of morphisms to the completions"]
public def nbhdHomComparison :
    ToType (colimit (C := Ab.{u})
        (sectionsNearVanishing A I a (internalHomNear A a G F).obj)) →
      ((completionFunctor (complementZeroLocus A a : Scheme)
          (idealSheafNearVanishing A I a)).obj G ⟶
        (completionFunctor (complementZeroLocus A a : Scheme)
          (idealSheafNearVanishing A I a)).obj F) :=
  ⇑(completionInternalHomEquiv (complementZeroLocus A a : Scheme)
      (idealSheafNearVanishing A I a) G F) ∘
    ConcreteCategory.hom (globalSectionsLimitIso (idealSheafNearVanishing A I a)
      (internalHomNear A a G F)).hom ∘
    ConcreteCategory.hom ((sectionsAb (complementZeroLocus A a : Scheme)).map
      (adicCompletionLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom) ∘
    ConcreteCategory.hom (sectionsAbLimitIso
      (adicQuotientSystem (idealSheafNearVanishing A I a)
        (internalHomNear A a G F).obj)).inv ∘
    ConcreteCategory.hom (comparisonMap A I a (internalHomNear A a G F).obj)

end Neighbourhood

/-! ### The completion functor on finite locally free objects -/

section FiniteLocallyFree

open Stacks.LocalCohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)

end FiniteLocallyFree

end Stacks.Algebraization.NeighbourhoodHoms

end
