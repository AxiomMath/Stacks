module

public import StacksFrontier.RingTheory.Module.DirectLimit.FinitePresentation

/-!
# The directed system of finite type models of a finitely presented algebra

Let `R₀ ⊆ R` be a subring of finite type over `ℤ` and let `S₀` be an `R₀`-algebra with a map
`S₀ → S` exhibiting `S = R ⊗_{R₀} S₀`. The subalgebras of `R` of finite type over `ℤ`
containing `R₀` form a directed set with union `R`, and base changing `S₀` to each of them
gives a directed system of rings `R_λ ⊗_{R₀} S₀` whose colimit is `S`, with cartesian
transition maps.

## Main definitions

* `Algebra.FiniteTypeSystem.Index`: the directed set of finite type `ℤ`-subalgebras of `R`
  containing `R₀`.
* `Algebra.FiniteTypeSystem.Base`, `Algebra.FiniteTypeSystem.Ring`: the rings `R_λ` and
  `R_λ ⊗_{R₀} S₀`, with transition maps `baseMap` and `ringMap` and cocone maps `baseToRing`
  and `ringToRing`.

## Main results

* `Algebra.FiniteTypeSystem.base_jointly_surjective`: every element of `R` lies in some `R_λ`.
* `Algebra.FiniteTypeSystem.ring_colimit`: `S` is the directed colimit of the `R_λ ⊗_{R₀} S₀`.
* `Algebra.FiniteTypeSystem.ringMap_isPushout`: the transition squares are cartesian.
* `Algebra.FiniteTypeSystem.ringToRing_isPushout`: `S = R ⊗_{R_λ} (R_λ ⊗_{R₀} S₀)`.

## References

* [Stacks Project, Tag 00R1](https://stacks.math.columbia.edu/tag/00R1)
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra.FiniteTypeSystem

variable {R : Type u} [CommRing R] (R₀ : Subring R)

/-- The subalgebras of `R` of finite type over `ℤ` containing `R₀`. -/
abbrev Index := { A : Subalgebra ℤ R // R₀ ≤ A.toSubring ∧ A.FG }

/-- If `R₀` is of finite type over `ℤ`, then the index set is nonempty: it contains `R₀`. -/
instance [Algebra.FiniteType ℤ R₀] : Nonempty (Index R₀) := by
  obtain ⟨t, ht⟩ := (‹Algebra.FiniteType ℤ R₀›).out
  exact ⟨⟨(⊤ : Subalgebra ℤ R₀).map R₀.subtype.toIntAlgHom,
    fun x hx => Subalgebra.mem_map.mpr ⟨⟨x, hx⟩, trivial, rfl⟩, Subalgebra.FG.map _ ⟨t, ht⟩⟩⟩

/-- The index set is directed: `λ` and `μ` are both contained in `λ ⊔ μ`. -/
instance : IsDirectedOrder (Index R₀) :=
  ⟨fun i j => ⟨⟨i.1 ⊔ j.1, fun _ hx => (le_sup_left : i.1 ≤ i.1 ⊔ j.1) (i.2.1 hx),
    i.2.2.sup j.2.2⟩, show i.1 ≤ i.1 ⊔ j.1 from le_sup_left,
    show j.1 ≤ i.1 ⊔ j.1 from le_sup_right⟩⟩

/-- The ring `R_λ` at an index `λ`: the subalgebra `λ`, as a type in its own right, so that
instances over `R` do not reach it through the subalgebra coercion. -/
def Base (i : Index R₀) : Type u := i.1

/-- The commutative ring structure of `R_λ`, as a subring of `R`. -/
instance (i : Index R₀) : CommRing (Base R₀ i) := inferInstanceAs (CommRing i.1)

/-- The algebra structure of `R` over `R_λ`, given by the inclusion `R_λ ⊆ R`. -/
instance (i : Index R₀) : Algebra (Base R₀ i) R := inferInstanceAs (Algebra i.1 R)

/-- `R_λ → R` is the inclusion of a subring. -/
theorem algebraMap_base_injective (i : Index R₀) :
    Function.Injective (algebraMap (Base R₀ i) R) := Subtype.val_injective

/-- The algebra structure of `R_λ` over `R₀`, given by the inclusion `R₀ ⊆ R_λ`. -/
instance (i : Index R₀) : Algebra R₀ (Base R₀ i) :=
  (RingHom.codRestrict R₀.subtype i.1 fun x => i.2.1 x.2).toAlgebra

/-- The inclusions `R₀ ⊆ R_λ ⊆ R` compose to `R₀ ⊆ R`. -/
instance (i : Index R₀) : IsScalarTower R₀ (Base R₀ i) R :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Finite type over `ℤ` does not depend on the choice of `ℤ`-algebra structure. -/
theorem finiteType_int_of_algebra {X : Type*} [CommRing X] (i₁ i₂ : Algebra ℤ X)
    (h : @Algebra.FiniteType ℤ X _ _ i₁) : @Algebra.FiniteType ℤ X _ _ i₂ :=
  Subsingleton.elim i₁ i₂ ▸ h

/-- Each `R_λ` is of finite type over `ℤ`. -/
instance (i : Index R₀) : Algebra.FiniteType ℤ (Base R₀ i) :=
  finiteType_int_of_algebra _ _ ((Subalgebra.fg_iff_finiteType _).mp i.2.2)

/-- The algebra structure of `R_λ` on an `R`-algebra, through `R_λ ⊆ R`. -/
instance (priority := low) (i : Index R₀) {S : Type*} [CommRing S] [Algebra R S] :
    Algebra (Base R₀ i) S :=
  ((algebraMap R S).comp (algebraMap (Base R₀ i) R)).toAlgebra

/-- For an `R`-algebra `S`, the map `R_λ → S` factors through `R`. -/
instance (i : Index R₀) {S : Type*} [CommRing S] [Algebra R S] :
    IsScalarTower (Base R₀ i) R S :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The transition map `R_λ → R_μ`, an inclusion of subrings of `R`. -/
def baseMap {i j : Index R₀} (h : i ≤ j) : Base R₀ i →ₐ[R₀] Base R₀ j :=
  { Subalgebra.inclusion h with commutes' := fun _ => rfl }

/-- The inclusion `R_λ → R`. -/
def baseToRing (i : Index R₀) : Base R₀ i →ₐ[R₀] R :=
  IsScalarTower.toAlgHom R₀ (Base R₀ i) R

/-- The rings `R_λ` with the transition maps `baseMap` form a directed system. -/
instance : DirectedSystem (Base R₀) (fun _ _ h => ⇑(baseMap R₀ h)) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- Every element of `R` lies in some `R_λ`. -/
theorem base_jointly_surjective [Algebra.FiniteType ℤ R₀] (r : R) :
    ∃ (i : Index R₀) (x : Base R₀ i), baseToRing R₀ i x = r := by
  let i₀ : Index R₀ := Classical.arbitrary _
  let i : Index R₀ := ⟨i₀.1 ⊔ Algebra.adjoin ℤ {r},
    fun _ hx => (le_sup_left : i₀.1 ≤ _) (i₀.2.1 hx),
    i₀.2.2.sup (by simpa using Subalgebra.fg_adjoin_finset (R := ℤ) {r})⟩
  exact ⟨i, (⟨r, (le_sup_right : Algebra.adjoin ℤ {r} ≤ i.1)
    (Algebra.subset_adjoin (Set.mem_singleton r))⟩ : i.1), rfl⟩

variable (S₀ : Type v) [CommRing S₀] [Algebra R₀ S₀]

/-- The ring `S_λ = R_λ ⊗_{R₀} S₀`. -/
abbrev Ring (i : Index R₀) := Base R₀ i ⊗[R₀] S₀

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The transition map `S_λ → S_μ`. -/
def ringMap {i j : Index R₀} (h : i ≤ j) : Ring R₀ S₀ i →ₐ[R₀] Ring R₀ S₀ j :=
  Algebra.TensorProduct.map (baseMap R₀ h) (AlgHom.id _ _)

/-- The transition map `S_λ → S_μ` on pure tensors. -/
@[simp]
theorem ringMap_tmul {i j : Index R₀} (h : i ≤ j) (r : Base R₀ i) (s : S₀) :
    ringMap R₀ S₀ h (r ⊗ₜ s) = baseMap R₀ h r ⊗ₜ s := rfl

/-- The rings `S_λ` with the transition maps `ringMap` form a directed system. -/
instance : DirectedSystem (Ring R₀ S₀) (fun _ _ h => ringMap R₀ S₀ h) where
  map_self i x := by
    have h : ringMap R₀ S₀ (le_refl i) = AlgHom.id _ _ := by ext <;> rfl
    exact DFunLike.congr_fun h x
  map_map i j k hij hjk x := by
    have h : (ringMap R₀ S₀ hjk).comp (ringMap R₀ S₀ hij) =
        ringMap R₀ S₀ (hij.trans hjk) := by ext <;> rfl
    exact DFunLike.congr_fun h x

/-- The ring transitions commute with the maps from the base rings. -/
theorem ringMap_algebraMap {i j : Index R₀} (h : i ≤ j) (r : Base R₀ i) :
    ringMap R₀ S₀ h (algebraMap (Base R₀ i) (Ring R₀ S₀ i) r) =
      algebraMap (Base R₀ j) (Ring R₀ S₀ j) (baseMap R₀ h r) := by
  simp [ringMap]

/-- The transition map `S_λ → S_μ`, as a map of `S₀`-algebras. -/
def ringMapOver {i j : Index R₀} (h : i ≤ j) : Ring R₀ S₀ i →ₐ[S₀] Ring R₀ S₀ j :=
  { (ringMap R₀ S₀ h).toRingHom with
    commutes' := fun s => by simp [ringMap, Algebra.TensorProduct.right_algebraMap_apply] }

/-- `ringMapOver` is `ringMap`. -/
@[simp]
theorem ringMapOver_apply {i j : Index R₀} (h : i ≤ j) (x : Ring R₀ S₀ i) :
    ringMapOver R₀ S₀ h x = ringMap R₀ S₀ h x := rfl

/-- If `S₀` is of finite type over `R₀`, then `S_λ` is of finite type over `R_λ`. -/
instance (i : Index R₀) [Algebra.FiniteType R₀ S₀] :
    Algebra.FiniteType (Base R₀ i) (Ring R₀ S₀ i) := inferInstance

variable {S : Type w} [CommRing S] [Algebra R S] [Algebra S₀ S] [IsScalarTower R₀ S₀ S]

/-- The map `S_λ → S` induced by `R_λ ⊆ R` and `S₀ → S`. -/
def ringToRing (i : Index R₀) : Ring R₀ S₀ i →ₐ[R₀] S :=
  Algebra.TensorProduct.productMap
    ((IsScalarTower.toAlgHom R₀ R S).comp (baseToRing R₀ i)) (IsScalarTower.toAlgHom R₀ S₀ S)

/-- The map `S_λ → S` on pure tensors. -/
@[simp]
theorem ringToRing_tmul (i : Index R₀) (r : Base R₀ i) (s : S₀) :
    ringToRing R₀ S₀ (S := S) i (r ⊗ₜ s) = algebraMap (Base R₀ i) S r * algebraMap S₀ S s := rfl

/-- The maps `S_λ → S` are compatible with the transition maps. -/
theorem ring_cocone {i j : Index R₀} (h : i ≤ j) (x : Ring R₀ S₀ i) :
    ringToRing R₀ S₀ (S := S) j (ringMap R₀ S₀ h x) = ringToRing R₀ S₀ (S := S) i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r s => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The algebra structure of `S` over `S_λ`, given by `ringToRing`. -/
instance ringAlgebra (i : Index R₀) : Algebra (Ring R₀ S₀ i) S :=
  (ringToRing R₀ S₀ (S := S) i).toAlgebra

/-- The algebra structure of `S` over `S_λ` is `ringToRing`. -/
theorem algebraMap_ring_eq (i : Index R₀) :
    algebraMap (Ring R₀ S₀ i) S = (ringToRing R₀ S₀ (S := S) i).toRingHom := rfl

/-- The map `R₀ → S` factors through `S_λ`. -/
instance (i : Index R₀) : IsScalarTower R₀ (Ring R₀ S₀ i) S :=
  IsScalarTower.of_algebraMap_eq fun x => ((ringToRing R₀ S₀ (S := S) i).commutes x).symm

/-- The map `S₀ → S` factors through `S_λ`. -/
instance (i : Index R₀) : IsScalarTower S₀ (Ring R₀ S₀ i) S :=
  IsScalarTower.of_algebraMap_eq fun x => by
    simp [algebraMap_ring_eq, Algebra.TensorProduct.right_algebraMap_apply]

/-- The map `R_λ → S` factors through `S_λ`. -/
instance (i : Index R₀) : IsScalarTower (Base R₀ i) (Ring R₀ S₀ i) S :=
  IsScalarTower.of_algebraMap_eq (R := Base R₀ i) (S := Ring R₀ S₀ i) (A := S) fun r => by
    simp [algebraMap_ring_eq, Algebra.TensorProduct.algebraMap_apply]

/-- `S` is the directed colimit of the rings `S_λ = R_λ ⊗_{R₀} S₀`: the maps `S_λ → S` are
jointly surjective, and two elements of `S_λ` with the same image in `S` agree in some `S_μ`. -/
theorem ring_colimit [Algebra.FiniteType ℤ R₀] [Algebra.IsPushout R₀ R S₀ S] :
    (∀ x : S, ∃ (i : Index R₀) (y : Ring R₀ S₀ i), ringToRing R₀ S₀ (S := S) i y = x) ∧
    (∀ (i : Index R₀) (x y : Ring R₀ S₀ i),
      ringToRing R₀ S₀ (S := S) i x = ringToRing R₀ S₀ (S := S) i y →
      ∃ (j : Index R₀) (h : i ≤ j), ringMap R₀ S₀ h x = ringMap R₀ S₀ h y) := by
  have hc := Stacks.ColimitPresentation.FPModules.isModuleColimit (fun _ _ h => baseMap R₀ h)
    (fun _ _ _ _ => rfl)
    (base_jointly_surjective R₀) (fun i s hs => ⟨i, le_rfl, Subtype.ext hs⟩) S₀
  let e := Algebra.IsPushout.equiv R₀ R S₀ S
  have he (i : Index R₀) (x : Ring R₀ S₀ i) :
      e (Stacks.FinitePresentation.ColimitDescent.canonMod
          (fun j => IsScalarTower.toAlgHom R₀ (Base R₀ j) R) S₀ i x) =
        ringToRing R₀ S₀ (S := S) i x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r s =>
      simp [e, Stacks.FinitePresentation.ColimitDescent.canonMod_tmul, Algebra.IsPushout.equiv_tmul,
        ← IsScalarTower.algebraMap_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  refine ⟨fun x => ?_, fun i x y h => ?_⟩
  · obtain ⟨i, y, hy⟩ := hc.jointly_surjective (e.symm x)
    exact ⟨i, y, (he i y).symm.trans ((congrArg e hy).trans (e.apply_symm_apply x))⟩
  · exact hc.exists_eq_of_canonMod_eq i x y
      (e.injective ((he i x).trans (h.trans (he i y).symm)))

/-- Each `S_λ` base changes to `S`: `S = R ⊗_{R_λ} S_λ`. -/
theorem ringToRing_isPushout [Algebra.IsPushout R₀ R S₀ S] (i : Index R₀) :
    Algebra.IsPushout (Base R₀ i) R (Ring R₀ S₀ i) S :=
  (Algebra.IsPushout.comp_iff R₀ (Base R₀ i) S₀ (Ring R₀ S₀ i)).mp inferInstance

section Transition

variable {i j : Index R₀} [h : Fact (i ≤ j)]

/-- For `λ ≤ μ`, the algebra structure of `R_μ` over `R_λ`, given by `baseMap`. -/
instance : Algebra (Base R₀ i) (Base R₀ j) := (baseMap R₀ h.out).toAlgebra

/-- For `λ ≤ μ`, the map `R₀ → R_μ` factors through `R_λ`. -/
instance : IsScalarTower R₀ (Base R₀ i) (Base R₀ j) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- For `λ ≤ μ`, the algebra structure of `S_μ` over `S_λ`, given by `ringMap`. -/
instance : Algebra (Ring R₀ S₀ i) (Ring R₀ S₀ j) := (ringMap R₀ S₀ h.out).toAlgebra

/-- For `λ ≤ μ`, the map `R_λ → S_μ` factors through `S_λ`. -/
instance : IsScalarTower (Base R₀ i) (Ring R₀ S₀ i) (Ring R₀ S₀ j) :=
  IsScalarTower.of_algebraMap_eq fun r => (ringMap_algebraMap R₀ S₀ h.out r).symm

/-- For `λ ≤ μ`, the map `R_λ → S_μ` factors through `R_μ`. -/
instance : IsScalarTower (Base R₀ i) (Base R₀ j) (Ring R₀ S₀ j) :=
  IsScalarTower.of_algebraMap_eq fun r => (ringMap_algebraMap R₀ S₀ h.out r).symm

/-- For `λ ≤ μ`, the map `S₀ → S_μ` factors through `S_λ`. -/
instance : IsScalarTower S₀ (Ring R₀ S₀ i) (Ring R₀ S₀ j) :=
  IsScalarTower.of_algebraMap_eq fun s => ((ringMapOver R₀ S₀ h.out).commutes s).symm

/-- The transition squares `R_λ → R_μ`, `S_λ → S_μ` are cartesian: `S_μ = R_μ ⊗_{R_λ} S_λ`. -/
theorem ringMap_isPushout :
    Algebra.IsPushout (Base R₀ i) (Base R₀ j) (Ring R₀ S₀ i) (Ring R₀ S₀ j) :=
  Algebra.IsPushout.tensorProduct_tensorProduct R₀ S₀ (Base R₀ i) (Base R₀ j)
    (by ext s; simp [RingHom.algebraMap_toAlgebra, ringMap])

end Transition

end Algebra.FiniteTypeSystem
