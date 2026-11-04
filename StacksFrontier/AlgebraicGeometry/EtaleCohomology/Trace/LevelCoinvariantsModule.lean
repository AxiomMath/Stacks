module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsLimit

/-!
# The level coinvariants as a finite continuous module

All names are in the namespace `Stacks.EtaleCohomology`.

Let `ρ : G → GL_r(ℤ_ℓ)` be a continuous representation and `H ⊆ G` a normal subgroup. The level
coinvariants `((ℤ/ℓ^k)^r)_H` carry the residual action of `G` (`coinvariantsFrobenius`), continuous
for the discrete topology, so they form a finite `ℤ/ℓ^k`-module with continuous `G`-action, on
which `H` acts trivially, and the quotient map from the level module is a morphism of such modules.
This is the module `F''` of the reformulation of [Stacks, Tag 03VK]: the maximal quotient of the
level of `ℱ_ρ` on which the geometric fundamental group acts trivially.

## Main definitions

* `levelCoinvariantsModule`: `((ℤ/ℓ^k)^r)_H` with the action of `G`.
* `levelCoinvariantsQuotient`: the quotient map from the level module.

## Main results

* `surjective_levelCoinvariantsQuotient`: the quotient map is surjective.
* `levelCoinvariantsRepresentation_eq_of_mem`: `H` acts trivially.
-/

@[expose] public noncomputable section

open CategoryTheory Representation Stacks.GroupCohomology

universe u v

namespace Stacks.EtaleCohomology

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) [H.Normal] {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ} (ρ : G →* GL (Fin r) ℤ_[ℓ])
  (hρ : Continuous ρ)

/-- The residual action of `G` on the level coinvariants, on a carrier in the universe `u + 1`. -/
def levelCoinvariantsRepresentation (k : ℕ) :
    Representation (ZMod (ℓ ^ k)) G (ULift.{u + 1} (levelCoinvariants H ρ k)) where
  toFun g :=
    (ULift.moduleEquiv (R := ZMod (ℓ ^ k)) (M := levelCoinvariants H ρ k)).symm.toLinearMap ∘ₗ
      levelCoinvariantsFrobenius H ρ g k ∘ₗ
        (ULift.moduleEquiv (R := ZMod (ℓ ^ k)) (M := levelCoinvariants H ρ k)).toLinearMap
  map_one' := by
    ext ⟨x⟩ : 1
    apply ULift.ext
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
    change Coinvariants.mk _ (matrixRepresentation (levelMatrixRepresentation ρ k) 1 v) =
      Coinvariants.mk _ v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext ⟨x⟩ : 1
    apply ULift.ext
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
    change Coinvariants.mk _ (matrixRepresentation (levelMatrixRepresentation ρ k) (g * h) v) =
      Coinvariants.mk _ (matrixRepresentation (levelMatrixRepresentation ρ k) g
        (matrixRepresentation (levelMatrixRepresentation ρ k) h v))
    rw [map_mul]
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- `g` sends the class of `v` to the class of `ρ(g) v`. -/
theorem levelCoinvariantsRepresentation_mk (k : ℕ) (g : G) (v : Fin r → ZMod (ℓ ^ k)) :
    (levelCoinvariantsRepresentation H ρ k g (ULift.up (Coinvariants.mk _ v))).down =
      Coinvariants.mk _ (levelRepresentation ρ k g v) :=
  rfl

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology

include hρ in
/-- The residual action of `G` on the level coinvariants is continuous for the discrete
topology. -/
theorem isContinuous_levelCoinvariantsRepresentation (k : ℕ) :
    (actionOfRepresentation (ZMod (ℓ ^ k)) G _
      (levelCoinvariantsRepresentation H ρ k)).IsContinuous :=
  (isContinuous_actionOfRepresentation_iff _).2 fun x => by
    obtain ⟨y⟩ := x
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ y
    refine isOpen_iff_mem_nhds.2 fun g hg => ?_
    have hopen := isOpen_setOf_levelRepresentation_apply_eq ρ hρ k v
    have hfix : ∀ h : G, levelRepresentation ρ k h v = v →
        levelCoinvariantsRepresentation H ρ k h (ULift.up (Coinvariants.mk _ v)) =
          ULift.up (Coinvariants.mk _ v) := fun h hh =>
      ULift.ext _ _ ((levelCoinvariantsRepresentation_mk H ρ k h v).trans (congrArg _ hh))
    have hsub : (g * ·) '' {h : G | levelRepresentation ρ k h v = v} ⊆
        {g' : G | levelCoinvariantsRepresentation H ρ k g' (ULift.up (Coinvariants.mk _ v)) =
          ULift.up (Coinvariants.mk _ v)} := by
      rintro _ ⟨h, hh, rfl⟩
      show levelCoinvariantsRepresentation H ρ k (g * h) _ = _
      rw [map_mul, Module.End.mul_apply, hfix h hh]
      exact hg
    have hmem : (g * ·) '' {h : G | levelRepresentation ρ k h v = v} ∈ nhds g :=
      (isOpenMap_mul_left g _ hopen).mem_nhds ⟨1, by simp, by simp⟩
    exact Filter.mem_of_superset hmem hsub

/-- **The level coinvariants as a finite `ℤ/ℓ^k`-module with continuous `G`-action.** -/
def levelCoinvariantsModule (k : ℕ) [NeZero (ℓ ^ k)] :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod (ℓ ^ k)) G :=
  ⟨ofRepresentation (levelCoinvariantsRepresentation H ρ k)
      (isContinuous_levelCoinvariantsRepresentation H ρ hρ k),
    (ModuleCat.isFG_iff _).2 (Module.Finite.equiv ULift.moduleEquiv.symm)⟩

/-- **The quotient map from the level module to the level coinvariants.** -/
def levelCoinvariantsQuotient (k : ℕ) [NeZero (ℓ ^ k)] :
    levelModule.{u + 1, u + 1} ρ hρ k ⟶ levelCoinvariantsModule H ρ hρ k :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun y => ULift.up (Coinvariants.mk _ y.down)
          map_add' := fun a b => ULift.ext _ _ (map_add _ _ _)
          map_smul' := fun a b => ULift.ext _ _ (map_smul _ _ _) }
      comm := fun g => by
        ext y
        exact ULift.ext _ _ rfl }))

/-- The quotient map sends `v` to its class in the level coinvariants. -/
theorem levelCoinvariantsQuotient_apply (k : ℕ) [NeZero (ℓ ^ k)]
    (y : ULift.{u + 1} (Fin r → ZMod (ℓ ^ k))) :
    ((levelCoinvariantsQuotient H ρ hρ k).hom.hom.hom.hom.hom y).down = Coinvariants.mk _ y.down :=
  rfl

/-- The quotient map from the level module to the level coinvariants is surjective. -/
theorem surjective_levelCoinvariantsQuotient (k : ℕ) [NeZero (ℓ ^ k)] :
    Function.Surjective (levelCoinvariantsQuotient H ρ hρ k).hom.hom.hom.hom.hom := fun x => by
  obtain ⟨v, hv⟩ := Coinvariants.mk_surjective _ x.down
  exact ⟨ULift.up v, ULift.ext _ _ hv⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- **`H` acts trivially on the level coinvariants.** -/
theorem levelCoinvariantsRepresentation_eq_of_mem (k : ℕ) {h : G} (hh : h ∈ H)
    (x : ULift.{u + 1} (levelCoinvariants H ρ k)) :
    levelCoinvariantsRepresentation H ρ k h x = x := by
  obtain ⟨x⟩ := x
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  exact ULift.ext _ _ ((levelCoinvariantsRepresentation_mk H ρ k h v).trans
    (Coinvariants.mk_self_apply ((levelRepresentation ρ k).comp H.subtype) ⟨h, hh⟩ v))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The action of `φ` on the level coinvariants is `levelCoinvariantsFrobenius`. -/
theorem levelCoinvariantsRepresentation_down (k : ℕ) (φ : G)
    (x : ULift.{u + 1} (levelCoinvariants H ρ k)) :
    (levelCoinvariantsRepresentation H ρ k φ x).down = levelCoinvariantsFrobenius H ρ φ k x.down :=
  rfl

end Stacks.EtaleCohomology

end
