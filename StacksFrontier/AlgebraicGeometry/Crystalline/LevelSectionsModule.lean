module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs

/-!
# The module `M = lim_e Γ(T_e, ℱ)` of [Stacks, Tag 07JG], over the ring `D = lim_e Γ(T_e, 𝒪)`

For a system of levels `T_0 ⟶ T_1 ⟶ ⋯` of `Cris(X/S)`, the ring
`Crystalline.GlobalCrystallineSituation.SmallSite.levelRingLimit` and the group
`...SmallSite.levelSectionsLimit` are the two limits that [Stacks, Lemma 60.17.3, Tag 07JG] calls
`D` and `M`. This module makes `M` a module over `D`, and makes the assignment
`ℱ ↦ lim_e Γ(T_e, ℱ)` a functor on the crystals in quasi-coherent `𝒪_{X/S}`-modules.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `instSMulLevelSectionsLimit` and `instModuleLevelSectionsLimit` — **the module structure of
  `M = lim_e Γ(T_e, ℱ)` over `D = lim_e Γ(T_e, 𝒪_{T_e})`**, acting level by level.
* `levelSectionsLimitMap` — a morphism of crystals induces a `D`-linear map of the limits.
* `levelSectionsLimitFunctor` — **the limit of `...SmallSite.crystalSectionsFunctor` over a system
  of levels, as a functor** `QuasiCoherentCrystal S ⥤ ModuleCat D`.
* `levelTowerLift` — the chain of lifts of a section of a crystal to every higher level, when each
  one-step restriction of the system is surjective.

## Main results

* `levelSectionsLimit_smul_val` and `levelSectionsLimitMap_val` — the action and the induced map
  are the level-by-level ones, which is what every clause of `...SmallSite.PreReduction07JG` is
  stated against; the second is the clause `...PreReduction07JG.sections_naturality` read at the
  identity identification.
* `levelSectionsLimitMap_id` and `levelSectionsLimitMap_comp` — functoriality, from which
  `levelSectionsLimitFunctor` is assembled.
* `exists_levelSectionsLimit_val_eq` — **the limit surjects onto the sections over each level** as
  soon as every one-step restriction of the system does, with `levelRestrict_comp` and
  `levelTowerLift_restrict` the two steps of the tower argument.

## What is and is not proved

Nothing here is any part of [Stacks, Tag 07JG] or [Stacks, Tag 07JH], and **no tag attribute is
placed in this module**.  What is proved is the structure that the clauses of
`...SmallSite.PreReduction07JG` presuppose:

* that `lim_e Γ(T_e, ℱ)` is a module over `lim_e Γ(T_e, 𝒪_{T_e})`.  The action is pointwise and
  the only thing to check is that it preserves the compatibility conditions, which is
  semilinearity of the restriction maps of a presheaf of modules,
  `PresheafOfModules.map_smul`;
* that the assignment is functorial, which is naturality of a morphism of sheaves of modules,
  `PresheafOfModules.naturality_apply`;
* that the limit surjects onto each level when the single steps do.  The lifts above the level are
  chosen one at a time and the levels below it are reached by restriction; the work is the proof
  that the result is a *compatible* family, which is an induction on the number of steps.  This
  is a statement about an `ℕ`-indexed inverse system of sections and uses nothing about
  `Cris(X/S)`; surjectivity of the single steps is **not** proved here.

Neither uses the crystal condition, the quasi-coherence condition, or any property of the system
of levels: they hold for an arbitrary functor `ℕ ⥤ Cris(X/S)` and an arbitrary sheaf of
`𝒪_{X/S}`-modules.  They are stated on `...SmallSite.QuasiCoherentCrystal` only because that is
the category the clauses of `...SmallSite.PreReduction07JG` quantify over.

This module structure is different from `...SmallSite.levelSectionsModule`, which makes the
sections over *one* level `(n, e)` a module over the *one* envelope `D(n)`, by restriction of
scalars along `D(n) ⟶ D(n)/(p)^{N + e}`, and varies in the cosimplicial direction `n`.  Here the
level `e` is the direction taken the limit of, and the scalars are the limit ring.

In particular the four items of [Stacks, Tag 07JG] are untouched.  (07JB), `p`-adic completeness
of this module, is **not** proved here: it is the statement that the limit of the `Γ(T_e, ℱ)` is
`p`-adically complete, which needs the levels to be the ones of [Stacks, Tag 07JN] and their
section rings to be `D/(p)^{N + e}`, and it remains a carried field of
`Crystalline.FirstOrderCrystal`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (T : ℕ ⥤ CrystallineThickening S)

/-! ### The module structure of the limit of the level sections -/

/-- **The action of `D = lim_e Γ(T_e, 𝒪_{T_e})` on `M = lim_e Γ(T_e, ℱ)`**, level by level.  That
a compatible family of scalars times a compatible family of sections is again compatible is
semilinearity of the restriction maps of a presheaf of modules. -/
instance instSMulLevelSectionsLimit (F : QuasiCoherentCrystal S) :
    SMul ↥(levelRingLimit S T) ↥(levelSectionsLimit S T F) where
  smul a s := ⟨a.val • s.val, fun {e e'} h ↦ by
    change F.obj.val.map (T.map h).op (a.val e' • s.val e') = a.val e • s.val e
    rw [PresheafOfModules.map_smul, s.2 h]
    exact congrArg (· • s.val e) (a.2 h)⟩

/-- The action of the limit ring on the limit of the level sections is computed level by level. -/
@[simp] theorem levelSectionsLimit_smul_val {F : QuasiCoherentCrystal S}
    (a : ↥(levelRingLimit S T)) (s : ↥(levelSectionsLimit S T F)) (e : ℕ) :
    (a • s).val e = a.val e • s.val e :=
  rfl

/-- **The limit of the level sections of a crystal is a module over the limit of the level section
rings.**  With it, the module `M` of [Stacks, Tag 07JG] is a module over the ring `D` of that tag
on the nose, and not merely an abelian group with a level-by-level semilinearity clause. -/
instance instModuleLevelSectionsLimit (F : QuasiCoherentCrystal S) :
    Module ↥(levelRingLimit S T) ↥(levelSectionsLimit S T F) :=
  Subtype.coe_injective.module _ (AddSubgroup.subtype (levelSectionsLimit S T F))
    fun _ _ ↦ rfl

/-! ### Functoriality in the crystal -/

variable {T}

/-- **A morphism of crystals induces a `D`-linear map of the limits of the level sections**, level
by level.  That the family of images is again compatible is naturality of the morphism for the
restriction maps along the structure maps of the system. -/
def levelSectionsLimitMap {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) :
    ↥(levelSectionsLimit S T F) →ₗ[↥(levelRingLimit S T)] ↥(levelSectionsLimit S T G) where
  toFun s := ⟨fun e ↦ (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
      (op (T.obj e))).hom (s.val e), fun {e e'} h ↦ by
    change G.obj.val.map (T.map h).op
        ((PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
          (op (T.obj e'))).hom (s.val e')) =
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
        (op (T.obj e))).hom (s.val e)
    conv_rhs => rw [← s.2 h]
    exact (PresheafOfModules.naturality_apply ((quasiCoherentCrystalι S).map psi).val
      (T.map h).op (s.val e')).symm⟩
  map_add' s t := Subtype.ext (funext fun e ↦ map_add _ _ _)
  map_smul' a s := Subtype.ext (funext fun e ↦ map_smul _ _ _)

/-- **The induced map of limits is computed by its components.**  This is also the shape in which
the clause `Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG.sections_naturality`
asks for naturality, so a datum whose module is this limit discharges that clause by this
lemma. -/
@[simp] theorem levelSectionsLimitMap_val {F G : QuasiCoherentCrystal S} (psi : F ⟶ G)
    (s : ↥(levelSectionsLimit S T F)) (e : ℕ) :
    (levelSectionsLimitMap psi s).val e =
      (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
        (op (T.obj e))).hom (s.val e) :=
  rfl

/-- The identity morphism of a crystal induces the identity map of the limits. -/
theorem levelSectionsLimitMap_id (F : QuasiCoherentCrystal S) :
    levelSectionsLimitMap (T := T) (𝟙 F) = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)

/-- The map of limits induced by a composite of morphisms of crystals is the composite of the
induced maps. -/
theorem levelSectionsLimitMap_comp {F G H : QuasiCoherentCrystal S} (psi : F ⟶ G) (chi : G ⟶ H) :
    levelSectionsLimitMap (T := T) (psi ≫ chi) =
      (levelSectionsLimitMap chi).comp (levelSectionsLimitMap psi) :=
  LinearMap.ext fun _ ↦ Subtype.ext (funext fun _ ↦ rfl)

/-- **The limit of the level sections, as a functor on the crystals in quasi-coherent
`𝒪_{X/S}`-modules.**  Its value at `ℱ` is the module `M = lim_e Γ(T_e, ℱ)` of
[Stacks, Tag 07JG] over the ring `D = lim_e Γ(T_e, 𝒪_{T_e})` of that tag, and its value at a
morphism is the level-by-level map. -/
def levelSectionsLimitFunctor (S : GlobalCrystallineSituation.{u})
    (T : ℕ ⥤ CrystallineThickening S) :
    QuasiCoherentCrystal S ⥤ ModuleCat.{u} ↥(levelRingLimit S T) where
  obj F := ModuleCat.of _ ↥(levelSectionsLimit S T F)
  map psi := ModuleCat.ofHom (levelSectionsLimitMap psi)
  map_id F := by rw [levelSectionsLimitMap_id]; rfl
  map_comp psi chi := by rw [levelSectionsLimitMap_comp]; rfl

/-- The value of `levelSectionsLimitFunctor` at a crystal is the limit of its level sections. -/
@[simp] theorem levelSectionsLimitFunctor_obj (F : QuasiCoherentCrystal S) :
    (levelSectionsLimitFunctor S T).obj F = ModuleCat.of _ ↥(levelSectionsLimit S T F) :=
  rfl

/-- The value of `levelSectionsLimitFunctor` at a morphism is the induced map of limits. -/
@[simp] theorem levelSectionsLimitFunctor_map {F G : QuasiCoherentCrystal S} (psi : F ⟶ G) :
    (levelSectionsLimitFunctor S T).map psi = ModuleCat.ofHom (levelSectionsLimitMap psi) :=
  rfl

/-! ### Surjectivity of the limit onto a level -/

section Surjective

variable {F : QuasiCoherentCrystal S}

/-- **Restriction of the sections of a crystal along the system composes.**  The one lemma the
tower argument below runs on, stated for arbitrary morphisms of `ℕ` rather than for the
one-step ones. -/
theorem levelRestrict_comp {a b c : ℕ} (hab : a ⟶ b) (hbc : b ⟶ c)
    (x : F.obj.val.obj (op (T.obj c))) :
    F.obj.val.map (T.map hab).op (F.obj.val.map (T.map hbc).op x) =
      F.obj.val.map (T.map (hab ≫ hbc)).op x := by
  rw [T.map_comp, op_comp, PresheafOfModules.map_comp_apply]

/-- **A chain of lifts of a section above its own level.**  Given that each one-step restriction
`Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)` is surjective, a section over `T_{e₀}` is lifted to every higher
level by choosing a preimage at each step.  `levelTowerLift_restrict_succ` is the step it
satisfies and `levelTowerLift_restrict` the consequence for an arbitrary pair of levels. -/
noncomputable def levelTowerLift
    (hstep : ∀ e : ℕ, Function.Surjective
      (F.obj.val.map (T.map (homOfLE (Nat.le_succ e))).op))
    (e₀ : ℕ) (s : F.obj.val.obj (op (T.obj e₀))) :
    (k : ℕ) → F.obj.val.obj (op (T.obj (e₀ + k)))
  | 0 => s
  | k + 1 => (hstep (e₀ + k) (levelTowerLift hstep e₀ s k)).choose

/-- The lift at step `0` is the given section. -/
@[simp] theorem levelTowerLift_zero
    (hstep : ∀ e : ℕ, Function.Surjective
      (F.obj.val.map (T.map (homOfLE (Nat.le_succ e))).op))
    (e₀ : ℕ) (s : F.obj.val.obj (op (T.obj e₀))) :
    levelTowerLift hstep e₀ s 0 = s :=
  rfl

/-- Restricting the lift at step `k + 1` along the one-step map gives the lift at step `k`. -/
theorem levelTowerLift_restrict_succ
    (hstep : ∀ e : ℕ, Function.Surjective
      (F.obj.val.map (T.map (homOfLE (Nat.le_succ e))).op))
    (e₀ : ℕ) (s : F.obj.val.obj (op (T.obj e₀))) (k : ℕ) :
    F.obj.val.map (T.map (homOfLE (Nat.le_succ (e₀ + k)))).op
        (levelTowerLift hstep e₀ s (k + 1)) =
      levelTowerLift hstep e₀ s k :=
  (hstep (e₀ + k) (levelTowerLift hstep e₀ s k)).choose_spec

/-- **The chain of lifts is a compatible family.**  Restricting the lift at a higher level to a
lower one gives the lift there, by induction on the number of steps between them. -/
theorem levelTowerLift_restrict
    (hstep : ∀ e : ℕ, Function.Surjective
      (F.obj.val.map (T.map (homOfLE (Nat.le_succ e))).op))
    (e₀ : ℕ) (s : F.obj.val.obj (op (T.obj e₀))) {k j : ℕ} (h : k ≤ j) :
    F.obj.val.map (T.map (homOfLE (Nat.add_le_add_left h e₀))).op
        (levelTowerLift hstep e₀ s j) =
      levelTowerLift hstep e₀ s k := by
  induction j, h using Nat.le_induction with
  | base =>
    rw [show homOfLE (Nat.add_le_add_left (le_refl k) e₀) = 𝟙 (e₀ + k) from rfl, T.map_id,
      op_id, PresheafOfModules.map_id]
    rfl
  | succ j hkj ih =>
    rw [← ih, ← levelTowerLift_restrict_succ hstep e₀ s j, levelRestrict_comp]
    rfl

/-- **The limit of the level sections surjects onto the sections over each level**, as soon as
every one-step restriction of the system does.

This is the hypothesis `hsurj` of
`...SmallSite.LevelComparison07JG.faithful_functor`, reduced to a condition on the single steps of
the tower.  The levels below `e₀` are reached by restricting `s` itself and those above by
`levelTowerLift`; nothing here is about crystals, only about an `ℕ`-indexed inverse system of
sections. -/
theorem exists_levelSectionsLimit_val_eq
    (hstep : ∀ e : ℕ, Function.Surjective
      (F.obj.val.map (T.map (homOfLE (Nat.le_succ e))).op))
    (e₀ : ℕ) (s : F.obj.val.obj (op (T.obj e₀))) :
    ∃ m : ↥(levelSectionsLimit S T F), m.val e₀ = s := by
  refine ⟨⟨fun e ↦ F.obj.val.map (T.map (homOfLE (Nat.le_add_left e e₀))).op
    (levelTowerLift hstep e₀ s e), fun {e e'} h ↦ ?_⟩, ?_⟩
  · show F.obj.val.map (T.map h).op
        (F.obj.val.map (T.map (homOfLE (Nat.le_add_left e' e₀))).op
          (levelTowerLift hstep e₀ s e')) = _
    rw [levelRestrict_comp]
    have hle : e ≤ e' := leOfHom h
    rw [show h ≫ homOfLE (Nat.le_add_left e' e₀) =
      homOfLE (Nat.le_add_left e e₀) ≫ homOfLE (Nat.add_le_add_left hle e₀) from rfl,
      ← levelRestrict_comp, levelTowerLift_restrict hstep e₀ s hle]
  · show F.obj.val.map (T.map (homOfLE (Nat.le_add_left e₀ e₀))).op
        (levelTowerLift hstep e₀ s e₀) = s
    rw [levelTowerLift_restrict hstep e₀ s (Nat.zero_le e₀), levelTowerLift_zero]

end Surjective

end Crystalline.GlobalCrystallineSituation.SmallSite
