module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.Grading

/-!
# Functoriality of the twisted-section module in the twisted object

The graded module of twisted sections `Γ_*(X, F, L) = ⨁_{m ≥ 0} Γ(X, F ⊗ L ^⊗ m)` is covariant
in `F`: a morphism `φ : F ⟶ G` whiskered by `m` copies of `L` carries `F ⊗ L ^⊗ m` to
`G ⊗ L ^⊗ m`, hence twisted sections of degree `m` to twisted sections of degree `m`, and the
resulting map on the direct sum is linear over the section ring `Γ_*(X, L)` and preserves the
grading.

## Main definitions

* `Stacks.TwistedSections.twistPowMap`: `F ⊙ m ⟶ G ⊙ m`, the morphism `φ` whiskered by `m`
  copies of `L`.
* `Stacks.TwistedSections.twistSectionsHom`: the induced map on twisted sections of degree `m`.
* `Stacks.TwistedSections.twistModuleHom`: the induced map on the whole direct sum.
* `Stacks.TwistedSections.twistModuleLinearMap`: the same map, as a linear map over the section
  ring.

## Main results

* `Stacks.TwistedSections.twistPowMap_id` and `Stacks.TwistedSections.twistPowMap_comp`: the
  whiskered morphism of an identity is the identity, and whiskering commutes with composition.
* `Stacks.TwistedSections.actMap_comp_twistPowMap`: the action of a tensor power on twisted
  sections is natural in the twisted object.
* `Stacks.TwistedSections.twistModuleHom_smul`: the induced map is linear over the section ring.
* `Stacks.TwistedSections.twistModuleHom_mem_moduleGrading`: the induced map preserves the
  `ℤ`-grading of `Stacks.TwistedSections.moduleGrading`.

## References

* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections sectionRing HasTrivialSelfBraiding)

universe v u

namespace Stacks.TwistedSections

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {F G H L : C}

section Monoidal

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

/-- **The morphism `φ : F ⟶ G` whiskered by `m` copies of `L`**, as a morphism
`F ⊙ m ⟶ G ⊙ m` between the twisted objects, defined by `twistPowMap L φ 0 = φ` and
`twistPowMap L φ (m + 1) = twistPowMap L φ m ▷ L`. -/
def twistPowMap (L : C) (φ : F ⟶ G) : (m : ℕ) → (twistPow F L m ⟶ twistPow G L m)
  | 0 => φ
  | m + 1 => twistPowMap L φ m ▷ L

/-- In degree `0` the whiskered morphism is `φ` itself. -/
@[simp] theorem twistPowMap_zero (φ : F ⟶ G) : twistPowMap L φ 0 = φ := rfl

/-- In degree `m + 1` the whiskered morphism is the degree-`m` one whiskered on the right by
`L`. -/
theorem twistPowMap_succ (φ : F ⟶ G) (m : ℕ) :
    twistPowMap L φ (m + 1) = twistPowMap L φ m ▷ L := rfl

/-- The identity of `F`, whiskered by `m` copies of `L`, is the identity of `F ⊙ m`. -/
@[simp] theorem twistPowMap_id (m : ℕ) :
    twistPowMap L (𝟙 F) m = 𝟙 (twistPow F L m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [twistPowMap_succ, ih]
      exact id_whiskerRight _ _

/-- Whiskering by `m` copies of `L` sends a composite `φ ≫ ψ` to the composite of the whiskered
morphisms. -/
theorem twistPowMap_comp (φ : F ⟶ G) (ψ : G ⟶ H) (m : ℕ) :
    twistPowMap L (φ ≫ ψ) m = twistPowMap L φ m ≫ twistPowMap L ψ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [twistPowMap_succ, ih]
      exact comp_whiskerRight _ _ _

/-- Reindexing the degree commutes with the whiskered morphism. -/
theorem twistPowMap_eqToHom (φ : F ⟶ G) {m m' : ℕ} (h : m = m') :
    twistPowMap L φ m ≫ eqToHom (congrArg (twistPow G L) h) =
      eqToHom (congrArg (twistPow F L) h) ≫ twistPowMap L φ m' := by
  subst h; simp

/-- **The induced map on twisted sections of degree `m`**: postcomposition with the whiskered
morphism. -/
def twistSectionsMap (φ : F ⟶ G) (m : ℕ) (t : twistSections F L m) : twistSections G L m :=
  t ≫ twistPowMap L φ m

/-- **The action of a tensor power on a twisted section is natural in the twisted object.** -/
theorem actMap_comp_twistPowMap (φ : F ⟶ G) {m : ℕ} (t : twistSections F L m) (n : ℕ) :
    actMap (t ≫ twistPowMap L φ m) n = actMap t n ≫ twistPowMap L φ (m + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : actMap (t ≫ twistPowMap L φ m) n ▷ L
          = (actMap t n ≫ twistPowMap L φ (m + n)) ▷ L := by rw [ih]
      exact hstep.trans (comp_whiskerRight _ _ _)

/-- **The induced map is compatible with the action of the section ring on homogeneous
elements.** -/
theorem twistSectionsMap_gsmul (φ : F ⟶ G) {n m : ℕ} (a : powSections L n)
    (t : twistSections F L m) :
    twistSectionsMap φ (n + m) (gsmul a t) = gsmul a (twistSectionsMap φ m t) := by
  simp only [twistSectionsMap, gsmul_def, twistCongr, actMap_comp_twistPowMap, Category.assoc]
  rw [twistPowMap_eqToHom]
  exact Nat.add_comm m n

end Monoidal

section Preadditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable [Preadditive C]

/-- The induced map on twisted sections of degree `m`, as a homomorphism of additive groups. -/
def twistSectionsHom (φ : F ⟶ G) (m : ℕ) : twistSections F L m →+ twistSections G L m where
  toFun t := twistSectionsMap φ m t
  map_zero' := Limits.zero_comp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- The additive homomorphism `twistSectionsHom φ m` acts as `twistSectionsMap φ m`. -/
@[simp] theorem twistSectionsHom_apply (φ : F ⟶ G) (m : ℕ) (t : twistSections F L m) :
    twistSectionsHom φ m t = twistSectionsMap φ m t := rfl

/-- **The induced map on the graded module of twisted sections.** -/
noncomputable def twistModuleHom (φ : F ⟶ G) : twistModule F L →+ twistModule G L :=
  DirectSum.toAddMonoid fun m =>
    (DirectSum.of (twistSections G L) m).comp (twistSectionsHom (L := L) φ m)

/-- On the summand of degree `m`, the induced map on the direct sum is `twistSectionsMap φ m`. -/
@[simp] theorem twistModuleHom_of (φ : F ⟶ G) (m : ℕ) (t : twistSections F L m) :
    twistModuleHom (L := L) φ (DirectSum.of (twistSections F L) m t) =
      DirectSum.of (twistSections G L) m (twistSectionsMap φ m t) :=
  DirectSum.toAddMonoid_of _ _ _

/-- The map induced by the identity of `F` is the identity of `Γ_*(X, F, L)`. -/
@[simp] theorem twistModuleHom_id :
    twistModuleHom (L := L) (𝟙 F) = AddMonoidHom.id (twistModule F L) := by
  refine DirectSum.addHom_ext fun m t => ?_
  rw [twistModuleHom_of, twistSectionsMap, twistPowMap_id, Category.comp_id,
    AddMonoidHom.id_apply]

/-- The map induced by a composite `φ ≫ ψ` is the composite of the induced maps. -/
theorem twistModuleHom_comp (φ : F ⟶ G) (ψ : G ⟶ H) :
    twistModuleHom (L := L) (φ ≫ ψ) =
      (twistModuleHom (L := L) ψ).comp (twistModuleHom (L := L) φ) := by
  refine DirectSum.addHom_ext fun m t => ?_
  rw [twistModuleHom_of, AddMonoidHom.comp_apply, twistModuleHom_of, twistModuleHom_of,
    twistSectionsMap, twistSectionsMap, twistSectionsMap, twistPowMap_comp, Category.assoc]

/-- **The induced map preserves the `ℤ`-grading of the twisted-section module.** -/
theorem twistModuleHom_mem_moduleGrading (φ : F ⟶ G) (i : ℤ) (x : twistModule F L)
    (hx : x ∈ moduleGrading F L i) : twistModuleHom (L := L) φ x ∈ moduleGrading G L i := by
  obtain ⟨m⟩ | ⟨k⟩ := i
  · obtain ⟨t, rfl⟩ := mem_moduleGrading_natCast_iff.mp hx
    exact ⟨twistSectionsMap φ m t, (twistModuleHom_of φ m t).symm⟩
  · have hx0 : x = 0 := by simpa [moduleGrading_negSucc] using hx
    rw [hx0, map_zero]
    exact zero_mem _

variable [(tensorRight L).Additive] [BraidedCategory C] [HasTrivialSelfBraiding L]

/-- **The induced map is linear over the section ring.** -/
theorem twistModuleHom_smul (φ : F ⟶ G) (r : sectionRing L) (x : twistModule F L) :
    twistModuleHom (L := L) φ (r • x) = r • twistModuleHom (L := L) φ x := by
  induction r using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | of m t =>
          rw [of_smul_of, twistModuleHom_of, twistModuleHom_of, of_smul_of,
            twistSectionsMap_gsmul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  | add r r' hr hr' => rw [add_smul, map_add, hr, hr', add_smul]

/-- **The induced map on the graded module of twisted sections, as a linear map over the section
ring `Γ_*(X, L)`.** -/
noncomputable def twistModuleLinearMap (φ : F ⟶ G) :
    twistModule F L →ₗ[sectionRing L] twistModule G L where
  toFun := twistModuleHom (L := L) φ
  map_add' := map_add _
  map_smul' := twistModuleHom_smul φ

/-- The linear map `twistModuleLinearMap φ` acts as the additive homomorphism
`twistModuleHom φ`. -/
@[simp] theorem twistModuleLinearMap_apply (φ : F ⟶ G) (x : twistModule F L) :
    twistModuleLinearMap (L := L) φ x = twistModuleHom (L := L) φ x := rfl

end Preadditive

end Stacks.TwistedSections

end
