module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianModuleAbelian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerreModules
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PointSimplicialIdealModule
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PointSimplicialTransitionFlat
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SphereCosimplicialRing

/-!
# Cartesian modules can be abelian without being a Serre subcategory

Stacks 0D7K observes that, Stacks 0D7J notwithstanding, the cartesian `O`-modules can form an
abelian category without being a Serre subcategory of `Mod(O)`. This file gives an example: the
constant simplicial site on the point, with `O` the cosimplicial ring
`CategoryTheory.SphereCosimplicialRing.sphereRing` of functions on `Spec ℤ ⊔ (Δ[3] / ∂Δ[3])`, which
is `ℤ` in degrees at most two and has `2`-torsion in degree three.

All transition maps between degrees at most two are bijective, so `f_{δ¹₁}`, `f_{δ¹₀}` and the
degree-two faces are flat, and the cartesian `O`-modules form an abelian category by the corrected
form of Stacks 0D7K. But the kernel in `Mod(O)` of multiplication by `2` on `O` is not cartesian:
if it were, it would vanish, being zero in degree zero, while it contains the ideal
`I₃ = ker (O₃ ⟶ ℤ)`, which is nonzero and killed by `2`. So the cartesian `O`-modules are not
closed under kernels in `Mod(O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.PointSimplicialSite.SphereExample

open SphereCosimplicialRing

noncomputable section

/-- The cosimplicial ring of `Δ[3] / ∂Δ[3]`. -/
abbrev B : SimplexCategory ⥤ CommRingCat.{u} := sphereRing.{u}

/-- The degree-one faces are flat. -/
theorem isFlat_δ₁ (i : Fin 2) :
    (situation.{u}.transitionRingedToposHom (ringSheaf B) (SimplexCategory.δ i)).IsFlat :=
  isFlat_transitionRingedToposHom B _ (flat_map _ (by simp) (by simp))

/-- The degree-two faces are flat. -/
theorem isFlat_δ₂ (i : Fin 3) :
    (situation.{u}.transitionRingedToposHom (ringSheaf B) (SimplexCategory.δ i)).IsFlat :=
  isFlat_transitionRingedToposHom B _ (flat_map _ (by simp) (by simp))

/-- The cartesian modules form an abelian category. -/
abbrev abelian : Abelian (situation.{u}.CartesianModuleSheaf (ringSheaf B)) :=
  situation.cartesianModuleSheafAbelian (ringSheaf B) (isFlat_δ₁ 1) (isFlat_δ₁ 0) ⟨1, isFlat_δ₂ 1⟩

/-- Multiplication by `2` on the structure sheaf. -/
abbrev two : unitModule B.{u} ⟶ unitModule B := 𝟙 _ + 𝟙 _

/-- Multiplication by `2` on the structure sheaf sends a section `x` in degree `n` to `x + x`. -/
theorem two_app (n : SimplexCategory) (x : (unitModule B.{u}).val.obj (op (tot n))) :
    two.val.app (op (tot n)) x = x + x := rfl

/-- If the kernel of multiplication by `2` is cartesian, its inclusion vanishes, since `O₀ = ℤ`
has no `2`-torsion. -/
private theorem kernel_ι_two_eq_zero
    (hK : situation.{u}.IsCartesianModule (ringSheaf B) (kernel two.{u})) :
    kernel.ι two.{u} = 0 := by
  refine eq_zero_of_isCartesian hK _ (fun y => ?_)
  have h := congrArg (fun g => g.val.app (op (tot.{u} ⦋0⦌)) y) (kernel.condition two.{u})
  change two.{u}.val.app (op (tot.{u} ⦋0⦌)) ((kernel.ι two.{u}).val.app (op (tot.{u} ⦋0⦌)) y) = 0
    at h
  rw [two_app] at h
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := (⊥ : Ideal (B.{u}.obj ⦋0⦌)))
    ((kernel.ι two.{u}).val.app (op (tot.{u} ⦋0⦌)) y)
  rw [← ha] at h ⊢
  change Ideal.Quotient.mk (⊥ : Ideal (B.{u}.obj ⦋0⦌)) (a + a) = 0 at h
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at h
  change Ideal.Quotient.mk (⊥ : Ideal (B.{u}.obj ⦋0⦌)) a = 0
  rw [eq_zero_of_add_self_eq_zero h, map_zero]

/-- The augmentation ideal is killed by `2`. -/
private theorem idealIncl_augIdeal_comp_two :
    idealIncl B.{u} augIdeal (fun φ => augIdeal_comap φ) ≫ two = 0 := by
  apply tot_hom_ext
  intro n x
  change Ideal.Quotient.mk ⊥ x.1 + Ideal.Quotient.mk ⊥ x.1 = 0
  rw [← map_add, add_self_eq_zero_of_mem x.2, map_zero]

/-- **The cartesian modules are not closed under kernels in `Mod(O)`.** -/
theorem not_isWeakSerreClass :
    ¬ ObjectProperty.IsWeakSerreClass (situation.{u}.IsCartesianModule (ringSheaf B)) := by
  intro hW
  have hO := unitModule_isCartesian B.{u}
  have ht : idealIncl B.{u} augIdeal (fun φ => augIdeal_comap φ) = 0 := by
    rw [← kernel.lift_ι two _ idealIncl_augIdeal_comp_two.{u}, kernel_ι_two_eq_zero.{u}
      (ObjectProperty.prop_kernel (P := situation.{u}.IsCartesianModule (ringSheaf B)) two hO hO),
      comp_zero]
  have h3 := congrArg (fun g => g.val.app (op (tot.{u} ⦋3⦌)) ⟨top, top_mem⟩) ht
  change Ideal.Quotient.mk ⊥ top = 0 at h3
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at h3
  exact top_ne_zero h3

end

/-- **Stacks 0D7K: cartesian modules can be abelian without being a Serre subcategory.** There is a
simplicial site (the constant simplicial site on the point, in case (A) of Stacks 09WE) and a sheaf
of rings `O` on its total site with `f_{δ¹₁}` and `f_{δ¹₀}` flat, such that the cartesian
`O`-modules form an abelian category but are neither a Serre subcategory nor a weak Serre
subcategory of `Mod(O)`: they are not closed under kernels in `Mod(O)`. Here `O` is the
cosimplicial ring of functions on `Spec ℤ ⊔ (Δ[3] / ∂Δ[3])`; the non-flat transitions are those
into degree three. -/
@[stacks 0D7K "the assertion that the category of cartesian O-modules can be abelian without \
being a Serre subcategory of Mod(O): an example with f_{δ¹₁}, f_{δ¹₀} flat where the cartesian \
O-modules form an abelian category but are neither a Serre nor a weak Serre subcategory of \
Mod(O). The source's remark that, when f_{δ²₀} is not flat, there is no reason for the \
inclusion into Mod(O) to be exact is a heuristic, not an assertion; in this example the \
non-flat transitions are those into degree three"]
theorem exists_abelian_not_isSerreClass :
    ∃ (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u}),
      (S.transitionRingedToposHom O (SimplexCategory.δ (1 : Fin 2))).IsFlat ∧
      (S.transitionRingedToposHom O (SimplexCategory.δ (0 : Fin 2))).IsFlat ∧
      Nonempty (Abelian (S.CartesianModuleSheaf O)) ∧
      ¬ ObjectProperty.IsSerreClass (S.IsCartesianModule O) ∧
      ¬ ObjectProperty.IsWeakSerreClass (S.IsCartesianModule O) :=
  ⟨situation, ringSheaf B, isFlat_δ₁ 1, isFlat_δ₁ 0, ⟨abelian⟩,
    fun h => not_isWeakSerreClass (by have := h; infer_instance), not_isWeakSerreClass⟩

end CategoryTheory.PointSimplicialSite.SphereExample

end
