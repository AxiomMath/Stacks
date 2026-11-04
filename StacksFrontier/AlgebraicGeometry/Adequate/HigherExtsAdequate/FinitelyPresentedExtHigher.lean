module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Kernels
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.FinitelyPresentedExtTwo
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.Vanishing

/-!
# Higher Ext vanishing out of a finitely presented module functor

Let `A` be a ring, let `M` and `P` be `A`-modules with `P` of finite presentation, and let `𝒫`
be the category of module-valued functors on the commutative `A`-algebras. This file proves
`Ext³_𝒫(P̲, M̲) = 0`, where `X̲` is `B ↦ B ⊗[A] X`.

Choose a finite presentation `Aᵐ --d--> Aⁿ ⟶ P ⟶ 0`, so that `P̲` is the cokernel of `d̲`.
Both `Aᵐ̲` and `Aⁿ̲` are projective, so the contravariant long exact sequences of
`0 ⟶ ker d̲ ⟶ Aᵐ̲ ⟶ im d̲ ⟶ 0` and `0 ⟶ im d̲ ⟶ Aⁿ̲ ⟶ P̲ ⟶ 0` give, for every `k`, that
`Ext^{k+1}(ker d̲, M̲) = 0` implies `Ext^{k+3}(P̲, M̲) = 0`
(`AdequateFunctor.subsingleton_ext_cokernel_of_kernel`). The functor `ker d̲` is linearly
adequate and `M̲` is adequate, so `Ext¹(ker d̲, M̲) = 0` by Tag 06V7, in the form
`AdequateFunctor.subsingleton_zExt_one_of_isLinearlyAdequate`.

## Main results

* `AdequateFunctor.subsingleton_ext_cokernel_of_kernel` — the dimension shift from the kernel
  to the cokernel of a morphism between projective objects.
* `AdequateFunctor.subsingleton_zExt_moduleExtension_three` — Tag 06ZG in degree three.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06ZG](https://stacks.math.columbia.edu/tag/06ZG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t v u w

namespace AdequateFunctor

section ExtShift

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{t} C]

/-- For a morphism `δ : X ⟶ Y` between projective objects, the vanishing of
`Ext^{k+1}(ker δ, Z)` forces the vanishing of `Ext^{k+3}(coker δ, Z)`: the long exact sequences
of `0 ⟶ ker δ ⟶ X ⟶ im δ ⟶ 0` and `0 ⟶ im δ ⟶ Y ⟶ coker δ ⟶ 0` shift the degree twice. -/
lemma subsingleton_ext_cokernel_of_kernel {X Y : C} (δ : X ⟶ Y) (hX : Projective X)
    (hY : Projective Y) (Z : C) (k : ℕ)
    (hker : Subsingleton (Abelian.Ext.{t} (kernel δ) Z (k + 1))) :
    Subsingleton (Abelian.Ext.{t} (cokernel δ) Z (k + 3)) := by
  have hX2 : Subsingleton (Abelian.Ext.{t} X Z (k + 2)) :=
    Abelian.Ext.subsingleton_of_projective X Z (k + 1)
  have hY3 : Subsingleton (Abelian.Ext.{t} Y Z (k + 3)) :=
    Abelian.Ext.subsingleton_of_projective Y Z (k + 2)
  have himage : Subsingleton (Abelian.Ext.{t} (Abelian.image δ) Z (k + 2)) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃
      (coimageShortComplex_shortExact δ) (Y := Z) x (hX2.elim _ _) (n₀ := k + 1)
      (by omega)
    rw [← hx₁, hker.elim x₁ 0, Abelian.Ext.comp_zero]
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (abelianImageShortComplex_shortExact δ) (Y := Z) x (hY3.elim _ _) (n₀ := k + 2)
    (by omega)
  rw [← hx₁, himage.elim x₁ 0, Abelian.Ext.comp_zero]

end ExtShift

section DegreeThree

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (M P : ModuleCat.{max u v w} A)

/-- The finite free module of rank `n` at two universe annotations that produce the same
universe of carriers. -/
noncomputable def finiteFreeModuleUliftIso (n : ℕ) :
    finiteFreeModule.{max v w} A n ≅ finiteFreeModule.{max u v w} A n :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv.trans ULift.moduleEquiv.symm)

/-- The kernel of the base change of a map of finite free modules is linearly adequate. -/
lemma isLinearlyAdequate_kernel_moduleExtension {m n : ℕ}
    (d : finiteFreeModule.{max v w} A m ⟶ finiteFreeModule.{max v w} A n) :
    IsLinearlyAdequate (𝟭 _) (kernel ((moduleExtensionFunctor.{max u v w, v} A).map d)) := by
  let G := moduleExtensionFunctor.{max u v w, v} A
  let em := G.mapIso (finiteFreeModuleUliftIso.{v, u, w} A m)
  let en := G.mapIso (finiteFreeModuleUliftIso.{v, u, w} A n)
  exact (isLinearlyAdequate_iff _).2 ⟨m, n, em.inv ≫ G.map d ≫ en.hom,
    ⟨(kernelCompMono (G.map d) en.hom).symm ≪≫ (kernelIsIsoComp em.inv _).symm⟩⟩

/-- Degree `k + 3` of Tag 06ZG, given the vanishing of degree `k + 1` out of linearly adequate
functors, by the dimension shift along a finite free presentation of `P`. -/
private theorem subsingleton_zExt_moduleExtension_add_three [Module.FinitePresentation A P]
    (k : ℕ)
    (hL : ∀ L : ModuleValuedFunctor.{max u v w, v} A, IsLinearlyAdequate (𝟭 _) L →
      Subsingleton (Abelian.zExt L (moduleExtension.{max u v w, v} A M) ((k : ℤ) + 1))) :
    Subsingleton (Abelian.zExt (moduleExtension.{max u v w, v} A P)
      (moduleExtension.{max u v w, v} A M) ((k : ℤ) + 3)) := by
  let _ : HasExt.{max (u + 1) (v + 1) (w + 1)} (ModuleValuedFunctor.{max u v w, v} A) :=
    HasExt.standard (ModuleValuedFunctor.{max u v w, v} A)
  obtain ⟨n, m, d, p, hp, hdp⟩ := exists_finiteFree_presentation_large.{v} P
  have hker : Subsingleton (Abelian.Ext.{max (u + 1) (v + 1) (w + 1)}
      (kernel ((moduleExtensionFunctor.{max u v w, v} A).map d))
      (moduleExtension.{max u v w, v} A M) (k + 1)) :=
    (Abelian.Ext.homAddEquiv (n := k + 1)).subsingleton_congr.mpr
      (by exact_mod_cast hL _ (isLinearlyAdequate_kernel_moduleExtension A d))
  have h3 : Subsingleton (Abelian.Ext.{max (u + 1) (v + 1) (w + 1)}
      (moduleExtension.{max u v w, v} A P) (moduleExtension.{max u v w, v} A M) (k + 3)) :=
    subsingleton_ext_of_iso_left (presentationCokernelIso_large hp hdp) (k + 3)
      (subsingleton_ext_cokernel_of_kernel ((moduleExtensionFunctor.{max u v w, v} A).map d)
        (projective_moduleExtension (finiteFreeModule.{max v w} A m))
        (projective_moduleExtension (finiteFreeModule.{max v w} A n)) _ k hker)
  exact_mod_cast (Abelian.Ext.homAddEquiv
    (X := moduleExtension.{max u v w, v} A P) (Y := moduleExtension.{max u v w, v} A M)
    (n := k + 3)).symm.subsingleton

/-- **Stacks Project, Tag 06ZG in degree three.** For an `A`-module `P` of finite
presentation, `Ext³` from the module-valued functor `B ↦ B ⊗[A] P` to `B ↦ B ⊗[A] M` vanishes
in the category of module-valued functors on the commutative `A`-algebras. -/
@[stacks 06ZG "degree 3, by a double dimension shift to Ext¹ out of a linearly adequate \
functor, which vanishes by Tag 06V7"]
theorem subsingleton_zExt_moduleExtension_three [Module.FinitePresentation A P] :
    Subsingleton (Abelian.zExt (moduleExtension.{max u v w, v} A P)
      (moduleExtension.{max u v w, v} A M) 3) := by
  simpa using subsingleton_zExt_moduleExtension_add_three A M P 0 fun L hL => by
    simpa using subsingleton_zExt_one_of_isLinearlyAdequate.{u, v, w} A L
      (moduleExtension.{max u v w, v} A M) hL (isAdequate_moduleExtension M)

/-- Every positive degree of Tag 06ZG follows from the positive-degree vanishing of `Ext` out of
linearly adequate functors into `M̲`: degrees `1` and `2` are unconditional, and degree `k + 3`
is degree `k + 1` out of the kernel of a finite free presentation, by
`AdequateFunctor.subsingleton_ext_cokernel_of_kernel`. -/
theorem subsingleton_zExt_moduleExtension_of_linearlyAdequate [Module.FinitePresentation A P]
    (hL : ∀ L : ModuleValuedFunctor.{max u v w, v} A, IsLinearlyAdequate (𝟭 _) L →
      ∀ k : ℕ, Subsingleton (Abelian.zExt L (moduleExtension.{max u v w, v} A M) (k + 1)))
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (Abelian.zExt (moduleExtension.{max u v w, v} A P)
      (moduleExtension.{max u v w, v} A M) i) := by
  obtain ⟨k, rfl⟩ | rfl | rfl : (∃ k : ℕ, i = (k : ℤ) + 3) ∨ i = 1 ∨ i = 2 := by
    rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl ⟨(i - 3).toNat, by omega⟩
  · exact subsingleton_zExt_moduleExtension_add_three A M P k (hL · · k)
  · exact subsingleton_zExt_moduleExtension_one.{v} A M P
  · exact subsingleton_zExt_moduleExtension_two_large.{v} A M P

end DegreeThree

section DualUnit

variable {A : Type u} [CommRing A]

/-- For `N₀ ≅ A`, the values of `B ↦ B ⊗[A] A` and `B ↦ Hom_A(N₀, B)` agree. -/
noncomputable def tensorUnitDualEquiv {N₀ : Type (max u v)} [AddCommGroup N₀] [Module A N₀]
    (ε : N₀ ≃ₗ[A] A) (B : Type (max u v)) [CommRing B] [Algebra A B] :
    TensorProduct A B (ULift.{max u v w} A) ≃ₗ[B] (N₀ →ₗ[A] B) :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) ULift.moduleEquiv).trans <|
    (TensorProduct.AlgebraTensorModule.rid A B B).trans <|
      (LinearMap.ringLmapEquivSelf A B B).symm.trans (homCongrLeftLarge ε B)

/-- `tensorUnitDualEquiv ε B (b ⊗ₜ x)` sends `n : N₀` to `(ε n * x.down) • b`. -/
lemma tensorUnitDualEquiv_tmul {N₀ : Type (max u v)} [AddCommGroup N₀] [Module A N₀]
    (ε : N₀ ≃ₗ[A] A) (B : Type (max u v)) [CommRing B] [Algebra A B] (b : B)
    (x : ULift.{max u v w} A) (n : N₀) :
    tensorUnitDualEquiv ε B (b ⊗ₜ[A] x) n = (ε n * x.down) • b := by
  simp [tensorUnitDualEquiv, homCongrLeftLarge, mul_smul]

/-- `AdequateFunctor.tensorUnitDualEquiv` is natural in the algebra. -/
lemma tensorUnitDualEquiv_naturality {N₀ : Type (max u v)} [AddCommGroup N₀] [Module A N₀]
    (ε : N₀ ≃ₗ[A] A) {B C : Type (max u v)} [CommRing B] [Algebra A B] [CommRing C]
    [Algebra A C] (f : B →ₐ[A] C) (t : TensorProduct A B (ULift.{max u v w} A)) :
    tensorUnitDualEquiv ε C (TensorProduct.map f.toLinearMap LinearMap.id t) =
      f.toLinearMap.comp (tensorUnitDualEquiv ε B t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul b x =>
    ext n
    rw [TensorProduct.map_tmul, LinearMap.comp_apply, tensorUnitDualEquiv_tmul,
      tensorUnitDualEquiv_tmul]
    simp [Algebra.smul_def, map_mul]
  | add t t' ht ht' => simp only [map_add, ht, ht', LinearMap.comp_add]

/-- A module-valued functor whose values are naturally `Hom_A(N₀, B)` for a module `N₀ ≅ A` is
isomorphic to the functor of the free module of rank one, hence projective. -/
lemma projective_of_linearEquiv_dual {N₀ : Type (max u v)} [AddCommGroup N₀] [Module A N₀]
    (ε : N₀ ≃ₗ[A] A) (F : ModuleValuedFunctor.{max u v w, v} A)
    (e : ∀ B : CommAlgCat.{max u v} A, algebraValueLarge F B ≃ₗ[B] (N₀ →ₗ[A] B))
    (he : ∀ (B C : CommAlgCat.{max u v} A) (f : B ⟶ C) (x : algebraValueLarge F B),
      e C (algebraMapValueLarge F f.hom x) = f.hom.toLinearMap.comp (e B x)) :
    Projective F := by
  let Q : ModuleCat.{max u v w} A := ModuleCat.of A (ULift.{max u v w} A)
  have : Module.Projective A Q := Module.Projective.of_equiv ULift.moduleEquiv.symm
  refine Projective.of_iso (PresheafOfModules.isoMk (M₁ := moduleExtension.{max u v w, v} A Q)
    (M₂ := F) (fun X => ((tensorUnitDualEquiv ε X.unop.unop).trans
      (e X.unop.unop).symm).toModuleIso) ?_) inferInstance
  intro X Y f
  ext t
  show (e Y.unop.unop).symm (tensorUnitDualEquiv ε Y.unop.unop
      ((moduleExtension.{max u v w, v} A Q).map f t)) =
    F.map f ((e X.unop.unop).symm (tensorUnitDualEquiv ε X.unop.unop t))
  apply (e Y.unop.unop).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := he X.unop.unop Y.unop.unop f.unop.unop
    ((e X.unop.unop).symm (tensorUnitDualEquiv ε X.unop.unop t))
  show _ = e Y.unop.unop (F.map f _)
  refine Eq.trans ?_ h.symm
  rw [LinearEquiv.apply_symm_apply]
  exact tensorUnitDualEquiv_naturality ε f.unop.unop.hom t

end DualUnit

end AdequateFunctor

end
