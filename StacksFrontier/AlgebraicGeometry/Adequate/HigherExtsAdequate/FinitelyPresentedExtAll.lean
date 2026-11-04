module

public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.FinitelyPresentedExtHigher
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.PairsScaling

/-!
# Tag 06ZG in every positive degree

Let `A` be a ring, let `𝒫` be the category of module-valued functors on the commutative
`A`-algebras, and let `X̲` denote `B ↦ B ⊗[A] X`. For `A`-modules `M` and `P` with `P` of finite
presentation, `Ext^i_𝒫(P̲, M̲) = 0` for every `i > 0`.

The proof given in the Stacks Project goes through Tag 06ZA, which is false as stated
(`StacksFrontier/Examples/Algebra/InjectiveTangentNotRightExact.lean`; its proof step fails by
`AdequateFunctor.TangentEqualizer.free_not_equalizer`). This file uses a different argument. A
linearly adequate functor `L` is `φ_N^* V` for a finitely presented `A`-module `N`
(`AdequateFunctor.exists_iso_linearPairPullback`), where `V` is the tautological functor
`(C, V) ↦ V` on pairs and `φ_N : D ↦ (D, Hom_A(N, D))`. The exact adjunction `φ_N^* ⊣ ψ_N^*` then
identifies `Ext^n_𝒫(L, M̲)` with `Ext^n(V, ψ_N^* M̲)`, where `ψ_N^* M̲` is
`(C, V) ↦ Sym_C(V ⊗_A N) ⊗_A M` (`AdequateFunctor.extMap_pairsPushforwardAdjunction_bijective`).
Scaling by the dual numbers shows that every class `ξ` there satisfies `ξ = ξ ∘ Π`, where `Π` is
the weight-one projection (`AdequateFunctor.ext_comp_pairsWeightOneProjection`). `Π` factors
through `ψ_A^* (N ⊗ M)̲` (`AdequateFunctor.pairsWeightOneOut_comp_in`), and the higher `Ext` out of
`V` into that functor vanish because `φ_A^* V ≅ O` is projective. So `Ext^{n+1}_𝒫(L, M̲) = 0`, and
the double dimension shift `AdequateFunctor.subsingleton_zExt_moduleExtension_of_linearlyAdequate`
gives Tag 06ZG in every degree.

## Main results

* `AdequateFunctor.projective_linearPairPullback_unit`: `φ_A^* V` is projective.
* `AdequateFunctor.subsingleton_ext_tautological_symPairExtension_unit`:
  `Ext^{n+1}(V, ψ_A^* G̲) = 0`.
* `AdequateFunctor.subsingleton_ext_isLinearlyAdequate_moduleExtension`:
  `Ext^{n+1}_𝒫(L, M̲) = 0` for `L` linearly adequate.
* `AdequateFunctor.subsingleton_zExt_moduleExtension_of_finitePresentation`: Tag 06ZG.

## References

* [Stacks Project, Tag 06ZG](https://stacks.math.columbia.edu/tag/06ZG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe t v u w

namespace AdequateFunctor

section UnitPair

variable {A : Type u} [CommRing A]

/-- The values of `φ_A^* V`, `B ↦ Hom_A(A, B)`. -/
noncomputable def linearPairPullbackUnitValue (B : CommAlgCat.{max u v} A) :
    algebraValueLarge ((PresheafOfModules.pushforward.{max (u + 1) (v + 1) w}
      (linearPairRingHom.{v, u} (A := A) (unitPairModule.{v} A))).obj
        (tautologicalPairModule.{w, v} A)) B ≃ₗ[B] (unitPairModule.{v} A →ₗ[A] B) where
  toFun x := x.down
  invFun y := ULift.up y
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **`φ_A^* V` is projective**: it is the functor `B ↦ Hom_A(A, B) ≅ B`. -/
theorem projective_linearPairPullback_unit :
    Projective ((PresheafOfModules.pushforward.{max (u + 1) (v + 1) w}
      (linearPairRingHom.{v, u} (A := A) (unitPairModule.{v} A))).obj
        (tautologicalPairModule.{w, v} A)) :=
  projective_of_linearEquiv_dual.{v, u, max (u + 1) (v + 1) w} ULift.moduleEquiv _
    linearPairPullbackUnitValue fun _ _ _ _ => rfl

/-- **The higher `Ext` out of `V` into `ψ_A^* G̲` vanish**, by the adjunction `φ_A^* ⊣ ψ_A^*`
and the projectivity of `φ_A^* V`. -/
theorem subsingleton_ext_tautological_symPairExtension_unit
    [HasExt.{t} (PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)]
    (G : ModuleCat.{max (u + 1) (v + 1) w} A) (n : ℕ) :
    Subsingleton (Ext.{t} (tautologicalPairModule.{w, v} A)
      (symPairExtension.{w, v} (unitPairModule.{v} A) G) (n + 1)) := by
  let := HasExt.standard (ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
  have : Projective ((PresheafOfModules.pushforward.{max (u + 1) (v + 1) w}
      (linearPairRingHom.{v, u} (A := A) (unitPairModule.{v} A))).obj
        (tautologicalPairModule.{w, v} A)) := projective_linearPairPullback_unit
  have : Subsingleton (Ext ((PresheafOfModules.pushforward.{max (u + 1) (v + 1) w}
      (linearPairRingHom.{v, u} (A := A) (unitPairModule.{v} A))).obj
        (tautologicalPairModule.{w, v} A))
      (moduleExtension.{max (u + 1) (v + 1) w, v} A G) (n + 1)) :=
    Ext.subsingleton_of_projective _ _ n
  exact (extMap_pairsPushforwardAdjunction_bijective (unitPairModule.{v} A)
    (tautologicalPairModule.{w, v} A) (moduleExtension.{max (u + 1) (v + 1) w, v} A G)
    (n + 1)).1.subsingleton

end UnitPair

section LinearlyAdequate

variable {A : Type u} [CommRing A]

/-- **The higher `Ext` out of `V` into `ψ_N^* M̲` vanish.** Every class is fixed by the
weight-one projection, which factors through `ψ_A^* (N ⊗ M)̲`. -/
theorem subsingleton_ext_tautological_symPairExtension
    [HasExt.{t} (PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)]
    (N : Type (max u v)) [AddCommGroup N] [Module A N]
    (M : ModuleCat.{max (u + 1) (v + 1) w} A) (n : ℕ) :
    Subsingleton (Ext.{t} (tautologicalPairModule.{w, v} A) (symPairExtension.{w, v} N M)
      (n + 1)) := by
  have := subsingleton_ext_tautological_symPairExtension_unit (A := A)
    (pairCoefficient.{w, v} N M) n
  refine subsingleton_of_forall_eq 0 fun ξ => ?_
  calc ξ = ξ.comp (Ext.mk₀ (pairsWeightOneProjection.{w, v} N M)) (add_zero _) :=
        (ext_comp_pairsWeightOneProjection N M (n + 1) ξ).symm
    _ = ξ.comp ((Ext.mk₀ (pairsWeightOneOut.{w, v} N M)).comp
          (Ext.mk₀ (pairsWeightOneIn.{w, v} N M)) (add_zero 0)) (add_zero _) := by
        rw [Ext.mk₀_comp_mk₀, pairsWeightOneOut_comp_in]
    _ = (ξ.comp (Ext.mk₀ (pairsWeightOneOut.{w, v} N M)) (add_zero _)).comp
          (Ext.mk₀ (pairsWeightOneIn.{w, v} N M)) (add_zero _) :=
        (Ext.comp_assoc_of_third_deg_zero _ _ _ _).symm
    _ = 0 := by
        rw [Subsingleton.elim (ξ.comp (Ext.mk₀ (pairsWeightOneOut.{w, v} N M)) (add_zero _)) 0,
          Ext.zero_comp]

/-- **The higher `Ext` from a linearly adequate functor into `M̲` vanish**, in every degree. -/
theorem subsingleton_ext_isLinearlyAdequate_moduleExtension
    [HasExt.{t} (ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)]
    (L : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (hL : IsLinearlyAdequate (𝟭 _) L)
    (M : ModuleCat.{max (u + 1) (v + 1) w} A) (n : ℕ) :
    Subsingleton (Ext.{t} L (moduleExtension.{max (u + 1) (v + 1) w, v} A M) (n + 1)) := by
  obtain ⟨N, _, _, -, ⟨e⟩⟩ := exists_iso_linearPairPullback L hL
  let := HasExt.standard (PairModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
  have := subsingleton_ext_tautological_symPairExtension N M n
  have : Subsingleton (Ext.{t} ((PresheafOfModules.pushforward.{max (u + 1) (v + 1) w}
      (linearPairRingHom.{v, u} (A := A) N)).obj (tautologicalPairModule.{w, v} A))
      (moduleExtension.{max (u + 1) (v + 1) w, v} A M) (n + 1)) :=
    (extMap_pairsPushforwardAdjunction_bijective N (tautologicalPairModule.{w, v} A)
      (moduleExtension.{max (u + 1) (v + 1) w, v} A M) (n + 1)).2.subsingleton
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso e.hom (n + 1)).2.subsingleton

end LinearlyAdequate

section AllDegrees

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- **Stacks Project, Tag 06ZG.** For `A`-modules `M` and `P` with `P` of finite presentation,
`Ext^i(P̲, M̲) = 0` for every `i > 0` in the category of module-valued functors on the commutative
`A`-algebras, where `X̲` is `B ↦ B ⊗[A] X`. -/
@[stacks 06ZG "every degree i > 0; the published proof via Tag 06ZA is replaced by the \
transfer along phi_N^* -| psi_N^* and a dual-number scaling argument"]
theorem subsingleton_zExt_moduleExtension_of_finitePresentation
    (M P : ModuleCat.{max (u + 1) (v + 1) w} A) [Module.FinitePresentation A P]
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (Abelian.zExt (moduleExtension.{max (u + 1) (v + 1) w, v} A P)
      (moduleExtension.{max (u + 1) (v + 1) w, v} A M) i) := by
  refine subsingleton_zExt_moduleExtension_of_linearlyAdequate.{v, u, max (u + 1) (v + 1) w}
    A M P (fun L hL k => ?_) i hi
  let := HasExt.standard (ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A)
  have := subsingleton_ext_isLinearlyAdequate_moduleExtension L hL M k
  exact (Abelian.Ext.homAddEquiv (X := L)
    (Y := moduleExtension.{max (u + 1) (v + 1) w, v} A M) (n := k + 1)).symm.subsingleton

/-- Tag 06ZG with the finite presentation of `P` as an explicit hypothesis. -/
private theorem subsingleton_zExt_moduleExtension_of_finitePresentation_of_forall
    (M P : ModuleCat.{max (u + 1) (v + 1) w} A) (hP : Module.FinitePresentation A P)
    (j : ℤ) (hj : 0 < j) :
    Subsingleton (Abelian.zExt (moduleExtension.{max (u + 1) (v + 1) w, v} A P)
      (moduleExtension.{max (u + 1) (v + 1) w, v} A M) j) :=
  have := hP
  subsingleton_zExt_moduleExtension_of_finitePresentation.{v, u, w} A M P j hj

/-- **Stacks Project, Tag 06ZH.** Let `A` be a ring, `M` an `A`-module and `L` a linearly adequate
module-valued functor on the commutative `A`-algebras. Then `Ext^i(L, M̲) = 0` for every `i > 0`,
where `M̲` is `B ↦ B ⊗[A] M`. -/
@[stacks 06ZH "every degree i > 0, by the source's two dimension shifts from Tag 06ZG"]
theorem subsingleton_zExt_isLinearlyAdequate_moduleExtension
    (L : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (hL : IsLinearlyAdequate (𝟭 _) L)
    (M : ModuleCat.{max (u + 1) (v + 1) w} A) (i : ℤ) (hi : 0 < i) :
    Subsingleton (Abelian.zExt L (moduleExtension.{max (u + 1) (v + 1) w, v} A M) i) :=
  subsingleton_zExt_of_isLinearlyAdequate.{u, v, max (u + 1) (v + 1) w} L hL M
    (subsingleton_zExt_moduleExtension_of_finitePresentation_of_forall A M) i hi

/-- **Stacks Project, Tag 06ZI.** The higher right derived functors of the coreflection `Q` onto
the adequate module-valued functors vanish: `R^p Q(F) = 0` for every `p > 0` and every adequate
functor `F`. -/
@[stacks 06ZI "every degree p > 0 and every adequate F"]
theorem isZero_rightDerivedPlus_adequateCoreflection_of_isAdequate
    (F : ModuleValuedFunctor.{max (u + 1) (v + 1) w, v} A) (hF : IsAdequate (𝟭 _) F)
    (p : ℤ) (hp : 0 < p) :
    IsZero (((adequateCoreflection.{u, v, w} A).rightDerivedPlus p).obj F) :=
  isZero_rightDerivedPlus_adequateCoreflection.{u, v, w} A
    (subsingleton_zExt_moduleExtension_of_finitePresentation_of_forall A) F hF p hp

end AllDegrees

end AdequateFunctor

end
