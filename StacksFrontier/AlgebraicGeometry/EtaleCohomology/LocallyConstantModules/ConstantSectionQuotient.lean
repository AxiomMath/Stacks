module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Separating the value of a constant sheaf of modules

Let `J` be a Grothendieck topology on a category `C` with a final object `T` and let `R` be a ring.
The constant sheaf functor on `R`-modules is left adjoint to sections over `T`
(`CategoryTheory.constantSheafAdj`), and the unit of that adjunction is the map `B ⟶ B̲(T)` sending
an element of `B` to the corresponding constant section. That map need not be injective: over a
site in which the empty sieve is covering every sheaf is zero, and in general nothing identifies
`B` with a submodule of `B̲(T)`.

What *is* true is that the kernel `N` of the unit is invisible to the constant sheaf functor. A
homomorphism from `B` to the sections of any sheaf over `T` factors through the unit, hence kills
`N`, so `B` and `B/N` corepresent the same functor and `B̲ ⟶ (B/N)̲` is an isomorphism. Replacing
`B` by `B/N` therefore changes nothing about the sheaf `B̲` and makes the unit injective.

This is the `ModuleCat` form of the device of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantAbelian.ConstantSectionQuotient`,
and it plays the same role: it replaces the hypothesis
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, under which injectivity of the unit
follows from local injectivity of the sheafification map, but which is available for
`ModuleCat.{w} R` only when the carrier universe `w` is the universe `max u v` fixed by the site.

## Main results

* `Stacks.ConstantSheaf.constantSheafUnitKernelModule` — the kernel of `B ⟶ B̲(T)`.
* `Stacks.ConstantSheaf.constantQuotientModule` and
  `Stacks.ConstantSheaf.constantQuotientModuleMk` — the quotient of `B` by that kernel, and the
  projection onto it.
* `Stacks.ConstantSheaf.constantSheafUnitKernelModule_le_ker` — every homomorphism from `B` to the
  sections of a sheaf over `T` kills that kernel.
* `Stacks.ConstantSheaf.isIso_constantSheaf_map_constantQuotientModuleMk` — the constant sheaf
  functor carries the projection to an isomorphism.
* `Stacks.ConstantSheaf.injective_constantSection_constantQuotientModule` — the constant section
  map of the quotient is injective.

## References

* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w r v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Type r} [Ring R]
  [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The unit of the constant sheaf adjunction on modules is the sheafification map of the constant
presheaf, evaluated at the final object. -/
lemma constantSheafAdjModule_unit_app {T : C} (hT : IsTerminal T) (B : ModuleCat.{w} R) :
    (constantSheafAdj J (ModuleCat.{w} R) hT).unit.app B =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T) := by
  simp only [constantSheafAdj, Adjunction.comp_unit_app]
  exact Category.id_comp _

/-- The submodule of elements of `B` whose constant section over `T` vanishes. -/
def constantSheafUnitKernelModule (T : C) (B : ModuleCat.{w} R) : Submodule R B :=
  LinearMap.ker ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T)).hom

/-- The quotient of `B` by the elements whose constant section over `T` vanishes. -/
def constantQuotientModule (T : C) (B : ModuleCat.{w} R) : ModuleCat.{w} R :=
  ModuleCat.of R (B ⧸ constantSheafUnitKernelModule J T B)

/-- The projection of `B` onto `Stacks.ConstantSheaf.constantQuotientModule`. -/
def constantQuotientModuleMk (T : C) (B : ModuleCat.{w} R) :
    B ⟶ constantQuotientModule J T B :=
  ModuleCat.ofHom (constantSheafUnitKernelModule J T B).mkQ

/-- The constant section map of `B` over `T`, read on the quotient by its kernel. -/
def constantQuotientModuleSection (T : C) (B : ModuleCat.{w} R) :
    constantQuotientModule J T B ⟶ ((sheafSections J (ModuleCat.{w} R)).obj (op T)).obj
      ((constantSheaf J (ModuleCat.{w} R)).obj B) :=
  ModuleCat.ofHom ((constantSheafUnitKernelModule J T B).liftQ
    ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T)).hom le_rfl)

/-- The projection followed by the descended section map is the constant section map. -/
lemma constantQuotientModuleMk_comp_constantQuotientModuleSection (T : C) (B : ModuleCat.{w} R) :
    constantQuotientModuleMk J T B ≫ constantQuotientModuleSection J T B =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T) := by
  ext _
  rfl

/-- The descended section map is injective: the quotient was taken by its kernel. -/
lemma injective_constantQuotientModuleSection (T : C) (B : ModuleCat.{w} R) :
    Function.Injective (constantQuotientModuleSection J T B) := by
  rw [← LinearMap.ker_eq_bot (f := (constantQuotientModuleSection J T B).hom)]
  exact Submodule.ker_liftQ_eq_bot' _ _ rfl

/-- The constant section map of the quotient, precomposed with the quotient's own section map,
is the constant section map of `B` read on the quotient. This is naturality of the sheafification
map together with surjectivity of the projection. -/
lemma constantQuotientModuleSection_comp_map (T : C) (B : ModuleCat.{w} R) :
    constantQuotientModuleSection J T B ≫ ((sheafSections J (ModuleCat.{w} R)).obj (op T)).map
        ((constantSheaf J (ModuleCat.{w} R)).map (constantQuotientModuleMk J T B)) =
      (CategoryTheory.toSheafify J
        ((Functor.const Cᵒᵖ).obj (constantQuotientModule J T B))).app (op T) := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ b =>
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (CategoryTheory.toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (constantQuotientModuleMk J T B))) (op T)) b).symm

section Terminal

variable {T : C} (hT : IsTerminal T) (B : ModuleCat.{w} R)

include hT in
/-- The identity of a constant sheaf of modules corresponds, under the constant sheaf adjunction,
to the constant section map. -/
lemma constantSheafAdjModule_homEquiv_id :
    (constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv B
        ((constantSheaf J (ModuleCat.{w} R)).obj B) (𝟙 _) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op T) := by
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (constantSheafAdjModule_unit_app J hT B)

include hT in
/-- A homomorphism from `B` to the sections of a sheaf over the final object annihilates the
kernel of the constant section map: by the constant sheaf adjunction it factors through that
map. -/
lemma constantSheafUnitKernelModule_le_ker (S : Sheaf J (ModuleCat.{w} R))
    (k : B ⟶ ((sheafSections J (ModuleCat.{w} R)).obj (op T)).obj S) :
    constantSheafUnitKernelModule J T B ≤ LinearMap.ker k.hom := by
  intro b hb
  have hk := (constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv_unit
    (f := ((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv B S).symm k)
  rw [Equiv.apply_symm_apply] at hk
  have hb' : ((constantSheafAdj J (ModuleCat.{w} R) hT).unit.app B) b = 0 := by
    rw [constantSheafAdjModule_unit_app J hT B]
    exact hb
  change k b = 0
  rw [ConcreteCategory.congr_hom hk b, ConcreteCategory.comp_apply, hb', map_zero]

include hT in
/-- **The quotient does not change the constant sheaf.** The constant sheaf functor carries the
projection `B ⟶ B/N`, with `N` the kernel of the constant section map over the final object, to an
isomorphism: by the constant sheaf adjunction both `B` and `B/N` corepresent sections over the
final object, because every homomorphism from `B` to such sections kills `N`. -/
lemma isIso_constantSheaf_map_constantQuotientModuleMk :
    IsIso ((constantSheaf J (ModuleCat.{w} R)).map (constantQuotientModuleMk J T B)) := by
  refine ⟨((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv _ _).symm
    (constantQuotientModuleSection J T B), ?_, ?_⟩
  · rw [← Adjunction.homEquiv_naturality_left_symm,
      constantQuotientModuleMk_comp_constantQuotientModuleSection J T B,
      ← constantSheafAdjModule_homEquiv_id J hT B, Equiv.symm_apply_apply]
  · apply ((constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      constantSheafAdjModule_homEquiv_id J hT (constantQuotientModule J T B),
      constantQuotientModuleSection_comp_map J T B]

include hT in
/-- **The constant section map of the quotient is injective.** -/
lemma injective_constantSection_constantQuotientModule :
    Function.Injective ((CategoryTheory.toSheafify J
      ((Functor.const Cᵒᵖ).obj (constantQuotientModule J T B))).app (op T)) := by
  have hiso := isIso_constantSheaf_map_constantQuotientModuleMk J hT B
  have hbij := ConcreteCategory.bijective_of_isIso
    (((sheafSections J (ModuleCat.{w} R)).obj (op T)).map
      ((constantSheaf J (ModuleCat.{w} R)).map (constantQuotientModuleMk J T B)))
  rw [← constantQuotientModuleSection_comp_map J T B]
  exact hbij.injective.comp (injective_constantQuotientModuleSection J T B)

end Terminal

end Stacks.ConstantSheaf

end
