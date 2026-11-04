module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of the shifted algebra

Let `R` be a sheaf of rings on a site `(C, J)` and let `A` be a sheaf of `ℤ`-graded `R`-algebras.
For an object `U` of the site and `k : ℤ`, the graded `A`-module `j_{U!} A_U[k]`, the extension by
zero of the degree-`k` shift of the restriction of `A` to `U`, is the free graded `A`-module on one
homogeneous generator of degree `k` supported on `U`: the free graded module on the sheaf of sets
represented by `U`, all of whose sections are declared to have degree `k`. A homomorphism
`j_{U!} A_U[k] ⟶ M` may carry the universal generator to any degree-`k` section of `M` over `U`,
and the modules `j_{U!} A_U[k]` jointly separate graded `A`-modules.

## Main definitions

* `Stacks.reprPresheaf U` is the presheaf of sets represented by `U`, with values lifted into a
  larger universe, and `Stacks.reprPresheafLift` the morphism out of it determined by a section
  over `U`.
* `Stacks.reprSheaf J U` is its sheafification, `Stacks.reprUnit` the canonical map to it, and
  `Stacks.reprSection J U` the image of `𝟙 U`: the universal section.
* `Stacks.reprSheafLift F x` is the morphism of sheaves of sets `reprSheaf J U ⟶ F` determined by a
  section `x` of `F` over `U`.
* `Stacks.constDegPre` and `Stacks.constDeg F k` regard a sheaf of sets as a sheaf of graded sets
  all of whose local sections have degree `k`.
* `Stacks.setSheaf M` is the sheaf of sets underlying a sheaf of modules.
* `SheafOfModules.degSection M k n V y` transports a degree-`k` section into degree `n` when the
  two degrees agree and is zero otherwise.
* `SheafOfModules.reprGradedSets J U k` is the sheaf represented by `U` with all sections in degree
  `k`, and `SheafOfModules.extByZero A U k` is `j_{U!} A_U[k]`: the free graded `A`-module on it.
* `SheafOfModules.extByZeroGen A U k` is the universal degree-`k` section of `j_{U!} A_U[k]` over
  `U`, `SheafOfModules.extByZeroFamily` the family of generators attached to a degree-`k` section
  of a graded module over `U`, and `SheafOfModules.extByZeroHom` the resulting homomorphism out of
  `j_{U!} A_U[k]`.

## Main results

* `Stacks.reprSheafLift_reprSection`: the sheaf represented by `U` corepresents evaluation at `U`,
  i.e. the lift of `x` carries the universal section to `x`.
* `Stacks.constDeg_hasDegree`: every local section of `constDeg F k` has degree `k`.
* `SheafOfModules.extByZeroHom_gen`: the homomorphism `j_{U!} A_U[k] ⟶ M` attached to a degree-`k`
  section `x` of `M` over `U` carries the universal generator to `x`.
* `SheafOfModules.gradedModule_hom_ext_of_extByZero`: the objects `j_{U!} A_U[k]` jointly separate
  graded modules.

## References

* [Stacks Project, Tag 0FRD](https://stacks.math.columbia.edu/tag/0FRD)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w a t v u

namespace Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### The presheaf and the sheaf represented by an object -/

/-- The presheaf of sets represented by an object `U`, with values lifted. -/
def reprPresheaf (U : C) : Cᵒᵖ ⥤ Type max v w :=
  yoneda.obj U ⋙ uliftFunctor.{w, v}

/-- The value of `reprPresheaf U` at `V` is the lifted type of morphisms `V ⟶ U`. -/
theorem reprPresheaf_obj (U : C) (V : Cᵒᵖ) :
    (reprPresheaf.{w} U).obj V = ULift.{w} (V.unop ⟶ U) := rfl

/-- The morphism out of `reprPresheaf U` determined by a section over `U`: the Yoneda map, which
sends `f : V ⟶ U` to the restriction of the section along `f`. -/
def reprPresheafLift (P : Cᵒᵖ ⥤ Type max v w) {U : C} (x : P.obj (Opposite.op U)) :
    reprPresheaf.{w} U ⟶ P where
  app _ := TypeCat.ofHom fun f ↦ P.map (Quiver.Hom.op f.down) x
  naturality _ _ g :=
    ConcreteCategory.hom_ext _ _ fun f ↦ P.map_comp_apply (Quiver.Hom.op f.down) g x

/-- `reprPresheafLift P x` sends `f : V ⟶ U` to the restriction of `x` along `f`. -/
theorem reprPresheafLift_app (P : Cᵒᵖ ⥤ Type max v w) {U : C} (x : P.obj (Opposite.op U))
    (V : Cᵒᵖ) (f : ULift.{w} (V.unop ⟶ U)) :
    (reprPresheafLift.{w} P x).app V f = P.map (Quiver.Hom.op f.down) x := rfl

/-- `reprPresheafLift P x` sends `𝟙 U` to `x`. -/
theorem reprPresheafLift_id (P : Cᵒᵖ ⥤ Type max v w) {U : C} (x : P.obj (Opposite.op U)) :
    (reprPresheafLift.{w} P x).app (Opposite.op U) (ULift.up (𝟙 U)) = x :=
  P.map_id_apply (Opposite.op U) x

section Repr

variable (J) [HasWeakSheafify J (Type max v w)]

/-- The sheaf of sets represented by `U`: the sheafification of `reprPresheaf U`. -/
noncomputable def reprSheaf (U : C) : Sheaf J (Type max v w) :=
  (presheafToSheaf J (Type max v w)).obj (reprPresheaf.{w} U)

/-- The canonical map from the representable presheaf to the representable sheaf. -/
noncomputable def reprUnit (U : C) : reprPresheaf.{w} U ⟶ (reprSheaf.{w} J U).obj :=
  CategoryTheory.toSheafify J (reprPresheaf.{w} U)

/-- The universal section of the representable sheaf, over `U` itself: the image of `𝟙 U`. -/
noncomputable def reprSection (U : C) : (reprSheaf.{w} J U).obj.obj (Opposite.op U) :=
  (reprUnit.{w} J U).app (Opposite.op U) (ULift.up (𝟙 U))

variable {J}

/-- The morphism of sheaves of sets out of `reprSheaf J U` determined by a section over `U`. -/
noncomputable def reprSheafLift (F : Sheaf J (Type max v w)) {U : C}
    (x : F.obj.obj (Opposite.op U)) : reprSheaf.{w} J U ⟶ F :=
  ⟨CategoryTheory.sheafifyLift J (reprPresheafLift.{w} F.obj x) F.property⟩

/-- `reprSheafLift F x` sends the image of `f : V ⟶ U` under the unit to the restriction of `x`
along `f`. -/
theorem reprSheafLift_reprUnit (F : Sheaf J (Type max v w)) {U : C}
    (x : F.obj.obj (Opposite.op U)) (V : Cᵒᵖ) (f : ULift.{w} (V.unop ⟶ U)) :
    (reprSheafLift.{w} F x).hom.app V ((reprUnit.{w} J U).app V f) =
      F.obj.map (Quiver.Hom.op f.down) x :=
  congrArg (fun φ : reprPresheaf.{w} U ⟶ F.obj ↦ φ.app V f)
    (CategoryTheory.toSheafify_sheafifyLift J (reprPresheafLift.{w} F.obj x) F.property)

/-- The representable sheaf corepresents evaluation: the lift of a section `x` of `F` over `U`
sends the universal section to `x`. -/
theorem reprSheafLift_reprSection (F : Sheaf J (Type max v w)) {U : C}
    (x : F.obj.obj (Opposite.op U)) :
    (reprSheafLift.{w} F x).hom.app (Opposite.op U) (reprSection.{w} J U) = x :=
  (reprSheafLift_reprUnit.{w} F x (Opposite.op U) (ULift.up (𝟙 U))).trans
    (F.obj.map_id_apply (Opposite.op U) x)

end Repr

/-! ### Sheaves of graded sets concentrated in one degree -/

section ConstDeg

universe m

variable [HasWeakSheafify J (Type m)]

/-- The constant map from a sheaf of sets to the constant presheaf at `ULift ℤ`. -/
def constDegPre (F : Sheaf J (Type m)) (k : ℤ) :
    F.obj ⟶ (Functor.const Cᵒᵖ).obj (ULift.{m} ℤ) where
  app _ := TypeCat.ofHom fun _ ↦ ⟨k⟩
  naturality _ _ _ := rfl

/-- A sheaf of sets regarded as a sheaf of graded sets all of whose sections have degree `k`. -/
noncomputable def constDeg (F : Sheaf J (Type m)) (k : ℤ) : SheafOfGradedSets.{m} J where
  sheaf := F
  degree := ⟨constDegPre F k ≫ CategoryTheory.toSheafify J _⟩

/-- The underlying sheaf of sets of `constDeg F k` is `F`. -/
theorem constDeg_sheaf (F : Sheaf J (Type m)) (k : ℤ) : (constDeg F k).sheaf = F := rfl

/-- Every local section of `constDeg F k` has degree `k`. -/
theorem constDeg_hasDegree (F : Sheaf J (Type m)) (k : ℤ) (V : Cᵒᵖ) (s : F.obj.obj V) :
    (constDeg F k).HasDegree V s k :=
  rfl

end ConstDeg

/-! ### The sheaf of sets underlying a sheaf of modules -/

section SetSheaf

universe m

variable {R : Sheaf J RingCat.{t}}

/-- The sheaf of sets underlying a sheaf of modules. -/
noncomputable def setSheaf (M : SheafOfModules.{m} R) : Sheaf J (Type m) :=
  (sheafCompose J (forget AddCommGrpCat.{m})).obj ⟨M.val.presheaf, M.isSheaf⟩

/-- The sections of `setSheaf M` over `V` are the sections of `M` over `V`. -/
theorem setSheaf_obj_obj (M : SheafOfModules.{m} R) (V : Cᵒᵖ) :
    (setSheaf M).obj.obj V = M.val.obj V := rfl

/-- The restriction maps of `setSheaf M` are those of `M`. -/
theorem setSheaf_obj_map (M : SheafOfModules.{m} R) {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) :
    (setSheaf M).obj.map f x = M.val.map f x := rfl

end SetSheaf

end Stacks

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Transporting a section into another degree -/

section DegSection

universe m

/-- A section of `M.piece k` over `V`, transported into degree `n` when `n = k` and replaced by
zero otherwise. -/
noncomputable def degSection {A : GradedAlgebra.{t, a} R} (M : GradedModule.{t, a, m} A)
    (k n : ℤ) (V : Cᵒᵖ) (y : (M.piece k).val.obj V) : (M.piece n).val.obj V :=
  if h : k = n then castHom M.piece h V y else 0

/-- Transporting a degree-`k` section into degree `k` does nothing. -/
theorem degSection_self {A : GradedAlgebra.{t, a} R} (M : GradedModule.{t, a, m} A)
    (k : ℤ) (V : Cᵒᵖ) (y : (M.piece k).val.obj V) : degSection M k k V y = y := by
  simp [degSection, castHom_rfl]

/-- `degSection` commutes with restriction. -/
theorem degSection_naturality {A : GradedAlgebra.{t, a} R} (M : GradedModule.{t, a, m} A)
    (k n : ℤ) {V V' : Cᵒᵖ} (f : V ⟶ V') (y : (M.piece k).val.obj V) :
    (M.piece n).val.map f (degSection M k n V y) =
      degSection M k n V' ((M.piece k).val.map f y) := by
  by_cases h : k = n
  · subst h
    rw [degSection_self]
    exact (degSection_self M k V' _).symm
  · simp only [degSection, h, reduceDIte, map_zero]
    rfl

end DegSection

/-! ### `j_{U!} A_U[k]` and its universal property -/

section ExtByZero

variable [HasWeakSheafify J (Type max u v a w)]
  [HasWeakSheafify J AddCommGrpCat.{max u v a w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v a w}]

/-- The sheaf represented by `U`, regarded as a sheaf of graded sets all of whose local sections
have degree `k`. -/
noncomputable def reprGradedSets (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type max u v w)] (U : C) (k : ℤ) :
    Stacks.SheafOfGradedSets.{max u v w} J :=
  Stacks.constDeg (Stacks.reprSheaf.{max u w} J U) k

/-- The extension by zero of the degree-`k` shift of the algebra, `j_{U!} A_U[k]`: the free graded
`A`-module on one homogeneous generator of degree `k` supported on `U`. -/
noncomputable def extByZero (A : GradedAlgebra.{t, a} R) (U : C) (k : ℤ) :
    GradedModule.{t, a, max u v a w} A :=
  freeGradedModule A (reprGradedSets.{max a w} J U k)

/-- The universal degree-`k` section of `j_{U!} A_U[k]` over `U`. -/
noncomputable def extByZeroGen (A : GradedAlgebra.{t, a} R) (U : C) (k : ℤ) :
    ((extByZero.{w} A U k).piece k).val.obj (Opposite.op U) :=
  freeGeneratorSection A (reprGradedSets.{max a w} J U k) k (Opposite.op U)
    (Stacks.reprSection.{max u a w} J U) (Stacks.constDeg_hasDegree _ k _ _)

/-- The family of homogeneous generators attached to a single degree-`k` section `x` of `M` over
`U`: the generator of a local section `s` of the representable sheaf is the image of `x` under the
morphism of sheaves of sets that `s` names. -/
noncomputable def extByZeroFamily (A : GradedAlgebra.{t, a} R)
    (M : GradedModule.{t, a, max u v a w} A) (U : C) (k : ℤ)
    (x : (M.piece k).val.obj (Opposite.op U)) :
    GradedGeneratorFamily (reprGradedSets.{max a w} J U k) M where
  app n V s _ :=
    degSection M k n V
      ((Stacks.reprSheafLift.{max u a w} (Stacks.setSheaf (M.piece k)) x).hom.app V s)
  naturality n {_V V'} f s _ _ :=
    (degSection_naturality M k n f _).trans
      (congrArg (fun z ↦ degSection M k n V' z)
        (NatTrans.naturality_apply
          (Stacks.reprSheafLift.{max u a w} (Stacks.setSheaf (M.piece k)) x).hom f s).symm)

/-- The homomorphism `j_{U!} A_U[k] ⟶ M` attached to a degree-`k` section of `M` over `U`. -/
noncomputable def extByZeroHom (A : GradedAlgebra.{t, a} R)
    (M : GradedModule.{t, a, max u v a w} A) (U : C) (k : ℤ)
    (x : (M.piece k).val.obj (Opposite.op U)) : extByZero.{w} A U k ⟶ M :=
  liftHom A (reprGradedSets.{max a w} J U k) M (extByZeroFamily.{w} A M U k x)

/-- The homomorphism `j_{U!} A_U[k] ⟶ M` attached to a degree-`k` section `x` of `M` over `U`
carries the universal generator to `x`. -/
theorem extByZeroHom_gen (A : GradedAlgebra.{t, a} R)
    (M : GradedModule.{t, a, max u v a w} A) (U : C) (k : ℤ)
    (x : (M.piece k).val.obj (Opposite.op U)) :
    ((extByZeroHom.{w} A M U k x).app k).val.app (Opposite.op U)
      (extByZeroGen.{w} A U k) = x :=
  (liftHom_generator A (reprGradedSets.{max a w} J U k) M (extByZeroFamily.{w} A M U k x) k
      (Opposite.op U) _ _).trans
    ((degSection_self M k (Opposite.op U) _).trans
      (Stacks.reprSheafLift_reprSection (Stacks.setSheaf (M.piece k)) x))

/-- The objects `j_{U!} A_U[k]` jointly separate graded modules: two homomorphisms of graded
modules which agree after composition with every homomorphism out of every `j_{U!} A_U[k]` are
equal. -/
theorem gradedModule_hom_ext_of_extByZero (A : GradedAlgebra.{t, a} R)
    {M N : GradedModule.{t, a, max u v a w} A} {f₁ f₂ : M ⟶ N}
    (h : ∀ (U : C) (k : ℤ) (g : extByZero.{w} A U k ⟶ M), g ≫ f₁ = g ≫ f₂) : f₁ = f₂ := by
  refine GradedModule.Hom.ext fun n ↦ ?_
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  have hg := congrArg
    (fun q : extByZero.{w} A V.unop n ⟶ N ↦ (q.app n).val.app V (extByZeroGen.{w} A V.unop n))
    (h V.unop n (extByZeroHom.{w} A M V.unop n x))
  change (f₁.app n).val.app V
      (((extByZeroHom.{w} A M V.unop n x).app n).val.app V (extByZeroGen.{w} A V.unop n)) =
    (f₂.app n).val.app V
      (((extByZeroHom.{w} A M V.unop n x).app n).val.app V (extByZeroGen.{w} A V.unop n)) at hg
  rwa [extByZeroHom_gen A M V.unop n x] at hg

end ExtByZero

end SheafOfModules
