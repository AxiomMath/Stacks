module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
import all StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multiplication by a global section of a tensor power, as a morphism of sheaves

Let `O` be a sheaf of commutative rings on a site with a terminal object and let `L` be an
invertible `O`-module in the sense of [Stacks, Tag 01CS], so that the integer tensor powers
`L^{⊗ n}` of [Stacks, Tag 01CU] are available. A global section `s` of `L^{⊗ n}` multiplies the
twist `F ⊗ L^{⊗ j}` of an arbitrary `O`-module `F` into the twist `F ⊗ L^{⊗ (n + j)}`. This
file packages that multiplication as a **morphism of sheaves**
`F ⊗ L^{⊗ j} ⟶ F ⊗ L^{⊗ (n + j)}` and proves the laws it satisfies: multiplying by the unit
section is the reindexing comparison, multiplying by a product of two sections is multiplying
by each in turn, and multiplication is additive in the multiplying section.

The underlying morphism of a *morphism* `O ⟶ L^{⊗ n}` is
`Stacks.SheafOfModules.twistActionHom`, built with the graded structures in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TwistSectionRing.lean`. The laws here are laws
about morphisms, so any additive functor out of the category of `O`-modules carries them along;
applying the right derived functors of sections turns them into the graded module structure on
`⨁_{j} H^p(U, F ⊗ L^{⊗ j})` in every cohomological degree `p`, which is done in
`StacksFrontier/AlgebraicGeometry/TwistedCohomologyLocalization/GradedModule.lean`.

## Main definitions

* `Stacks.SheafOfModules.TwistAction.actionOf`: multiplication by a global section of
  `L^{⊗ n}`, that is `Stacks.SheafOfModules.twistActionHom` applied to the morphism
  `O ⟶ L^{⊗ n}` the section determines.

## Main results

* `Stacks.SheafOfModules.TwistAction.actionOf_assoc`: **multiplying by a product of two
  sections is multiplying by each in turn**, up to the reindexing comparison that moves the
  bracketing of the three degrees.
* `Stacks.SheafOfModules.TwistAction.actionOf_one`: **multiplying by the unit section is the
  reindexing comparison** `L^{⊗ j} ≅ L^{⊗ (0 + j)}`.
* `Stacks.SheafOfModules.TwistAction.actionOf_add` and
  `Stacks.SheafOfModules.TwistAction.actionOf_zero`: multiplication by a global section is
  additive in that section.
* `Stacks.SheafOfModules.TwistAction.actionOf_sectionRingMul`: the associativity law for a
  product taken in the graded section ring, which is graded by the natural numbers while the
  twists are indexed by the integers.
* `Stacks.SheafOfModules.TwistAction.actionOf_app_top`: the morphism of multiplication by a
  global section acts on global sections as `Stacks.SheafOfModules.sectionModuleAction`, the
  action of [Stacks, Tag 01CV]. This identifies the action built here with that one, so
  the degree-`0` shadow of the cohomological module structure is the graded section module.

## Implementation notes

The laws are proved by evaluating both sides on sections, which is legitimate because a
morphism out of a sheaf tensor product is determined by its values on the sections determined
by pairs of sections. The structural isomorphisms of the sheaf tensor product are not the
constraints of a monoidal category instance, so no coherence theorem applies to them; what is
available instead are their formulas on sections,
`Stacks.SheafOfModules.tensorSections_associatorAt` and its companions.

`Stacks.SheafOfModules.TwistAction.twistActionHom_congr` is what makes the section-level laws
follow from the morphism-level ones: a morphism out of the structure sheaf is determined by its
value on the unit section over the terminal object, because its value over any other object is
the restriction of that one. It is therefore enough to compare values at the terminal object,
and no uniqueness statement about the morphism is needed.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped DirectSum TensorProduct

universe v u w

namespace Stacks.SheafOfModules.TwistAction

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasTerminal C]
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### Multiplication by a global section -/

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The value of a morphism out of the structure sheaf on the unit section over any object is
the restriction of its value over the terminal object.** The unit section restricts to the unit
section, so this is naturality of the morphism. -/
theorem unitHom_app_eq_map
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (f : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶ M) (U : Cᵒᵖ) :
    f.val.app U (1 : O.obj U) =
      M.val.map (terminal.from U.unop).op (f.val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C)))) :=
  (PresheafOfModules.sections_property (M.val.unitHomEquiv f.val) (terminal.from U.unop).op).symm

/-- **Multiplication by a global section of `L^{⊗ n}` depends only on that section.** -/
theorem twistActionHom_congr
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ)
    {s s' : SheafOfModules.unit (TensorSheafification.structureSheaf O hO) ⟶
      TensorPower.tensorPower O hO L n}
    (h : s.val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C))) =
      s'.val.app (op (⊤_ C)) (1 : O.obj (op (⊤_ C)))) :
    twistActionHom O hO L F n j s = twistActionHom O hO L F n j s' := by
  apply tensorSheaf_hom_ext O hO
  intro U x y
  rw [twistActionHom_pure, twistActionHom_pure]
  rw [unitHom_app_eq_map O hO _ s U, unitHom_app_eq_map O hO _ s' U, h]

/-- **Multiplication of the twist `F ⊗ L^{⊗ j}` by a global section of `L^{⊗ n}`**, as a
morphism of sheaves of modules. -/
def actionOf
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C))) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (F)).obj ((TensorPower.tensorPower O hO L j))) ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (F)).obj ((TensorPower.tensorPower O hO L (n + j)))) :=
  twistActionHom O hO L F n j (globalSectionHom O hO _ s)

/-- **Multiplying by a product of two global sections is multiplying by each in turn**, up to
the reindexing comparison that moves the bracketing of the three degrees. -/
theorem actionOf_assoc
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m j : ℤ)
    (s : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L m).val.obj (op (⊤_ C))) :
    actionOf O hO L F (n + m) j (tensorPowerMulSectionAt O hO (op (⊤_ C)) L n m s t) =
      actionOf O hO L F m j t ≫ actionOf O hO L F n (m + j) s ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L (Int.add_assoc n m j).symm)).hom := by
  have hcongr : actionOf O hO L F (n + m) j (tensorPowerMulSectionAt O hO (op (⊤_ C)) L n m s t) =
      twistActionHom O hO L F (n + m) j
        (tensorPowerMulHom O hO L n m (globalSectionHom O hO _ s) (globalSectionHom O hO _ t)) := by
    refine twistActionHom_congr O hO L F (n + m) j ?_
    rw [globalSectionHom_apply, tensorPowerMulHom_apply, globalSectionHom_apply,
      globalSectionHom_apply]
  rw [hcongr, twistActionHom_assoc]
  rfl

/-- **Multiplying by the unit global section is the reindexing comparison.** -/
theorem actionOf_one
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (j : ℤ) :
    actionOf O hO L F 0 j (1 : O.obj (op (⊤_ C))) =
      (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (Int.zero_add j).symm)).hom := by
  have hcongr : actionOf O hO L F 0 j (1 : O.obj (op (⊤_ C))) =
      twistActionHom O hO L F 0 j (unitToPowerZero O hO L) := by
    refine twistActionHom_congr O hO L F 0 j ?_
    exact (globalSectionHom_apply O hO (TensorPower.tensorPower O hO L 0)
      (1 : O.obj (op (⊤_ C)))).trans rfl
  rw [hcongr, twistActionHom_one]

/-! ### Additivity of multiplication in the multiplying section -/

section Additivity

omit [HasTerminal C]

/-- The pairing of sections over an object is additive in its left argument. -/
theorem tensorSectionsAt_add_left (U : Cᵒᵖ)
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s s' : F.val.obj U) (t : G.val.obj U) :
    tensorSectionsAt O hO U F G (s + s') t =
      tensorSectionsAt O hO U F G s t + tensorSectionsAt O hO U F G s' t := by
  simp only [tensorSectionsAt, TensorProduct.add_tmul]
  exact map_add ((TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U).hom _ _

/-- The pairing of sections over an object is additive in its right argument. -/
theorem tensorSectionsAt_add_right (U : Cᵒᵖ)
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj U) (t t' : G.val.obj U) :
    tensorSectionsAt O hO U F G s (t + t') =
      tensorSectionsAt O hO U F G s t + tensorSectionsAt O hO U F G s t' := by
  simp only [tensorSectionsAt, TensorProduct.tmul_add]
  exact map_add ((TensorSheafification.toSheafify O hO (F.val ⊗ G.val)).app U).hom _ _

/-- Pairing with the zero section on the left gives the zero section. -/
theorem tensorSectionsAt_zero_left (U : Cᵒᵖ)
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (t : G.val.obj U) :
    tensorSectionsAt O hO U F G 0 t = 0 := by
  simp only [tensorSectionsAt, TensorProduct.zero_tmul]
  exact map_zero _

/-- Pairing with the zero section on the right gives the zero section. -/
theorem tensorSectionsAt_zero_right (U : Cᵒᵖ)
    (F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : F.val.obj U) :
    tensorSectionsAt O hO U F G s 0 = 0 := by
  simp only [tensorSectionsAt, TensorProduct.tmul_zero]
  exact map_zero _

/-- The product of sections of tensor powers is additive in its left argument. -/
theorem tensorPowerMulSectionAt_add_left (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ)
    (s s' : (TensorPower.tensorPower O hO L n).val.obj U)
    (t : (TensorPower.tensorPower O hO L m).val.obj U) :
    tensorPowerMulSectionAt O hO U L n m (s + s') t =
      tensorPowerMulSectionAt O hO U L n m s t + tensorPowerMulSectionAt O hO U L n m s' t := by
  unfold tensorPowerMulSectionAt
  rw [tensorSectionsAt_add_left]
  exact map_add _ _ _

/-- The product of sections of tensor powers vanishes on the zero section. -/
theorem tensorPowerMulSectionAt_zero_left (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℤ)
    (t : (TensorPower.tensorPower O hO L m).val.obj U) :
    tensorPowerMulSectionAt O hO U L n m 0 t = 0 := by
  unfold tensorPowerMulSectionAt
  rw [tensorSectionsAt_zero_left]
  exact map_zero _

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The value of a sum of two morphisms of sheaves of modules on a section is the sum of their
values. -/
theorem add_val_app
    {F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (φ ψ : F ⟶ G) (U : Cᵒᵖ) (z : F.val.obj U) :
    (φ + ψ).val.app U z = φ.val.app U z + ψ.val.app U z := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The value of the zero morphism of sheaves of modules on a section is zero. -/
theorem zero_val_app
    {F G : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO)}
    (U : Cᵒᵖ) (z : F.val.obj U) : (0 : F ⟶ G).val.app U z = 0 := rfl

end Additivity

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The value of `globalSectionHom` on the unit section over any object is the restriction of the
given global section. -/
theorem globalSectionHom_app
    (M : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (s : M.val.obj (op (⊤_ C))) (U : Cᵒᵖ) :
    (globalSectionHom O hO M s).val.app U (1 : O.obj U) =
      M.val.map (terminal.from U.unop).op s := by
  rw [unitHom_app_eq_map, globalSectionHom_apply]

/-- **Multiplication by a global section is additive in that section.** -/
theorem actionOf_add
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ)
    (s s' : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C))) :
    actionOf O hO L F n j (s + s') =
      actionOf O hO L F n j s + actionOf O hO L F n j s' := by
  apply tensorSheaf_hom_ext O hO
  intro U x y
  have e : ∀ a : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C)),
      (actionOf O hO L F n j a).val.app U
          (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L j) x y) =
        tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x
          (tensorPowerMulSectionAt O hO U L n j
            ((TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op a) y) := by
    intro a
    change (twistActionHom O hO L F n j (globalSectionHom O hO _ a)).val.app U _ = _
    rw [twistActionHom_pure, globalSectionHom_app]
  refine (e (s + s')).trans (Eq.trans ?_ ((congrArg₂ (· + ·) (e s).symm (e s').symm).trans
    (add_val_app O hO (actionOf O hO L F n j s) (actionOf O hO L F n j s') U
      (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L j) x y)).symm))
  have hm : (TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op (s + s') =
      (TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op s +
        (TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op s' :=
    map_add _ _ _
  refine Eq.trans (congrArg (fun z =>
    tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x
      (tensorPowerMulSectionAt O hO U L n j z y)) hm) ?_
  exact (congrArg (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x)
      (tensorPowerMulSectionAt_add_left O hO U L n j _ _ y)).trans
    (tensorSectionsAt_add_right O hO U F (TensorPower.tensorPower O hO L (n + j)) x _ _)

/-- **Multiplication by the zero global section is the zero morphism.** -/
theorem actionOf_zero
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n j : ℤ) :
    actionOf O hO L F n j (0 : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C))) = 0 := by
  apply tensorSheaf_hom_ext O hO
  intro U x y
  refine Eq.trans ?_ (zero_val_app O hO U
    (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L j) x y)).symm
  change (twistActionHom O hO L F n j (globalSectionHom O hO _
    (0 : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C))))).val.app U _ = 0
  rw [twistActionHom_pure, globalSectionHom_app]
  have hm : (TensorPower.tensorPower O hO L n).val.map (terminal.from U.unop).op
      (0 : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C))) = 0 := map_zero _
  refine Eq.trans (congrArg (fun z =>
    tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x
      (tensorPowerMulSectionAt O hO U L n j z y)) hm) ?_
  refine (congrArg (tensorSectionsAt O hO U F (TensorPower.tensorPower O hO L (n + j)) x)
      (tensorPowerMulSectionAt_zero_left O hO U L n j y)).trans ?_
  exact tensorSectionsAt_zero_right O hO U F (TensorPower.tensorPower O hO L (n + j)) x

/-! ### Degree bookkeeping for the graded section ring -/

omit [HasTerminal C] in
/-- The reindexing comparison of tensor powers, tensored with `F`, acts on sections as
transport along the equality of exponents. -/
theorem reindexTensorAt (U : Cᵒᵖ)
    (F L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {i j : ℤ} (h : i = j)
    (x : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F)).obj ((TensorPower.tensorPower O hO L i)))).val.obj U) :
    ((Invertible.tensorProductIso O hO (Iso.refl F)
      (TensorPower.tensorPowerReindex O hO L h)).hom.val.app U) x =
        Eq.mp (congrArg (fun k => ↑(
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              (F)).obj ((TensorPower.tensorPower O hO L k)))).val.obj
            U) ) h) x := by
  cases h
  simp [Invertible.tensorProductIso, Invertible.tensorProductBifunctor,
    TensorPower.tensorPowerReindex]
  rfl

omit [HasTerminal C] in
/-- The reindexing comparison along an equality of an exponent with itself is the identity: any
proof of such an equality is the reflexivity proof. -/
theorem reindexAt_self (U : Cᵒᵖ)
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {i : ℤ} (h : i = i)
    (x : (TensorPower.tensorPower O hO L i).val.obj U) :
    (TensorPower.tensorPowerReindex O hO L h).hom.val.app U x = x := rfl

omit [HasTerminal C] in
/-- The reindexing comparison along an equality of an exponent with itself, tensored with `F`,
is the identity morphism. -/
theorem tensorProductIso_reindex_hom_of_eq
    (F L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {i : ℤ} (h : i = i) :
    (Invertible.tensorProductIso O hO (Iso.refl F)
      (TensorPower.tensorPowerReindex O hO L h)).hom =
      𝟙 ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (F)).obj ((TensorPower.tensorPower O hO L i)))) :=
  (Invertible.tensorProductBifunctor O hO).map_id _

omit [HasTerminal C] in
/-- Two reindexing comparisons of twists compose to the comparison along the composed
equality. -/
theorem reindexTwist_comp
    (F L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {a b c : ℤ} (h₁ : a = b) (h₂ : b = c) :
    (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L h₁)).hom ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L h₂)).hom =
      (Invertible.tensorProductIso O hO (Iso.refl F)
        (TensorPower.tensorPowerReindex O hO L (h₁.trans h₂))).hom := by
  subst h₁
  subst h₂
  rw [tensorProductIso_reindex_hom_of_eq, Category.comp_id]

/-- **Multiplication by a reindexed global section** is multiplication by the section followed by
the reindexing comparison of the twists. -/
theorem actionOf_reindex
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] {n n' : ℤ} (hn : n = n') (j : ℤ) (hj : n + j = n' + j)
    (s : (TensorPower.tensorPower O hO L n).val.obj (op (⊤_ C))) :
    actionOf O hO L F n' j
        ((TensorPower.tensorPowerReindex O hO L hn).hom.val.app (op (⊤_ C)) s) =
      actionOf O hO L F n j s ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L hj)).hom := by
  subst hn
  rw [reindexAt_self, tensorProductIso_reindex_hom_of_eq, Category.comp_id]

/-- The product of two homogeneous global sections in the graded section ring is the product of
tensor powers, reindexed from the integer sum of the degrees to the cast of their natural-number
sum. -/
theorem sectionRingMul_eq
    (L : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C))) :
    sectionRingMul O hO L n m s t =
      (TensorPower.tensorPowerReindex O hO L (Int.natCast_add n m).symm).hom.val.app
        (op (⊤_ C)) (tensorPowerMulSectionAt O hO (op (⊤_ C)) L (n : ℤ) (m : ℤ) s t) := rfl

/-- **Multiplying by a product in the graded section ring is multiplying by each factor in
turn**, up to the reindexing comparison between the two spellings of the total degree. This is
the form in which the coherence enters the graded module structure, whose ring is graded by the
natural numbers while the twists are indexed by the integers. -/
@[ega "0 5.4.6" "partial"]
theorem actionOf_sectionRingMul
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n m : ℕ) (j : ℤ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : (TensorPower.tensorPower O hO L (m : ℤ)).val.obj (op (⊤_ C)))
    (h : (n : ℤ) + ((m : ℤ) + j) = ((n + m : ℕ) : ℤ) + j) :
    actionOf O hO L F ((n + m : ℕ) : ℤ) j (sectionRingMul O hO L n m s t) =
      actionOf O hO L F (m : ℤ) j t ≫ actionOf O hO L F (n : ℤ) ((m : ℤ) + j) s ≫
        (Invertible.tensorProductIso O hO (Iso.refl F)
          (TensorPower.tensorPowerReindex O hO L h)).hom := by
  rw [sectionRingMul_eq, actionOf_reindex O hO L F (Int.natCast_add n m).symm j
      (show (n : ℤ) + (m : ℤ) + j = ((n + m : ℕ) : ℤ) + j by push_cast; ring),
    actionOf_assoc, Category.assoc, Category.assoc, reindexTwist_comp]

/-- **The morphism of multiplication by a global section acts on global sections as the graded
module action of [Stacks, Tag 01CV].** This identifies the action built here with that
one, in the degrees where the latter is defined. -/
theorem actionOf_app_top
    (L F : SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℕ) (j : ℤ)
    (s : (TensorPower.tensorPower O hO L (n : ℤ)).val.obj (op (⊤_ C)))
    (t : ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        (F)).obj ((TensorPower.tensorPower O hO L j)))).val.obj (op (⊤_ C))) :
    (actionOf O hO L F (n : ℤ) j s).val.app (op (⊤_ C)) t =
      sectionModuleAction O hO L F n j s t :=
  (twistActionHom_apply O hO L F (n : ℤ) j (globalSectionHom O hO _ s) t).trans
    (congrArg (fun z => twistActionSection O hO L F (n : ℤ) j z t)
      (globalSectionHom_apply O hO _ s))

end Stacks.SheafOfModules.TwistAction

end
