module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality

/-!
# Transport of a sheaf of differential graded modules along a monoidal functor

Let `L : SheafOfModules R ⥤ SheafOfModules S` be an additive **lax** monoidal functor for the
tensor product of Tag 01CA, let `A` be a sheaf of differential graded `R`-algebras and let `M`
be a right differential graded `A`-module. Then `L` carries `M` to a right differential graded
module over the sheaf of differential graded algebras
`SheafOfModules.DifferentialGradedAlgebra.transport L A`: the underlying cochain complex is `L`
applied degreewise, and the action in degrees `n` and `i` is the action of `M`, conjugated by
the tensorator,

`L(M_n) ⊗ L(A_i) ⟶ L(M_n ⊗ A_i) ⟶ L(M_{n+i})`.

This is functorial in `M`. For a morphism of ringed topoi `(f, f♯)` and `L = f^*` it is the
pullback of right differential graded modules; for `L = f_*`, which is lax monoidal and not
strong, it is the **direct image**.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.smulSheaf`: the **morphism-level right action**
  `M_n ⊗ A_i ⟶ M_{n+i}` of a right differential graded module.
* `SheafOfModules.DifferentialGradedModule.SmulSheafLeibniz`: the **morphism-level** signed
  Leibniz rule for a right action, with the degree-addition transports inserted.
* `SheafOfModules.DifferentialGradedModule.ofMorphismData`: a right differential graded module
  assembled from an action given as a family of **morphisms** satisfying associativity, the
  unit law and the Leibniz rule as equalities of morphisms.
* `SheafOfModules.DifferentialGradedModule.transportedSmul`: the action of `M` conjugated by
  the tensorator of `L`.
* `SheafOfModules.DifferentialGradedModule.transport`: **the right differential graded
  `transport L A`-module `L(M)`**, and
  `SheafOfModules.DifferentialGradedModule.transportHom` the image of a morphism.
* `SheafOfModules.DifferentialGradedModule.transportFunctor`: the induced functor from right
  differential graded `A`-modules to right differential graded `transport L A`-modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.smulSheaf_assoc` and `smulSheaf_mul_one`: the
  morphism-level associativity and unit law of the action of a right differential graded module.
* `SheafOfModules.DifferentialGradedModule.smulSheafLeibniz_iff`: **the morphism-level signed
  Leibniz rule for an action holds if and only if the sectionwise one does**, and
  `smulSheafLeibniz_complex` is the instance of it carried by a right differential graded
  module.
* `SheafOfModules.DifferentialGradedModule.smulSheaf_comp_eq_iff`: **a degreewise family of
  morphisms of sheaves of modules commutes with the morphism-level actions if and only if it
  preserves products of a module section with a homogeneous algebra section.**
* `SheafOfModules.DifferentialGradedModule.transportedSmul_assoc`,
  `transportedSmul_mul_one` and `transportedSmulLeibniz`: the transported action is associative
  and unital and satisfies the Leibniz rule, as equalities of morphisms.
* `SheafOfModules.DifferentialGradedModule.smulSheaf_transport`: the morphism-level action of
  `L(M)` is the transported action, so a consumer never unfolds `transport`.

## Implementation notes

**Why the algebra enters only through morphisms and sections.** `ofMorphismData` takes the
multiplication and the unit of the algebra as an unconstrained morphism family `amul` and a
morphism `aone`, identified with the structure fields of `A` by two sectionwise hypotheses
`hamul` and `haone`. This is the discipline of `Stacks.MonoidalGraded.mapMul_leibniz`, and here
it is what keeps the transport free of any defeq fight: the multiplication of
`SheafOfModules.DifferentialGradedAlgebra.transport L A` is *defined* as the bilinear map read
off the transported multiplication, so both identifications are `rfl`, whereas rewriting with
`SheafOfModules.GradedAlgebra.mulSheaf_transport` underneath a whiskering is not.

**The three levels at which the axioms live.** The structure fields of
`SheafOfModules.DifferentialGradedModule` are `HEq`s and equalities between values of bilinear
maps at *arbitrary* local sections; a monoidal functor transports equalities of morphisms; and
an additive one transports sums and integer multiples of morphisms. The passage is the same as
one level up: the associativity and unit fields are read off morphism identities evaluated at
sheafification-unit images of pure tensors, and the Leibniz field is turned into an equality of
morphisms out of the tensor product sheaf (`smulSheafLeibniz_iff`), transported there by
`Stacks.MonoidalGraded.mapMul_leibniz`, and read back.

**No `rw` crosses the tensor-product boundary.** `(M ⊗ N).val.obj U` and
`(((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M).obj N).val.obj U` are definitionally
but not syntactically equal, so every step of the section-level computations is `Eq.trans` or
`congrArg`, and the extensionality principles are applied with their sheaf arguments passed
explicitly. This is the discipline of the imported files, recorded in their implementation
notes.

**Universes.** The two sites are independent, but the ring sheaves, the algebras and the
modules on both sides live in one universe `w`. That constraint is inherited from the monoidal
structure on sheaves of modules of Tag 01CA, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraFunctoriality`.

## References

* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI) — sheaves of
  differential graded modules and their homomorphisms.
* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG) — functoriality of
  sheaves of differential graded algebras for a morphism of ringed topoi.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

open scoped TensorProduct

universe v₁ v₂ u₁ u₂ w

namespace SheafOfModules.DifferentialGradedModule

/-! ### The right action of a differential graded module at morphism level -/

section Smul

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (M : DifferentialGradedModule.{w, w, w} A)

/-- **The right action in degrees `n` and `i`, `M_n ⊗ A_i ⟶ M_{n+i}`, as a morphism of sheaves
of modules out of the tensor product sheaf.** The action of a right differential graded module
is given on local sections, as a bilinear map; this is the morphism it descends to. -/
noncomputable def smulSheaf (n i : ℤ) :
    M.complex.X n ⊗ A.complex.X i ⟶ M.complex.X (n + i) :=
  tensorSheafDesc (PresheafOfModules.ofBilinear (M.mul n i))

/-- `smulSheaf M n i` sends the image of `x ⊗ₜ y` under the sheafification unit to the action
`M.mul n i` evaluated at `x` and `y`. -/
@[simp]
theorem smulSheaf_unit (n i : ℤ) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (smulSheaf M n i).val.app U
        ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
      (M.mul n i).app U x y :=
  (tensorSheafDesc_unit (PresheafOfModules.ofBilinear (M.mul n i)) U x y).trans
    (PresheafOfModules.ofBilinear_tmul (M.mul n i) U x y)

variable (hO : Presheaf.IsSheaf J
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO

/-- **The right action of a differential graded module is associative with the multiplication of
the algebra, as an equality of morphisms out of `M_n ⊗ A_i ⊗ A_j`.** -/
theorem smulSheaf_assoc (n i j : ℤ) :
    smulSheaf M n i ▷ A.complex.X j ≫ smulSheaf M (n + i) j =
      (α_ (M.complex.X n) (A.complex.X i) (A.complex.X j)).hom ≫
        M.complex.X n ◁ GradedAlgebra.mulSheaf A.toGradedAlgebra i j ≫
          smulSheaf M n (i + j) ≫ eqToHom (congrArg M.complex.X (add_assoc n i j).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext₂ (Osharp := Osharp) (F := M.complex.X n)
    (G := A.complex.X i) (H := A.complex.X j) (Q := M.complex.X (n + i + j)) fun U x y z ↦ ?_
  have hL : (smulSheaf M n i ▷ A.complex.X j ≫ smulSheaf M (n + i) j).val.app U
        ((tensorSheafUnit (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (M.complex.X
            n)).obj (A.complex.X i)) (A.complex.X j)).app U
          ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y) ⊗ₜ z)) =
      (M.mul (n + i) j).app U ((M.mul n i).app U x y) z :=
    (congrArg ((smulSheaf M (n + i) j).val.app U)
        ((Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit Osharp hO U
            (smulSheaf M n i) (A.complex.X j)
            ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) z).trans
          (congrArg (fun t ↦ (tensorSheafUnit (M.complex.X (n + i)) (A.complex.X j)).app U
              (t ⊗ₜ z))
            (smulSheaf_unit M n i U x y)))).trans
      (smulSheaf_unit M (n + i) j U ((M.mul n i).app U x y) z)
  have h2 : (M.complex.X n ◁ GradedAlgebra.mulSheaf A.toGradedAlgebra i j).val.app U
        ((tensorSheafUnit (M.complex.X n) (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
            (A.complex.X i)).obj (A.complex.X j))).app U
          (x ⊗ₜ (tensorSheafUnit (A.complex.X i) (A.complex.X j)).app U (y ⊗ₜ z))) =
      (tensorSheafUnit (M.complex.X n) (A.complex.X (i + j))).app U
        (x ⊗ₜ (A.mul i j).app U y z) :=
    (Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO U
        (M.complex.X n) (GradedAlgebra.mulSheaf A.toGradedAlgebra i j) x
        ((tensorSheafUnit (A.complex.X i) (A.complex.X j)).app U (y ⊗ₜ z))).trans
      (congrArg (fun t ↦ (tensorSheafUnit (M.complex.X n) (A.complex.X (i + j))).app U (x ⊗ₜ t))
        (GradedAlgebra.mulSheaf_unit A.toGradedAlgebra i j U y z))
  have h4 : (M.mul (n + i) j).app U ((M.mul n i).app U x y) z =
      (eqToHom (congrArg M.complex.X (add_assoc n i j).symm)).val.app U
        ((M.mul n (i + j)).app U x ((A.mul i j).app U y z)) :=
    eq_of_heq ((M.mul_assoc n i j U x y z).trans
      (Stacks.TensorSheafWorld.heq_eqToHom_val_app M.complex.X (add_assoc n i j).symm U
        ((M.mul n (i + j)).app U x ((A.mul i j).app U y z))).symm)
  refine hL.trans (h4.trans ?_)
  refine congrArg ((eqToHom (congrArg M.complex.X (add_assoc n i j).symm)).val.app U) ?_
  exact ((smulSheaf_unit M n (i + j) U x ((A.mul i j).app U y z)).symm.trans
      (congrArg ((smulSheaf M n (i + j)).val.app U) h2.symm)).trans
    (congrArg (fun t ↦ (smulSheaf M n (i + j)).val.app U
      ((M.complex.X n ◁ GradedAlgebra.mulSheaf A.toGradedAlgebra i j).val.app U t))
      (Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit Osharp hO
        (M.complex.X n) (A.complex.X i) (A.complex.X j) U x y z).symm)

omit hO in
/-- Acting on a local section of `M_n` by the image of a scalar under the unit morphism of the
algebra is multiplication by that scalar, transported along `n + 0 = n`. -/
theorem smul_oneHom_right (n : ℤ) (U : Cᵒᵖ) (r : (toRingCat J Osharp).obj.obj U)
    (x : (M.complex.X n).val.obj U) :
    (M.mul n 0).app U x ((GradedAlgebra.oneHom A.toGradedAlgebra).val.app U r) =
      (eqToHom (congrArg M.complex.X (add_zero n).symm)).val.app U (r • x) :=
  (congrArg ((M.mul n 0).app U x) (GradedAlgebra.oneHom_val_app A.toGradedAlgebra U r)).trans
    (((M.mul n 0).map_smul_right U r x (A.one.eval U)).trans
      ((congrArg (r • ·) (eq_of_heq ((M.mul_one n U x).trans
        (Stacks.TensorSheafWorld.heq_eqToHom_val_app M.complex.X
          (add_zero n).symm U x).symm))).trans
        (((eqToHom (congrArg M.complex.X (add_zero n).symm)).val.app U).hom.map_smul r x).symm))

/-- **The unit of the algebra acts as the identity, as an equality of morphisms out of
`M_n ⊗ 𝟙_`.** -/
theorem smulSheaf_mul_one (n : ℤ) :
    M.complex.X n ◁ GradedAlgebra.oneHom A.toGradedAlgebra ≫ smulSheaf M n 0 =
      (ρ_ (M.complex.X n)).hom ≫ eqToHom (congrArg M.complex.X (add_zero n).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := M.complex.X n) (G := 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))
    (Q := M.complex.X (n + 0)) fun V y s ↦ ?_
  exact (congrArg ((smulSheaf M n 0).val.app V)
      (Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO V
        (M.complex.X n) (GradedAlgebra.oneHom A.toGradedAlgebra) y s)).trans
    ((smulSheaf_unit M n 0 V y ((GradedAlgebra.oneHom A.toGradedAlgebra).val.app V s)).trans
      ((smul_oneHom_right M n V s y).trans
        (congrArg ((eqToHom (congrArg M.complex.X (add_zero n).symm)).val.app V)
          (Stacks.TensorSheafWorld.rightUnitor_hom_val_app_tensorSheafUnit Osharp hO
            (M.complex.X n) V y s).symm)))

/-- The action of `N` after `φ ⊗ₘ 𝟙` on the image of `x ⊗ₜ y` under the sheafification unit is
the action of `N` at `φ x` and `y`. -/
private theorem tensorHom_id_smulSheaf_unit (N : DifferentialGradedModule.{w, w, w} A) (n m i : ℤ)
    (φ : M.complex.X n ⟶ N.complex.X m) (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    ((φ ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N m i).val.app U
        ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
      (N.mul m i).app U (φ.val.app U x) y :=
  (congrArg ((smulSheaf N m i).val.app U)
      (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
        φ (𝟙 (A.complex.X i)) x y)).trans
    (smulSheaf_unit N m i U (φ.val.app U x) y)

/-- **A degreewise family of morphisms of sheaves of modules commutes with the morphism-level
actions if and only if it preserves the action on local sections.** The right-hand side is the
`map_mul` field of `SheafOfModules.DifferentialGradedModule.Hom`; the left-hand side is the
form a monoidal functor transports. -/
theorem smulSheaf_comp_eq_iff (N : DifferentialGradedModule.{w, w, w} A)
    (φ : ∀ n : ℤ, M.complex.X n ⟶ N.complex.X n) (n i : ℤ) :
    smulSheaf M n i ≫ φ (n + i) = (φ n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N n i ↔
      ∀ (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U),
        (φ (n + i)).val.app U ((M.mul n i).app U x y) =
          (N.mul n i).app U ((φ n).val.app U x) y := by
  constructor
  · intro h U x y
    exact (congrArg ((φ (n + i)).val.app U) (smulSheaf_unit M n i U x y).symm).trans
      ((congrArg (fun ψ : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (M.complex.X
          n)).obj (A.complex.X i) ⟶ N.complex.X (n + i) ↦
            ψ.val.app U ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y))) h).trans
        (tensorHom_id_smulSheaf_unit M hO N n n i (φ n) U x y))
  · intro h
    refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := M.complex.X n)
      (G := A.complex.X i) (Q := N.complex.X (n + i)) fun U x y ↦ ?_
    exact (congrArg ((φ (n + i)).val.app U) (smulSheaf_unit M n i U x y)).trans
      ((h U x y).trans
        (tensorHom_id_smulSheaf_unit M hO N n n i (φ n) U x y).symm)

/-- **A degreewise family of morphisms of sheaves of modules lowering the degree by one
commutes with the morphism-level actions if and only if it preserves the action on local
sections.** The right-hand side is the `map_mul` field of
`SheafOfModules.DifferentialGradedModule.Homotopy`; the left-hand side is the form a monoidal
functor transports. The transport `eqToHom` identifies the two readings `(n + i) - 1` and
`(n - 1) + i` of the target degree. -/
theorem smulSheaf_comp_heq_iff (N : DifferentialGradedModule.{w, w, w} A)
    (φ : ∀ n : ℤ, M.complex.X n ⟶ N.complex.X (n - 1)) (n i : ℤ) :
    smulSheaf M n i ≫ φ (n + i) ≫
          eqToHom (congrArg N.complex.X (show n + i - 1 = n - 1 + i by omega)) =
        (φ n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N (n - 1) i ↔
      ∀ (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U),
        HEq ((φ (n + i)).val.app U ((M.mul n i).app U x y))
          ((N.mul (n - 1) i).app U ((φ n).val.app U x) y) := by
  have key : ∀ (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) (y : (A.complex.X i).val.obj U),
      ((smulSheaf M n i ≫ φ (n + i) ≫
            eqToHom (congrArg N.complex.X (show n + i - 1 = n - 1 + i by omega))).val.app U
          ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
        ((φ n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N (n - 1) i).val.app U
          ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y))) ↔
      HEq ((φ (n + i)).val.app U ((M.mul n i).app U x y))
        ((N.mul (n - 1) i).app U ((φ n).val.app U x) y) := by
    intro U x y
    have hL : (smulSheaf M n i ≫ φ (n + i) ≫
          eqToHom (congrArg N.complex.X (show n + i - 1 = n - 1 + i by omega))).val.app U
            ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
        (eqToHom (congrArg N.complex.X (show n + i - 1 = n - 1 + i by omega))).val.app U
          ((φ (n + i)).val.app U ((M.mul n i).app U x y)) :=
      congrArg (fun t ↦ (eqToHom (congrArg N.complex.X
          (show n + i - 1 = n - 1 + i by omega))).val.app U ((φ (n + i)).val.app U t))
        (smulSheaf_unit M n i U x y)
    have hR : ((φ n ⊗ₘ 𝟙 (A.complex.X i)) ≫ smulSheaf N (n - 1) i).val.app U
            ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
        (N.mul (n - 1) i).app U ((φ n).val.app U x) y :=
      tensorHom_id_smulSheaf_unit M hO N n (n - 1) i (φ n) U x y
    rw [hL, hR]
    exact ⟨fun h ↦ (Stacks.TensorSheafWorld.heq_eqToHom_val_app N.complex.X
        (show n + i - 1 = n - 1 + i by omega) U _).symm.trans (heq_of_eq h),
      fun h ↦ eq_of_heq ((Stacks.TensorSheafWorld.heq_eqToHom_val_app N.complex.X
        (show n + i - 1 = n - 1 + i by omega) U _).trans h)⟩
  exact ⟨fun h U x y ↦ (key U x y).mp (congrArg (fun ψ :
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (M.complex.X n)).obj (A.complex.X i) ⟶
        N.complex.X (n - 1 + i) ↦
      ψ.val.app U ((tensorSheafUnit (M.complex.X n) (A.complex.X i)).app U (x ⊗ₜ y))) h),
    fun h ↦ PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := M.complex.X n)
      (G := A.complex.X i) (Q := N.complex.X (n - 1 + i)) fun U x y ↦ (key U x y).mpr (h U x y)⟩

end Smul

/-! ### The morphism-level reading of the signed Leibniz rule for an action -/

section Leibniz

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (cpx : CochainComplex (SheafOfModules.{w} (toRingCat J Osharp)) ℤ)
  (act : ∀ n i : ℤ, (cpx.X n ⊗ A.complex.X i : SheafOfModules.{w} (toRingCat J Osharp)) ⟶
    cpx.X (n + i))
  (n i : ℤ)

/-- The bilinear map on local sections underlying a morphism-level right action:
`x, y ↦ act (η (x ⊗ₜ y))`, for `η` the sheafification unit. -/
noncomputable def bilinearOfAct : BilinearMap (cpx.X n) (A.complex.X i) (cpx.X (n + i)) :=
  PresheafOfModules.toBilinear (tensorSheafUnit (cpx.X n) (A.complex.X i) ≫ (act n i).val)

/-- `bilinearOfAct` on a pure tensor of local sections. -/
theorem bilinearOfAct_app (U : Cᵒᵖ) (x : (cpx.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (bilinearOfAct (A := A) cpx act n i).app U x y =
      (act n i).val.app U ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y)) :=
  rfl

/-- The first summand of the morphism-level Leibniz rule for an action: differentiate the
module factor. -/
noncomputable def leibnizLeft :
    (cpx.X n ⊗ A.complex.X i : SheafOfModules.{w} (toRingCat J Osharp)) ⟶ cpx.X (n + i + 1) :=
  (cpx.d n (n + 1) ⊗ₘ 𝟙 (A.complex.X i)) ≫ act (n + 1) i ≫
    eqToHom (congrArg cpx.X (add_right_comm n 1 i))

/-- The second summand of the morphism-level Leibniz rule for an action: differentiate the
algebra factor. -/
noncomputable def leibnizRight :
    (cpx.X n ⊗ A.complex.X i : SheafOfModules.{w} (toRingCat J Osharp)) ⟶ cpx.X (n + i + 1) :=
  (𝟙 (cpx.X n) ⊗ₘ A.complex.d i (i + 1)) ≫ act n (i + 1) ≫
    eqToHom (congrArg cpx.X (add_assoc n i 1).symm)

/-- **The morphism-level signed Leibniz rule** for a morphism-level right action: the
differential of a product is the product of the differentiated module factor with the algebra
factor, plus `(-1)^n` times the product of the module factor with the differentiated algebra
factor. -/
def SmulSheafLeibniz : Prop :=
  act n i ≫ cpx.d (n + i) (n + i + 1) =
    leibnizLeft (A := A) cpx act n i + (Int.negOnePow n : ℤ) • leibnizRight (A := A) cpx act n i

variable (hO : Presheaf.IsSheaf J
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO

/-- The first summand of the morphism-level Leibniz rule on a pure tensor of local sections. -/
theorem leibnizLeft_app (U : Cᵒᵖ) (x : (cpx.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (leibnizLeft (A := A) cpx act n i).val.app U
        ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
      gradedCast (fun q ↦ (cpx.X q).val.obj U) (add_right_comm n 1 i)
        ((bilinearOfAct (A := A) cpx act (n + 1) i).app U
          ((cpx.d n (n + 1)).val.app U x) y) :=
  (congrArg (fun z ↦ (eqToHom (congrArg cpx.X (add_right_comm n 1 i))).val.app U
        ((act (n + 1) i).val.app U z))
      (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
        (cpx.d n (n + 1)) (𝟙 (A.complex.X i)) x y)).trans
    (eqToHom_val_app cpx.X (add_right_comm n 1 i) U _)

/-- The second summand of the morphism-level Leibniz rule on a pure tensor of local sections. -/
theorem leibnizRight_app (U : Cᵒᵖ) (x : (cpx.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (leibnizRight (A := A) cpx act n i).val.app U
        ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
      gradedCast (fun q ↦ (cpx.X q).val.obj U) (add_assoc n i 1).symm
        ((bilinearOfAct (A := A) cpx act n (i + 1)).app U x
          ((A.complex.d i (i + 1)).val.app U y)) :=
  (congrArg (fun z ↦ (eqToHom (congrArg cpx.X (add_assoc n i 1).symm)).val.app U
        ((act n (i + 1)).val.app U z))
      (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
        (𝟙 (cpx.X n)) (A.complex.d i (i + 1)) x y)).trans
    (eqToHom_val_app cpx.X (add_assoc n i 1).symm U _)

/-- The right-hand side of the morphism-level Leibniz rule on a pure tensor of local
sections. -/
theorem leibnizSum_app (U : Cᵒᵖ) (x : (cpx.X n).val.obj U)
    (y : (A.complex.X i).val.obj U) :
    (leibnizLeft (A := A) cpx act n i +
          (Int.negOnePow n : ℤ) • leibnizRight (A := A) cpx act n i).val.app U
        ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
      gradedCast (fun q ↦ (cpx.X q).val.obj U) (add_right_comm n 1 i)
          ((bilinearOfAct (A := A) cpx act (n + 1) i).app U
            ((cpx.d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (cpx.X q).val.obj U) (add_assoc n i 1).symm
            ((bilinearOfAct (A := A) cpx act n (i + 1)).app U x
              ((A.complex.d i (i + 1)).val.app U y)) := by
  have hright : ((Int.negOnePow n : ℤ) • leibnizRight (A := A) cpx act n i).val.app U
      ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y)) =
        (Int.negOnePow n : ℤ) • gradedCast (fun q ↦ (cpx.X q).val.obj U)
          (add_assoc n i 1).symm ((bilinearOfAct (A := A) cpx act n (i + 1)).app U x
            ((A.complex.d i (i + 1)).val.app U y)) :=
    (zsmul_val_app _ _ U _).trans
      (congrArg (fun t ↦ (Int.negOnePow n : ℤ) • t) (leibnizRight_app cpx act n i hO U x y))
  exact (add_val_app _ _ U _).trans (by rw [leibnizLeft_app cpx act n i hO U x y, hright])

/-- **The morphism-level signed Leibniz rule for an action holds if and only if the sectionwise
one does.** The right-hand side is the `leibniz` field of
`SheafOfModules.DifferentialGradedModule` for the action `bilinearOfAct`; the left-hand side is
the form an additive lax monoidal functor transports. -/
theorem smulSheafLeibniz_iff :
    SmulSheafLeibniz (A := A) cpx act n i ↔
      ∀ (U : Cᵒᵖ) (x : (cpx.X n).val.obj U) (y : (A.complex.X i).val.obj U),
        (cpx.d (n + i) (n + i + 1)).val.app U
            ((bilinearOfAct (A := A) cpx act n i).app U x y) =
          gradedCast (fun q ↦ (cpx.X q).val.obj U) (add_right_comm n 1 i)
              ((bilinearOfAct (A := A) cpx act (n + 1) i).app U
                ((cpx.d n (n + 1)).val.app U x) y) +
            (Int.negOnePow n : ℤ) •
              gradedCast (fun q ↦ (cpx.X q).val.obj U) (add_assoc n i 1).symm
                ((bilinearOfAct (A := A) cpx act n (i + 1)).app U x
                  ((A.complex.d i (i + 1)).val.app U y)) :=
  ⟨fun h U x y ↦ (congrArg (fun φ : (cpx.X n ⊗ A.complex.X i :
        SheafOfModules.{w} (toRingCat J Osharp)) ⟶ cpx.X (n + i + 1) ↦
      φ.val.app U ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y))) h).trans
    (leibnizSum_app cpx act n i hO U x y),
  fun h ↦ PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := cpx.X n)
    (G := A.complex.X i) (Q := cpx.X (n + i + 1)) fun U x y ↦
      (h U x y).trans (leibnizSum_app cpx act n i hO U x y).symm⟩

end Leibniz

/-! ### The Leibniz rule of a right differential graded module at morphism level -/

section ModuleLeibniz

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (M : DifferentialGradedModule.{w, w, w} A)
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO

/-- The signed Leibniz rule of a right differential graded module, read at morphism level. -/
theorem smulSheafLeibniz_complex (n i : ℤ) :
    SmulSheafLeibniz (A := A) M.complex (smulSheaf M) n i := by
  refine (smulSheafLeibniz_iff M.complex (smulSheaf M) n i hO).mpr fun U x y ↦ ?_
  have e₁ : (bilinearOfAct (A := A) M.complex (smulSheaf M) n i).app U x y =
      (M.mul n i).app U x y := smulSheaf_unit M n i U x y
  have e₂ : (bilinearOfAct (A := A) M.complex (smulSheaf M) (n + 1) i).app U
        ((M.complex.d n (n + 1)).val.app U x) y =
      (M.mul (n + 1) i).app U ((M.complex.d n (n + 1)).val.app U x) y :=
    smulSheaf_unit M (n + 1) i U _ y
  have e₃ : (bilinearOfAct (A := A) M.complex (smulSheaf M) n (i + 1)).app U x
        ((A.complex.d i (i + 1)).val.app U y) =
      (M.mul n (i + 1)).app U x ((A.complex.d i (i + 1)).val.app U y) :=
    smulSheaf_unit M n (i + 1) U x _
  rw [e₁, e₂, e₃]
  exact M.leibniz n i U x y

end ModuleLeibniz

/-! ### A right differential graded module from morphism-level data -/

section OfMorphismData

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (cpx : CochainComplex (SheafOfModules.{w} (toRingCat J Osharp)) ℤ)
  (act : ∀ n i : ℤ, (cpx.X n ⊗ A.complex.X i : SheafOfModules.{w} (toRingCat J Osharp)) ⟶
    cpx.X (n + i))
  (amul : ∀ i j : ℤ, (A.complex.X i ⊗ A.complex.X j :
    SheafOfModules.{w} (toRingCat J Osharp)) ⟶ A.complex.X (i + j))
  (aone : 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⟶ A.complex.X 0)

include hO

/-- **A right differential graded module assembled from morphism-level data.** The action is
given as a family of morphisms of sheaves of modules and the three module axioms as equalities
of morphisms; the multiplication and the unit of the algebra enter as the unconstrained `amul`
and `aone`, identified with the structure fields of `A` on local sections. -/
noncomputable def ofMorphismData
    (hamul : ∀ (i j : ℤ) (U : Cᵒᵖ) (y : (A.complex.X i).val.obj U)
      (z : (A.complex.X j).val.obj U),
      (amul i j).val.app U
          ((tensorSheafUnit (A.complex.X i) (A.complex.X j)).app U (y ⊗ₜ z)) =
        (A.mul i j).app U y z)
    (haone : ∀ U : Cᵒᵖ,
      aone.val.app U (1 : (toRingCat J Osharp).obj.obj U) = A.one.eval U)
    (hassoc : ∀ n i j : ℤ, act n i ▷ A.complex.X j ≫ act (n + i) j =
      (α_ (cpx.X n) (A.complex.X i) (A.complex.X j)).hom ≫
        cpx.X n ◁ amul i j ≫ act n (i + j) ≫
          eqToHom (congrArg cpx.X (add_assoc n i j).symm))
    (hone : ∀ n : ℤ, cpx.X n ◁ aone ≫ act n 0 =
      (ρ_ (cpx.X n)).hom ≫ eqToHom (congrArg cpx.X (add_zero n).symm))
    (hleib : ∀ n i : ℤ, SmulSheafLeibniz (A := A) cpx act n i) :
    DifferentialGradedModule.{w, w, w} A where
  complex := cpx
  mul := bilinearOfAct (A := A) cpx act
  mul_assoc n i j U x y z := by
    have hL : (act n i ▷ A.complex.X j ≫ act (n + i) j).val.app U
          ((tensorSheafUnit (cpx.X n ⊗ A.complex.X i) (A.complex.X j)).app U
            ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y) ⊗ₜ z)) =
        (bilinearOfAct (A := A) cpx act (n + i) j).app U
          ((bilinearOfAct (A := A) cpx act n i).app U x y) z :=
      congrArg ((act (n + i) j).val.app U)
        (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit Osharp hO U
          (act n i) (A.complex.X j)
          ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y)) z)
    have hR : ((α_ (cpx.X n) (A.complex.X i) (A.complex.X j)).hom ≫
          cpx.X n ◁ amul i j ≫ act n (i + j) ≫
            eqToHom (congrArg cpx.X (add_assoc n i j).symm)).val.app U
          ((tensorSheafUnit (cpx.X n ⊗ A.complex.X i) (A.complex.X j)).app U
            ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y) ⊗ₜ z)) =
        (eqToHom (congrArg cpx.X (add_assoc n i j).symm)).val.app U
          ((bilinearOfAct (A := A) cpx act n (i + j)).app U x ((A.mul i j).app U y z)) :=
      congrArg ((eqToHom (congrArg cpx.X (add_assoc n i j).symm)).val.app U)
        (congrArg ((act n (i + j)).val.app U)
          (((congrArg ((cpx.X n ◁ amul i j).val.app U)
                (Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit Osharp hO
                  (cpx.X n) (A.complex.X i) (A.complex.X j) U x y z)).trans
              (Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO U
                (cpx.X n) (amul i j) x
                ((tensorSheafUnit (A.complex.X i) (A.complex.X j)).app U (y ⊗ₜ z)))).trans
            (congrArg (fun t ↦ (tensorSheafUnit (cpx.X n) (A.complex.X (i + j))).app U (x ⊗ₜ t))
              (hamul i j U y z))))
    refine HEq.trans (heq_of_eq (hL.symm.trans ((congrArg
      (fun ψ : (cpx.X n ⊗ A.complex.X i) ⊗ A.complex.X j ⟶ cpx.X (n + i + j) ↦ ψ.val.app U
        ((tensorSheafUnit (cpx.X n ⊗ A.complex.X i) (A.complex.X j)).app U
          ((tensorSheafUnit (cpx.X n) (A.complex.X i)).app U (x ⊗ₜ y) ⊗ₜ z)))
      (hassoc n i j)).trans hR))) ?_
    exact Stacks.TensorSheafWorld.heq_eqToHom_val_app cpx.X (add_assoc n i j).symm U _
  mul_one n U x := by
    have hL : (cpx.X n ◁ aone ≫ act n 0).val.app U
          ((tensorSheafUnit (cpx.X n) (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))).app U
            (x ⊗ₜ (1 : (toRingCat J Osharp).obj.obj U))) =
        (bilinearOfAct (A := A) cpx act n 0).app U x (A.one.eval U) :=
      congrArg ((act n 0).val.app U)
        ((Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO U
            (cpx.X n) aone x (1 : (toRingCat J Osharp).obj.obj U)).trans
          (congrArg (fun t ↦ (tensorSheafUnit (cpx.X n) (A.complex.X 0)).app U (x ⊗ₜ t))
            (haone U)))
    have hR : ((ρ_ (cpx.X n)).hom ≫ eqToHom (congrArg cpx.X (add_zero n).symm)).val.app U
          ((tensorSheafUnit (cpx.X n) (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))).app U
            (x ⊗ₜ (1 : (toRingCat J Osharp).obj.obj U))) =
        (eqToHom (congrArg cpx.X (add_zero n).symm)).val.app U x :=
      congrArg ((eqToHom (congrArg cpx.X (add_zero n).symm)).val.app U)
        ((Stacks.TensorSheafWorld.rightUnitor_hom_val_app_tensorSheafUnit Osharp hO
          (cpx.X n) U x (1 : (toRingCat J Osharp).obj.obj U)).trans (one_smul _ x))
    refine HEq.trans (heq_of_eq (hL.symm.trans ((congrArg
      (fun ψ : cpx.X n ⊗ 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⟶ cpx.X (n + 0) ↦
        ψ.val.app U ((tensorSheafUnit (cpx.X n)
          (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))).app U
            (x ⊗ₜ (1 : (toRingCat J Osharp).obj.obj U))))
      (hone n)).trans hR))) ?_
    exact Stacks.TensorSheafWorld.heq_eqToHom_val_app cpx.X (add_zero n).symm U x
  leibniz n i := (smulSheafLeibniz_iff cpx act n i hO).mp (hleib n i)

variable (hamul : ∀ (i j : ℤ) (U : Cᵒᵖ) (y : (A.complex.X i).val.obj U)
    (z : (A.complex.X j).val.obj U),
    (amul i j).val.app U
        ((tensorSheafUnit (A.complex.X i) (A.complex.X j)).app U (y ⊗ₜ z)) =
      (A.mul i j).app U y z)
  (haone : ∀ U : Cᵒᵖ, aone.val.app U (1 : (toRingCat J Osharp).obj.obj U) = A.one.eval U)
  (hassoc : ∀ n i j : ℤ, act n i ▷ A.complex.X j ≫ act (n + i) j =
    (α_ (cpx.X n) (A.complex.X i) (A.complex.X j)).hom ≫
      cpx.X n ◁ amul i j ≫ act n (i + j) ≫
        eqToHom (congrArg cpx.X (add_assoc n i j).symm))
  (hone : ∀ n : ℤ, cpx.X n ◁ aone ≫ act n 0 =
    (ρ_ (cpx.X n)).hom ≫ eqToHom (congrArg cpx.X (add_zero n).symm))
  (hleib : ∀ n i : ℤ, SmulSheafLeibniz (A := A) cpx act n i)

/-- The underlying cochain complex of `ofMorphismData` is the given one. -/
theorem ofMorphismData_complex :
    (ofMorphismData hO cpx act amul aone hamul haone hassoc hone hleib).complex = cpx :=
  rfl

/-- **The morphism-level action of `ofMorphismData` is the given one.** -/
theorem smulSheaf_ofMorphismData (n i : ℤ) :
    smulSheaf (ofMorphismData hO cpx act amul aone hamul haone hassoc hone hleib) n i =
      act n i :=
  PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := cpx.X n)
    (G := A.complex.X i) (Q := cpx.X (n + i)) fun U x y ↦
      smulSheaf_unit (ofMorphismData hO cpx act amul aone hamul haone hassoc hone hleib) n i U x y

end OfMorphismData

/-! ### Transport along an additive lax monoidal functor -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (L : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [L.LaxMonoidal] [L.Additive] {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (M : DifferentialGradedModule.{w, w, w} A)

/-- **The transported right action** `L(M_n) ⊗ L(A_i) ⟶ L(M_{n+i})`: the action of `M` in
degrees `n` and `i`, conjugated by the tensorator of `L`. -/
noncomputable def transportedSmul (n i : ℤ) :
    L.obj (M.complex.X n) ⊗ L.obj (A.complex.X i) ⟶ L.obj (M.complex.X (n + i)) :=
  Stacks.MonoidalGraded.mapMul L (X := M.complex.X n) (Y := A.complex.X i)
    (Z := M.complex.X (n + i)) (smulSheaf M n i)

omit [L.Additive] in
/-- The transported action followed by a degree transport is the transport of the action
followed by that degree transport. -/
theorem transportedSmul_comp_eqToHom (n i : ℤ) {p : ℤ} (h : n + i = p) :
    transportedSmul L M n i ≫ eqToHom (congrArg (fun q ↦ L.obj (M.complex.X q)) h) =
      Stacks.MonoidalGraded.mapMul L (smulSheaf M n i ≫ eqToHom (congrArg M.complex.X h)) :=
  (congrArg (fun ϑ ↦ transportedSmul L M n i ≫ ϑ)
      (eqToHom_map L (congrArg M.complex.X h)).symm).trans
    (Stacks.MonoidalGraded.mapMul_comp L (smulSheaf M n i)
      (eqToHom (congrArg M.complex.X h))).symm

variable (hO : Presheaf.IsSheaf J
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO

omit [L.Additive] in
/-- **The transported action is associative with the transported multiplication**, as an
equality of morphisms out of `L(M_n) ⊗ L(A_i) ⊗ L(A_j)`. -/
theorem transportedSmul_assoc (n i j : ℤ) :
    transportedSmul L M n i ▷ L.obj (A.complex.X j) ≫ transportedSmul L M (n + i) j =
      (α_ (L.obj (M.complex.X n)) (L.obj (A.complex.X i)) (L.obj (A.complex.X j))).hom ≫
        L.obj (M.complex.X n) ◁ GradedAlgebra.transportedMul L A.toGradedAlgebra i j ≫
          transportedSmul L M n (i + j) ≫
            eqToHom (congrArg (fun q ↦ L.obj (M.complex.X q)) (add_assoc n i j).symm) := by
  refine (Stacks.MonoidalGraded.mapMul_assoc L (smulSheaf M n i)
    (GradedAlgebra.mulSheaf A.toGradedAlgebra i j) (smulSheaf M (n + i) j)
    (smulSheaf M n (i + j) ≫ eqToHom (congrArg M.complex.X (add_assoc n i j).symm))
    (smulSheaf_assoc M hO n i j)).trans ?_
  exact congrArg (fun ϑ ↦ (α_ (L.obj (M.complex.X n)) (L.obj (A.complex.X i))
      (L.obj (A.complex.X j))).hom ≫
    L.obj (M.complex.X n) ◁ GradedAlgebra.transportedMul L A.toGradedAlgebra i j ≫ ϑ)
    (transportedSmul_comp_eqToHom L M n (i + j) (add_assoc n i j).symm).symm

omit [L.Additive] in
/-- **The transported unit acts as the identity**, as an equality of morphisms out of
`L(M_n) ⊗ 𝟙_`. -/
theorem transportedSmul_mul_one (n : ℤ) :
    L.obj (M.complex.X n) ◁ GradedAlgebra.transportedOne L A.toGradedAlgebra ≫
        transportedSmul L M n 0 =
      (ρ_ (L.obj (M.complex.X n))).hom ≫
        eqToHom (congrArg (fun q ↦ L.obj (M.complex.X q)) (add_zero n).symm) := by
  refine (Stacks.MonoidalGraded.mapMul_one L (GradedAlgebra.oneHom A.toGradedAlgebra)
    (smulSheaf M n 0) (eqToHom (congrArg M.complex.X (add_zero n).symm))
    (smulSheaf_mul_one M hO n)).trans ?_
  exact congrArg (fun ϑ ↦ (ρ_ (L.obj (M.complex.X n))).hom ≫ ϑ)
    (eqToHom_map L (congrArg M.complex.X (add_zero n).symm))

variable (hP : Presheaf.IsSheaf K
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hP

/-- **An additive lax monoidal functor transports the morphism-level Leibniz rule of an
action.** -/
theorem transportedSmulLeibniz (n i : ℤ) :
    SmulSheafLeibniz (A := DifferentialGradedAlgebra.transport L hO hP A)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.complex) (transportedSmul L M) n i :=
  Stacks.MonoidalGraded.mapMul_leibniz L (M.complex.d n (n + 1)) (A.complex.d i (i + 1))
    (smulSheaf M n i) (M.complex.d (n + i) (n + i + 1))
    (smulSheaf M (n + 1) i ≫ eqToHom (congrArg M.complex.X (add_right_comm n 1 i)))
    (smulSheaf M n (i + 1) ≫ eqToHom (congrArg M.complex.X (add_assoc n i 1).symm))
    (Int.negOnePow n : ℤ) rfl
    (transportedSmul_comp_eqToHom L M (n + 1) i (add_right_comm n 1 i))
    (transportedSmul_comp_eqToHom L M n (i + 1) (add_assoc n i 1).symm)
    (smulSheafLeibniz_complex M hO n i)

/-- **The transport of a right differential graded module along an additive lax monoidal
functor between categories of sheaves of modules.** Its cochain complex is `L` applied
degreewise and its action is the action of `M` conjugated by the tensorator; it is a module over
the transported sheaf of differential graded algebras. -/
noncomputable def transport :
    DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hO hP A) :=
  ofMorphismData (A := DifferentialGradedAlgebra.transport L hO hP A) hP
    ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.complex)
    (transportedSmul L M) (GradedAlgebra.transportedMul L A.toGradedAlgebra)
    (GradedAlgebra.transportedOne L A.toGradedAlgebra) (fun _ _ _ _ _ ↦ rfl) (fun _ ↦ rfl)
    (transportedSmul_assoc L M hO) (transportedSmul_mul_one L M hO)
    (transportedSmulLeibniz L M hO hP)

/-- The cochain complex of `L(M)` is `L` applied to the cochain complex of `M` degreewise. -/
theorem transport_complex :
    (transport L M hO hP).complex =
      (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.complex :=
  rfl

/-- The morphism-level action of `L(M)` is the transported action. -/
@[simp]
theorem smulSheaf_transport (n i : ℤ) :
    smulSheaf (transport L M hO hP) n i = transportedSmul L M n i :=
  smulSheaf_ofMorphismData hP _ _ _ _ _ _ _ _ _ n i

end Transport

/-! ### Functoriality of the transport -/

section Functoriality

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (L : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [L.LaxMonoidal] [L.Additive] {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO

omit [L.Additive] in
/-- The degreewise image of a morphism of right differential graded modules intertwines the
transported actions. -/
theorem transportedSmul_comp {M N : DifferentialGradedModule.{w, w, w} A} (φ : M ⟶ N) (n i : ℤ) :
    transportedSmul L M n i ≫ L.map (φ.toHomologicalComplex.f (n + i)) =
      (L.map (φ.toHomologicalComplex.f n) ⊗ₘ 𝟙 (L.obj (A.complex.X i))) ≫
        transportedSmul L N n i :=
  (Stacks.MonoidalGraded.mapMul_naturality L (smulSheaf M n i) (smulSheaf N n i)
      (φ.toHomologicalComplex.f n) (𝟙 (A.complex.X i)) (φ.toHomologicalComplex.f (n + i))
      ((smulSheaf_comp_eq_iff M hO N (fun q ↦ φ.toHomologicalComplex.f q) n i).mpr
        (φ.map_mul n i))).trans
    (congrArg (fun ϑ ↦ (L.map (φ.toHomologicalComplex.f n) ⊗ₘ ϑ) ≫ transportedSmul L N n i)
      (L.map_id (A.complex.X i)))

include hP

/-- **The image of a morphism of right differential graded modules under an additive lax
monoidal functor.** Degreewise it is `L` applied to the component; it is a morphism of cochain
complexes because `L` is a functor, and compatible with the action because the tensorator of
`L` is natural. -/
noncomputable def transportHom {M N : DifferentialGradedModule.{w, w, w} A} (φ : M ⟶ N) :
    transport L M hO hP ⟶ transport L N hO hP where
  toHomologicalComplex :=
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.toHomologicalComplex
  map_mul n i := by
    refine (smulSheaf_comp_eq_iff (transport L M hO hP) hP (transport L N hO hP)
      (fun q ↦ L.map (φ.toHomologicalComplex.f q)) n i).mp ?_
    simp only [smulSheaf_transport]
    exact transportedSmul_comp L hO φ n i

/-- The degree `n` component of `transportHom L hO hP φ` is `L` applied to the degree `n`
component of `φ`. -/
@[simp]
theorem transportHom_f {M N : DifferentialGradedModule.{w, w, w} A} (φ : M ⟶ N) (n : ℤ) :
    (transportHom L hO hP φ).toHomologicalComplex.f n = L.map (φ.toHomologicalComplex.f n) :=
  rfl

/-- **An additive lax monoidal functor between categories of sheaves of modules induces a
functor from right differential graded `A`-modules to right differential graded modules over
the transported algebra.** For a morphism of ringed topoi `(f, f♯)` and `L = f^*` it is the
pullback `M ↦ (f^*M, f^*d)`; for `L = f_*` it is the direct image. -/
noncomputable def transportFunctor :
    DifferentialGradedModule.{w, w, w} A ⥤
      DifferentialGradedModule.{w, w, w} (DifferentialGradedAlgebra.transport L hO hP A) where
  obj M := transport L M hO hP
  map φ := transportHom L hO hP φ
  map_id M := Hom.ext fun n ↦ (transportHom_f L hO hP (𝟙 M) n).trans (L.map_id _)
  map_comp φ ψ := Hom.ext fun n ↦ (transportHom_f L hO hP (φ ≫ ψ) n).trans
    ((congrArg L.map (comp_f φ ψ n)).trans (L.map_comp _ _))

/-- `transportFunctor L hO hP` sends `M` to `transport L M hO hP`. -/
@[simp]
theorem transportFunctor_obj (M : DifferentialGradedModule.{w, w, w} A) :
    (transportFunctor L hO hP).obj M = transport L M hO hP :=
  rfl

/-- The degree `n` component of the image of `φ` under `transportFunctor L hO hP` is `L` applied
to the degree `n` component of `φ`. -/
@[simp]
theorem transportFunctor_map_f {M N : DifferentialGradedModule.{w, w, w} A} (φ : M ⟶ N) (n : ℤ) :
    ((transportFunctor L hO hP).map φ).toHomologicalComplex.f n =
      L.map (φ.toHomologicalComplex.f n) :=
  rfl

end Functoriality

end SheafOfModules.DifferentialGradedModule

end
