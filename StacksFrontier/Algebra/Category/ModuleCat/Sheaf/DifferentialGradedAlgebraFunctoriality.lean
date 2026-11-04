module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraMonoidalAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of sheaves of differential graded algebras

Let `L ⊣ G` be an adjunction between categories of sheaves of modules, with `L` strong monoidal
for the tensor product of Tag 01CA, `G` lax monoidal compatibly with the adjunction, and both
additive. For a morphism of ringed topoi `(f, f♯)` this is the adjunction `f^* ⊣ f_*` of
Tag 03D7. Then

* `G` carries a sheaf of differential graded algebras `A` to one whose underlying cochain
  complex is `G` applied degreewise, whose multiplication is the one transported by the
  tensorator, and whose differential is `G(d)`;
* `L` does the same, dually;
* the two are adjoint: homomorphisms `L(B) ⟶ A` of sheaves of differential graded algebras
  correspond bijectively, and naturally in both arguments, to homomorphisms `B ⟶ G(A)`.

These are the three parts of the Stacks remark on functoriality of sheaves of differential
graded algebras. The graded parts are `SheafOfModules.GradedAlgebra.transport` and
`SheafOfModules.GradedAlgebra.transportHomForward`, so the content here is the
**differential**: the signed Leibniz rule is a statement about arbitrary local sections, and
what a monoidal functor transports is an equality of morphisms. The reconciliation is
`SheafOfModules.GradedAlgebra.mulSheafLeibniz_iff`.

## Main definitions

* `SheafOfModules.GradedAlgebra.MulSheafLeibniz`: the **morphism-level** signed Leibniz rule,
  `mulSheaf A i j ≫ d = (d ⊗ 1) ≫ mulSheaf A (i+1) j + (-1)^i • (1 ⊗ d) ≫ mulSheaf A i (j+1)`
  with the degree-addition transports inserted.
* `SheafOfModules.DifferentialGradedAlgebra.transport`: **the sheaf of differential graded
  algebras `F(A)`** for an additive lax monoidal `F`, and
  `SheafOfModules.DifferentialGradedAlgebra.transportHom` the image of a homomorphism.
* `SheafOfModules.DifferentialGradedAlgebra.pushforwardDifferentialGradedAlgebra`: **part (1)**,
  the induced functor on categories of sheaves of differential graded algebras; for a morphism
  of ringed topoi and `F = f_*` it is the pushforward.
* `SheafOfModules.DifferentialGradedAlgebra.pullbackDifferentialGradedAlgebra`: **part (2)**,
  the same transport read at the strong monoidal left adjoint; for a morphism of ringed topoi
  and `F = f^*` it is the pullback.
* `SheafOfModules.DifferentialGradedAlgebra.differentialGradedAlgebraAdjunction`: **part (3)**,
  the adjunction between them, whose two functors are the previous two constructions rather
  than functors merely asserted to exist.

## Main results

* `Stacks.MonoidalGraded.mapMul_tensorHom_comp`, `mapMul_add` and `mapMul_zsmul`: transport of a
  multiplication along a lax monoidal functor commutes with precomposition by a tensor product
  of morphisms, and is additive and `ℤ`-linear when the functor is additive.
* `Stacks.MonoidalGraded.mapMul_leibniz`: **an additive lax monoidal functor transports a
  morphism-level signed Leibniz rule**, with the degree bookkeeping absorbed into two
  unconstrained morphisms, so that no `CategoryTheory.eqToHom` appears in the general statement.
* `SheafOfModules.GradedAlgebra.mulSheafLeibniz_iff`: **the morphism-level signed Leibniz rule
  holds if and only if the sectionwise one does.** This is the differential-graded counterpart
  of `SheafOfModules.GradedAlgebra.mulSheaf_comp_eq_iff`.
* `SheafOfModules.GradedAlgebra.mulSheafLeibniz_transport`: **an additive lax monoidal functor
  transports the morphism-level Leibniz rule.**
* `SheafOfModules.DifferentialGradedAlgebra.transport_complex`,
  `toGradedAlgebra_transport`: the cochain complex of `F(A)` is `F` applied degreewise, and its
  underlying sheaf of graded algebras is the transport of the underlying sheaf of graded
  algebras of `A`.
* `SheafOfModules.DifferentialGradedAlgebra.transportHomEquiv`: the bijection
  `(L(B) ⟶ A) ≃ (B ⟶ G(A))` on homomorphisms of sheaves of differential graded algebras.

## Implementation notes

**Why the Leibniz rule needs a morphism-level reading at all.** The `leibniz` field of
`SheafOfModules.DifferentialGradedAlgebra` is an equality of local sections involving two
transports along `i + 1 + j = i + j + 1` and `i + (j + 1) = i + j + 1`, a sum, and a sign. A
monoidal functor transports equalities of morphisms, and an additive one transports sums and
integer multiples of morphisms; nothing it does sees local sections. So the field is first
turned into an equality of morphisms out of the tensor product sheaf
(`mulSheafLeibniz_iff`), transported there (`mulSheafLeibniz_transport`), and read back. The two
transports become `CategoryTheory.eqToHom`s, and
`SheafOfModules.eqToHom_val_app` is the one lemma relating them to the `SheafOfModules.gradedCast`
of the structure field.

**Additivity on local sections.** `SheafOfModules.add_val_app` is `rfl`, but
`SheafOfModules.zsmul_val_app` is not: the `ℤ`-action on a hom group is not the pointwise one by
definition. It is obtained from `SheafOfModules.evalSectionAddHom`, evaluation at a fixed local
section read as an additive map in the morphism.

**No `rw` crosses the tensor-product boundary.** `(M ⊗ N).val.obj U` and
`(((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj M).obj N).val.obj U` are definitionally
but not syntactically equal, so the section-level computations
`SheafOfModules.GradedAlgebra.leibnizLeft_app` and `leibnizRight_app` are `Eq.trans`/`congrArg`
chains and the two summands are given names (`leibnizLeft`, `leibnizRight`) so that the sum and
the scaling can be evaluated without rewriting underneath a tensor product. For the same reason
the whole transport computation is carried out in `Stacks.MonoidalGraded.mapMul_leibniz`, in an
abstract monoidal preadditive category where `rw` is available, and consumed at the sheaf level
through three identifications supplied by the caller.

**Why part (2) is part (1) applied to the left adjoint.** The Stacks remark constructs the
pullback "dually", and the dual construction is the same transport: a strong monoidal functor is
in particular lax monoidal. What the stronger hypothesis buys is part (3), where
`Stacks.MonoidalGraded.mapMul_comp_iff` needs the tensorator of `L` to be invertible. So
`pullbackDifferentialGradedAlgebra` differs from `pushforwardDifferentialGradedAlgebra` only in
asking for `CategoryTheory.Functor.Monoidal` instead of
`CategoryTheory.Functor.LaxMonoidal`, which is what makes it usable in the adjunction.

**Universes.** The two sites are independent, but the ring sheaves and the modules on both sides
live in one universe `w`. That constraint is inherited from the monoidal structure on sheaves of
modules of Tag 01CA, exactly as for `SheafOfModules.GradedAlgebra.transport`; a sheaf of
differential graded algebras over `R : Sheaf J RingCat.{t}` with pieces in
`SheafOfModules.{a} R` is available for independent `t` and `a`, and it is the graded transport
that forces `t = a = w` here.

## References

* [Stacks Project, Tag 0FRG](https://stacks.math.columbia.edu/tag/0FRG) — functoriality of
  sheaves of differential graded algebras for a morphism of ringed topoi.
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF) — sheaves of
  differential graded algebras and their homomorphisms.
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras.
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7) — the adjunction
  between pullback and pushforward of sheaves of modules.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CategoryTheory.Sheaf PresheafOfModules

open scoped TensorProduct

universe v₁ v₂ u₁ u₂ w

namespace Stacks.MonoidalGraded

/-! ### Transport of a multiplication along an additive lax monoidal functor -/

section Additive

variable {E : Type u₁} [Category.{v₁} E] [MonoidalCategory E]
  {E' : Type u₂} [Category.{v₂} E'] [MonoidalCategory E'] (F : E ⥤ E') [F.LaxMonoidal]

/-- Transport of a multiplication commutes with precomposition by a tensor product of
morphisms, by naturality of the tensorator. -/
theorem mapMul_tensorHom_comp {X Y X' Y' Z : E} (a : X ⟶ X') (b : Y ⟶ Y')
    (m : X' ⊗ Y' ⟶ Z) :
    mapMul F ((a ⊗ₘ b) ≫ m) = (F.map a ⊗ₘ F.map b) ≫ mapMul F m := by
  simp only [mapMul, Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]

variable [Preadditive E] [Preadditive E'] [F.Additive]

/-- Transport of a multiplication along an additive lax monoidal functor is additive. -/
theorem mapMul_add {X Y Z : E} (m m' : X ⊗ Y ⟶ Z) :
    mapMul F (m + m') = mapMul F m + mapMul F m' := by
  simp only [mapMul, Functor.map_add, Preadditive.comp_add]

/-- Transport of a multiplication along an additive lax monoidal functor commutes with integer
scaling. -/
theorem mapMul_zsmul {X Y Z : E} (k : ℤ) (m : X ⊗ Y ⟶ Z) :
    mapMul F (k • m) = k • mapMul F m := by
  simp only [mapMul, Functor.map_zsmul, Preadditive.comp_zsmul]

/-- **An additive lax monoidal functor transports a morphism-level signed Leibniz rule.** The
two "outer" multiplications `mL` and `mR` and their transports `ML` and `MR` are unconstrained,
so the degree bookkeeping of a graded algebra never enters the statement; the caller supplies it
inside `mL`, `mR` and the three identifications `hM`, `hML`, `hMR`. -/
theorem mapMul_leibniz {X Y X' Y' Z W : E} (dX : X ⟶ X') (dY : Y ⟶ Y') (m : X ⊗ Y ⟶ Z)
    (d : Z ⟶ W) (mL : X' ⊗ Y ⟶ W) (mR : X ⊗ Y' ⟶ W) (k : ℤ)
    {M : F.obj X ⊗ F.obj Y ⟶ F.obj Z} {ML : F.obj X' ⊗ F.obj Y ⟶ F.obj W}
    {MR : F.obj X ⊗ F.obj Y' ⟶ F.obj W}
    (hM : M = mapMul F m) (hML : ML = mapMul F mL) (hMR : MR = mapMul F mR)
    (h : m ≫ d = (dX ⊗ₘ 𝟙 Y) ≫ mL + k • ((𝟙 X ⊗ₘ dY) ≫ mR)) :
    M ≫ F.map d =
      (F.map dX ⊗ₘ 𝟙 (F.obj Y)) ≫ ML + k • ((𝟙 (F.obj X) ⊗ₘ F.map dY) ≫ MR) := by
  subst hM hML hMR
  rw [← mapMul_comp, h, mapMul_add, mapMul_zsmul, mapMul_tensorHom_comp,
    mapMul_tensorHom_comp, F.map_id, F.map_id]

end Additive

end Stacks.MonoidalGraded

namespace SheafOfModules

/-! ### Sums, integer multiples and degree transports on local sections -/

section Sections

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M N : SheafOfModules.{w} R}

/-- Evaluation at a fixed local section, read as an additive map in the morphism. -/
def evalSectionAddHom (U : Cᵒᵖ) (z : M.val.obj U) : (M ⟶ N) →+ N.val.obj U :=
  AddMonoidHom.mk' (fun φ ↦ φ.val.app U z) fun _ _ ↦ rfl

/-- `evalSectionAddHom U z` sends a morphism `φ` to the section `φ.val.app U z`. -/
@[simp]
theorem evalSectionAddHom_apply (U : Cᵒᵖ) (z : M.val.obj U) (φ : M ⟶ N) :
    evalSectionAddHom U z φ = φ.val.app U z :=
  rfl

/-- A sum of morphisms of sheaves of modules acts on local sections as the sum of their
actions. -/
theorem add_val_app (φ ψ : M ⟶ N) (U : Cᵒᵖ) (z : M.val.obj U) :
    (φ + ψ).val.app U z = φ.val.app U z + ψ.val.app U z :=
  rfl

/-- An integer multiple of a morphism of sheaves of modules acts on local sections as that
multiple of its action. -/
theorem zsmul_val_app (k : ℤ) (φ : M ⟶ N) (U : Cᵒᵖ) (z : M.val.obj U) :
    (k • φ).val.app U z = k • φ.val.app U z :=
  map_zsmul (evalSectionAddHom (N := N) U z) k φ

/-- Transport of a degreewise family of sheaves of modules along an equality of degrees acts on
local sections as `SheafOfModules.gradedCast`. -/
theorem eqToHom_val_app (Y : ℤ → SheafOfModules.{w} R) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (y : (Y i).val.obj U) :
    (eqToHom (congrArg Y h)).val.app U y = gradedCast (fun q ↦ (Y q).val.obj U) h y := by
  subst h
  rfl

end Sections

namespace GradedAlgebra

/-! ### The morphism-level reading of the signed Leibniz rule -/

section Leibniz

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (A : GradedAlgebra.{w, w} (toRingCat J Osharp))
  (dd : ∀ n : ℤ, A.piece n ⟶ A.piece (n + 1)) (i j : ℤ)

/-- The first summand of the morphism-level Leibniz rule: differentiate the left factor. -/
noncomputable def leibnizLeft :
    (A.piece i ⊗ A.piece j : SheafOfModules.{w} (toRingCat J Osharp)) ⟶ A.piece (i + j + 1) :=
  (dd i ⊗ₘ 𝟙 (A.piece j)) ≫ mulSheaf A (i + 1) j ≫
    eqToHom (congrArg A.piece (add_right_comm i 1 j))

/-- The second summand of the morphism-level Leibniz rule: differentiate the right factor. -/
noncomputable def leibnizRight :
    (A.piece i ⊗ A.piece j : SheafOfModules.{w} (toRingCat J Osharp)) ⟶ A.piece (i + j + 1) :=
  (𝟙 (A.piece i) ⊗ₘ dd j) ≫ mulSheaf A i (j + 1) ≫
    eqToHom (congrArg A.piece (add_assoc i j 1).symm)

/-- **The morphism-level signed Leibniz rule** for a degreewise family of morphisms `dd` on a
sheaf of graded algebras: the differential of a product is the product of the differentiated
left factor with the right factor, plus `(-1)^i` times the product of the left factor with the
differentiated right factor. -/
def MulSheafLeibniz : Prop :=
  mulSheaf A i j ≫ dd (i + j) =
    leibnizLeft A dd i j + (Int.negOnePow i : ℤ) • leibnizRight A dd i j

/-- The left-hand side of the morphism-level Leibniz rule on a pure tensor of local
sections. -/
theorem mulSheafLeibniz_app (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    (mulSheaf A i j ≫ dd (i + j)).val.app U
        ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) =
      (dd (i + j)).val.app U ((A.mul i j).app U x y) :=
  congrArg ((dd (i + j)).val.app U) (mulSheaf_unit A i j U x y)

/-- A product of pure tensors, followed by a degree transport, acts as the cast of the product. -/
private theorem eqToHom_mulSheaf_app {a b p : ℤ} (h : a + b = p) (U : Cᵒᵖ)
    (x : (A.piece a).val.obj U) (y : (A.piece b).val.obj U) :
    (eqToHom (congrArg A.piece h)).val.app U ((mulSheaf A a b).val.app U
        ((tensorSheafUnit (A.piece a) (A.piece b)).app U (x ⊗ₜ y))) =
      gradedCast (fun q ↦ (A.piece q).val.obj U) h ((A.mul a b).app U x y) :=
  (congrArg ((eqToHom (congrArg A.piece h)).val.app U) (mulSheaf_unit A a b U x y)).trans
    (eqToHom_val_app A.piece h U _)

variable (hO : Presheaf.IsSheaf J
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO

/-- The first summand of the morphism-level Leibniz rule on a pure tensor of local sections. -/
theorem leibnizLeft_app (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (leibnizLeft A dd i j).val.app U
        ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) =
      gradedCast (fun q ↦ (A.piece q).val.obj U) (add_right_comm i 1 j)
        ((A.mul (i + 1) j).app U ((dd i).val.app U x) y) :=
  (congrArg (fun z ↦ (eqToHom (congrArg A.piece (add_right_comm i 1 j))).val.app U
        ((mulSheaf A (i + 1) j).val.app U z))
      (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U (dd i)
        (𝟙 (A.piece j)) x y)).trans
    (eqToHom_mulSheaf_app A (add_right_comm i 1 j) U ((dd i).val.app U x) y)

/-- The second summand of the morphism-level Leibniz rule on a pure tensor of local
sections. -/
theorem leibnizRight_app (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (leibnizRight A dd i j).val.app U
        ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) =
      gradedCast (fun q ↦ (A.piece q).val.obj U) (add_assoc i j 1).symm
        ((A.mul i (j + 1)).app U x ((dd j).val.app U y)) :=
  (congrArg (fun z ↦ (eqToHom (congrArg A.piece (add_assoc i j 1).symm)).val.app U
        ((mulSheaf A i (j + 1)).val.app U z))
      (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Osharp hO U
        (𝟙 (A.piece i)) (dd j) x y)).trans
    (eqToHom_mulSheaf_app A (add_assoc i j 1).symm U x ((dd j).val.app U y))

/-- The right-hand side of the morphism-level Leibniz rule on a pure tensor of local
sections. -/
theorem leibnizSum_app (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (leibnizLeft A dd i j + (Int.negOnePow i : ℤ) • leibnizRight A dd i j).val.app U
        ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) =
      gradedCast (fun q ↦ (A.piece q).val.obj U) (add_right_comm i 1 j)
          ((A.mul (i + 1) j).app U ((dd i).val.app U x) y) +
        (Int.negOnePow i : ℤ) •
          gradedCast (fun q ↦ (A.piece q).val.obj U) (add_assoc i j 1).symm
            ((A.mul i (j + 1)).app U x ((dd j).val.app U y)) := by
  have hright : ((Int.negOnePow i : ℤ) • leibnizRight A dd i j).val.app U
      ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y)) =
        (Int.negOnePow i : ℤ) • gradedCast (fun q ↦ (A.piece q).val.obj U)
          (add_assoc i j 1).symm ((A.mul i (j + 1)).app U x ((dd j).val.app U y)) :=
    (zsmul_val_app _ _ U _).trans
      (congrArg (fun t ↦ (Int.negOnePow i : ℤ) • t) (leibnizRight_app A dd i j hO U x y))
  exact (add_val_app _ _ U _).trans (by rw [leibnizLeft_app A dd i j hO U x y, hright])

/-- **The morphism-level signed Leibniz rule holds if and only if the sectionwise one does.**
The right-hand side is the `leibniz` field of `SheafOfModules.DifferentialGradedAlgebra`; the
left-hand side is the form an additive lax monoidal functor transports. -/
theorem mulSheafLeibniz_iff :
    MulSheafLeibniz A dd i j ↔
      ∀ (U : Cᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U),
        (dd (i + j)).val.app U ((A.mul i j).app U x y) =
          gradedCast (fun q ↦ (A.piece q).val.obj U) (add_right_comm i 1 j)
              ((A.mul (i + 1) j).app U ((dd i).val.app U x) y) +
            (Int.negOnePow i : ℤ) •
              gradedCast (fun q ↦ (A.piece q).val.obj U) (add_assoc i j 1).symm
                ((A.mul i (j + 1)).app U x ((dd j).val.app U y)) :=
  ⟨fun h U x y ↦ (mulSheafLeibniz_app A dd i j U x y).symm.trans
      ((congrArg (fun φ : (A.piece i ⊗ A.piece j :
            SheafOfModules.{w} (toRingCat J Osharp)) ⟶ A.piece (i + j + 1) ↦
          φ.val.app U ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y))) h).trans
        (leibnizSum_app A dd i j hO U x y)),
    fun h ↦ PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp) (F := A.piece i)
      (G := A.piece j) (Q := A.piece (i + j + 1)) fun U x y ↦
        (mulSheafLeibniz_app A dd i j U x y).trans
          ((h U x y).trans (leibnizSum_app A dd i j hO U x y).symm)⟩

end Leibniz

/-! ### An additive lax monoidal functor transports the morphism-level Leibniz rule -/

section LeibnizTransport

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (F : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [F.LaxMonoidal] [F.Additive] (A : GradedAlgebra.{w, w} (toRingCat J Osharp))
  (dd : ∀ n : ℤ, A.piece n ⟶ A.piece (n + 1)) (i j : ℤ)
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO hP

omit [F.Additive] in
/-- The multiplication of the transported sheaf of graded algebras is the transport of the
multiplication, followed by a degree transport. -/
theorem mulSheaf_transport_comp_eqToHom {p : ℤ} (h : i + j = p) :
    mulSheaf (transport F A hO hP) i j ≫
        eqToHom (congrArg (fun n ↦ F.obj (A.piece n)) h) =
      Stacks.MonoidalGraded.mapMul F (mulSheaf A i j ≫ eqToHom (congrArg A.piece h)) :=
  (congrArg (fun m : (transport F A hO hP).piece i ⊗ (transport F A hO hP).piece j ⟶
        (transport F A hO hP).piece (i + j) ↦
      m ≫ eqToHom (congrArg (fun n ↦ F.obj (A.piece n)) h))
    (mulSheaf_transport F A hO hP i j)).trans
    ((congrArg (fun ϑ ↦ Stacks.MonoidalGraded.mapMul F (mulSheaf A i j) ≫ ϑ)
        (eqToHom_map F (congrArg A.piece h)).symm).trans
      (Stacks.MonoidalGraded.mapMul_comp F (mulSheaf A i j) (eqToHom (congrArg A.piece h))).symm)

/-- **An additive lax monoidal functor transports the morphism-level Leibniz rule.** -/
theorem mulSheafLeibniz_transport (h : MulSheafLeibniz A dd i j) :
    MulSheafLeibniz (transport F A hO hP) (fun n ↦ F.map (dd n)) i j :=
  Stacks.MonoidalGraded.mapMul_leibniz F (dd i) (dd j) (mulSheaf A i j) (dd (i + j))
    (mulSheaf A (i + 1) j ≫ eqToHom (congrArg A.piece (add_right_comm i 1 j)))
    (mulSheaf A i (j + 1) ≫ eqToHom (congrArg A.piece (add_assoc i j 1).symm))
    (Int.negOnePow i : ℤ) (mulSheaf_transport F A hO hP i j)
    (mulSheaf_transport_comp_eqToHom F A (i + 1) j hO hP (add_right_comm i 1 j))
    (mulSheaf_transport_comp_eqToHom F A i (j + 1) hO hP (add_assoc i j 1).symm) h

end LeibnizTransport

end GradedAlgebra

namespace DifferentialGradedAlgebra

/-! ### The underlying homomorphism of sheaves of graded algebras -/

section ToGradedAlgebra

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The homomorphism of underlying sheaves of graded algebras of a homomorphism of sheaves of
differential graded algebras: forget that it is a morphism of cochain complexes. -/
def Hom.toGradedAlgebraHom {A B : DifferentialGradedAlgebra.{w, w} R} (φ : A ⟶ B) :
    A.toGradedAlgebra ⟶ B.toGradedAlgebra where
  app n := φ.toHomologicalComplex.f n
  map_mul := φ.map_mul

/-- The degree-`n` component of `φ.toGradedAlgebraHom` is the degree-`n` component of `φ`. -/
@[simp]
theorem Hom.toGradedAlgebraHom_app {A B : DifferentialGradedAlgebra.{w, w} R} (φ : A ⟶ B)
    (n : ℤ) : φ.toGradedAlgebraHom.app n = φ.toHomologicalComplex.f n :=
  rfl

end ToGradedAlgebra

/-! ### The Leibniz rule of a sheaf of differential graded algebras at morphism level -/

section Leibniz

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- The signed Leibniz rule of a sheaf of differential graded algebras, read at morphism
level. -/
theorem mulSheafLeibniz_complex
    (hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
    (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) (i j : ℤ) :
    GradedAlgebra.MulSheafLeibniz A.toGradedAlgebra (fun n ↦ A.complex.d n (n + 1)) i j :=
  (GradedAlgebra.mulSheafLeibniz_iff A.toGradedAlgebra (fun n ↦ A.complex.d n (n + 1)) i j
    hO).mpr fun U x y ↦ A.leibniz i j U x y

end Leibniz

/-! ### Transport of a sheaf of differential graded algebras -/

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

variable (F : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [F.LaxMonoidal] [F.Additive]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO hP

/-- **The transport of a sheaf of differential graded algebras along an additive lax monoidal
functor between categories of sheaves of modules.** Its cochain complex is `F` applied
degreewise, its multiplication and unit are those of the transported sheaf of graded algebras,
and its differential is `F(d)`. -/
noncomputable def transport (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp) where
  complex := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A.complex
  mul := (GradedAlgebra.transport F A.toGradedAlgebra hO hP).mul
  one := (GradedAlgebra.transport F A.toGradedAlgebra hO hP).one
  mul_assoc := (GradedAlgebra.transport F A.toGradedAlgebra hO hP).mul_assoc
  one_mul := (GradedAlgebra.transport F A.toGradedAlgebra hO hP).one_mul
  mul_one := (GradedAlgebra.transport F A.toGradedAlgebra hO hP).mul_one
  leibniz i j := (GradedAlgebra.mulSheafLeibniz_iff
    (GradedAlgebra.transport F A.toGradedAlgebra hO hP)
      (fun n ↦ F.map (A.complex.d n (n + 1))) i j hP).mp
    (GradedAlgebra.mulSheafLeibniz_transport F A.toGradedAlgebra
      (fun n ↦ A.complex.d n (n + 1)) i j hO hP (mulSheafLeibniz_complex hO A i j))

/-- The cochain complex of `F(A)` is `F` applied to the cochain complex of `A` degreewise. -/
theorem transport_complex (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    (transport F hO hP A).complex =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj A.complex :=
  rfl

/-- The underlying sheaf of graded algebras of `F(A)` is the transport of the underlying sheaf
of graded algebras of `A`. -/
theorem toGradedAlgebra_transport (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    (transport F hO hP A).toGradedAlgebra = GradedAlgebra.transport F A.toGradedAlgebra hO hP :=
  rfl

/-- **The image of a homomorphism of sheaves of differential graded algebras under an additive
lax monoidal functor.** Degreewise it is `F` applied to the component; it is a morphism of
cochain complexes because `F` is a functor, and multiplicative because the tensorator of `F` is
natural. -/
noncomputable def transportHom {A B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
    (φ : A ⟶ B) : transport F hO hP A ⟶ transport F hO hP B where
  toHomologicalComplex :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ.toHomologicalComplex
  map_mul := (GradedAlgebra.transportHom F hO hP φ.toGradedAlgebraHom).map_mul

/-- The degree-`n` component of `transportHom F hO hP φ` is `F` applied to the degree-`n`
component of `φ`. -/
@[simp]
theorem transportHom_f {A B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B)
    (n : ℤ) : (transportHom F hO hP φ).toHomologicalComplex.f n =
      F.map (φ.toHomologicalComplex.f n) :=
  rfl

/-- **An additive lax monoidal functor between categories of sheaves of modules induces a
functor between the categories of sheaves of differential graded algebras.** This is part (1)
of the functoriality of sheaves of differential graded algebras: for a morphism of ringed topoi
`(f, f♯)` and `F = f_*` — lax monoidal because it is right adjoint to the strong monoidal
pullback, and additive because it is a right adjoint between abelian categories — it is the
pushforward `A ↦ (f_*A, f_*d)`. -/
@[stacks 0FRG "part (1): pushforward"]
noncomputable def pushforwardDifferentialGradedAlgebra :
    DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp) ⥤
      DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp) where
  obj A := transport F hO hP A
  map φ := transportHom F hO hP φ
  map_id A := Hom.ext fun n ↦ (transportHom_f F hO hP (𝟙 A) n).trans (F.map_id _)
  map_comp φ ψ := Hom.ext fun n ↦ (transportHom_f F hO hP (φ ≫ ψ) n).trans
    ((congrArg F.map (comp_f φ ψ n)).trans (F.map_comp _ _))

/-- The pushforward of a sheaf of differential graded algebras `A` is `transport F hO hP A`. -/
@[simp]
theorem pushforwardDifferentialGradedAlgebra_obj
    (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)) :
    (pushforwardDifferentialGradedAlgebra F hO hP).obj A = transport F hO hP A :=
  rfl

/-- The degree-`n` component of the pushforward of a homomorphism `φ` is `F` applied to the
degree-`n` component of `φ`. -/
@[simp]
theorem pushforwardDifferentialGradedAlgebra_map_f
    {A B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)} (φ : A ⟶ B) (n : ℤ) :
    ((pushforwardDifferentialGradedAlgebra F hO hP).map φ).toHomologicalComplex.f n =
      F.map (φ.toHomologicalComplex.f n) :=
  rfl

end Transport

/-! ### Pullback: the transport read at a strong monoidal functor -/

section Pullback

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (L : SheafOfModules.{w} (toRingCat K Psharp) ⥤ SheafOfModules.{w} (toRingCat J Osharp))
  [L.Monoidal] [L.Additive]
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))

include hO hP

/-- **An additive strong monoidal functor between categories of sheaves of modules induces a
functor between the categories of sheaves of differential graded algebras.** This is part (2)
of the functoriality of sheaves of differential graded algebras: for a morphism of ringed topoi
`(f, f♯)` and `L = f^*` — strong monoidal for the tensor product of Tag 01CA, and additive
because it is a left adjoint between abelian categories — it is the pullback
`B ↦ (f^*B, f^*d)`. -/
@[stacks 0FRG "part (2): pullback"]
noncomputable def pullbackDifferentialGradedAlgebra :
    DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp) ⥤
      DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp) :=
  pushforwardDifferentialGradedAlgebra L hP hO

/-- The pullback of a sheaf of differential graded algebras `B` is `transport L hP hO B`. -/
@[simp]
theorem pullbackDifferentialGradedAlgebra_obj
    (B : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)) :
    (pullbackDifferentialGradedAlgebra L hP hO).obj B = transport L hP hO B :=
  rfl

/-- The degree-`n` component of the pullback of a homomorphism `φ` is `L` applied to the
degree-`n` component of `φ`. -/
@[simp]
theorem pullbackDifferentialGradedAlgebra_map_f
    {A B : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)} (φ : A ⟶ B) (n : ℤ) :
    ((pullbackDifferentialGradedAlgebra L hP hO).map φ).toHomologicalComplex.f n =
      L.map (φ.toHomologicalComplex.f n) :=
  rfl

end Pullback

/-! ### The adjunction -/

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {L : SheafOfModules.{w} (toRingCat K Psharp) ⥤ SheafOfModules.{w} (toRingCat J Osharp)}
  {G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp)}
  (adj : L ⊣ G) [L.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal] [L.Additive] [G.Additive]
  (hO : Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hO hP

variable {A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}

/-- **The adjoint transpose of a homomorphism of sheaves of differential graded algebras
`L(B) ⟶ A`**: a homomorphism `B ⟶ G(A)`, given degreewise by the hom-set bijection of the
adjunction on sheaves of modules. -/
noncomputable def transportHomForward (φ : transport L hP hO B ⟶ A) :
    B ⟶ transport G hO hP A where
  toHomologicalComplex :=
    { f := fun n ↦ adj.homEquiv (B.complex.X n) (A.complex.X n) (φ.toHomologicalComplex.f n)
      comm' := fun n m hnm ↦
        ((adj.homEquiv_naturality_right (φ.toHomologicalComplex.f n)
              (A.complex.d n m)).symm.trans
          (congrArg (fun t : L.obj (B.complex.X n) ⟶ A.complex.X m ↦
              adj.homEquiv (B.complex.X n) (A.complex.X m) t)
            (φ.toHomologicalComplex.comm' n m hnm))).trans
          (adj.homEquiv_naturality_left (B.complex.d n m)
            (φ.toHomologicalComplex.f m)) }
  map_mul := (GradedAlgebra.transportHomForward (A := A.toGradedAlgebra)
    (B := B.toGradedAlgebra) adj hO hP φ.toGradedAlgebraHom).map_mul

/-- The degree-`n` component of `transportHomForward adj hO hP φ` is the image of the degree-`n`
component of `φ` under the hom-set bijection of `adj`. -/
@[simp]
theorem transportHomForward_f (φ : transport L hP hO B ⟶ A) (n : ℤ) :
    (transportHomForward adj hO hP φ).toHomologicalComplex.f n =
      adj.homEquiv (B.complex.X n) (A.complex.X n) (φ.toHomologicalComplex.f n) :=
  rfl

/-- **The adjoint transpose of a homomorphism of sheaves of differential graded algebras
`B ⟶ G(A)`**: a homomorphism `L(B) ⟶ A`, given degreewise by the inverse hom-set bijection. -/
noncomputable def transportHomBackward (ψ : B ⟶ transport G hO hP A) :
    transport L hP hO B ⟶ A where
  toHomologicalComplex :=
    { f := fun n ↦ (adj.homEquiv (B.complex.X n) (A.complex.X n)).symm
        (ψ.toHomologicalComplex.f n)
      comm' := fun n m hnm ↦
        ((adj.homEquiv_naturality_right_symm (ψ.toHomologicalComplex.f n)
              (A.complex.d n m)).symm.trans
          (congrArg (fun t : B.complex.X n ⟶ G.obj (A.complex.X m) ↦
              (adj.homEquiv (B.complex.X n) (A.complex.X m)).symm t)
            (ψ.toHomologicalComplex.comm' n m hnm))).trans
          (adj.homEquiv_naturality_left_symm (B.complex.d n m)
            (ψ.toHomologicalComplex.f m)) }
  map_mul := (GradedAlgebra.transportHomBackward (A := A.toGradedAlgebra)
    (B := B.toGradedAlgebra) adj hO hP ψ.toGradedAlgebraHom).map_mul

/-- The degree-`n` component of `transportHomBackward adj hO hP ψ` is the image of the degree-`n`
component of `ψ` under the inverse hom-set bijection of `adj`. -/
@[simp]
theorem transportHomBackward_f (ψ : B ⟶ transport G hO hP A) (n : ℤ) :
    (transportHomBackward adj hO hP ψ).toHomologicalComplex.f n =
      (adj.homEquiv (B.complex.X n) (A.complex.X n)).symm (ψ.toHomologicalComplex.f n) :=
  rfl

/-- **Homomorphisms of sheaves of differential graded algebras out of `L(B)` correspond
bijectively to homomorphisms into `G(A)`.** Degreewise the bijection is the hom-set bijection of
the adjunction on sheaves of modules; its content is that it matches both the multiplicativity
and the commutation with the differential on the two sides. -/
noncomputable def transportHomEquiv (A : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp))
    (B : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)) :
    (transport L hP hO B ⟶ A) ≃ (B ⟶ transport G hO hP A) where
  toFun := transportHomForward adj hO hP
  invFun := transportHomBackward adj hO hP
  left_inv φ := Hom.ext fun n ↦ by
    simp only [transportHomBackward_f, transportHomForward_f]
    exact (adj.homEquiv (B.complex.X n) (A.complex.X n)).symm_apply_apply
      (φ.toHomologicalComplex.f n)
  right_inv ψ := Hom.ext fun n ↦ by
    simp only [transportHomForward_f, transportHomBackward_f]
    exact (adj.homEquiv (B.complex.X n) (A.complex.X n)).apply_symm_apply
      (ψ.toHomologicalComplex.f n)

/-- **Pullback of sheaves of differential graded algebras is left adjoint to pushforward.**
This is part (3) of the functoriality of sheaves of differential graded algebras: for a morphism
of ringed topoi `(f, f♯)`, homomorphisms `f^*B ⟶ A` correspond to homomorphisms `B ⟶ f_*A`,
naturally in both arguments. The two functors are the constructions of parts (1) and (2), not
functors merely asserted to exist. -/
@[stacks 0FRG "part (3): adjunction"]
noncomputable def differentialGradedAlgebraAdjunction :
    pullbackDifferentialGradedAlgebra L hP hO ⊣ pushforwardDifferentialGradedAlgebra G hO hP :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun B A ↦ transportHomEquiv adj hO hP A B
      homEquiv_naturality_left_symm := fun β ψ ↦ Hom.ext fun n ↦ by
        simp only [comp_f, pullbackDifferentialGradedAlgebra_map_f]
        exact adj.homEquiv_naturality_left_symm (β.toHomologicalComplex.f n)
          (ψ.toHomologicalComplex.f n)
      homEquiv_naturality_right := fun φ α ↦ Hom.ext fun n ↦ by
        simp only [comp_f, pushforwardDifferentialGradedAlgebra_map_f]
        exact adj.homEquiv_naturality_right (φ.toHomologicalComplex.f n)
          (α.toHomologicalComplex.f n) }

/-- The hom-set bijection of the adjunction is the degreewise adjoint transpose. -/
theorem differentialGradedAlgebraAdjunction_homEquiv :
    (differentialGradedAlgebraAdjunction adj hO hP).homEquiv =
      fun B A ↦ transportHomEquiv adj hO hP A B :=
  Adjunction.mkOfHomEquiv_homEquiv _

end Adjunction

end DifferentialGradedAlgebra

end SheafOfModules

end
