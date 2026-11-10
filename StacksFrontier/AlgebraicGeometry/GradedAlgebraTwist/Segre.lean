module

public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic

/-!
# The degreewise tensor product of two sheaves of `ℤ`-graded algebras

Let `𝒜` and `ℬ` be sheaves of `ℤ`-graded algebras over a sheaf of commutative rings `𝒪` on a
site. Their **degreewise tensor product** `𝒜 ⊙ ℬ` is the sheaf of `ℤ`-graded algebras whose piece
of degree `n` is `𝒜_n ⊗_𝒪 ℬ_n`, with the product
`(𝒜_i ⊗ ℬ_i) ⊗ (𝒜_j ⊗ ℬ_j) ⟶ 𝒜_{i + j} ⊗ ℬ_{i + j}` given by the two products, read through the
middle-four interchange of the sheaf tensor product: `(a ⊗ b)(a' ⊗ b') = a a' ⊗ b b'`.

For `ℬ` the Laurent algebra `⨁_n ℒ^{⊗ n}` of an invertible module this is the twist
`⨁_n 𝒜_n ⊗ ℒ^{⊗ n}` of `Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist`, whose proofs this file
follows; the algebra of Tag 02NC's clause (1), `⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`, is the degreewise tensor
product of the twists of a relative Proj with the pullback of the Laurent algebra.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.mulHomOf`: the product of a sheaf of graded
  algebras, as a morphism out of the tensor product sheaf.
* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.segre`: **the degreewise tensor product.**

## Main results

* `Stacks.AlgebraicGeometry.GradedAlgebraTwist.segre_mul_tensorSectionsAt`: the product on pure
  local sections is the product in each factor.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules
open Stacks.SheafOfModules.Invertible (tensorProductAssociator tensorProductLeftUnitor
  tensorProductRightUnitor)
open Stacks.SheafOfModules.TensorSheafification (sheafify toSheafify sheafifyAdjunction
  structureSheaf structureRingPresheaf)
open scoped TensorProduct

universe v u w

namespace Stacks.AlgebraicGeometry.GradedAlgebraTwist

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf Stacks.SheafOfModules.Tensor.sheafTensor

/-! ### The product as a morphism out of the tensor product sheaf -/

section MulHom

variable {O hO} (A : _root_.SheafOfModules.GradedAlgebra.{w, w} (structureSheaf O hO))

/-- **The product of a sheaf of graded algebras, as a morphism out of the tensor product
sheaf**: the bilinear map on sections extends uniquely over the sheafification. -/
def mulHomOf (i j : ℤ) : (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
      ((A.piece i))).obj ((A.piece j))) ⟶ A.piece (i + j) :=
  ((sheafifyAdjunction O hO).homEquiv
    ((PresheafOfModules.tensorObj (O := O) ((A.piece i).val) ((A.piece j).val)))
      (A.piece (i + j))).symm
      (PresheafOfModules.ofBilinear (A.mul i j))

/-- The product morphism on the local section determined by two local sections. -/
theorem mulHomOf_app (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    (mulHomOf A i j).val.app U (tensorSectionsAt O hO U (A.piece i) (A.piece j) x y) =
      (A.mul i j).app U x y :=
  (congrArg
      (fun φ => φ.app U (ptmul O hO (A.piece i).val (A.piece j).val U x y))
      (((sheafifyAdjunction O hO).homEquiv
        ((PresheafOfModules.tensorObj (O := O) ((A.piece i).val) ((A.piece j).val)))
          (A.piece (i + j))).apply_symm_apply
          (PresheafOfModules.ofBilinear (A.mul i j)))).trans
    (PresheafOfModules.ofBilinear_tmul (A.mul i j) U x y)

end MulHom

/-! ### The degreewise tensor product -/

section Segre

variable {O hO} (A B : _root_.SheafOfModules.GradedAlgebra.{w, w} (structureSheaf O hO))

/-- The piece of degree `n` of the degreewise tensor product. -/
abbrev segrePiece (n : ℤ) : _root_.SheafOfModules.{w} (structureSheaf O hO) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
      ((A.piece n))).obj ((B.piece n)))

/-- **The product of the degreewise tensor product**, as a morphism of sheaves of modules: the
middle-four interchange followed by the two products. -/
def segreMulMor (i j : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((segrePiece A B i))).obj ((segrePiece A B j))) ⟶ segrePiece A B (i + j) :=
  (interchange O hO (A.piece i) (B.piece i) (A.piece j) (B.piece j)).hom ≫
    tensorMap O hO (mulHomOf A i j) (mulHomOf B i j)

/-- The product of the degreewise tensor product, on local sections. -/
def segreMulSection (i j : ℤ) (U : Cᵒᵖ) (a : (segrePiece A B i).val.obj U)
    (b : (segrePiece A B j).val.obj U) : (segrePiece A B (i + j)).val.obj U :=
  (segreMulMor A B i j).val.app U
    (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) a b)

/-- **The product on pure local sections is the product in each factor.** -/
theorem segreMulMor_app_pure (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (s : (B.piece i).val.obj U) (y : (A.piece j).val.obj U) (t : (B.piece j).val.obj U) :
    (segreMulMor A B i j).val.app U
        (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j)
          (tensorSectionsAt O hO U (A.piece i) (B.piece i) x s)
          (tensorSectionsAt O hO U (A.piece j) (B.piece j) y t)) =
      tensorSectionsAt O hO U (A.piece (i + j)) (B.piece (i + j))
        ((A.mul i j).app U x y) ((B.mul i j).app U s t) := by
  change (tensorMap O hO (mulHomOf A i j) (mulHomOf B i j)).val.app U
    ((interchange O hO (A.piece i) (B.piece i) (A.piece j) (B.piece j)).hom.val.app U
      (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j)
        (tensorSectionsAt O hO U (A.piece i) (B.piece i) x s)
        (tensorSectionsAt O hO U (A.piece j) (B.piece j) y t))) = _
  rw [interchange_pure, tensorMap_app, mulHomOf_app, mulHomOf_app]

/-- Reindexing the pieces of the degreewise tensor product along an equality of degrees. -/
def segreReindex {i j : ℤ} (hij : i = j) : segrePiece A B i ≅ segrePiece A B j := by
  subst hij
  exact Iso.refl _

theorem heq_segreReindex (U : Cᵒᵖ) {i j : ℤ} (hij : i = j)
    (x : (segrePiece A B i).val.obj U) :
    HEq ((segreReindex A B hij).hom.val.app U x) x := by
  cases hij
  exact HEq.refl _

theorem eq_segreReindex_of_heq (U : Cᵒᵖ) {i j : ℤ} (hij : i = j)
    (p : (segrePiece A B j).val.obj U) (q : (segrePiece A B i).val.obj U) (h : HEq p q) :
    p = (segreReindex A B hij).hom.val.app U q :=
  eq_of_heq (h.trans (heq_segreReindex A B U hij q).symm)

theorem heq_tensorSectionsAt_segre (U : Cᵒᵖ) {i j : ℤ} (hij : i = j)
    {x : (A.piece i).val.obj U} {x' : (A.piece j).val.obj U} (hx : HEq x x')
    {s : (B.piece i).val.obj U} {s' : (B.piece j).val.obj U} (hs : HEq s s') :
    HEq (tensorSectionsAt O hO U (A.piece i) (B.piece i) x s)
      (tensorSectionsAt O hO U (A.piece j) (B.piece j) x' s') := by
  subst hij
  rw [eq_of_heq hx, eq_of_heq hs]

/-- Pure tensors of `HEq` sections correspond under the reindexing `segreReindex`. -/
private theorem tensorSectionsAt_eq_segreReindex (U : Cᵒᵖ) {i j : ℤ} (hji : j = i)
    {x : (A.piece i).val.obj U} {x' : (A.piece j).val.obj U} (hx : HEq x x')
    {s : (B.piece i).val.obj U} {s' : (B.piece j).val.obj U} (hs : HEq s s') :
    tensorSectionsAt O hO U (A.piece i) (B.piece i) x s =
      (segreReindex A B hji).hom.val.app U
        (tensorSectionsAt O hO U (A.piece j) (B.piece j) x' s') :=
  eq_segreReindex_of_heq A B U hji _ _ (heq_tensorSectionsAt_segre A B U hji.symm hx hs)

/-- The unit of the degreewise tensor product, on local sections. -/
def segreOneSec (U : Cᵒᵖ) : (segrePiece A B 0).val.obj U :=
  tensorSectionsAt O hO U (A.piece 0) (B.piece 0) (A.one.eval U) (B.one.eval U)

theorem segreOneSec_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    (segrePiece A B 0).val.map f (segreOneSec A B U) = segreOneSec A B V := by
  rw [segreOneSec, segreOneSec, tensorSectionsAt_naturality]
  congr 1
  · exact A.one.property f
  · exact B.one.property f

/-- The unit of the degreewise tensor product, as a global section. -/
def segreOne : (segrePiece A B 0).sections :=
  ⟨fun U => segreOneSec A B U, fun f => segreOneSec_naturality A B f⟩

/-- Inserting the unit on the left, as a morphism. -/
def segreInsertOneLeft (i : ℤ) :
    segrePiece A B i ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((segrePiece A B 0))).obj ((segrePiece A B i))) :=
  (tensorProductLeftUnitor O hO (segrePiece A B i)).inv ≫
    tensorMap O hO ((segrePiece A B 0).unitHomEquiv.symm (segreOne A B)) (𝟙 _)

/-- Inserting the unit on the right, as a morphism. -/
def segreInsertOneRight (i : ℤ) :
    segrePiece A B i ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((segrePiece A B i))).obj ((segrePiece A B 0))) :=
  (tensorProductRightUnitor O hO (segrePiece A B i)).inv ≫
    tensorMap O hO (𝟙 _) ((segrePiece A B 0).unitHomEquiv.symm (segreOne A B))

theorem unitHomEquiv_symm_segreOne_app (U : Cᵒᵖ) :
    ((segrePiece A B 0).unitHomEquiv.symm (segreOne A B)).val.app U (unitSection O hO U) =
      segreOneSec A B U := by
  have h := congrArg (fun σ : (segrePiece A B 0).sections => σ.val U)
    ((segrePiece A B 0).unitHomEquiv.apply_symm_apply (segreOne A B))
  exact h

theorem segreInsertOneLeft_app (i : ℤ) (U : Cᵒᵖ) (m : (segrePiece A B i).val.obj U) :
    (segreInsertOneLeft A B i).val.app U m =
      tensorSectionsAt O hO U (segrePiece A B 0) (segrePiece A B i) (segreOneSec A B U) m := by
  change (tensorMap O hO ((segrePiece A B 0).unitHomEquiv.symm (segreOne A B))
      (𝟙 (segrePiece A B i))).val.app U
    ((tensorProductLeftUnitor O hO (segrePiece A B i)).inv.val.app U m) = _
  rw [tensorSections_leftUnitorInvAt, tensorMap_app, id_app, unitHomEquiv_symm_segreOne_app]

theorem segreInsertOneRight_app (i : ℤ) (U : Cᵒᵖ) (m : (segrePiece A B i).val.obj U) :
    (segreInsertOneRight A B i).val.app U m =
      tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B 0) m (segreOneSec A B U) := by
  change (tensorMap O hO (𝟙 (segrePiece A B i))
      ((segrePiece A B 0).unitHomEquiv.symm (segreOne A B))).val.app U
    ((tensorProductRightUnitor O hO (segrePiece A B i)).inv.val.app U m) = _
  rw [tensorSections_rightUnitorInvAt, tensorMap_app, id_app, unitHomEquiv_symm_segreOne_app]

theorem segreMulMor_assoc (i j k : ℤ) :
    tensorMap O hO (segreMulMor A B i j) (𝟙 (segrePiece A B k)) ≫ segreMulMor A B (i + j) k =
      (tensorProductAssociator O hO (segrePiece A B i) (segrePiece A B j)
          (segrePiece A B k)).hom ≫
        tensorMap O hO (𝟙 (segrePiece A B i)) (segreMulMor A B j k) ≫
        segreMulMor A B i (j + k) ≫ (segreReindex A B (Int.add_assoc i j k).symm).hom := by
  refine hom_ext_tensor3 O hO (fun U x s y t z u => ?_)
  simp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [tensorMap_app, id_app, segreMulMor_app_pure, segreMulMor_app_pure,
    tensorSections_associatorAt, tensorMap_app, id_app, segreMulMor_app_pure,
    segreMulMor_app_pure]
  exact tensorSectionsAt_eq_segreReindex A B U _ (A.mul_assoc i j k U x y z)
    (B.mul_assoc i j k U s t u)

theorem segreMulMor_one_mul (i : ℤ) :
    segreInsertOneLeft A B i ≫ segreMulMor A B 0 i =
      (segreReindex A B (Int.zero_add i).symm).hom := by
  refine hom_ext_tensor O hO (fun U x s => ?_)
  simp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [segreInsertOneLeft_app, segreOneSec, segreMulMor_app_pure]
  exact tensorSectionsAt_eq_segreReindex A B U _ (A.one_mul i U x) (B.one_mul i U s)

theorem segreMulMor_mul_one (i : ℤ) :
    segreInsertOneRight A B i ≫ segreMulMor A B i 0 =
      (segreReindex A B (Int.add_zero i).symm).hom := by
  refine hom_ext_tensor O hO (fun U x s => ?_)
  simp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [segreInsertOneRight_app, segreOneSec, segreMulMor_app_pure]
  exact tensorSectionsAt_eq_segreReindex A B U _ (A.mul_one i U x) (B.mul_one i U s)

theorem segreMulSection_add_left (i j : ℤ) (U : Cᵒᵖ) (a a' : (segrePiece A B i).val.obj U)
    (b : (segrePiece A B j).val.obj U) :
    segreMulSection A B i j U (a + a') b =
      segreMulSection A B i j U a b + segreMulSection A B i j U a' b := by
  change (segreMulMor A B i j).val.app U
    (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) (a + a') b) = _
  rw [tensorSectionsAt_add_left]
  exact map_add _ _ _

theorem segreMulSection_add_right (i j : ℤ) (U : Cᵒᵖ) (a : (segrePiece A B i).val.obj U)
    (b b' : (segrePiece A B j).val.obj U) :
    segreMulSection A B i j U a (b + b') =
      segreMulSection A B i j U a b + segreMulSection A B i j U a b' := by
  change (segreMulMor A B i j).val.app U
    (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) a (b + b')) = _
  rw [tensorSectionsAt_add_right]
  exact map_add _ _ _

theorem segreMulSection_smul_left (i j : ℤ) (U : Cᵒᵖ) (r : (structureSheaf O hO).obj.obj U)
    (a : (segrePiece A B i).val.obj U) (b : (segrePiece A B j).val.obj U) :
    segreMulSection A B i j U (r • a) b = r • segreMulSection A B i j U a b := by
  change (segreMulMor A B i j).val.app U
    (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) (r • a) b) = _
  rw [show tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) (r • a) b =
    r • tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) a b from
      map_smul _ r (ptmul O hO (segrePiece A B i).val (segrePiece A B j).val U a b)]
  exact map_smul _ _ _

theorem segreMulSection_smul_right (i j : ℤ) (U : Cᵒᵖ) (r : (structureSheaf O hO).obj.obj U)
    (a : (segrePiece A B i).val.obj U) (b : (segrePiece A B j).val.obj U) :
    segreMulSection A B i j U a (r • b) = r • segreMulSection A B i j U a b := by
  change (segreMulMor A B i j).val.app U
    (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) a (r • b)) = _
  have hleft : tensorSectionsAt O hO U (segrePiece A B j) (segrePiece A B i) (r • b) a =
      r • tensorSectionsAt O hO U (segrePiece A B j) (segrePiece A B i) b a :=
    map_smul _ r (ptmul O hO (segrePiece A B j).val (segrePiece A B i).val U b a)
  rw [← tensorSections_braidingAt O hO U (segrePiece A B j) (segrePiece A B i) (r • b) a,
    hleft, map_smul, tensorSections_braidingAt]
  exact map_smul _ _ _

theorem segreMulSection_naturality (i j : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (segrePiece A B i).val.obj U) (b : (segrePiece A B j).val.obj U) :
    (segrePiece A B (i + j)).val.map f (segreMulSection A B i j U a b) =
      segreMulSection A B i j V ((segrePiece A B i).val.map f a)
        ((segrePiece A B j).val.map f b) := by
  change (segrePiece A B (i + j)).val.map f
      ((segreMulMor A B i j).val.app U
        (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) a b)) =
    (segreMulMor A B i j).val.app V
      (tensorSectionsAt O hO V (segrePiece A B i) (segrePiece A B j)
        ((segrePiece A B i).val.map f a) ((segrePiece A B j).val.map f b))
  rw [← tensorSectionsAt_naturality]
  exact (PresheafOfModules.naturality_apply (segreMulMor A B i j).val f _).symm

/-- **The degreewise tensor product of two sheaves of `ℤ`-graded algebras**: the piece of degree
`n` is `𝒜_n ⊗ ℬ_n`, and the product of `a ⊗ b` and `a' ⊗ b'` is `a a' ⊗ b b'`. -/
def segre : _root_.SheafOfModules.GradedAlgebra.{w, w} (structureSheaf O hO) where
  piece n := segrePiece A B n
  mul i j :=
    { app := fun U => AddMonoidHom.mk'
        (fun a => AddMonoidHom.mk' (fun b => segreMulSection A B i j U a b)
          (fun b b' => segreMulSection_add_right A B i j U a b b'))
        (fun a a' => by
          ext b
          exact segreMulSection_add_left A B i j U a a' b)
      map_smul_left := fun U r x y => segreMulSection_smul_left A B i j U r x y
      map_smul_right := fun U r x y => segreMulSection_smul_right A B i j U r x y
      naturality := fun f x y => segreMulSection_naturality A B i j f x y }
  one := segreOne A B
  mul_assoc i j k U a b c := by
    have h := congrArg
      (fun φ : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
            (((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
                ((segrePiece A B i))).obj ((segrePiece A B j)))))).obj ((segrePiece A B k))) ⟶
            segrePiece A B (i + j + k) =>
        φ.val.app U (tensorSectionsAt O hO U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
              ((segrePiece A B i))).obj ((segrePiece A B j)))) (segrePiece A B k)
          (tensorSectionsAt O hO U (segrePiece A B i) (segrePiece A B j) a b) c))
      (segreMulMor_assoc A B i j k)
    simp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at h
    rw [tensorMap_app, id_app, tensorSections_associatorAt, tensorMap_app, id_app] at h
    exact (heq_of_eq h).trans (heq_segreReindex A B U _ _)
  one_mul i U a := by
    have h := congrArg
      (fun φ : segrePiece A B i ⟶ segrePiece A B (0 + i) => φ.val.app U a)
      (segreMulMor_one_mul A B i)
    simp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at h
    rw [segreInsertOneLeft_app] at h
    exact (heq_of_eq h).trans (heq_segreReindex A B U _ a)
  mul_one i U a := by
    have h := congrArg
      (fun φ : segrePiece A B i ⟶ segrePiece A B (i + 0) => φ.val.app U a)
      (segreMulMor_mul_one A B i)
    simp only [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply] at h
    rw [segreInsertOneRight_app] at h
    exact (heq_of_eq h).trans (heq_segreReindex A B U _ a)

@[simp] theorem segre_piece (n : ℤ) :
    (segre A B).piece n = (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
        ((A.piece n))).obj ((B.piece n))) := rfl

/-- **The product of the degreewise tensor product on pure local sections.** -/
theorem segre_mul_tensorSectionsAt (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (s : (B.piece i).val.obj U) (y : (A.piece j).val.obj U) (t : (B.piece j).val.obj U) :
    ((segre A B).mul i j).app U (tensorSectionsAt O hO U (A.piece i) (B.piece i) x s)
        (tensorSectionsAt O hO U (A.piece j) (B.piece j) y t) =
      tensorSectionsAt O hO U (A.piece (i + j)) (B.piece (i + j))
        ((A.mul i j).app U x y) ((B.mul i j).app U s t) :=
  segreMulMor_app_pure A B i j U x s y t

/-- The unit of the degreewise tensor product is the tensor product of the two units. -/
theorem segre_one_eval (U : Cᵒᵖ) :
    (segre A B).one.eval U =
      tensorSectionsAt O hO U (A.piece 0) (B.piece 0) (A.one.eval U) (B.one.eval U) :=
  rfl

end Segre

end Stacks.AlgebraicGeometry.GradedAlgebraTwist

end
