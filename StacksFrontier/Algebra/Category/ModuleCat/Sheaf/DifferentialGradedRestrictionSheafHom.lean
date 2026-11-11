module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorGradedShift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorHomFunctorAdjunction

/-!
# Restriction of scalars is the internal hom out of `{}_A B_B`

Let `R` be a sheaf of rings on a site, let `φ : A ⟶ B` be a unit-preserving homomorphism of
sheaves of differential graded `R`-algebras and let `L` be a right differential graded
`B`-module. This file proves the two identities of
[Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP) involving the internal hom:

`SheafHom^dg_B({}_A B_B, L) = res_φ(L)` as right differential graded `A`-modules, and

`SheafHom^dg_B(M ⊗_A B, L) = SheafHom^dg_A(M, res_φ L)`,

the second one differentials included, which is more than the identity of graded `R`-modules
the source records.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.mulLocalHom`: a degree-`n` local section `p` of `L`
  over `U`, read as the degree-`n` local homomorphism `x ↦ p x` from `{}_A B_B` to `L`.
* `SheafOfModules.DifferentialGradedModule.mulLocalHomEquiv`: this is a bijection, with inverse
  `f ↦ f (1)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isSheafHomRestrictionObj`:
  `res_φ L` is the internal hom `SheafHom^dg_B({}_A B_B, L)`.
* `SheafOfModules.DifferentialGradedModule.isInternalHomRestrictionObjOfTensor`: an internal hom
  `SheafHom^dg_B(T, L)` out of a tensor product `T = M ⊗_A {}_A B_B` is the internal hom
  `SheafHom^dg_A(M, res_φ L)`.

## Implementation notes

The internal hom is pinned by its sections, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedInternalHom.lean`: the
structures `SheafOfModules.IsInternalHom` and `SheafOfModules.IsSheafHom` say that a given
module *is* the internal hom. The first identity is therefore the construction of an
`IsSheafHom` for `res_φ L`, and the second is the tensor-hom identity
`SheafOfModules.isInternalHom_tensor` of [Stacks, Tag 0FRS] applied to it.

## References

* [Stacks Project, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)
* [Stacks Project, Tag 0FRN](https://stacks.math.columbia.edu/tag/0FRN)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a m s v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R} (φ : A ⟶ B) (hφ : φ.PreservesOne)
  (L : DifferentialGradedModule.{t, a, m} B)

/-- The restriction of a local section over `U` to an object `V` of the slice site over `U`. -/
def sectionOver (X : SheafOfModules.{s} R) {U : C} (V : Over U)
    (p : X.val.obj (Opposite.op U)) : X.val.obj (Opposite.op V.left) :=
  X.val.map V.hom.op p

/-- Restricting a restricted local section along a morphism of the slice site. -/
theorem sectionOver_naturality (X : SheafOfModules.{s} R) {U : C} {V W : Over U} (g : W ⟶ V)
    (p : X.val.obj (Opposite.op U)) :
    X.val.map g.left.op (sectionOver X V p) = sectionOver X W p := by
  unfold sectionOver
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]

/-- Restriction to the identity object of the slice site does not move a local section. -/
theorem sectionOver_mk_id (X : SheafOfModules.{s} R) {U : C} (p : X.val.obj (Opposite.op U)) :
    sectionOver X (Over.mk (𝟙 U)) p = p :=
  map_over_id_sections X U p

/-- Restricting a section restricted along `g : U' ⟶ U` to `V` over `U'` is restricting it to
`V` viewed over `U`. -/
theorem sectionOver_map (X : SheafOfModules.{s} R) {U U' : C} (g : U' ⟶ U) (V : Over U')
    (p : X.val.obj (Opposite.op U)) :
    sectionOver X V (X.val.map g.op p) = sectionOver X (Over.mk (V.hom ≫ g)) p := by
  unfold sectionOver
  rw [← PresheafOfModules.map_comp_apply, ← op_comp]
  rfl

/-- Restriction of local sections is additive. -/
theorem sectionOver_add (X : SheafOfModules.{s} R) {U : C} (V : Over U)
    (p q : X.val.obj (Opposite.op U)) :
    sectionOver X V (p + q) = sectionOver X V p + sectionOver X V q :=
  map_add _ p q

/-- Restriction of local sections is semilinear over the restriction of the sheaf of rings. -/
theorem sectionOver_smul (X : SheafOfModules.{s} R) {U : C} (V : Over U)
    (r : R.obj.obj (Opposite.op U)) (p : X.val.obj (Opposite.op U)) :
    sectionOver X V (r • p) = R.obj.map V.hom.op r • sectionOver X V p :=
  PresheafOfModules.map_smul _ _ _ _

/-- Restriction of local sections commutes with a morphism of sheaves of modules. -/
theorem sectionOver_hom {X Y : SheafOfModules.{s} R} (f : X ⟶ Y) {U : C} (V : Over U)
    (p : X.val.obj (Opposite.op U)) :
    sectionOver Y V (f.val.app (Opposite.op U) p) = f.val.app (Opposite.op V.left)
      (sectionOver X V p) :=
  homSections_naturality f V.hom.op p

/-- Restriction of local sections commutes with the right action of `B` on `L`. -/
theorem sectionOver_mul {n i : ℤ} {U : C} (V : Over U)
    (p : (L.complex.X n).val.obj (Opposite.op U)) (b : (B.complex.X i).val.obj (Opposite.op U)) :
    sectionOver (L.complex.X (n + i)) V ((L.mul n i).app (Opposite.op U) p b) =
      (L.mul n i).app (Opposite.op V.left) (sectionOver (L.complex.X n) V p)
        (sectionOver (B.complex.X i) V b) :=
  (L.mul n i).naturality V.hom.op p b

/-- A degree-`n` local section `p` of `L` over `U`, read as the degree-`n` local homomorphism
`x ↦ p x` from the bimodule `{}_A B_B`, viewed as a right differential graded `B`-module, to
`L`. -/
def mulLocalHom {n : ℤ} {U : C} (p : (L.complex.X n).val.obj (Opposite.op U)) :
    LocalHom (φ.toBimodule hφ).toRightModule L n U where
  app i j hij V := (castHom L.complex.X (show n + i = j by omega) (Opposite.op V.left)).comp
    ((L.mul n i).app (Opposite.op V.left) (sectionOver (L.complex.X n) V p))
  map_smul i j hij V r x :=
    (congrArg (castHom L.complex.X (show n + i = j by omega) (Opposite.op V.left))
      ((L.mul n i).map_smul_right _ r _ x)).trans (castHom_smul _ _ _ _ _)
  naturality i j hij {V W} g x :=
    (castHom_naturality L.complex.X _ g.left.op _).trans
      (congrArg (castHom L.complex.X (show n + i = j by omega) (Opposite.op W.left))
        (((L.mul n i).naturality g.left.op (sectionOver (L.complex.X n) V p) x).trans
          (congrArg (fun y => (L.mul n i).app (Opposite.op W.left) y
            ((B.complex.X i).val.map g.left.op x)) (sectionOver_naturality _ g p))))
  isLinear i j hij q V x b :=
    (castHom_heq L.complex.X _ _ _
      (L.mul_assoc n i q (Opposite.op V.left) (sectionOver (L.complex.X n) V p) x b).symm).trans
      (mul_app_castHom L (show n + i = j by omega) q (Opposite.op V.left) _ b).symm

/-- The value of `mulLocalHom` on a local section `x` is `p x`. -/
theorem mulLocalHom_app {n : ℤ} {U : C} (p : (L.complex.X n).val.obj (Opposite.op U))
    (i j : ℤ) (hij : i + n = j) (V : Over U)
    (x : ((φ.toBimodule hφ).complex.X i).val.obj (Opposite.op V.left)) :
    (mulLocalHom φ hφ L p).app i j hij V x =
      castHom L.complex.X (show n + i = j by omega) (Opposite.op V.left)
        ((L.mul n i).app (Opposite.op V.left) (sectionOver (L.complex.X n) V p) x) :=
  rfl

/-- The unit of `B`, as a local section of `{}_A B_B` over the identity object of the slice
site over `U`. -/
def oneOver (U : C) :
    ((φ.toBimodule hφ).toRightModule.complex.X 0).val.obj (Opposite.op (Over.mk (𝟙 U)).left) :=
  B.one.eval (Opposite.op U)

/-- A degree-`n` local homomorphism `f` from `{}_A B_B` to `L` over `U` is multiplication by
its value `f (1)` at the unit. -/
theorem mulLocalHom_app_one {n : ℤ} {U : C}
    (f : LocalHom (φ.toBimodule hφ).toRightModule L n U) (i j : ℤ) (hij : i + n = j)
    (V : Over U) (x : ((φ.toBimodule hφ).complex.X i).val.obj (Opposite.op V.left)) :
    (mulLocalHom φ hφ L
        (f.app 0 n (zero_add n) (Over.mk (𝟙 U)) (oneOver φ hφ U))).app i j hij V x =
      f.app i j hij V x := by
  have h1 : sectionOver (L.complex.X n) V
      (f.app 0 n (zero_add n) (Over.mk (𝟙 U)) (oneOver φ hφ U)) =
      f.app 0 n (zero_add n) V (B.one.eval (Opposite.op V.left)) :=
    (f.naturality 0 n (zero_add n) (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U))
      (oneOver φ hφ U)).trans
      (congrArg (f.app 0 n (zero_add n) V) (PresheafOfModules.sections_property B.one V.hom.op))
  rw [mulLocalHom_app, h1]
  refine (congrArg (castHom L.complex.X (show n + i = j by omega) (Opposite.op V.left))
    (f.isLinear 0 n (zero_add n) i V (B.one.eval (Opposite.op V.left)) x).symm).trans ?_
  refine (f.toLocalGradedHom.app_castHom_target (show n + i = j by omega) (by omega)
    (by omega) V _).symm.trans ?_
  exact f.toLocalGradedHom.app_heq_congr (zero_add i) _ hij V (B.one_mul i _ x)

/-- **Sections of `L` are the local homomorphisms out of `{}_A B_B`**: a degree-`n` local section
`p` of `L` over `U` corresponds to multiplication `x ↦ p x`, with inverse `f ↦ f (1)`. -/
def mulLocalHomEquiv (n : ℤ) (U : C) :
    (L.complex.X n).val.obj (Opposite.op U) ≃ LocalHom (φ.toBimodule hφ).toRightModule L n U where
  toFun p := mulLocalHom φ hφ L p
  invFun f := f.app 0 n (zero_add n) (Over.mk (𝟙 U)) (oneOver φ hφ U)
  left_inv p := by
    change castHom L.complex.X (show n + 0 = n by omega) (Opposite.op U)
      ((L.mul n 0).app (Opposite.op U) (sectionOver (L.complex.X n) (Over.mk (𝟙 U)) p)
        (B.one.eval (Opposite.op U))) = p
    rw [sectionOver_mk_id]
    exact eq_of_heq ((heq_castHom L.complex.X _ _ _).trans (L.mul_one n _ p))
  right_inv f := LocalHom.ext fun i j hij V x => mulLocalHom_app_one φ hφ L f i j hij V x

/-- The differential of `mulLocalHom`: the local homomorphism named by `d p` is the differential
`x ↦ d (p x) - (-1)^n p (d x)` of the local homomorphism named by `p`. -/
theorem localDiffApp_mulLocalHom {n : ℤ} {U : C} (p : (L.complex.X n).val.obj (Opposite.op U))
    (m i j : ℤ) (hij : i + m = j) (V : Over U)
    (x : ((φ.toBimodule hφ).complex.X i).val.obj (Opposite.op V.left)) :
    (mulLocalHom φ hφ L ((L.complex.d n m).val.app (Opposite.op U) p)).app i j hij V x =
      localDiffApp (mulLocalHom φ hφ L p).toLocalGradedHom m i j hij V x := by
  unfold localDiffApp
  rw [mulLocalHom_app, mulLocalHom_app, mulLocalHom_app, sectionOver_hom]
  by_cases hm : n + 1 = m
  · subst hm
    have hl := L.leibniz n i (Opposite.op V.left) (sectionOver (L.complex.X n) V p) x
    have e1 : ∀ (a b : ℤ) (ha : n + i = a) (hb : n + i + 1 = b)
        (y : (L.complex.X (n + i)).val.obj (Opposite.op V.left)),
        (L.complex.d a b).val.app (Opposite.op V.left)
          (castHom L.complex.X ha (Opposite.op V.left) y) =
        castHom L.complex.X hb (Opposite.op V.left)
          ((L.complex.d (n + i) (n + i + 1)).val.app (Opposite.op V.left) y) := by
      intro a b ha hb y
      subst ha hb
      rfl
    have e2 : ∀ (k : ℤ) (hk : i + 1 = k),
        HEq ((L.mul n k).app (Opposite.op V.left) (sectionOver (L.complex.X n) V p)
          ((B.complex.d i k).val.app (Opposite.op V.left) x))
        ((L.mul n (i + 1)).app (Opposite.op V.left) (sectionOver (L.complex.X n) V p)
          ((B.complex.d i (i + 1)).val.app (Opposite.op V.left) x)) := by
      intro k hk
      subst hk
      rfl
    have e3 := castHom_heq L.complex.X (show n + (i + (n + 1) - n) = j by omega)
      (show n + (i + 1) = j by omega) (Opposite.op V.left) (e2 _ (by omega))
    change _ = _ + _ • castHom L.complex.X (show n + (i + (n + 1) - n) = j by omega) _
      ((L.mul n (i + (n + 1) - n)).app _ (sectionOver (L.complex.X n) V p)
        ((B.complex.d i (i + (n + 1) - n)).val.app _ x))
    rw [e3, e1 _ _ _ (show n + i + 1 = j by omega), hl, map_add, castHom_zsmul,
      ← castHom_apply, ← castHom_apply, castHom_castHom, castHom_castHom,
      Int.negOnePow_succ, Units.val_neg, neg_smul]
    abel
  · have h1 : ¬ (ComplexShape.up ℤ).Rel n m := by simpa using hm
    have h2 : ¬ (ComplexShape.up ℤ).Rel (i + n) j := by simp; omega
    have h3 : ¬ (ComplexShape.up ℤ).Rel i (i + m - n) := by simp; omega
    rw [L.complex.shape n m h1, L.complex.shape (i + n) j h2]
    change castHom L.complex.X _ _ ((L.mul m i).app _ (0 : (L.complex.X m).val.obj _) x) =
      0 + _ • castHom L.complex.X _ _ ((L.mul n (i + m - n)).app _ _
        ((B.complex.d i (i + m - n)).val.app _ x))
    rw [B.complex.shape i (i + m - n) h3]
    change castHom L.complex.X _ _ ((L.mul m i).app _ 0 x) =
      0 + _ • castHom L.complex.X _ _ ((L.mul n (i + m - n)).app _ _ 0)
    simp only [map_zero, smul_zero, add_zero]
    exact map_zero (castHom L.complex.X _ (Opposite.op V.left))

/-- **`SheafHom^dg_B({}_A B_B, L) = res_φ(L)` as complexes**: the underlying complex of `L` is the
internal hom out of the bimodule `{}_A B_B`, a section `p` naming `x ↦ p x`. -/
def isInternalHomComplex :
    IsInternalHom (φ.toBimodule hφ).toRightModule L L.complex where
  sectionsEquiv n U := mulLocalHomEquiv φ hφ L n U
  sectionsEquiv_add n U p q i j hij V x := by
    change (mulLocalHom φ hφ L (p + q)).app i j hij V x =
      (mulLocalHom φ hφ L p).app i j hij V x + (mulLocalHom φ hφ L q).app i j hij V x
    rw [mulLocalHom_app, mulLocalHom_app, mulLocalHom_app, sectionOver_add, map_add]
    exact map_add (castHom L.complex.X _ (Opposite.op V.left)) _ _
  sectionsEquiv_smul n U r p i j hij V x := by
    change (mulLocalHom φ hφ L (r • p)).app i j hij V x =
      R.obj.map V.hom.op r • (mulLocalHom φ hφ L p).app i j hij V x
    rw [mulLocalHom_app, mulLocalHom_app, sectionOver_smul]
    exact (congrArg (castHom L.complex.X _ (Opposite.op V.left))
      ((L.mul n i).map_smul_left _ _ _ x)).trans (castHom_smul _ _ _ _ _)
  sectionsEquiv_naturality n U U' g p i j hij V := by
    change (mulLocalHom φ hφ L (n := n) (U := U') ((L.complex.X n).val.map g.op p)).app
        i j hij V = (mulLocalHom φ hφ L p).app i j hij (Over.mk (V.hom ≫ g))
    ext x
    exact congrArg (fun y => castHom L.complex.X (show n + i = j by omega) (Opposite.op V.left)
      ((L.mul n i).app (Opposite.op V.left) y x)) (sectionOver_map (L.complex.X n) g V p)
  sectionsEquiv_d n m U p i j hij V x := localDiffApp_mulLocalHom φ hφ L p m i j hij V x

/-- **`SheafHom^dg_B({}_A B_B, L) = res_φ(L)` as right differential graded `A`-modules**
([Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)): the restriction `res_φ L` is
the internal hom out of the bimodule `{}_A B_B`, with its right `A`-module structure by
precomposition with the left action of `A` on `{}_A B_B`. -/
@[stacks 0FRP "SheafHom^dg_B(_A B_B, L) = res_φ(L) as right differential graded A-modules"]
def isSheafHomRestrictionObj :
    IsSheafHom (φ.toBimodule hφ) L (restrictionObj φ hφ L) where
  isInternalHom := isInternalHomComplex φ hφ L
  mul_spec n p U q b i j hij V x := by
    change castHom L.complex.X _ (Opposite.op V.left) ((L.mul (n + p) i).app _
        (sectionOver (L.complex.X (n + p)) V ((L.mul n p).app (Opposite.op U) q
          ((φ.toHomologicalComplex.f p).val.app (Opposite.op U) b))) x) =
      castHom L.complex.X _ (Opposite.op V.left) ((L.mul n (p + i)).app _
        (sectionOver (L.complex.X n) V q) ((B.mul p i).app _
          ((φ.toHomologicalComplex.f p).val.app (Opposite.op V.left)
            ((A.complex.X p).val.map V.hom.op b)) x))
    exact (congrArg (fun y => castHom L.complex.X (show n + p + i = j by omega)
        (Opposite.op V.left) ((L.mul (n + p) i).app (Opposite.op V.left) y x))
      ((sectionOver_mul L V q _).trans
        (congrArg ((L.mul n p).app (Opposite.op V.left) (sectionOver (L.complex.X n) V q))
          (sectionOver_hom (φ.toHomologicalComplex.f p) V b)))).trans
      (castHom_heq L.complex.X _ _ _ (L.mul_assoc n p i _ _ _ _))

/-- **`SheafHom^dg_B(M ⊗_A B, L) = SheafHom^dg_A(M, res_φ L)`**
([Stacks, Tag 0FRP](https://stacks.math.columbia.edu/tag/0FRP)): for a right differential
graded `A`-module `M`, a tensor product `T = M ⊗_{A, φ} B` with the bimodule `{}_A B_B` and a
complex `G` which is the internal hom `SheafHom^dg_B(T, L)`, the complex `G` is also the
internal hom `SheafHom^dg_A(M, res_φ L)`, differentials included. -/
@[stacks 0FRP "SheafHom^dg_B(M ⊗_A B, L) = SheafHom^dg_A(M, res_φ L)"]
def isInternalHomRestrictionObjOfTensor {M : DifferentialGradedModule.{t, a, m} A}
    {T : DifferentialGradedModule.{t, a, m} B} (hT : IsTensorProduct M (φ.toBimodule hφ) T)
    {G : CochainComplex (SheafOfModules.{s} R) ℤ} (hG : IsInternalHom T L G) :
    IsInternalHom M (restrictionObj φ hφ L) G :=
  isInternalHom_tensor hT (isSheafHomRestrictionObj φ hφ L) hG

end DifferentialGradedModule

end SheafOfModules
