module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone

/-!
# Maps out of a cone, and the graded shift down by one

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of differential graded `R`-algebras and
let `f : K ⟶ L` be a morphism of right differential graded `A`-modules. This file describes the
homomorphisms out of the cone of `f` in terms of their two coordinates, and introduces the graded
module obtained from a differential graded module by moving every piece down one degree.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.gradedShiftDown` is the graded module whose degree-`n`
  piece is the degree-`n - 1` piece of a differential graded module, with the action transported
  along `(n - 1) + i = (n + i) - 1`.
* `SheafOfModules.DifferentialGradedModule.ConePackage.desc` is the homomorphism out of the cone
  of `f` determined by a homomorphism `β : L ⟶ N` together with a degreewise family
  `α n : K^{n+1} ⟶ N^n` which is right `A`-linear and which is a null-homotopy of `f ≫ β`.

## Main results

* `SheafOfModules.DifferentialGradedModule.ConePackage.inclusion_desc`: the composite of the
  canonical inclusion with `ConePackage.desc` is the homomorphism it was built from.
* `SheafOfModules.DifferentialGradedModule.ConePackage.desc_f`: in degree `n` the homomorphism
  `ConePackage.desc` is the degreewise splitting of the cone followed by `biprod.desc` of its two
  coordinates.
* `SheafOfModules.DifferentialGradedModule.gradedShiftDown_piece` and
  `SheafOfModules.DifferentialGradedModule.gradedShiftDown_smul_heq` identify the pieces and the
  action of the shift down by one.

## Implementation notes

The underlying map of complexes of `ConePackage.desc` is Mathlib's
`CochainComplex.mappingCone.desc` for the degree `-1` cochain assembled from the family `α`,
transported along the equality `ConePackage.cone_complex` between the complex of the cone and
Mathlib's mapping cone. The hypothesis `hδ` is the degreewise form of the cocycle condition
`δ (-1) 0 α = Cochain.ofHom (f ≫ β)` required by `CochainComplex.mappingCone.desc`: expanding it
with `CochainComplex.HomComplex.δ_v` at `n = -1`, `m = 0` and `p = q = n + 1` produces the two
terms `α n ≫ d` and `d ≫ α (n + 1)`, the second with the sign `(0 : ℤ).negOnePow = 1`.

The compatibility `hα` of the family `α` with the right action is stated with
`SheafOfModules.gradedCast` because the two degrees `(n + 1) + i` and `(n + i) + 1` are
propositionally but not definitionally equal; this matches the `HEq` of `ConePackage.action_first`
from which it is used.

The degrees appearing on the two sides of the module laws of `gradedShiftDown` are again only
propositionally equal, so those laws are proved by transporting the laws of the given module
along `SheafOfModules.gradedCast`, exactly as for the degree-one shift. The transport
`SheafOfModules.DifferentialGradedModule.castBilinearMap` of a bilinear map along an equality of
its target, and its two evaluation lemmas, are the ones of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedCone.lean`, where the degree-one
shift already uses them.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### The graded module shifted down by one -/

/-- The right action of the shift down by one: the action of the given module in degree `n - 1`,
transported along `(n - 1) + i = (n + i) - 1`. -/
noncomputable def shiftDownMul {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) :
    BilinearMap (M.complex.X (n - 1)) (A.complex.X i) (M.complex.X ((n + i) - 1)) :=
  castBilinearMap (congrArg M.complex.X (show (n - 1) + i = (n + i) - 1 by omega))
    (M.mul (n - 1) i)

/-- **The graded module underlying a differential graded module, shifted down by one.** Its
degree-`n` piece is the degree-`n - 1` piece of the given module, and its action is the action of
the given module transported along `(n - 1) + i = (n + i) - 1`. -/
noncomputable def gradedShiftDown {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) :
    GradedModule.{t, a, m} A.toGradedAlgebra where
  piece n := M.complex.X (n - 1)
  smul n i U := (shiftDownMul M n i).app U
  smul_smul_left n i U r x y := (shiftDownMul M n i).map_smul_left U r x y
  smul_smul_right n i U r x y := (shiftDownMul M n i).map_smul_right U r x y
  smul_naturality n i _U _V g x y := (shiftDownMul M n i).naturality g x y
  smul_mul n i j U x a b := by
    have hInner := castBilinearMap_eval_heq
      (congrArg M.complex.X (show (n - 1) + i = (n + i) - 1 by omega)) (M.mul (n - 1) i) U x a
    have hOuter := castBilinearMap_eval_heq
      (congrArg M.complex.X (show ((n + i) - 1) + j = ((n + i) + j) - 1 by omega))
      (M.mul ((n + i) - 1) j) U ((shiftDownMul M n i).app U x a) b
    have hRight := castBilinearMap_eval_heq
      (congrArg M.complex.X (show (n - 1) + (i + j) = (n + (i + j)) - 1 by omega))
      (M.mul (n - 1) (i + j)) U x ((A.mul i j).app U a b)
    have hMiddle := heq_dependent_apply
      (fun d : ℤ => fun y : (M.complex.X d).val.obj U => ((M.mul d j).app U y) b)
      (show (n + i) - 1 = (n - 1) + i by omega) hInner
    exact hOuter.trans (hMiddle.trans ((M.mul_assoc (n - 1) i j U x a b).trans hRight.symm))
  smul_one n U x :=
    (castBilinearMap_eval_heq
      (congrArg M.complex.X (show (n - 1) + 0 = (n + 0) - 1 by omega))
      (M.mul (n - 1) 0) U x (A.one.eval U)).trans (M.mul_one (n - 1) U x)

/-- The pieces of the shift down by one. -/
@[simp] theorem gradedShiftDown_piece {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) (n : ℤ) :
    (gradedShiftDown M).piece n = M.complex.X (n - 1) := rfl

/-- The action of the shift down by one is the action of the given module in degree `n - 1`. -/
theorem gradedShiftDown_smul_heq {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ) :
    HEq ((gradedShiftDown M).smul n i U) ((M.mul (n - 1) i).app U) :=
  castBilinearMap_app_heq _ _ U

/-- The values of the action of the shift down by one. -/
theorem gradedShiftDown_smul_eval_heq {A : DifferentialGradedAlgebra.{t, a} R}
    (M : DifferentialGradedModule.{t, a, m} A) (n i : ℤ) (U : Cᵒᵖ)
    (x : (M.complex.X (n - 1)).val.obj U) (y : (A.complex.X i).val.obj U) :
    HEq ((gradedShiftDown M).smul n i U x y) ((M.mul (n - 1) i).app U x y) :=
  castBilinearMap_eval_heq _ _ U x y

/-! ### The two coordinates of the mapping cone -/

section Cone

variable {A : DifferentialGradedAlgebra.{t, a} R} {K L : DifferentialGradedModule.{t, a, m} A}

/-- The first coordinate of the splitting of the mapping cone is Mathlib's first projection. -/
theorem coneFirst_eq (f : K ⟶ L) (n : ℤ) :
    coneFirst f n =
      (CochainComplex.mappingCone.fst f.toHomologicalComplex).1.v n (n + 1) rfl := rfl

/-- The second coordinate of the splitting of the mapping cone is Mathlib's second
projection. -/
theorem coneSecond_eq_v (f : K ⟶ L) (n : ℤ) :
    coneSecond f n =
      (CochainComplex.mappingCone.snd f.toHomologicalComplex).v n n (add_zero n) := by
  rw [coneSecond_eq]
  exact (CochainComplex.HomComplex.Cochain.ofHoms_v
    (F := CochainComplex.mappingCone f.toHomologicalComplex) (G := L.complex)
    (HomologicalComplex.homotopyCofiber.sndX f.toHomologicalComplex) n).symm

end Cone

/-! ### Sections of a map into a biproduct of sheaves of modules -/

section Biprod

/-- Local sections of a composite of morphisms of sheaves of modules. -/
theorem comp_val_app {P Q Z : SheafOfModules.{m} R} (u : P ⟶ Q) (v : Q ⟶ Z) (U : Cᵒᵖ)
    (x : P.val.obj U) : (u ≫ v).val.app U x = v.val.app U (u.val.app U x) := by
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]

/-- Local sections of a sum of morphisms of sheaves of modules. -/
theorem add_val_app {P Z : SheafOfModules.{m} R} (u u' : P ⟶ Z) (U : Cᵒᵖ) (x : P.val.obj U) :
    (u + u').val.app U x = u.val.app U x + u'.val.app U x := homSections_add u u' U x

/-- Local sections of a morphism out of a binary biproduct, in terms of the two coordinates of
the section it is applied to. -/
theorem biprodDesc_val_app {P Q Z : SheafOfModules.{m} R} (u : P ⟶ Z) (v : Q ⟶ Z) (U : Cᵒᵖ)
    (z : (P ⊞ Q).val.obj U) :
    (biprod.desc u v).val.app U z =
      u.val.app U ((biprod.fst : P ⊞ Q ⟶ P).val.app U z) +
        v.val.app U ((biprod.snd : P ⊞ Q ⟶ Q).val.app U z) := by
  rw [biprod.desc_eq, add_val_app, comp_val_app, comp_val_app]

/-- Local sections of a morphism which factors through a binary biproduct, in terms of the two
coordinates of the factorisation. -/
theorem biprodDesc_comp_val_app {P Q Z W : SheafOfModules.{m} R} (e : W ⟶ P ⊞ Q) (u : P ⟶ Z)
    (v : Q ⟶ Z) (U : Cᵒᵖ) (w : W.val.obj U) :
    (e ≫ biprod.desc u v).val.app U w =
      u.val.app U ((e ≫ (biprod.fst : P ⊞ Q ⟶ P)).val.app U w) +
        v.val.app U ((e ≫ (biprod.snd : P ⊞ Q ⟶ Q)).val.app U w) := by
  rw [comp_val_app, biprodDesc_val_app, comp_val_app, comp_val_app]

end Biprod

/-! ### Transport along an equality of complexes -/

section Transport

/-- Two heterogeneously equal splittings of degree-`n` pieces differ by the transport along the
equality of the complexes they split. -/
theorem heq_iso_hom_eq {X Y : CochainComplex (SheafOfModules.{m} R) ℤ} (h : X = Y) (n : ℤ)
    {B : SheafOfModules.{m} R} (i₁ : X.X n ≅ B) (i₂ : Y.X n ≅ B) (hi : HEq i₁ i₂) :
    i₁.hom = (eqToHom h).f n ≫ i₂.hom := by
  subst h
  rw [eq_of_heq hi]
  simp

/-- A morphism heterogeneously equal to another becomes it after the transport along the
equality of the targets. -/
theorem heq_comp_eqToHom_eq {X Y Z : CochainComplex (SheafOfModules.{m} R) ℤ} (h : X = Y)
    (u : Z ⟶ X) (v : Z ⟶ Y) (hu : HEq u v) : u ≫ eqToHom h = v := by
  subst h
  rw [eq_of_heq hu]
  simp

end Transport

/-! ### The homomorphism out of a cone determined by a null-homotopy -/

section Desc

variable {A : DifferentialGradedAlgebra.{t, a} R} {K L : DifferentialGradedModule.{t, a, m} A}
  {f : K ⟶ L} (Pk : ConePackage f) {N : DifferentialGradedModule.{t, a, m} A} (β : L ⟶ N)
  (α : ∀ n : ℤ, K.complex.X (n + 1) ⟶ N.complex.X n)

/-- The degree `-1` cochain assembled from a degreewise family `α n : K^{n+1} ⟶ N^n`. -/
def coneDescCochain : CochainComplex.HomComplex.Cochain K.complex N.complex (-1) :=
  CochainComplex.HomComplex.Cochain.mk fun p q hpq =>
    eqToHom (congrArg K.complex.X (show p = q + 1 by omega)) ≫ α q

/-- The components of the cochain assembled from a degreewise family. -/
@[simp] theorem coneDescCochain_v (n : ℤ) :
    (coneDescCochain α).v (n + 1) n (by omega) = α n := by
  simp [coneDescCochain]

/-- **The cocycle condition required by Mathlib's `CochainComplex.mappingCone.desc`**, in the
degreewise form in which it is used: `α` is a null-homotopy of `f ≫ β`. -/
theorem coneDescCochain_delta
    (hδ : ∀ n : ℤ, α n ≫ N.complex.d n (n + 1)
        + K.complex.d (n + 1) ((n + 1) + 1) ≫ α (n + 1)
        = f.toHomologicalComplex.f (n + 1) ≫ β.toHomologicalComplex.f (n + 1)) :
    CochainComplex.HomComplex.δ (-1) 0 (coneDescCochain α) =
      CochainComplex.HomComplex.Cochain.ofHom
        (f.toHomologicalComplex ≫ β.toHomologicalComplex) := by
  refine CochainComplex.HomComplex.Cochain.ext₀ _ _ fun p => ?_
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, p = n + 1 := ⟨p - 1, by omega⟩
  rw [CochainComplex.HomComplex.δ_v (-1) 0 (by omega) (coneDescCochain α) (n + 1) (n + 1)
      (add_zero _) n (n + 1 + 1) (by omega) rfl,
    coneDescCochain_v, coneDescCochain_v,
    CochainComplex.HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f]
  simp only [Int.negOnePow_zero, one_smul]
  exact hδ n

namespace ConePackage

/-- The splitting recorded by a cone package, compared with the canonical splitting of Mathlib's
mapping cone. -/
theorem componentIso_hom_eq (n : ℤ) :
    (Pk.componentIso n).hom =
      (eqToHom Pk.cone_complex).f n ≫ (coneComponentIso f n).hom :=
  heq_iso_hom_eq Pk.cone_complex n _ (coneComponentIso f n) (Pk.componentIso_eq n)

variable (hα : ∀ (n i : ℤ) (U : Cᵒᵖ) (x : (K.complex.X (n + 1)).val.obj U)
    (y : (A.complex.X i).val.obj U),
  (α (n + i)).val.app U (gradedCast (fun q ↦ (K.complex.X q).val.obj U)
      (add_right_comm n 1 i) ((K.mul (n + 1) i).app U x y))
    = (N.mul n i).app U ((α n).val.app U x) y)

variable (hδ : ∀ n : ℤ, α n ≫ N.complex.d n (n + 1)
    + K.complex.d (n + 1) ((n + 1) + 1) ≫ α (n + 1)
    = f.toHomologicalComplex.f (n + 1) ≫ β.toHomologicalComplex.f (n + 1))

/-- The underlying map of complexes of `SheafOfModules.DifferentialGradedModule.ConePackage.desc`:
Mathlib's `CochainComplex.mappingCone.desc`, transported along the equality between the complex
of the cone and the mapping cone. -/
noncomputable def descComplexHom : Pk.cone.complex ⟶ N.complex :=
  eqToHom Pk.cone_complex ≫
    CochainComplex.mappingCone.desc f.toHomologicalComplex (coneDescCochain α)
      β.toHomologicalComplex (coneDescCochain_delta β α hδ)

/-- The degree-`n` component of `descComplexHom` splits as the two given coordinates. -/
theorem descComplexHom_f (n : ℤ) :
    (descComplexHom Pk β α hδ).f n =
      (Pk.componentIso n).hom ≫ biprod.desc (α n) (β.toHomologicalComplex.f n) := by
  rw [descComplexHom, HomologicalComplex.comp_f,
    CochainComplex.mappingCone.desc_f _ _ _ _ n (n + 1) rfl, ← coneFirst_eq,
    coneDescCochain_v, ← coneSecond_eq_v, componentIso_hom_eq, biprod.desc_eq]
  simp [coneFirst, coneSecond]

/-- The composite of the canonical inclusion with `descComplexHom`. -/
theorem inclusion_descComplexHom :
    Pk.inclusion.toHomologicalComplex ≫ descComplexHom Pk β α hδ =
      β.toHomologicalComplex := by
  rw [descComplexHom, ← Category.assoc,
    heq_comp_eqToHom_eq Pk.cone_complex _ _ Pk.inclusion_complex]
  exact CochainComplex.mappingCone.inr_desc _ _ _ _

/-- **The homomorphism out of the cone of `f : K ⟶ L` determined by a null-homotopy.** It is
given by a homomorphism `β : L ⟶ N` of right differential graded modules together with a
degreewise family `α n : K^{n+1} ⟶ N^n` which is compatible with the right action (`hα`) and
which is a null-homotopy of `f ≫ β` (`hδ`). -/
noncomputable def desc : Pk.cone ⟶ N where
  toHomologicalComplex := descComplexHom Pk β α hδ
  map_mul n i U x a := by
    have hF : ((Pk.componentIso (n + i)).hom ≫ biprod.fst).val.app U
          ((Pk.cone.mul n i).app U x a) =
        gradedCast (fun q ↦ (K.complex.X q).val.obj U)
          (add_right_comm n 1 i)
          ((K.mul (n + 1) i).app U
            (((Pk.componentIso n).hom ≫ biprod.fst).val.app U x) a) :=
      eq_of_heq ((Pk.action_first n i U x a).trans
        (gradedCast_heq (fun q ↦ (K.complex.X q).val.obj U) _ _).symm)
    rw [descComplexHom_f, descComplexHom_f, biprodDesc_comp_val_app,
      biprodDesc_comp_val_app, hF, hα n i U _ a, Pk.action_second n i U x a,
      β.map_mul n i U _ a, map_add, AddMonoidHom.add_apply]

/-- **The composite of the canonical inclusion with
`SheafOfModules.DifferentialGradedModule.ConePackage.desc` is the homomorphism it was built
from.** -/
theorem inclusion_desc : Pk.inclusion ≫ Pk.desc β α hα hδ = β :=
  Hom.ext fun n => congrArg (fun g => HomologicalComplex.Hom.f g n)
    (inclusion_descComplexHom Pk β α hδ)

/-- **The degree-`n` component of
`SheafOfModules.DifferentialGradedModule.ConePackage.desc`**: the degreewise splitting of the
cone followed by the map out of the biproduct given by the two coordinates. -/
theorem desc_f (n : ℤ) :
    (Pk.desc β α hα hδ).toHomologicalComplex.f n
      = (Pk.componentIso n).hom ≫ biprod.desc (α n) (β.toHomologicalComplex.f n) :=
  descComplexHom_f Pk β α hδ n

end ConePackage

end Desc

end SheafOfModules.DifferentialGradedModule

end
