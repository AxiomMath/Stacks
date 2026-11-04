module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModule

/-!
# Pullback of a left graded module along a morphism of ringed spaces

Let `f : X ⟶ Y` be a morphism of ringed spaces, `A` a sheaf of `ℤ`-graded `𝒪_Y`-algebras and
`ℳ` a left graded `A`-module in the sense of [Stacks, Tag 0FQZ]. Then `f^*ℳ` is a left graded
module over the pulled-back algebra `f^*A` of `Stacks.RingedSpace.pullbackGradedAlgebra`: the
pieces are the pullbacks of the pieces and the action is the pullback of the action, through
[Stacks, Tag 01CD].

## Main definitions

* `Stacks.RingedSpace.smulBilinear`: the action of a left graded module, in one pair of degrees,
  as a bilinear map of sheaves of modules.
* `Stacks.RingedSpace.pullbackLeftGradedModule`: the pullback of a left graded module.

## Main results

* `Stacks.RingedSpace.pullbackBilinear_assoc`: an associativity law between four bilinear maps
  pulls back.
* `Stacks.RingedSpace.pullbackBilinear_one`: a unit law pulls back.
* `Stacks.RingedSpace.pullbackLeftGradedModule_smul_pullbackUnit`: on pullback-unit images the
  pulled-back action is the pullback-unit image of the action.

## Implementation notes

The two laws, associativity of the action and the unit law, are statements about arbitrary local
sections of the pullbacks, and are proved on stalks by the generation argument of
`StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra`, here for arbitrary bilinear maps of
sheaves of modules satisfying an associativity or a unit law.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

section General

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The germ at `p` of the pulled-back value of a bilinear map on two pullback-unit images. -/
alias stalkMul_pullbackBilinear_pullbackUnit := stalkMul_pullbackBilinear_germ

/-- The transport of a germ of a pullback-unit image along an equality of the sheaves. -/
alias sheafCast_grpGerm_pullbackUnit := sheafCast_germ_pullbackUnit

/-- The germ of the global section of `f^*M` attached to a global section of `M`, at a point
lying over an open `V`, is the germ of the pullback-unit image of its value over `V`. -/
lemma grpGerm_pullbackSectionsUnit_eval (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) (p : X.carrier) (U : Opens X.carrier) (hp : p ∈ U) (V : Opens Y.carrier)
    (hx : f.hom.base p ∈ V) :
    grpGerm X ((pullbackFunctor f).obj M).val p U hp
        ((pullbackSectionsUnit f M t).eval (op U)) =
      grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
        (pullbackUnit f M (op V) (t.eval (op V))) := by
  have key : ∀ (W : Opens X.carrier) (hw : p ∈ W),
      grpGerm X ((pullbackFunctor f).obj M).val p W hw ((pullbackSectionsUnit f M t).eval (op W)) =
        grpGerm X ((pullbackFunctor f).obj M).val p ⊤ (Set.mem_univ p) (pullbackUnitTop f M t) :=
    fun W hw => TopCat.Presheaf.germ_res_apply ((pullbackFunctor f).obj M).val.presheaf
      (homOfLE (le_top : W ≤ ⊤)) p hw (pullbackUnitTop f M t)
  rw [key U hp, ← key ((opensMap f).obj V) hx]
  exact congrArg _ (pullbackSectionsUnit_eval f M t V)

variable {M₁ M₂ M₃ M₁₂ M₂₃ P P' : SheafOfModules.{u} (structureRingSheaf Y)}
  (β₁ : SheafOfModules.BilinearMap M₁ M₂ M₁₂) (β₂ : SheafOfModules.BilinearMap M₂ M₃ M₂₃)
  (β₃ : SheafOfModules.BilinearMap M₁₂ M₃ P) (β₄ : SheafOfModules.BilinearMap M₁ M₂₃ P')
  (hP : P = P')
  (hassoc : ∀ (V : Opens Y.carrier) (a : M₁.val.obj (op V)) (b : M₂.val.obj (op V))
    (c : M₃.val.obj (op V)),
    HEq (β₃.app (op V) (β₁.app (op V) a b) c) (β₄.app (op V) a (β₂.app (op V) b c)))

include hassoc in
private lemma assoc_common (p : X.carrier) (V : Opens Y.carrier) (hx : f.hom.base p ∈ V)
    (a : M₁.val.obj (op V)) (b : M₂.val.obj (op V)) (c : M₃.val.obj (op V)) :
    sheafCast (congrArg (pullbackFunctor f).obj hP) p
        (stalkMul (pullbackBilinear f β₃) p
          (stalkMul (pullbackBilinear f β₁) p
            (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj V) hx
              (pullbackUnit f M₁ (op V) a))
            (grpGerm X ((pullbackFunctor f).obj M₂).val p ((opensMap f).obj V) hx
              (pullbackUnit f M₂ (op V) b)))
          (grpGerm X ((pullbackFunctor f).obj M₃).val p ((opensMap f).obj V) hx
            (pullbackUnit f M₃ (op V) c))) =
      stalkMul (pullbackBilinear f β₄) p
        (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj V) hx
          (pullbackUnit f M₁ (op V) a))
        (stalkMul (pullbackBilinear f β₂) p
          (grpGerm X ((pullbackFunctor f).obj M₂).val p ((opensMap f).obj V) hx
            (pullbackUnit f M₂ (op V) b))
          (grpGerm X ((pullbackFunctor f).obj M₃).val p ((opensMap f).obj V) hx
            (pullbackUnit f M₃ (op V) c))) := by
  simp only [stalkMul_pullbackBilinear_pullbackUnit]
  exact sheafCast_grpGerm_pullbackUnit f hP p V hx _ _ (hassoc V a b c)

include hassoc in
private lemma assoc_gen (p : X.carrier) (Va Vb Vc : Opens Y.carrier) (ha : f.hom.base p ∈ Va)
    (hb : f.hom.base p ∈ Vb) (hc : f.hom.base p ∈ Vc) (a : M₁.val.obj (op Va))
    (b : M₂.val.obj (op Vb)) (c : M₃.val.obj (op Vc)) :
    sheafCast (congrArg (pullbackFunctor f).obj hP) p
        (stalkMul (pullbackBilinear f β₃) p
          (stalkMul (pullbackBilinear f β₁) p
            (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
              (pullbackUnit f M₁ (op Va) a))
            (grpGerm X ((pullbackFunctor f).obj M₂).val p ((opensMap f).obj Vb) hb
              (pullbackUnit f M₂ (op Vb) b)))
          (grpGerm X ((pullbackFunctor f).obj M₃).val p ((opensMap f).obj Vc) hc
            (pullbackUnit f M₃ (op Vc) c))) =
      stalkMul (pullbackBilinear f β₄) p
        (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
          (pullbackUnit f M₁ (op Va) a))
        (stalkMul (pullbackBilinear f β₂) p
          (grpGerm X ((pullbackFunctor f).obj M₂).val p ((opensMap f).obj Vb) hb
            (pullbackUnit f M₂ (op Vb) b))
          (grpGerm X ((pullbackFunctor f).obj M₃).val p ((opensMap f).obj Vc) hc
            (pullbackUnit f M₃ (op Vc) c))) := by
  have hxW : f.hom.base p ∈ Va ⊓ Vb ⊓ Vc := ⟨⟨ha, hb⟩, hc⟩
  rw [← grpGerm_pullbackUnit_restrict f M₁
      p (le_trans inf_le_left inf_le_left : Va ⊓ Vb ⊓ Vc ≤ Va) hxW a,
    ← grpGerm_pullbackUnit_restrict f M₂
      p (le_trans inf_le_left inf_le_right : Va ⊓ Vb ⊓ Vc ≤ Vb) hxW b,
    ← grpGerm_pullbackUnit_restrict f M₃
      p (inf_le_right : Va ⊓ Vb ⊓ Vc ≤ Vc) hxW c]
  exact assoc_common f β₁ β₂ β₃ β₄ hP hassoc p (Va ⊓ Vb ⊓ Vc) hxW _ _ _

include hassoc in
private lemma assoc_z (p : X.carrier) (Va Vb : Opens Y.carrier) (ha : f.hom.base p ∈ Va)
    (hb : f.hom.base p ∈ Vb) (a : M₁.val.obj (op Va)) (b : M₂.val.obj (op Vb))
    (gz : grpStalk X ((pullbackFunctor f).obj M₃).val p) :
    sheafCast (congrArg (pullbackFunctor f).obj hP) p
        (stalkMul (pullbackBilinear f β₃) p
          (stalkMul (pullbackBilinear f β₁) p
            (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
              (pullbackUnit f M₁ (op Va) a))
            (grpGerm X ((pullbackFunctor f).obj M₂).val p ((opensMap f).obj Vb) hb
              (pullbackUnit f M₂ (op Vb) b))) gz) =
      stalkMul (pullbackBilinear f β₄) p
        (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
          (pullbackUnit f M₁ (op Va) a))
        (stalkMul (pullbackBilinear f β₂) p
          (grpGerm X ((pullbackFunctor f).obj M₂).val p ((opensMap f).obj Vb) hb
            (pullbackUnit f M₂ (op Vb) b)) gz) := by
  set gx := grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
    (pullbackUnit f M₁ (op Va) a) with hgx
  set gy := grpGerm X ((pullbackFunctor f).obj M₂).val p ((opensMap f).obj Vb) hb
    (pullbackUnit f M₂ (op Vb) b) with hgy
  exact LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f M₃ p
      (((sheafCast (congrArg (pullbackFunctor f).obj hP) p).toLinearMap).comp
        (stalkMulLeft (pullbackBilinear f β₃) p
          (stalkMul (pullbackBilinear f β₁) p gx gy)))
      ((stalkMulLeft (pullbackBilinear f β₄) p gx).comp
        (stalkMulLeft (pullbackBilinear f β₂) p gy))
      (fun Vc hc c => by
        rw [hgx, hgy]
        exact assoc_gen f β₁ β₂ β₃ β₄ hP hassoc p Va Vb Vc ha hb hc a b c)) gz

include hassoc in
private lemma assoc_y (p : X.carrier) (Va : Opens Y.carrier) (ha : f.hom.base p ∈ Va)
    (a : M₁.val.obj (op Va)) (gy : grpStalk X ((pullbackFunctor f).obj M₂).val p)
    (gz : grpStalk X ((pullbackFunctor f).obj M₃).val p) :
    sheafCast (congrArg (pullbackFunctor f).obj hP) p
        (stalkMul (pullbackBilinear f β₃) p
          (stalkMul (pullbackBilinear f β₁) p
            (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
              (pullbackUnit f M₁ (op Va) a)) gy) gz) =
      stalkMul (pullbackBilinear f β₄) p
        (grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
          (pullbackUnit f M₁ (op Va) a))
        (stalkMul (pullbackBilinear f β₂) p gy gz) := by
  set gx := grpGerm X ((pullbackFunctor f).obj M₁).val p ((opensMap f).obj Va) ha
    (pullbackUnit f M₁ (op Va) a) with hgx
  exact LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f M₂ p
      (((sheafCast (congrArg (pullbackFunctor f).obj hP) p).toLinearMap).comp
        ((stalkMulRight (pullbackBilinear f β₃) p gz).comp
          (stalkMulLeft (pullbackBilinear f β₁) p gx)))
      ((stalkMulLeft (pullbackBilinear f β₄) p gx).comp
        (stalkMulRight (pullbackBilinear f β₂) p gz))
      (fun Vb hb b => by
        rw [hgx]
        exact assoc_z f β₁ β₂ β₃ β₄ hP hassoc p Va Vb ha hb a b gz)) gy

include hassoc in
private lemma assoc_stalk (p : X.carrier)
    (gx : grpStalk X ((pullbackFunctor f).obj M₁).val p)
    (gy : grpStalk X ((pullbackFunctor f).obj M₂).val p)
    (gz : grpStalk X ((pullbackFunctor f).obj M₃).val p) :
    sheafCast (congrArg (pullbackFunctor f).obj hP) p
        (stalkMul (pullbackBilinear f β₃) p (stalkMul (pullbackBilinear f β₁) p gx gy) gz) =
      stalkMul (pullbackBilinear f β₄) p gx (stalkMul (pullbackBilinear f β₂) p gy gz) :=
  LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f M₁ p
      (((sheafCast (congrArg (pullbackFunctor f).obj hP) p).toLinearMap).comp
        ((stalkMulRight (pullbackBilinear f β₃) p gz).comp
          (stalkMulRight (pullbackBilinear f β₁) p gy)))
      (stalkMulRight (pullbackBilinear f β₄) p (stalkMul (pullbackBilinear f β₂) p gy gz))
      (fun Va ha a => assoc_y f β₁ β₂ β₃ β₄ hP hassoc p Va ha a gy gz)) gx

include hP hassoc in
/-- An associativity law between four bilinear maps of sheaves of modules pulls back. -/
theorem pullbackBilinear_assoc (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj M₁).val.obj (op U))
    (y : ((pullbackFunctor f).obj M₂).val.obj (op U))
    (z : ((pullbackFunctor f).obj M₃).val.obj (op U)) :
    HEq ((pullbackBilinear f β₃).app (op U) ((pullbackBilinear f β₁).app (op U) x y) z)
      ((pullbackBilinear f β₄).app (op U) x ((pullbackBilinear f β₂).app (op U) y z)) := by
  refine heq_of_sheafCast_grpGerm (congrArg (pullbackFunctor f).obj hP) U _ _ fun p hp => ?_
  rw [← stalkMul_grpGerm (pullbackBilinear f β₃) p U hp _ z,
    ← stalkMul_grpGerm (pullbackBilinear f β₁) p U hp x y,
    ← stalkMul_grpGerm (pullbackBilinear f β₄) p U hp x _,
    ← stalkMul_grpGerm (pullbackBilinear f β₂) p U hp y z]
  exact assoc_stalk f β₁ β₂ β₃ β₄ hP hassoc p _ _ _

section Unit

variable {M₀ N Q : SheafOfModules.{u} (structureRingSheaf Y)} (t : M₀.sections)
  (β : SheafOfModules.BilinearMap M₀ N Q) (hQ : Q = N)
  (hone : ∀ (V : Opens Y.carrier) (a : N.val.obj (op V)),
    HEq (β.app (op V) (t.eval (op V)) a) a)

include hQ hone in
/-- A unit law for a bilinear map of sheaves of modules pulls back, the unit being the global
section of the pullback attached to a global section. -/
theorem pullbackBilinear_one (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj N).val.obj (op U)) :
    HEq ((pullbackBilinear f β).app (op U) ((pullbackSectionsUnit f M₀ t).eval (op U)) x) x := by
  refine heq_of_sheafCast_grpGerm (congrArg (pullbackFunctor f).obj hQ) U _ _ fun p hp => ?_
  rw [← stalkMul_grpGerm (pullbackBilinear f β) p U hp _ x]
  exact LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f N p
      (((sheafCast (congrArg (pullbackFunctor f).obj hQ) p).toLinearMap).comp
        (stalkMulLeft (pullbackBilinear f β) p
          (grpGerm X ((pullbackFunctor f).obj M₀).val p U hp
            ((pullbackSectionsUnit f M₀ t).eval (op U)))))
      LinearMap.id
      (fun V hx a => by
        show sheafCast (congrArg (pullbackFunctor f).obj hQ) p
            (stalkMul (pullbackBilinear f β) p
              (grpGerm X ((pullbackFunctor f).obj M₀).val p U hp
                ((pullbackSectionsUnit f M₀ t).eval (op U)))
              (grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj V) hx
                (pullbackUnit f N (op V) a))) =
          grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj V) hx
            (pullbackUnit f N (op V) a)
        rw [grpGerm_pullbackSectionsUnit_eval f M₀ t p U hp V hx,
          stalkMul_pullbackBilinear_pullbackUnit]
        exact sheafCast_grpGerm_pullbackUnit f hQ p V hx _ _ (hone V a)))
    (grpGerm X ((pullbackFunctor f).obj N).val p U hp x)

end Unit

end General

section Module

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))

/-- The action of a left graded module in the degrees `(i, n)`, as a bilinear map of sheaves of
modules. -/
def smulBilinear (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A) (i n : ℤ) :
    SheafOfModules.BilinearMap (A.piece i) (ℳ.piece n) (ℳ.piece (i + n)) where
  app U := ℳ.smul i n U
  map_smul_left U r a x := ℳ.smul_smul_left i n U r a x
  map_smul_right U r a x := ℳ.smul_smul_right i n U r a x
  naturality g a x := ℳ.smul_naturality i n g a x

/-- The pullback of a left graded module along a morphism of ringed spaces, a left graded module
over the pulled-back graded algebra: the pieces are the pullbacks of the pieces and the action is
the pullback of the action. -/
noncomputable def pullbackLeftGradedModule (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A) :
    SheafOfModules.LeftGradedModule.{u, u, u} (pullbackGradedAlgebra f A) where
  piece n := (pullbackFunctor f).obj (ℳ.piece n)
  smul i n U := (pullbackBilinear f (smulBilinear A ℳ i n)).app U
  smul_smul_left i n U r a x := (pullbackBilinear f (smulBilinear A ℳ i n)).map_smul_left U r a x
  smul_smul_right i n U r a x :=
    (pullbackBilinear f (smulBilinear A ℳ i n)).map_smul_right U r a x
  smul_naturality i n _ _ g a x := (pullbackBilinear f (smulBilinear A ℳ i n)).naturality g a x
  mul_smul i j n U a b x := by
    obtain ⟨U⟩ := U
    exact pullbackBilinear_assoc f (A.mul i j) (smulBilinear A ℳ j n)
      (smulBilinear A ℳ (i + j) n) (smulBilinear A ℳ i (j + n))
      (congrArg ℳ.piece (add_assoc i j n)) (fun V a b c => ℳ.mul_smul i j n (op V) a b c) U a b x
  one_smul n U x := by
    obtain ⟨U⟩ := U
    exact pullbackBilinear_one f A.one (smulBilinear A ℳ 0 n) (congrArg ℳ.piece (zero_add n))
      (fun V a => ℳ.one_smul n (op V) a) U x

/-- The pieces of the pulled-back left graded module are the pullbacks of the pieces. -/
@[simp] lemma pullbackLeftGradedModule_piece (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A)
    (n : ℤ) : (pullbackLeftGradedModule f A ℳ).piece n = (pullbackFunctor f).obj (ℳ.piece n) :=
  rfl

/-- The pulled-back action on pullback-unit images is the pullback-unit image of the action. -/
lemma pullbackLeftGradedModule_smul_pullbackUnit
    (ℳ : SheafOfModules.LeftGradedModule.{u, u, u} A) (i n : ℤ) (V : Opens Y.carrier)
    (a : (A.piece i).val.obj (op V)) (x : (ℳ.piece n).val.obj (op V)) :
    (pullbackLeftGradedModule f A ℳ).smul i n (op ((opensMap f).obj V))
        (pullbackUnit f (A.piece i) (op V) a) (pullbackUnit f (ℳ.piece n) (op V) x) =
      pullbackUnit f (ℳ.piece (i + n)) (op V) (ℳ.smul i n (op V) a x) :=
  pullbackBilinear_pullbackUnit f (smulBilinear A ℳ i n) (op V) a x

end Module

end Stacks.RingedSpace

end
