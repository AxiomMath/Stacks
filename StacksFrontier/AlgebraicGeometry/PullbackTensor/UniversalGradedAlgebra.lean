module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# Pullback of a universal graded algebra of a sheaf of modules

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `F` be a sheaf of `𝒪_Y`-modules and let
`A` be a sheaf of graded `𝒪_Y`-algebras with a degree-one generator `ι : F ⟶ A_1` which is
universal for a property `P` of degree-one generators in the sense of
`SheafOfModules.GradedAlgebra.IsUniversal`. This file shows that the pulled-back graded algebra
`Stacks.RingedSpace.pullbackGradedAlgebra` is universal for the corresponding property on `X`,
with the pulled-back generator `f^*ι`.

## Main results

* `Stacks.RingedSpace.bilinear_app_eq_of_pullbackUnit`: two bilinear maps out of a pair of
  pullbacks agree on all local sections as soon as they agree on pullback-unit images.
* `Stacks.RingedSpace.pairwiseCommutes_pullbackGradedAlgebra`: the pullback of a degree-one
  generator with pairwise commuting image again has pairwise commuting image.
* `Stacks.RingedSpace.pullbackAlgebraUnitalHom`: the unital homomorphism `f^*A ⟶ B` attached to
  a degree-one generator of `B` whose pushforward has the property `P`, together with
  `pullbackAlgebraUnitalHom_extends` and `pullbackAlgebraUnitalHom_unique`.
* `Stacks.RingedSpace.isUniversal_pullbackGradedAlgebra`: `f^*A` with `f^*ι` is universal for a
  property of degree-one generators on `X` which transfers to `P` under pushforward and which
  `f^*ι` has.
* `Stacks.RingedSpace.isSymmetricAlgebra_pullbackGradedAlgebra` and
  `isTensorAlgebra_pullbackGradedAlgebra`: the symmetric and tensor instances.

## Implementation notes

The invertibility of the comparison is obtained from the universal properties on both sides, so
the pullback has to carry a graded algebra structure. That is
`Stacks.RingedSpace.pullbackGradedAlgebra`, which exists because pullback commutes with tensor
products (Stacks 01CD), and the only thing missing from its API here is that a *bilinear* map
out of a pair of pullbacks is determined by its values on pullback-unit images — the pullback is
an abstract left adjoint and has no description of its sections. That is
`bilinear_app_eq_of_pullbackUnit`, proved by the same stalkwise generation argument that the
three graded-algebra laws are proved by: a section is determined by its germs, the germ of a
value of a bilinear map is a function of the germs of its arguments, and the stalk of a pullback
is generated over the local ring by the germs of pullback-unit images.

The exterior analogue is **not** available this way, and the reason is not a missing lemma:
`SquareZero` is a condition on `β (x, x)`, which is quadratic rather than bilinear, so the
generation argument gives only antisymmetry of `β` on all sections and `β (x, x) = -β (x, x)`
does not imply `β (x, x) = 0` in characteristic two.

Every statement is written in the `pullbackBilinear`/`pullbackSectionsUnit` spelling rather than
through the projections of `pullbackGradedAlgebra`, and `transposeUnitalHom` takes the
degreewise family as data rather than as a `UnitalHom` out of `pullbackGradedAlgebra f A`. The
reason is the same in both places: `(pullbackGradedAlgebra f A).piece n` and
`(pullbackFunctor f).obj (A.piece n)` are definitionally equal but a goal written with one and a
lemma written with the other are not type-correct at `implicit` transparency, which is the
transparency `rw` checks its motive at. Every conversion between the two spellings therefore
happens at `exact` or `change`, never inside a `rw`. The same holds for the two spellings of the
structure sheaf, `structureSheafRing` — which the pushforward side of the
adjunction is stated over — and the reducible abbreviation
`Stacks.RingedSpace.structureRingSheaf`, which the pullback side is stated over; this is why
`pairwiseCommutes_pushforwardGenerator` is written with `congrArg₂` and `Eq.trans` instead of
two rewrites.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct

universe u

namespace Stacks.RingedSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
open SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Pullback of sheaves of modules along a morphism of ringed spaces is a left adjoint**, at
the `Stacks.RingedSpace.structureRingSheaf` spelling of the structure sheaf.
`SheafOfModules.GradedAlgebra.modulePullback_isLeftAdjoint` is the same instance at the
`structureSheafRing` spelling; the two sheaves of rings are equal by
`Stacks.RingedSpace.structureRingSheaf_eq_ringSheaf`, but that is a `rfl` through a
semireducible definition and instance search runs at `instances` transparency, so the instance
has to be seated at both spellings. -/
instance isLeftAdjoint_pullbackFunctor : (pullbackFunctor f).IsLeftAdjoint :=
  (pullbackAdjunction f).isLeftAdjoint

/-! ### Bilinear extensionality for a pair of pullbacks -/

section BilinearExt

variable {M N : SheafOfModules.{u} (structureRingSheaf Y)}
  {P : SheafOfModules.{u} (structureRingSheaf X)}
  (β γ : SheafOfModules.BilinearMap ((pullbackFunctor f).obj M) ((pullbackFunctor f).obj N) P)

/-- The agreement hypothesis of `bilinear_app_eq_of_pullbackUnit`: the two bilinear maps take
the same value on the pullback-unit images of two local sections over a common open. -/
private def AgreeOnPullbackUnit : Prop :=
  ∀ (V : (Opens Y.carrier)ᵒᵖ) (a : M.val.obj V) (b : N.val.obj V),
    β.app ((opensMap f).op.obj V) (pullbackUnit f M V a) (pullbackUnit f N V b) =
      γ.app ((opensMap f).op.obj V) (pullbackUnit f M V a) (pullbackUnit f N V b)

/-- The two induced multiplications of germs agree when the first germ is the germ of a
pullback-unit image. -/
private lemma stalkMul_eq_of_pullbackUnit (h : AgreeOnPullbackUnit f β γ) (p : X.carrier)
    (V : Opens Y.carrier) (hx : f.hom.base p ∈ V) (a : M.val.obj (op V))
    (gy : grpStalk X ((pullbackFunctor f).obj N).val p) :
    stalkMul β p (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
        (pullbackUnit f M (op V) a)) gy =
      stalkMul γ p (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
        (pullbackUnit f M (op V) a)) gy :=
  LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f N p
      (stalkMulLeft β p (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
        (pullbackUnit f M (op V) a)))
      (stalkMulLeft γ p (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
        (pullbackUnit f M (op V) a)))
      (fun W hw b => by
        have hxW : f.hom.base p ∈ V ⊓ W := ⟨hx, hw⟩
        simp only [stalkMulLeft_apply]
        rw [← grpGerm_pullbackUnit_restrict f M p (inf_le_left : V ⊓ W ≤ V) hxW a,
          ← grpGerm_pullbackUnit_restrict f N p (inf_le_right : V ⊓ W ≤ W) hxW b,
          stalkMul_grpGerm β p ((opensMap f).obj (V ⊓ W)) hxW,
          stalkMul_grpGerm γ p ((opensMap f).obj (V ⊓ W)) hxW]
        exact congrArg _ (h (op (V ⊓ W)) _ _))) gy

/-- **Two bilinear maps out of a pair of pullbacks that agree on pullback-unit images agree on
all local sections.** Both sides are determined by their germs, the germ of a value is a
function of the germs of the two arguments, and the stalk of a pullback is generated over the
local ring by the germs of pullback-unit images. -/
theorem bilinear_app_eq_of_pullbackUnit
    (h : ∀ (V : (Opens Y.carrier)ᵒᵖ) (a : M.val.obj V) (b : N.val.obj V),
      β.app ((opensMap f).op.obj V) (pullbackUnit f M V a) (pullbackUnit f N V b) =
        γ.app ((opensMap f).op.obj V) (pullbackUnit f M V a) (pullbackUnit f N V b))
    (U : Opens X.carrier) (x : ((pullbackFunctor f).obj M).val.obj (op U))
    (y : ((pullbackFunctor f).obj N).val.obj (op U)) :
    β.app (op U) x y = γ.app (op U) x y := by
  refine section_ext_grpGerm P U _ _ fun p hp => ?_
  rw [← stalkMul_grpGerm β p U hp x y, ← stalkMul_grpGerm γ p U hp x y]
  exact LinearMap.congr_fun
    (pullbackStalk_linearMap_ext f M p
      (stalkMulRight β p (grpGerm X ((pullbackFunctor f).obj N).val p U hp y))
      (stalkMulRight γ p (grpGerm X ((pullbackFunctor f).obj N).val p U hp y))
      (fun V hx a => stalkMul_eq_of_pullbackUnit f β γ h p V hx a _)) _

end BilinearExt

/-! ### The pulled-back generator -/

section Generator

variable {F : SheafOfModules.{u} (structureRingSheaf Y)}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)} {ι : F ⟶ A.piece 1}

/-- The pulled-back product of the pullback-unit images of two sections, pushed through two
pulled-back degree-one generators. -/
private lemma pullbackBilinear_generator_pullbackUnit (i j : ℤ) (V : (Opens Y.carrier)ᵒᵖ)
    (ιi : F ⟶ A.piece i) (ιj : F ⟶ A.piece j) (a b : F.val.obj V) :
    (pullbackBilinear f (A.mul i j)).app ((opensMap f).op.obj V)
        (Hom.app ((pullbackFunctor f).map ιi).val ((opensMap f).op.obj V)
          (pullbackUnit f F V a))
        (Hom.app ((pullbackFunctor f).map ιj).val ((opensMap f).op.obj V)
          (pullbackUnit f F V b)) =
      pullbackUnit f (A.piece (i + j)) V
        ((A.mul i j).app V (Hom.app ιi.val V a) (Hom.app ιj.val V b)) := by
  rw [pullbackUnit_naturality f ιi V a, pullbackUnit_naturality f ιj V b]
  exact pullbackBilinear_pullbackUnit f (A.mul i j) V _ _

/-- **The pullback of a degree-one generator with pairwise commuting image has pairwise
commuting image.** -/
theorem pairwiseCommutes_pullbackGradedAlgebra (hι : PairwiseCommutes ι) :
    PairwiseCommutes (A := pullbackGradedAlgebra f A) ((pullbackFunctor f).map ι) := by
  intro U s t
  obtain ⟨U⟩ := U
  exact bilinear_app_eq_of_pullbackUnit f
    (((pullbackBilinear f (A.mul 1 1)).compLeft ((pullbackFunctor f).map ι).val).compRight
      ((pullbackFunctor f).map ι).val)
    ((((pullbackBilinear f (A.mul 1 1)).compLeft ((pullbackFunctor f).map ι).val).compRight
      ((pullbackFunctor f).map ι).val).flip)
    (fun V a b =>
      ((pullbackBilinear_generator_pullbackUnit f 1 1 V ι ι a b).trans
        (congrArg (pullbackUnit f (A.piece (1 + 1)) V) (hι V a b))).trans
        (pullbackBilinear_generator_pullbackUnit f 1 1 V ι ι b a).symm) U s t

end Generator

/-! ### The comparison with a graded algebra on the source -/

section Comparison

variable {F : SheafOfModules.{u} (structureRingSheaf Y)}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)} {ι : F ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj F ⟶ B.piece 1}
  {P : ∀ B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y),
    (F ⟶ B'.piece 1) → Prop}

/-- **The pushforward of a pairwise commuting degree-one generator is pairwise commuting.**
Multiplication in the pushforward algebra is multiplication over the image opens. -/
theorem pairwiseCommutes_pushforwardGenerator (hκ : PairwiseCommutes κ) :
    PairwiseCommutes (pushforwardGenerator f κ) := fun U x y =>
  (congrArg₂ (fun p q => (B.mul 1 1).app ((opensMap f).op.obj U) p q)
      (pushforwardGenerator_val_app f κ U x) (pushforwardGenerator_val_app f κ U y)).trans
    ((hκ ((opensMap f).op.obj U) _ _).trans
      (congrArg₂ (fun p q => (B.mul 1 1).app ((opensMap f).op.obj U) p q)
        (pushforwardGenerator_val_app f κ U y).symm
        (pushforwardGenerator_val_app f κ U x).symm))

variable (hA : IsUniversal P A ι)
  (hκ : P (pushforwardRingedSpace f B) (pushforwardGenerator f κ))

/-- The unique unital homomorphism from `A` to the pushforward of `B` extending the
pushed-forward generator. -/
noncomputable def pullbackAlgebraDesc : UnitalHom A (pushforwardRingedSpace f B) :=
  hA.desc _ (pushforwardGenerator f κ) hκ

/-- The comparison morphism `f^*(A_n) ⟶ B_n`: the adjoint transpose of
`pullbackAlgebraDesc` in degree `n`. -/
noncomputable def pullbackAlgebraCmp (n : ℤ) :
    (pullbackFunctor f).obj (A.piece n) ⟶ B.piece n :=
  ((pullbackAdjunction f).homEquiv (A.piece n) (B.piece n)).symm
    ((pullbackAlgebraDesc f hA hκ).app n)

/-- The comparison morphism computes `pullbackAlgebraDesc` on pullback-unit images. -/
theorem pullbackAlgebraCmp_pullbackUnit (n : ℤ) (V : (Opens Y.carrier)ᵒᵖ)
    (x : (A.piece n).val.obj V) :
    Hom.app (pullbackAlgebraCmp f hA hκ n).val ((opensMap f).op.obj V)
        (pullbackUnit f (A.piece n) V x) =
      Hom.app ((pullbackAlgebraDesc f hA hκ).app n).val V x :=
  homEquiv_symm_val_app_unit f ((pullbackAlgebraDesc f hA hκ).app n) V x

/-- **The comparison morphisms are multiplicative**, on all local sections of the pullback. -/
theorem pullbackAlgebraCmp_map_mul (i j : ℤ) (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U))
    (y : ((pullbackFunctor f).obj (A.piece j)).val.obj (op U)) :
    Hom.app (pullbackAlgebraCmp f hA hκ (i + j)).val (op U)
        ((pullbackBilinear f (A.mul i j)).app (op U) x y) =
      (B.mul i j).app (op U)
        (Hom.app (pullbackAlgebraCmp f hA hκ i).val (op U) x)
        (Hom.app (pullbackAlgebraCmp f hA hκ j).val (op U) y) :=
  bilinear_app_eq_of_pullbackUnit f
    ((pullbackBilinear f (A.mul i j)).postcomp (pullbackAlgebraCmp f hA hκ (i + j)).val)
    (((B.mul i j).compLeft (pullbackAlgebraCmp f hA hκ i).val).compRight
      (pullbackAlgebraCmp f hA hκ j).val)
    (fun V a b => by
      rw [Stacks.BilinearMap.postcomp_app, Stacks.BilinearMap.compRight_app,
        Stacks.BilinearMap.compLeft_app, pullbackBilinear_pullbackUnit f (A.mul i j) V a b,
        pullbackAlgebraCmp_pullbackUnit, pullbackAlgebraCmp_pullbackUnit,
        pullbackAlgebraCmp_pullbackUnit]
      exact (pullbackAlgebraDesc f hA hκ).map_mul i j V a b) U x y

/-- **The comparison morphism in degree zero carries the unit to the unit.** -/
theorem pullbackAlgebraCmp_map_one (U : Opens X.carrier) :
    Hom.app (pullbackAlgebraCmp f hA hκ 0).val (op U)
        ((pullbackSectionsUnit f (A.piece 0) A.one).eval (op U)) =
      B.one.eval (op U) := by
  have htop : Hom.app (pullbackAlgebraCmp f hA hκ 0).val (op (⊤ : Opens X.carrier))
      (pullbackUnitTop f (A.piece 0) A.one) = B.one.eval (op (⊤ : Opens X.carrier)) :=
    (pullbackAlgebraCmp_pullbackUnit f hA hκ 0 (op (⊤ : Opens Y.carrier)) _).trans
      ((pullbackAlgebraDesc f hA hκ).map_one (op (⊤ : Opens Y.carrier)))
  have hnat := naturality_apply (pullbackAlgebraCmp f hA hκ 0).val
    (homOfLE (le_top : U ≤ (⊤ : Opens X.carrier))).op (pullbackUnitTop f (A.piece 0) A.one)
  refine hnat.trans ?_
  rw [htop]
  exact PresheafOfModules.sections_property B.one
    (homOfLE (le_top : U ≤ (⊤ : Opens X.carrier))).op

/-- **The comparison, as a unital homomorphism of sheaves of graded algebras out of the
pulled-back algebra.** -/
noncomputable def pullbackAlgebraUnitalHom : UnitalHom (pullbackGradedAlgebra f A) B where
  app n := pullbackAlgebraCmp f hA hκ n
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    exact pullbackAlgebraCmp_map_mul f hA hκ i j U x y
  map_one U := by
    obtain ⟨U⟩ := U
    exact pullbackAlgebraCmp_map_one f hA hκ U

/-- The degree-`n` component of `pullbackAlgebraUnitalHom` is `pullbackAlgebraCmp` in
degree `n`. -/
@[simp] theorem pullbackAlgebraUnitalHom_app (n : ℤ) :
    (pullbackAlgebraUnitalHom f hA hκ).app n = pullbackAlgebraCmp f hA hκ n := rfl

/-- The comparison extends the given generator of `B`. -/
theorem pullbackAlgebraUnitalHom_extends :
    (pullbackFunctor f).map ι ≫ (pullbackAlgebraUnitalHom f hA hκ).app 1 = κ :=
  (((pullbackAdjunction f).homEquiv_naturality_left_symm ι
        ((pullbackAlgebraDesc f hA hκ).app 1)).symm.trans
      (congrArg ((pullbackAdjunction f).homEquiv F (B.piece 1)).symm
        (hA.desc_extends _ (pushforwardGenerator f κ) hκ))).trans
    (((pullbackAdjunction f).homEquiv F (B.piece 1)).symm_apply_apply κ)

end Comparison

/-! ### Uniqueness of the comparison -/

section Uniqueness

variable {F : SheafOfModules.{u} (structureRingSheaf Y)}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)} {ι : F ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj F ⟶ B.piece 1}
  {P : ∀ B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y),
    (F ⟶ B'.piece 1) → Prop}
  (e : ∀ n : ℤ, (pullbackFunctor f).obj (A.piece n) ⟶ B.piece n)

/-- The adjoint transpose of a degreewise family of morphisms out of the pullback which is
multiplicative and unital on all local sections: a unital homomorphism from `A` to the
pushforward of `B`.

The family is taken as data rather than as a `UnitalHom` out of `pullbackGradedAlgebra f A`,
because the latter's degree-`n` piece is only definitionally — not `implicit`-transparently —
the pullback of the degree-`n` piece of `A`. -/
private noncomputable def transposeUnitalHom
    (emul : ∀ (i j : ℤ) (U : Opens X.carrier)
      (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U))
      (y : ((pullbackFunctor f).obj (A.piece j)).val.obj (op U)),
      Hom.app (e (i + j)).val (op U) ((pullbackBilinear f (A.mul i j)).app (op U) x y) =
        (B.mul i j).app (op U) (Hom.app (e i).val (op U) x) (Hom.app (e j).val (op U) y))
    (eone : ∀ U : Opens X.carrier,
      Hom.app (e 0).val (op U) ((pullbackSectionsUnit f (A.piece 0) A.one).eval (op U)) =
        B.one.eval (op U)) :
    UnitalHom A (pushforwardRingedSpace f B) where
  app n := (pullbackAdjunction f).homEquiv (A.piece n) (B.piece n) (e n)
  map_mul i j V a b := by
    obtain ⟨V⟩ := V
    change Hom.app
        ((pullbackAdjunction f).homEquiv (A.piece (i + j)) (B.piece (i + j))
          (e (i + j))).val (op V) ((A.mul i j).app (op V) a b) =
      (B.mul i j).app ((opensMap f).op.obj (op V))
        (Hom.app ((pullbackAdjunction f).homEquiv (A.piece i) (B.piece i) (e i)).val (op V) a)
        (Hom.app ((pullbackAdjunction f).homEquiv (A.piece j) (B.piece j) (e j)).val (op V) b)
    rw [homEquiv_val_app, homEquiv_val_app, homEquiv_val_app,
      ← pullbackBilinear_pullbackUnit f (A.mul i j) (op V) a b]
    exact emul i j ((opensMap f).obj V) _ _
  map_one V := by
    obtain ⟨V⟩ := V
    change Hom.app ((pullbackAdjunction f).homEquiv (A.piece 0) (B.piece 0) (e 0)).val (op V)
        (A.one.eval (op V)) = B.one.eval ((opensMap f).op.obj (op V))
    rw [homEquiv_val_app, ← pullbackSectionsUnit_eval f (A.piece 0) A.one V]
    exact eone ((opensMap f).obj V)

variable (hA : IsUniversal P A ι)
  (hκ : P (pushforwardRingedSpace f B) (pushforwardGenerator f κ))

/-- **A multiplicative, unital degreewise family out of the pullback which extends the
generator is the comparison.** -/
theorem eq_pullbackAlgebraCmp
    (emul : ∀ (i j : ℤ) (U : Opens X.carrier)
      (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U))
      (y : ((pullbackFunctor f).obj (A.piece j)).val.obj (op U)),
      Hom.app (e (i + j)).val (op U) ((pullbackBilinear f (A.mul i j)).app (op U) x y) =
        (B.mul i j).app (op U) (Hom.app (e i).val (op U) x) (Hom.app (e j).val (op U) y))
    (eone : ∀ U : Opens X.carrier,
      Hom.app (e 0).val (op U) ((pullbackSectionsUnit f (A.piece 0) A.one).eval (op U)) =
        B.one.eval (op U))
    (hgen : (pullbackFunctor f).map ι ≫ e 1 = κ) (n : ℤ) :
    e n = pullbackAlgebraCmp f hA hκ n := by
  have hGgen : ι ≫ (transposeUnitalHom f e emul eone).app 1 = pushforwardGenerator f κ :=
    ((pullbackAdjunction f).homEquiv_naturality_left ι (e 1)).symm.trans
      (congrArg ((pullbackAdjunction f).homEquiv F (B.piece 1)) hgen)
  have hn : (pullbackAdjunction f).homEquiv (A.piece n) (B.piece n) (e n) =
      (pullbackAlgebraDesc f hA hκ).app n :=
    congrArg (fun h : UnitalHom A (pushforwardRingedSpace f B) => h.app n)
      (hA.desc_unique _ (pushforwardGenerator f κ) hκ hGgen)
  exact (((pullbackAdjunction f).homEquiv (A.piece n) (B.piece n)).symm_apply_apply
    (e n)).symm.trans
    (congrArg (fun h => ((pullbackAdjunction f).homEquiv (A.piece n) (B.piece n)).symm h) hn)

/-- **The comparison is the unique unital homomorphism out of the pulled-back algebra extending
the given generator.** -/
theorem pullbackAlgebraUnitalHom_unique {g : UnitalHom (pullbackGradedAlgebra f A) B}
    (hg : (pullbackFunctor f).map ι ≫ g.app 1 = κ) : g = pullbackAlgebraUnitalHom f hA hκ :=
  UnitalHom.ext fun n =>
    eq_pullbackAlgebraCmp f (fun m => g.app m) hA hκ
      (fun i j U x y => g.map_mul i j (op U) x y) (fun U => g.map_one (op U)) hg n

end Uniqueness

/-! ### Universality of the pulled-back algebra -/

section Universal

variable {F : SheafOfModules.{u} (structureRingSheaf Y)}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)} {ι : F ⟶ A.piece 1}
  {P : ∀ B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y),
    (F ⟶ B'.piece 1) → Prop}
  {Q : ∀ B' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X),
    ((pullbackFunctor f).obj F ⟶ B'.piece 1) → Prop}

/-- **The pulled-back graded algebra is universal for a property of degree-one generators that
transfers to `P` under pushforward.** -/
theorem isUniversal_pullbackGradedAlgebra (hA : IsUniversal P A ι)
    (htr : ∀ (B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X))
      (κ : (pullbackFunctor f).obj F ⟶ B.piece 1), Q B κ →
      P (pushforwardRingedSpace f B) (pushforwardGenerator f κ))
    (hQ : Q (pullbackGradedAlgebra f A) ((pullbackFunctor f).map ι)) :
    IsUniversal Q (pullbackGradedAlgebra f A) ((pullbackFunctor f).map ι) :=
  ⟨hQ, fun B κ hκ =>
    ⟨pullbackAlgebraUnitalHom f hA (htr B κ hκ),
      pullbackAlgebraUnitalHom_extends f hA (htr B κ hκ),
      fun _ hg => pullbackAlgebraUnitalHom_unique f hA (htr B κ hκ) hg⟩⟩

/-- **The pullback of the symmetric algebra of `F` is the symmetric algebra of `f^*F`.** -/
theorem isSymmetricAlgebra_pullbackGradedAlgebra (hA : IsSymmetricAlgebra A ι) :
    IsSymmetricAlgebra (pullbackGradedAlgebra f A) ((pullbackFunctor f).map ι) :=
  isUniversal_pullbackGradedAlgebra f hA.isUniversal
    (fun _ _ hκ => pairwiseCommutes_pushforwardGenerator f hκ)
    (pairwiseCommutes_pullbackGradedAlgebra f hA.1)

/-- **The pullback of the tensor algebra of `F` is the tensor algebra of `f^*F`.** -/
theorem isTensorAlgebra_pullbackGradedAlgebra (hA : IsTensorAlgebra A ι) :
    IsTensorAlgebra (pullbackGradedAlgebra f A) ((pullbackFunctor f).map ι) :=
  isUniversal_pullbackGradedAlgebra f hA.isUniversal (fun _ _ _ => trivial) trivial

end Universal

end Stacks.RingedSpace

end
