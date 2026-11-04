module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPowDegreeOpen
public import StacksFrontier.AlgebraicGeometry.TwistTensor.MultiplicationCommutativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence

/-!
# The twist multiplication pulled back along a morphism to `Proj S`, and on the degree `d` open

Let `S` be a graded ring, `f : X ⟶ Proj S` a morphism of ringed spaces, and `𝒪(a)` the twists of
`Proj S`. Stacks Tag 01CD gives the comparison `f^*(𝒪(a) ⊗ 𝒪(b)) ≅ f^*𝒪(a) ⊗ f^*𝒪(b)`, so the
canonical multiplication map of Stacks Tag 01MO transports to a multiplication

`f^*𝒪(a) ⊗ f^*𝒪(b) ⟶ f^*𝒪(a + b)`

on the pulled-back twists. This file computes that multiplication on local sections, proves it
associative and unital, and reads these statements on the degree `d` open `U_d` of Stacks Tag
01N5, where the multiplication so obtained is
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwist`: the twist `𝒪(a)`, pulled back along `f`.
* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul`: the pulled-back multiplication, the
  inverse of the comparison of Stacks Tag 01CD followed by the pullback of the canonical
  multiplication map.
* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistComparison₂`: the comparison for a
  twice-iterated tensor product, `f^*((𝒪(a) ⊗ 𝒪(b)) ⊗ 𝒪(c)) ≅ (f^*𝒪(a) ⊗ f^*𝒪(b)) ⊗ f^*𝒪(c)`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistRS`, `twistUnitRS` and `twistMulRS`: the twists of
  `Proj S`, their unit and their canonical multiplication, typed at the ringed-space spelling of
  the structure sheaf of rings, which is the spelling the comparison of Stacks Tag 01CD is typed
  in.
* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit`: the unit of the pulled-back
  multiplication, `𝒪_X ⟶ f^*𝒪(0)`.
* `Stacks.AlgebraicGeometry.TwistTensor.degreeOpenHom`: the open immersion `U_d ⟶ Proj S` as a
  morphism of ringed spaces.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom`: the forward map of
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso`, with its source typed as a
  tensor product of pulled-back twists.

## Main results

* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_tmul`: on the pure tensor of the
  pullback-unit images of two local sections `s`, `t` of `𝒪(a)` and `𝒪(b)`, the pulled-back
  multiplication is the pullback-unit image of their product
  `Stacks.AlgebraicGeometry.TwistTensor.mulSection`.
* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_assoc` and
  `pullbackTwistMul_assoc_transport`: associativity of the pulled-back multiplication, the
  second with all four degree sums carried along arbitrary equalities of degrees.
* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul_one_left`,
  `pullbackTwistMul_one_left_transport`, `pullbackTwistMul_one_right` and
  `pullbackTwistMul_one_right_transport`: the left and right unit laws of the pulled-back
  multiplication.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_eq_pullbackTwistMul`: the multiplication
  isomorphism of the degree `d` open is the pulled-back multiplication along `U_d ⟶ Proj S`,
  followed by the transport along `dn + dm = d(n + m)`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_tmul`: on the pure tensor of the
  pullback-unit images of two local sections of `𝒪(dn)` and `𝒪(dm)`, the multiplication
  isomorphism of the degree `d` open is the pullback-unit image of their product.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_assoc`: associativity of the multiplication
  isomorphism of the degree `d` open, in every triple of integer degrees.
* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit_eq_twistZeroIsoUnit_inv`: the unit of
  the multiplication on the degree `d` open is the inverse of
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMulHom_one_left` and `twistMulHom_one_right`: the
  left unit law of `twistMulIso` in bidegree `(0, m)` and the right unit law in bidegree
  `(n, 0)`.

## Implementation notes

`Stacks.AlgebraicGeometry.CommonDegreeTwist.restrictedTwist` is by definition
`RingedSpaceModuleAdjunction.modulePullback` of the open immersion applied to `twistingSheaf`, and
`twistMulIso` is built from `Stacks.RelativeVeryAmple.pullbackTensorModulesIso`, the comparison of
Stacks Tag 01CD for that morphism, so the multiplication is evaluated on pullback-unit images of
sections. The identifications used are all `rfl`: the module pullback of a morphism of schemes
is `Stacks.RingedSpace.pullbackFunctor` of the underlying morphism of ringed spaces, the two
spellings of the structure sheaf of rings of `Proj S` agree,
`Stacks.RelativeVeryAmple.tensorModules` is the tensor product of the monoidal structure
`Stacks.PullbackGradedAlgebra.monoidalCategory`, and the forward map of
`pullbackTensorModulesIso` is `Stacks.PullbackTensorCoherence.pullbackTensorComparison`.

Associativity reduces to `mulSection_assoc`, associativity of the products of sections in the
homogeneous localizations: by `Stacks.PullbackTensorCoherence.pullback_tensor_hom_ext₂`, a
morphism out of `f^*((A ⊗ B) ⊗ C)` is determined by its values on the pullback-unit images of
triple pure tensors, so associativity is proved after cancelling `pullbackTwistComparison₂`.

`Stacks.AlgebraicGeometry.TwistTensor.twist` is typed over `projStructureRing`, while the
comparison of Stacks Tag 01CD is typed over the ringed-space spelling
`Stacks.RingedSpace.structureRingSheaf` of the same sheaf. The two are equal by `rfl`, but a term
mixing them is type-correct only at default transparency, so `rw` and `simp` fail on it. This is
why the `IsIso` instances for the comparison are restated at the spelling of the twists, and why
the unit laws are stated through `twistRS`, `twistUnitRS` and `twistMulRS`.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO) — the twists of the
  structure sheaf on `Proj S` and the canonical maps between them.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5) — the degree `d` open.
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU) — the open on which the
  multiplication maps are isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction PresheafOfModules
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.PullbackTensorCoherence
open Stacks.RelativeVeryAmple
open Stacks.RingedSpace
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistTensor

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance_reducible] ProjectiveSpectrum.top

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### Transports and the monoidal structure -/

section Transport

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- A transport whiskered on the right is the transport of the whiskered equality. -/
theorem eqToHom_whiskerRight {A A' : C} (h : A = A') (Z : C) :
    eqToHom h ▷ Z = eqToHom (congrArg (fun W ↦ W ⊗ Z) h) := by
  subst h; simp

/-- A transport whiskered on the left is the transport of the whiskered equality. -/
theorem whiskerLeft_eqToHom (Z : C) {B B' : C} (h : B = B') :
    Z ◁ eqToHom h = eqToHom (congrArg (fun W ↦ Z ⊗ W) h) := by
  subst h; simp

end Transport

/-! ### The pulled-back twists and their multiplication -/

variable {X : RingedSpace.{u, u}} (f : X ⟶ (AlgebraicGeometry.Proj 𝒮).toRingedSpace)

/-- The twist `𝒪(a)` of `Proj S`, pulled back along `f`. -/
abbrev pullbackTwist (a : ℤ) : SheafOfModules.{u} (structureRingSheaf X) :=
  (pullbackFunctor f).obj (twist 𝒮 a)

/-- The comparison of Stacks Tag 01CD at a pair of twists is an isomorphism, at the spelling the
twists are typed in. -/
instance isIso_pullbackTensorComparison_twist (a b : ℤ) :
    IsIso (pullbackTensorComparison f (twist 𝒮 a) (twist 𝒮 b)) :=
  Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison f (twist 𝒮 a) (twist 𝒮 b)

/-- The comparison of Stacks Tag 01CD at a tensor product of twists and a twist is an
isomorphism. -/
instance isIso_pullbackTensorComparison_twist₂ (a b c : ℤ) :
    IsIso (pullbackTensorComparison f (twist 𝒮 a ⊗ twist 𝒮 b) (twist 𝒮 c)) :=
  Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison f
    (twist 𝒮 a ⊗ twist 𝒮 b) (twist 𝒮 c)

/-- **The pulled-back twist multiplication** `f^*𝒪(a) ⊗ f^*𝒪(b) ⟶ f^*𝒪(a + b)`: the inverse of
the comparison of Stacks Tag 01CD, followed by the pullback of the canonical multiplication map
of Stacks Tag 01MO. -/
def pullbackTwistMul (a b : ℤ) :
    pullbackTwist 𝒮 f a ⊗ pullbackTwist 𝒮 f b ⟶ pullbackTwist 𝒮 f (a + b) :=
  inv (pullbackTensorComparison f (twist 𝒮 a) (twist 𝒮 b)) ≫
    (pullbackFunctor f).map (twistMul 𝒮 a b)

/-- **The local-section formula for the pulled-back multiplication.** On the pure tensor of the
pullback-unit images of two local sections it is the pullback-unit image of their product. The
pullback-unit images do not exhaust the sections of a pullback, but they determine a morphism out
of one. -/
theorem pullbackTwistMul_tmul (a b : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twist 𝒮 a).val.obj U) (t : (twist 𝒮 b).val.obj U) :
    (pullbackTwistMul 𝒮 f a b).val.app ((opensMap f).op.obj U)
        (tmul X (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) ((opensMap f).op.obj U)
          (pullbackUnit f (twist 𝒮 a) U s) (pullbackUnit f (twist 𝒮 b) U t)) =
      pullbackUnit f (twist 𝒮 (a + b)) U (mulSection 𝒮 a b U s t) := by
  rw [pullbackTwistMul, SheafOfModules.comp_val_app_apply,
    ← pullbackTensorComparison_pullbackUnit f (twist 𝒮 a) (twist 𝒮 b) U s t,
    inv_val_app_apply]
  exact pullbackUnit_naturality f (twistMul 𝒮 a b) U
    (tmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twist 𝒮 a) (twist 𝒮 b) U s t)

/-! ### Associativity -/

/-- The comparison of Stacks Tag 01CD for a twice-iterated tensor product of twists,
`f^*((𝒪(a) ⊗ 𝒪(b)) ⊗ 𝒪(c)) ≅ (f^*𝒪(a) ⊗ f^*𝒪(b)) ⊗ f^*𝒪(c)`: the outer comparison followed by
the inner one whiskered with `f^*𝒪(c)`. -/
def pullbackTwistComparison₂ (a b c : ℤ) :
    (pullbackFunctor f).obj ((twist 𝒮 a ⊗ twist 𝒮 b) ⊗ twist 𝒮 c) ≅
      (pullbackTwist 𝒮 f a ⊗ pullbackTwist 𝒮 f b) ⊗ pullbackTwist 𝒮 f c :=
  asIso (pullbackTensorComparison f (twist 𝒮 a ⊗ twist 𝒮 b) (twist 𝒮 c)) ≪≫
    whiskerRightIso (asIso (pullbackTensorComparison f (twist 𝒮 a) (twist 𝒮 b)))
      (pullbackTwist 𝒮 f c)

/-- A composite acts on a local section as the second map does on the image under the first. -/
private theorem comp_val_app_eq_of_eq {A B C : SheafOfModules.{u} (structureRingSheaf X)}
    (φ : A ⟶ B) (ψ : B ⟶ C) (V : (Opens X.carrier)ᵒᵖ) {x : A.val.obj V} {y : B.val.obj V}
    (h : φ.val.app V x = y) : (φ ≫ ψ).val.app V x = ψ.val.app V y :=
  (SheafOfModules.comp_val_app_apply _ _ _ _).trans (congrArg _ h)

/-- Right whiskering on a local pure tensor whose first factor is sent to `a'`. -/
private theorem whiskerRight_tmul_of_eq {A A' B : SheafOfModules.{u} (structureRingSheaf X)}
    (u : A ⟶ A') (V : (Opens X.carrier)ᵒᵖ) {a : A.val.obj V} {a' : A'.val.obj V}
    (b : B.val.obj V) (h : u.val.app V a = a') :
    (u ▷ B).val.app V (tmul X A B V a b) = tmul X A' B V a' b :=
  (whiskerRight_tmul u V a b).trans (congrArg (fun z ↦ tmul X A' B V z b) h)

/-- Left whiskering on a local pure tensor whose second factor is sent to `b'`. -/
private theorem whiskerLeft_tmul_of_eq {A B B' : SheafOfModules.{u} (structureRingSheaf X)}
    (v : B ⟶ B') (V : (Opens X.carrier)ᵒᵖ) (a : A.val.obj V) {b : B.val.obj V}
    {b' : B'.val.obj V} (h : v.val.app V b = b') :
    (A ◁ v).val.app V (tmul X A B V a b) = tmul X A B' V a b' :=
  (whiskerLeft_tmul v V a b).trans (congrArg (fun z ↦ tmul X A B' V a z) h)

/-- The iterated comparison carries the pullback-unit image of a local triple pure tensor to the
triple pure tensor of the three pullback-unit images. -/
theorem pullbackTwistComparison₂_hom_pullbackUnit (a b c : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) (p : (twist 𝒮 a).val.obj U)
    (q : (twist 𝒮 b).val.obj U) (r : (twist 𝒮 c).val.obj U) :
    (pullbackTwistComparison₂ 𝒮 f a b c).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f ((twist 𝒮 a ⊗ twist 𝒮 b) ⊗ twist 𝒮 c) U
          (tmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twist 𝒮 a ⊗ twist 𝒮 b) (twist 𝒮 c) U
            (tmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twist 𝒮 a) (twist 𝒮 b) U p q) r)) =
      tmul X (pullbackTwist 𝒮 f a ⊗ pullbackTwist 𝒮 f b) (pullbackTwist 𝒮 f c)
        ((opensMap f).op.obj U)
        (tmul X (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) ((opensMap f).op.obj U)
          (pullbackUnit f (twist 𝒮 a) U p) (pullbackUnit f (twist 𝒮 b) U q))
        (pullbackUnit f (twist 𝒮 c) U r) :=
  (comp_val_app_eq_of_eq _ _ _
    (pullbackTensorComparison_pullbackUnit f (twist 𝒮 a ⊗ twist 𝒮 b) (twist 𝒮 c) U
      (tmul (AlgebraicGeometry.Proj 𝒮).toRingedSpace (twist 𝒮 a) (twist 𝒮 b) U p q) r)).trans
    (whiskerRight_tmul_of_eq _ _ _
      (pullbackTensorComparison_pullbackUnit f (twist 𝒮 a) (twist 𝒮 b) U p q))

/-- **Associativity of the pulled-back twist multiplication**, as an equality of morphisms out of
`(f^*𝒪(a) ⊗ f^*𝒪(b)) ⊗ f^*𝒪(c)`; the pullback of the transport along `a + b + c = a + (b + c)` is
the only reason the two targets are not literally the same object. The multiplication maps
need not be isomorphisms. -/
theorem pullbackTwistMul_assoc (a b c : ℤ) :
    pullbackTwistMul 𝒮 f a b ▷ pullbackTwist 𝒮 f c ≫ pullbackTwistMul 𝒮 f (a + b) c =
      (α_ (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) (pullbackTwist 𝒮 f c)).hom ≫
        pullbackTwist 𝒮 f a ◁ pullbackTwistMul 𝒮 f b c ≫
          pullbackTwistMul 𝒮 f a (b + c) ≫
            (pullbackFunctor f).map
              (eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm)) := by
  refine (Iso.cancel_iso_hom_left (pullbackTwistComparison₂ 𝒮 f a b c) _ _).mp ?_
  refine pullback_tensor_hom_ext₂ f fun U p q r ↦ ?_
  have he := pullbackTwistComparison₂_hom_pullbackUnit 𝒮 f a b c U p q r
  have hL : (pullbackTwistMul 𝒮 f a b ▷ pullbackTwist 𝒮 f c ≫
        pullbackTwistMul 𝒮 f (a + b) c).val.app ((opensMap f).op.obj U)
        (tmul X (pullbackTwist 𝒮 f a ⊗ pullbackTwist 𝒮 f b) (pullbackTwist 𝒮 f c)
          ((opensMap f).op.obj U)
          (tmul X (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) ((opensMap f).op.obj U)
            (pullbackUnit f (twist 𝒮 a) U p) (pullbackUnit f (twist 𝒮 b) U q))
          (pullbackUnit f (twist 𝒮 c) U r)) =
      pullbackUnit f (twist 𝒮 (a + b + c)) U
        (mulSection 𝒮 (a + b) c U (mulSection 𝒮 a b U p q) r) :=
    (comp_val_app_eq_of_eq _ _ _ (whiskerRight_tmul_of_eq _ _ _
      (pullbackTwistMul_tmul 𝒮 f a b U p q))).trans
      (pullbackTwistMul_tmul 𝒮 f (a + b) c U (mulSection 𝒮 a b U p q) r)
  have hR : ((α_ (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) (pullbackTwist 𝒮 f c)).hom ≫
        pullbackTwist 𝒮 f a ◁ pullbackTwistMul 𝒮 f b c ≫
          pullbackTwistMul 𝒮 f a (b + c) ≫
            (pullbackFunctor f).map
              (eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm))).val.app
        ((opensMap f).op.obj U)
        (tmul X (pullbackTwist 𝒮 f a ⊗ pullbackTwist 𝒮 f b) (pullbackTwist 𝒮 f c)
          ((opensMap f).op.obj U)
          (tmul X (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) ((opensMap f).op.obj U)
            (pullbackUnit f (twist 𝒮 a) U p) (pullbackUnit f (twist 𝒮 b) U q))
          (pullbackUnit f (twist 𝒮 c) U r)) =
      pullbackUnit f (twist 𝒮 (a + b + c)) U
        ((eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm)).val.app U
          (mulSection 𝒮 a (b + c) U p (mulSection 𝒮 b c U q r))) := by
    refine (comp_val_app_eq_of_eq _ _ _ (associator_hom_tmul _ _ _ _)).trans ?_
    refine (comp_val_app_eq_of_eq _ _ _ (whiskerLeft_tmul_of_eq _ _ _
      (pullbackTwistMul_tmul 𝒮 f b c U q r))).trans ?_
    refine (comp_val_app_eq_of_eq _ _ _ (pullbackTwistMul_tmul 𝒮 f a (b + c) U p
      (mulSection 𝒮 b c U q r))).trans ?_
    exact pullbackUnit_naturality f (eqToHom (congrArg (twist 𝒮) (add_assoc a b c).symm)) U
      (mulSection 𝒮 a (b + c) U p (mulSection 𝒮 b c U q r))
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _)
    (Eq.trans ?_ (SheafOfModules.comp_val_app_apply _ _ _ _).symm)
  rw [he]
  exact Eq.trans hL (Eq.trans (congrArg (pullbackUnit f (twist 𝒮 (a + b + c)) U)
    (mulSection_assoc 𝒮 a b c U p q r)) hR.symm)

/-- Associativity of the pulled-back twist multiplication with every degree sum carried along a
transport: the inner sums `a + b` and `b + c` are replaced by degrees `a'`, `b'` equal to them,
and both outer sums are carried to a common degree `e`. -/
theorem pullbackTwistMul_assoc_transport {a b c a' b' e : ℤ} (ha : a + b = a') (hb : b + c = b')
    (h₁ : a' + c = e) (h₂ : a + b' = e) :
    (pullbackTwistMul 𝒮 f a b ≫ eqToHom (congrArg (pullbackTwist 𝒮 f) ha)) ▷
          pullbackTwist 𝒮 f c ≫
        (pullbackTwistMul 𝒮 f a' c ≫ eqToHom (congrArg (pullbackTwist 𝒮 f) h₁)) =
      (α_ (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) (pullbackTwist 𝒮 f c)).hom ≫
        pullbackTwist 𝒮 f a ◁
            (pullbackTwistMul 𝒮 f b c ≫ eqToHom (congrArg (pullbackTwist 𝒮 f) hb)) ≫
          (pullbackTwistMul 𝒮 f a b' ≫ eqToHom (congrArg (pullbackTwist 𝒮 f) h₂)) := by
  subst ha
  subst hb
  subst h₁
  simp only [eqToHom_refl, Category.comp_id]
  refine Eq.trans (pullbackTwistMul_assoc 𝒮 f a b c) ?_
  refine congrArg (fun φ ↦
    (α_ (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b) (pullbackTwist 𝒮 f c)).hom ≫
      pullbackTwist 𝒮 f a ◁ pullbackTwistMul 𝒮 f b c ≫
        pullbackTwistMul 𝒮 f a (b + c) ≫ φ) ?_
  exact eqToHom_map (pullbackFunctor f) (congrArg (twist 𝒮) (add_assoc a b c).symm)

/-! ### The left unit law -/

section Unit

/-- A twist of `Proj S`, at the ringed-space spelling of its structure sheaf of rings — the
spelling the comparison of Stacks Tag 01CD is typed in. It is not an `abbrev`: a reducible
definition would be unfolded to `Stacks.AlgebraicGeometry.TwistTensor.twist`, whose type carries
the other spelling. -/
def twistRS (a : ℤ) :
    SheafOfModules.{u} (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace) :=
  twist 𝒮 a

/-- The unit `𝒪_{Proj S} ⟶ 𝒪(0)` of the twists of `Proj S`, at the ringed-space spelling. The body
is `Stacks.AlgebraicGeometry.TwistTensor.twistUnit`. -/
def twistUnitRS :
    𝟙_ (SheafOfModules.{u} (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace)) ⟶
      twistRS 𝒮 0 :=
  twistUnit 𝒮

/-- The canonical multiplication map of the twists of `Proj S`, at the ringed-space spelling. The
body is `Stacks.AlgebraicGeometry.TwistTensor.twistMul`. -/
def twistMulRS (a b : ℤ) : twistRS 𝒮 a ⊗ twistRS 𝒮 b ⟶ twistRS 𝒮 (a + b) :=
  twistMul 𝒮 a b

/-- `twistMulRS` is `twistMul`. -/
theorem twistMulRS_eq (a b : ℤ) : twistMulRS 𝒮 a b = twistMul 𝒮 a b := rfl

/-- The left unit law of the canonical twist multiplication on `Proj S`, at the ringed-space
spelling (`Stacks.AlgebraicGeometry.TwistTensor.one_twistMul`). -/
theorem twistUnitRS_twistMulRS (b : ℤ) :
    twistUnitRS 𝒮 ▷ twistRS 𝒮 b ≫ twistMulRS 𝒮 0 b =
      (λ_ (twistRS 𝒮 b)).hom ≫ eqToHom (congrArg (twistRS 𝒮) (zero_add b).symm) :=
  one_twistMul 𝒮 b

/-- The right unit law of the canonical twist multiplication on `Proj S`, at the ringed-space
spelling (`Stacks.AlgebraicGeometry.TwistTensor.twistMul_one`). -/
theorem twistMulRS_twistUnitRS (a : ℤ) :
    twistRS 𝒮 a ◁ twistUnitRS 𝒮 ≫ twistMulRS 𝒮 a 0 =
      (ρ_ (twistRS 𝒮 a)).hom ≫ eqToHom (congrArg (twistRS 𝒮) (add_zero a).symm) :=
  twistMul_one 𝒮 a

/-- The twist `𝒪(a)` of `Proj S`, pulled back along `f`, with the twist read at the ringed-space
spelling. -/
abbrev pullbackTwistRS (a : ℤ) : SheafOfModules.{u} (structureRingSheaf X) :=
  (pullbackFunctor f).obj (twistRS 𝒮 a)

/-- The comparison of Stacks Tag 01CD at a pair of twists is an isomorphism, at the ringed-space
spelling. -/
instance isIso_pullbackTensorComparison_twistRS (a b : ℤ) :
    IsIso (pullbackTensorComparison f (twistRS 𝒮 a) (twistRS 𝒮 b)) :=
  Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison f (twistRS 𝒮 a) (twistRS 𝒮 b)

/-- The comparison of Stacks Tag 01CD at the structure sheaf and a twist is an isomorphism, at the
ringed-space spelling. -/
instance isIso_pullbackTensorComparison_unit_twistRS (b : ℤ) :
    IsIso (pullbackTensorComparison f
      (𝟙_ (SheafOfModules.{u}
        (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace))) (twistRS 𝒮 b)) :=
  Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison f _ (twistRS 𝒮 b)

/-- The comparison of Stacks Tag 01CD at a twist and the structure sheaf is an isomorphism, at the
ringed-space spelling. -/
instance isIso_pullbackTensorComparison_twistRS_unit (a : ℤ) :
    IsIso (pullbackTensorComparison f (twistRS 𝒮 a)
      (𝟙_ (SheafOfModules.{u}
        (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace)))) :=
  Stacks.PullbackTensorCoherence.isIso_pullbackTensorComparison f (twistRS 𝒮 a) _

/-- **The unit of the pulled-back twist multiplication**, `𝒪_X ⟶ f^*𝒪(0)`: the inverse of the
structure-sheaf comparison of Stacks Tag 01CD, followed by the pullback of the unit of the twists
of `Proj S`. -/
def pullbackTwistUnit : 𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) ⟶ pullbackTwistRS 𝒮 f 0 :=
  inv (pullbackUnitComparison f) ≫ (pullbackFunctor f).map (twistUnitRS 𝒮)

/-- The pulled-back multiplication, with its factors read at the ringed-space spelling. -/
def pullbackTwistMulRS (a b : ℤ) :
    pullbackTwistRS 𝒮 f a ⊗ pullbackTwistRS 𝒮 f b ⟶ pullbackTwistRS 𝒮 f (a + b) :=
  pullbackTwistMul 𝒮 f a b

/-- `pullbackTwistMulRS` is `pullbackTwistMul`. -/
theorem pullbackTwistMulRS_eq (a b : ℤ) :
    pullbackTwistMulRS 𝒮 f a b = pullbackTwistMul 𝒮 f a b := rfl

/-- The pulled-back multiplication unfolded: the inverse of the comparison of Stacks Tag 01CD
followed by the pullback of the canonical multiplication map. -/
private theorem pullbackTwistMulRS_eq_inv_comp (a b : ℤ) :
    pullbackTwistMulRS 𝒮 f a b =
      inv (pullbackTensorComparison f (twistRS 𝒮 a) (twistRS 𝒮 b)) ≫
        (pullbackFunctor f).map (twistMulRS 𝒮 a b) := rfl

/-- The structure-sheaf comparison cancels against the inverse inside the pulled-back unit. -/
private theorem pullbackUnitComparison_comp_pullbackTwistUnit :
    pullbackUnitComparison f ≫ pullbackTwistUnit 𝒮 f =
      (pullbackFunctor f).map (twistUnitRS 𝒮) :=
  IsIso.hom_inv_id_assoc (pullbackUnitComparison f) ((pullbackFunctor f).map (twistUnitRS 𝒮))

/-- Naturality of the comparison of Stacks Tag 01CD at the unit in the first variable: the
pullback of the unit whiskered into `f^*𝒪(b)`, followed by the inverse of the comparison at
`(𝒪(0), 𝒪(b))`, is the inverse of the comparison at `(𝒪_{Proj S}, 𝒪(b))` followed by the
pullback of the unit whiskered into `𝒪(b)`. -/
private theorem map_twistUnitRS_whiskerRight_comp_inv (b : ℤ) :
    (pullbackFunctor f).map (twistUnitRS 𝒮) ▷ pullbackTwistRS 𝒮 f b ≫
        inv (pullbackTensorComparison f (twistRS 𝒮 0) (twistRS 𝒮 b)) =
      inv (pullbackTensorComparison f
          (𝟙_ (SheafOfModules.{u}
            (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace))) (twistRS 𝒮 b)) ≫
        (pullbackFunctor f).map (twistUnitRS 𝒮 ▷ twistRS 𝒮 b) := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (pullbackTensorComparison_naturality_left f (B := twistRS 𝒮 b) (twistUnitRS 𝒮)).symm

/-- **The left unit law of the pulled-back twist multiplication**: the pulled-back unit whiskered
into `f^*𝒪(b)` and multiplied is the left unitor of Stacks Tag 01CA, followed by the pullback of
the transport along `b = 0 + b`. -/
theorem pullbackTwistMul_one_left (b : ℤ) :
    pullbackTwistUnit 𝒮 f ▷ pullbackTwistRS 𝒮 f b ≫ pullbackTwistMulRS 𝒮 f 0 b =
      (λ_ (pullbackTwistRS 𝒮 f b)).hom ≫
        (pullbackFunctor f).map (eqToHom (congrArg (twistRS 𝒮) (zero_add b).symm)) := by
  have hlu := (congrArg (fun z ↦ inv (pullbackTensorComparison f
        (𝟙_ (SheafOfModules.{u}
          (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace))) (twistRS 𝒮 b)) ≫ z)
      (pullbackTensorComparison_leftUnitor f (twistRS 𝒮 b))).trans
    (IsIso.inv_hom_id_assoc _ _)
  rw [← cancel_epi (pullbackUnitComparison f ▷ pullbackTwistRS 𝒮 f b), ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, pullbackUnitComparison_comp_pullbackTwistUnit,
    pullbackTwistMulRS_eq_inv_comp, ← Category.assoc, map_twistUnitRS_whiskerRight_comp_inv,
    Category.assoc, ← (pullbackFunctor f).map_comp, twistUnitRS_twistMulRS,
    (pullbackFunctor f).map_comp, ← Category.assoc, hlu, Category.assoc]

/-- The left unit law of the pulled-back twist multiplication with every degree carried along a
transport: the zero degree is replaced by a degree `a` equal to it, and the sum `a + b` by a
degree `e` equal to it. -/
theorem pullbackTwistMul_one_left_transport {a b e : ℤ} (ha : (0 : ℤ) = a) (h₁ : a + b = e)
    (h₂ : b = e) :
    (pullbackTwistUnit 𝒮 f ≫ eqToHom (congrArg (pullbackTwistRS 𝒮 f) ha)) ▷
          pullbackTwistRS 𝒮 f b ≫
        (pullbackTwistMulRS 𝒮 f a b ≫ eqToHom (congrArg (pullbackTwistRS 𝒮 f) h₁)) =
      (λ_ (pullbackTwistRS 𝒮 f b)).hom ≫ eqToHom (congrArg (pullbackTwistRS 𝒮 f) h₂) := by
  subst ha
  subst h₂
  simp only [eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, pullbackTwistMul_one_left, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- Naturality of the comparison of Stacks Tag 01CD at the unit in the second variable: the
pullback of the unit whiskered into `f^*𝒪(a)` on the left, followed by the inverse of the
comparison at `(𝒪(a), 𝒪(0))`, is the inverse of the comparison at `(𝒪(a), 𝒪_{Proj S})` followed
by the pullback of the unit whiskered into `𝒪(a)`. -/
private theorem whiskerLeft_map_twistUnitRS_comp_inv (a : ℤ) :
    pullbackTwistRS 𝒮 f a ◁ (pullbackFunctor f).map (twistUnitRS 𝒮) ≫
        inv (pullbackTensorComparison f (twistRS 𝒮 a) (twistRS 𝒮 0)) =
      inv (pullbackTensorComparison f (twistRS 𝒮 a)
          (𝟙_ (SheafOfModules.{u}
            (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace)))) ≫
        (pullbackFunctor f).map (twistRS 𝒮 a ◁ twistUnitRS 𝒮) := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (pullbackTensorComparison_naturality_right f (A := twistRS 𝒮 a) (twistUnitRS 𝒮)).symm

/-- **The right unit law of the pulled-back twist multiplication**: the pulled-back unit whiskered
into `f^*𝒪(a)` on the left and multiplied is the right unitor of Stacks Tag 01CA, followed by the
pullback of the transport along `a = a + 0`. -/
theorem pullbackTwistMul_one_right (a : ℤ) :
    pullbackTwistRS 𝒮 f a ◁ pullbackTwistUnit 𝒮 f ≫ pullbackTwistMulRS 𝒮 f a 0 =
      (ρ_ (pullbackTwistRS 𝒮 f a)).hom ≫
        (pullbackFunctor f).map (eqToHom (congrArg (twistRS 𝒮) (add_zero a).symm)) := by
  have hru := (congrArg (fun z ↦ inv (pullbackTensorComparison f (twistRS 𝒮 a)
        (𝟙_ (SheafOfModules.{u}
          (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace)))) ≫ z)
      (pullbackTensorComparison_rightUnitor f (twistRS 𝒮 a))).trans
    (IsIso.inv_hom_id_assoc _ _)
  rw [← cancel_epi (pullbackTwistRS 𝒮 f a ◁ pullbackUnitComparison f), ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, pullbackUnitComparison_comp_pullbackTwistUnit,
    pullbackTwistMulRS_eq_inv_comp, ← Category.assoc, whiskerLeft_map_twistUnitRS_comp_inv,
    Category.assoc, ← (pullbackFunctor f).map_comp, twistMulRS_twistUnitRS,
    (pullbackFunctor f).map_comp, ← Category.assoc, hru, Category.assoc]

/-- The right unit law of the pulled-back twist multiplication with every degree carried along a
transport: the zero degree is replaced by a degree `b` equal to it, and the sum `a + b` by a
degree `e` equal to it. -/
theorem pullbackTwistMul_one_right_transport {a b e : ℤ} (hb : (0 : ℤ) = b) (h₁ : a + b = e)
    (h₂ : a = e) :
    pullbackTwistRS 𝒮 f a ◁
          (pullbackTwistUnit 𝒮 f ≫ eqToHom (congrArg (pullbackTwistRS 𝒮 f) hb)) ≫
        (pullbackTwistMulRS 𝒮 f a b ≫ eqToHom (congrArg (pullbackTwistRS 𝒮 f) h₁)) =
      (ρ_ (pullbackTwistRS 𝒮 f a)).hom ≫ eqToHom (congrArg (pullbackTwistRS 𝒮 f) h₂) := by
  subst hb
  subst h₂
  simp only [eqToHom_refl, Category.comp_id]
  rw [← Category.assoc, pullbackTwistMul_one_right, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

end Unit

/-! ### The multiplication isomorphism of the degree `d` open -/

section DegreeOpen

variable (d : ℕ)

/-- The open immersion of the degree `d` open of Stacks Tag 01N5 into `Proj S`, as a morphism of
ringed spaces. -/
abbrev degreeOpenHom : (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.toRingedSpace ⟶
    (AlgebraicGeometry.Proj 𝒮).toRingedSpace :=
  (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι.toLRSHom.toShHom

/-- **The multiplication isomorphism of the degree `d` open**, retyped so that its source is the
tensor product of the monoidal structure of Stacks Tag 01CA on the sheaves of modules of the
underlying ringed space of `U_d`, and its two factors are pulled-back twists. The body is
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso`. -/
def twistMulHom (n m : ℤ) :
    pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n) ⊗
        pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * m) ⟶
      pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * (n + m)) :=
  (ProjTwistTensorPowDegreeOpen.twistMulIso 𝒮 d n m).hom

/-- `twistMulHom` is the forward map of
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso`. -/
theorem twistMulHom_eq (n m : ℤ) :
    twistMulHom 𝒮 d n m = (ProjTwistTensorPowDegreeOpen.twistMulIso 𝒮 d n m).hom := rfl

/-- **The multiplication isomorphism of the degree `d` open is the pulled-back multiplication**
along the open immersion `U_d ⟶ Proj S`, followed by the transport along `dn + dm = d(n + m)`. -/
theorem twistMulHom_eq_pullbackTwistMul (n m : ℤ) :
    twistMulHom 𝒮 d n m =
      pullbackTwistMul 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n) ((d : ℤ) * m) ≫
        eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
          (show (d : ℤ) * n + (d : ℤ) * m = (d : ℤ) * (n + m) from by ring)) := by
  have hinv : inv (pullbackTensorComparison (degreeOpenHom 𝒮 d)
        (twist 𝒮 ((d : ℤ) * n)) (twist 𝒮 ((d : ℤ) * m))) =
      (pullbackTensorModulesIso (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι
        (twistingSheaf 𝒮 ((d : ℤ) * n)) (twistingSheaf 𝒮 ((d : ℤ) * m))).inv :=
    IsIso.inv_eq_of_hom_inv_id (pullbackTensorModulesIso
      (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).ι
      (twistingSheaf 𝒮 ((d : ℤ) * n)) (twistingSheaf 𝒮 ((d : ℤ) * m))).hom_inv_id
  rw [twistMulHom, pullbackTwistMul, hinv]
  rfl

/-- **The local-section formula for the multiplication isomorphism of the degree `d` open.** On
the pure tensor of the pullback-unit images of two local sections of `𝒪(dn)` and `𝒪(dm)` it is the
pullback-unit image of their product, transported along `dn + dm = d(n + m)`. -/
theorem twistMulHom_tmul (n m : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twist 𝒮 ((d : ℤ) * n)).val.obj U) (t : (twist 𝒮 ((d : ℤ) * m)).val.obj U) :
    (twistMulHom 𝒮 d n m).val.app ((opensMap (degreeOpenHom 𝒮 d)).op.obj U)
        (tmul _ (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n))
          (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * m))
          ((opensMap (degreeOpenHom 𝒮 d)).op.obj U)
          (pullbackUnit (degreeOpenHom 𝒮 d) (twist 𝒮 ((d : ℤ) * n)) U s)
          (pullbackUnit (degreeOpenHom 𝒮 d) (twist 𝒮 ((d : ℤ) * m)) U t)) =
      (eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
            (show (d : ℤ) * n + (d : ℤ) * m = (d : ℤ) * (n + m) from by ring))).val.app
        ((opensMap (degreeOpenHom 𝒮 d)).op.obj U)
        (pullbackUnit (degreeOpenHom 𝒮 d) (twist 𝒮 ((d : ℤ) * n + (d : ℤ) * m)) U
          (mulSection 𝒮 ((d : ℤ) * n) ((d : ℤ) * m) U s t)) := by
  rw [twistMulHom_eq_pullbackTwistMul]
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  exact congrArg
    ((eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
        (show (d : ℤ) * n + (d : ℤ) * m = (d : ℤ) * (n + m) from by ring))).val.app
      ((opensMap (degreeOpenHom 𝒮 d)).op.obj U))
    (pullbackTwistMul_tmul 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n) ((d : ℤ) * m) U s t)

/-- **Associativity of the multiplication isomorphism of the degree `d` open**, in every triple
of integer degrees: the two ways of multiplying `𝒪_{U_d}(dn) ⊗ 𝒪_{U_d}(dm) ⊗ 𝒪_{U_d}(dk)` down to
a single twist agree, the transport along `d(n + (m + k)) = d(n + m + k)` being the only reason
the two targets are not literally the same object. -/
theorem twistMulHom_assoc (n m k : ℤ) :
    twistMulHom 𝒮 d n m ▷ pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * k) ≫
        twistMulHom 𝒮 d (n + m) k =
      (α_ (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n))
          (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * m))
          (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * k))).hom ≫
        pullbackTwist 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n) ◁ twistMulHom 𝒮 d m k ≫
          twistMulHom 𝒮 d n (m + k) ≫
            eqToHom (congrArg (pullbackTwist 𝒮 (degreeOpenHom 𝒮 d))
              (show (d : ℤ) * (n + (m + k)) = (d : ℤ) * (n + m + k) from by ring)) := by
  rw [twistMulHom_eq_pullbackTwistMul, twistMulHom_eq_pullbackTwistMul,
    twistMulHom_eq_pullbackTwistMul, twistMulHom_eq_pullbackTwistMul, Category.assoc,
    eqToHom_trans]
  exact pullbackTwistMul_assoc_transport 𝒮 (degreeOpenHom 𝒮 d)
    (show (d : ℤ) * n + (d : ℤ) * m = (d : ℤ) * (n + m) from by ring)
    (show (d : ℤ) * m + (d : ℤ) * k = (d : ℤ) * (m + k) from by ring)
    (show (d : ℤ) * (n + m) + (d : ℤ) * k = (d : ℤ) * (n + m + k) from by ring)
    (show (d : ℤ) * n + (d : ℤ) * (m + k) = (d : ℤ) * (n + m + k) from by ring)

/-- **The unit of the multiplication on the degree `d` open is the inverse of
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit`**, and this holds by
`rfl`: that isomorphism is by definition the pullback of
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit` along the open immersion
followed by the structure-sheaf comparison of Stacks Tag 01CD. -/
theorem pullbackTwistUnit_eq_twistZeroIsoUnit_inv :
    pullbackTwistUnit 𝒮 (degreeOpenHom 𝒮 d) =
      (ProjTwistTensorPowDegreeOpen.twistZeroIsoUnit 𝒮 d).inv := rfl

/-- **The left unit law of the multiplication isomorphism of the degree `d` open**, in every
integer degree `m`: the unit, transported to degree `d · 0`, whiskered into `𝒪_{U_d}(dm)` and
multiplied, is the left unitor of Stacks Tag 01CA followed by the transport along
`dm = d(0 + m)`. -/
theorem twistMulHom_one_left (m : ℤ) :
    (pullbackTwistUnit 𝒮 (degreeOpenHom 𝒮 d) ≫
          eqToHom (congrArg (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d))
            (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ▷
          pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * m) ≫
        twistMulHom 𝒮 d 0 m =
      (λ_ (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * m))).hom ≫
        eqToHom (congrArg (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d))
          (show (d : ℤ) * m = (d : ℤ) * (0 + m) from by ring)) :=
  (congrArg (fun z ↦
      (pullbackTwistUnit 𝒮 (degreeOpenHom 𝒮 d) ≫
          eqToHom (congrArg (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d))
            (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ▷
        pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * m) ≫ z)
    (twistMulHom_eq_pullbackTwistMul 𝒮 d 0 m)).trans
    (pullbackTwistMul_one_left_transport 𝒮 (degreeOpenHom 𝒮 d)
      (show (0 : ℤ) = (d : ℤ) * 0 from by ring)
      (show (d : ℤ) * 0 + (d : ℤ) * m = (d : ℤ) * (0 + m) from by ring)
      (show (d : ℤ) * m = (d : ℤ) * (0 + m) from by ring))

/-- **The right unit law of the multiplication isomorphism of the degree `d` open**, in every
integer degree `n`: the unit, transported to degree `d · 0`, whiskered into `𝒪_{U_d}(dn)` on the
left and multiplied, is the right unitor of Stacks Tag 01CA followed by the transport along
`dn = d(n + 0)`. -/
theorem twistMulHom_one_right (n : ℤ) :
    pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n) ◁
          (pullbackTwistUnit 𝒮 (degreeOpenHom 𝒮 d) ≫
            eqToHom (congrArg (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d))
              (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ≫
        twistMulHom 𝒮 d n 0 =
      (ρ_ (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n))).hom ≫
        eqToHom (congrArg (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d))
          (show (d : ℤ) * n = (d : ℤ) * (n + 0) from by ring)) :=
  (congrArg (fun z ↦
      pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d) ((d : ℤ) * n) ◁
          (pullbackTwistUnit 𝒮 (degreeOpenHom 𝒮 d) ≫
            eqToHom (congrArg (pullbackTwistRS 𝒮 (degreeOpenHom 𝒮 d))
              (show (0 : ℤ) = (d : ℤ) * 0 from by ring))) ≫ z)
    (twistMulHom_eq_pullbackTwistMul 𝒮 d n 0)).trans
    (pullbackTwistMul_one_right_transport 𝒮 (degreeOpenHom 𝒮 d)
      (show (0 : ℤ) = (d : ℤ) * 0 from by ring)
      (show (d : ℤ) * n + (d : ℤ) * 0 = (d : ℤ) * (n + 0) from by ring)
      (show (d : ℤ) * n = (d : ℤ) * (n + 0) from by ring))

end DegreeOpen

end Stacks.AlgebraicGeometry.TwistTensor

end
