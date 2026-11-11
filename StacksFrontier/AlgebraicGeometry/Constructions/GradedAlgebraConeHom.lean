module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleEssSurj
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Full

/-!
# Morphisms of cones from homomorphisms of graded algebras

Let `S` be a scheme and `φ : 𝒜 ⟶ ℬ` a unital homomorphism of quasi-coherent sheaves of graded
`𝒪_S`-algebras, both concentrated in nonnegative degrees with degree-zero piece `𝒪_S` and with
commutative homogeneous multiplication. The relative spectrum is contravariant in the algebra, so
`φ` induces a morphism `Spec_S(ℬ) ⟶ Spec_S(𝒜)` over `S`. This file shows that this morphism is a
**morphism of cones** in the sense of Tag 062R between the cones
`AlgebraicGeometry.GradedAlgebraCone.cone` carried by the two relative spectra: its pullback on
functions realizes `φ` on every homogeneous piece.

## Main definitions

* `AlgebraicGeometry.AbstractCone.homOfOverHom`: a morphism of total spaces over `S` whose map on
  direct images realizes a graded map on the homogeneous pieces, as a morphism of cones.
* `AlgebraicGeometry.GradedAlgebraCone.coneOverHom`: the morphism `Spec_S(ℬ) ⟶ Spec_S(𝒜)` over
  `S` induced by `φ`.
* `AlgebraicGeometry.GradedAlgebraCone.coneHom`: **that morphism, as a morphism of cones** with
  graded part `φ`.

## Main results

* `AlgebraicGeometry.GradedAlgebraCone.ringSheafMap_coneOverHom_ι`: on direct images, the
  morphism realizes `φ` on homogeneous local sections.

## References

* [Stacks Project, Tag 062R](https://stacks.math.columbia.edu/tag/062R)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

namespace AlgebraicGeometry

universe u

namespace AbstractCone

/-- Sectionwise, the morphism of underlying sheaves of rings of the map on pushed-forward
structure sheaves induced by a morphism over `S` is the canonical map on sections. -/
theorem ringSheafMap_pushforwardAlgebraMap_apply {S : Scheme.{u}} {Xo Yo : Over S} (f : Xo ⟶ Yo)
    (U : S.Opens) (hle : Xo.hom ⁻¹ᵁ U ≤ f.left ⁻¹ᵁ (Yo.hom ⁻¹ᵁ U))
    (a : Yo.left.presheaf.obj (op (Yo.hom ⁻¹ᵁ U))) :
    ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap f)).hom.app (op U)).hom a =
      f.left.appLE (Yo.hom ⁻¹ᵁ U) (Xo.hom ⁻¹ᵁ U) hle a :=
  congrArg (fun ψ : (pushforwardAlgebra Yo.hom).right.obj.obj (op U) ⟶
      (pushforwardAlgebra Xo.hom).right.obj.obj (op U) => ψ.hom a)
    (pushforwardAlgebraMap_app f U hle)

/-- **A morphism of total spaces over `S` whose map on direct images realizes a graded map on the
homogeneous pieces is a morphism of cones.** -/
def homOfOverHom {S : Scheme.{u}} (V W : AbstractCone S) (g : Over.mk W.π ⟶ Over.mk V.π)
    (ψ : SheafOfModules.GradedAlgebra.Hom V.grading W.grading)
    (h : ∀ (n : ℤ) (U : S.Opens) (x : (V.grading.piece n).val.obj (op U)),
      ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap g)).hom.app (op U)).hom
          ((V.ι n).val.app (op U) x) =
        (W.ι n).val.app (op U) ((ψ.app n).val.app (op U) x)) :
    Hom W V where
  f := g.left
  comm := Over.w g
  pullback := AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap g)
  pullback_app U a :=
    (ringSheafMap_pushforwardAlgebraMap_apply g U (preimage_le_preimage_preimage _ _) a).trans
      (Hom.c_app_eq_appLE (Over.w g) U _ a).symm
  graded := ψ
  ι_naturality n := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T => ?_)
    induction T with
    | op U => exact ModuleCat.hom_ext (LinearMap.ext fun x => h n U x)

/-- The morphism of total spaces of `AlgebraicGeometry.AbstractCone.homOfOverHom` is the given
morphism. -/
@[simp] theorem homOfOverHom_f {S : Scheme.{u}} (V W : AbstractCone S)
    (g : Over.mk W.π ⟶ Over.mk V.π) (ψ : SheafOfModules.GradedAlgebra.Hom V.grading W.grading)
    (h : ∀ (n : ℤ) (U : S.Opens) (x : (V.grading.piece n).val.obj (op U)),
      ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap g)).hom.app (op U)).hom
          ((V.ι n).val.app (op U) x) =
        (W.ι n).val.app (op U) ((ψ.app n).val.app (op U) x)) :
    (homOfOverHom V W g ψ h).f = g.left := rfl

/-- **On direct images, a morphism over `S` whose map on pushed-forward structure sheaves is an
algebra map `ψ` read through two identifications realizes `ψ`**, as a statement about sections of
the underlying sheaves of rings. -/
theorem ringSheafMap_pushforwardAlgebraMap_inv_apply {S C D : Scheme.{u}} {p : C ⟶ S}
    {q : D ⟶ S} (g : Over.mk q ⟶ Over.mk p) {A' B' : AlgebraSheaf S}
    (eA : pushforwardAlgebra p ≅ A') (eB : pushforwardAlgebra q ≅ B') (ψ : A' ⟶ B')
    (hg : pushforwardAlgebraMap g = eA.hom ≫ ψ ≫ eB.inv) (U : (Opens ↥S)ᵒᵖ)
    (z : (AlgebraSheaf.ringSheaf A').obj.obj U) :
    ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap g)).hom.app U).hom
        (((AlgebraSheaf.ringSheafMap eA.inv).hom.app U).hom z) =
      ((AlgebraSheaf.ringSheafMap eB.inv).hom.app U).hom
        (((AlgebraSheaf.ringSheafMap ψ).hom.app U).hom z) := by
  have h : AlgebraSheaf.ringSheafMap eA.inv ≫
      AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap g) =
        AlgebraSheaf.ringSheafMap ψ ≫ AlgebraSheaf.ringSheafMap eB.inv := by
    rw [← AlgebraSheaf.ringSheafMap_comp, ← AlgebraSheaf.ringSheafMap_comp, hg,
      Iso.inv_hom_id_assoc]
  exact congrArg (fun k : AlgebraSheaf.ringSheaf A' ⟶
      AlgebraSheaf.ringSheaf (pushforwardAlgebra q) => (k.hom.app U).hom z) h

end AbstractCone

namespace GradedAlgebraCone

variable (X : Scheme.{u}) {A B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
  (hcA : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
    HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
  (hcB : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (B.piece i).val.obj W) (b : (B.piece j).val.obj W),
    HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))
  [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hcA)]
  [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X B hcB)]
  (φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
  (pzA : A.piece 0 ≅ SheafOfModules.unit X.ringCatSheaf)
  (hpzA : ∀ U : (Opens ↥X)ᵒᵖ, pzA.hom.val.app U (A.one.eval U) = (1 : X.ringCatSheaf.obj.obj U))
  (hzA : ∀ n : ℤ, n < 0 → IsZero (A.piece n))
  (pzB : B.piece 0 ≅ SheafOfModules.unit X.ringCatSheaf)
  (hpzB : ∀ U : (Opens ↥X)ᵒᵖ, pzB.hom.val.app U (B.one.eval U) = (1 : X.ringCatSheaf.obj.obj U))
  (hzB : ∀ n : ℤ, n < 0 → IsZero (B.piece n))

/-- The identification of Tag 01LX(3) of the direct image of the cone `Spec_S(𝒜)` with the
ungraded realization of `𝒜`, as an isomorphism of algebra sheaves. -/
def pushforwardAlgebraIsoCone :
    pushforwardAlgebra (cone X A hcA pzA hpzA hzA).π ≅ gradedAlgebraSheaf X A hcA :=
  pushforwardAlgebraIso (gradedAlgebraSheaf X A hcA)

/-- The inclusion of a homogeneous piece into the direct image of the cone `Spec_S(𝒜)` is the
sheafification unit followed by the identification of Tag 01LX(3). -/
theorem ι_cone_app (n : ℤ) (U : X.Opens) (x : (A.piece n).val.obj (op U)) :
    ((cone X A hcA pzA hpzA hzA).ι n).val.app (op U) x =
      ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraIsoCone X hcA pzA hpzA hzA).inv).hom.app
        (op U)).hom (A.ungradedIncl n x) := rfl

/-- **The morphism `Spec_S(ℬ) ⟶ Spec_S(𝒜)` over `S` induced by a unital homomorphism
`φ : 𝒜 ⟶ ℬ` of sheaves of graded algebras**: the morphism of relative spectra attached to the
morphism of ungraded realizations. -/
def coneOverHom :
    Over.mk (cone X B hcB pzB hpzB hzB).π ⟶ Over.mk (cone X A hcA pzA hpzA hzA).π :=
  haveI : IsAffineHom (Over.mk (cone X A hcA pzA hpzA hzA).π).hom :=
    (cone X A hcA pzA hpzA hzA).isAffine
  overHomOfAlgebraHom ((pushforwardAlgebraIsoCone X hcA pzA hpzA hzA).hom ≫
    gradedAlgebraSheafMap X φ hcA hcB ≫ (pushforwardAlgebraIsoCone X hcB pzB hpzB hzB).inv)

/-- The map on pushed-forward structure sheaves of the morphism induced by `φ` is the morphism of
ungraded realizations, read through the identifications of Tag 01LX(3). -/
theorem pushforwardAlgebraMap_coneOverHom :
    pushforwardAlgebraMap (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB) =
      (pushforwardAlgebraIsoCone X hcA pzA hpzA hzA).hom ≫
        gradedAlgebraSheafMap X φ hcA hcB ≫ (pushforwardAlgebraIsoCone X hcB pzB hpzB hzB).inv :=
  haveI : IsAffineHom (Over.mk (cone X A hcA pzA hpzA hzA).π).hom :=
    (cone X A hcA pzA hpzA hzA).isAffine
  pushforwardAlgebraMap_overHomOfAlgebraHom _

/-- The morphism induced by `φ` on direct images, on the image of a section of the ungraded
realization of `𝒜` under the identification of Tag 01LX(3). -/
theorem ringSheafMap_coneOverHom_apply (U : X.Opens)
    (z : (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X A hcA)).obj.obj (op U)) :
    ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap
        (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB))).hom.app (op U)).hom
        (((AlgebraSheaf.ringSheafMap (pushforwardAlgebraIsoCone X hcA pzA hpzA hzA).inv).hom.app
          (op U)).hom z) =
      ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraIsoCone X hcB pzB hpzB hzB).inv).hom.app
        (op U)).hom (((AlgebraSheaf.ringSheafMap (gradedAlgebraSheafMap X φ hcA hcB)).hom.app
          (op U)).hom z) :=
  AbstractCone.ringSheafMap_pushforwardAlgebraMap_inv_apply
    (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB)
    (pushforwardAlgebraIsoCone X hcA pzA hpzA hzA)
    (pushforwardAlgebraIsoCone X hcB pzB hpzB hzB)
    (gradedAlgebraSheafMap X φ hcA hcB)
    (pushforwardAlgebraMap_coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB) (op U) z

omit [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X A hcA)]
  [AlgebraSheaf.IsQuasicoherent (gradedAlgebraSheaf X B hcB)] in
/-- The morphism of algebra sheaves induced by `φ` is the degreewise map on homogeneous local
sections. -/
theorem ringSheafMap_gradedAlgebraSheafMap_ungradedIncl (n : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (op U)) :
    ((AlgebraSheaf.ringSheafMap (gradedAlgebraSheafMap X φ hcA hcB)).hom.app (op U)).hom
        (A.ungradedIncl n x) = B.ungradedIncl n ((φ.app n).val.app (op U) x) :=
  SheafOfModules.GradedAlgebra.ungradedIncl_ungradedSheafMap φ n x

/-- The morphism induced by `φ` on direct images, evaluated on the image of a homogeneous section
of `𝒜` under the identification of Tag 01LX(3). -/
theorem ringSheafMap_coneOverHom_ungradedIncl (n : ℤ) (U : X.Opens)
    (x : (A.piece n).val.obj (op U)) :
    ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap
        (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB))).hom.app (op U)).hom
        (((AlgebraSheaf.ringSheafMap (pushforwardAlgebraIsoCone X hcA pzA hpzA hzA).inv).hom.app
          (op U)).hom (A.ungradedIncl n x)) =
      ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraIsoCone X hcB pzB hpzB hzB).inv).hom.app
        (op U)).hom (B.ungradedIncl n ((φ.app n).val.app (op U) x)) :=
  (ringSheafMap_coneOverHom_apply X hcA hcB φ pzA hpzA hzA pzB hpzB hzB U
      (A.ungradedIncl n x)).trans
    (congrArg (fun z : (AlgebraSheaf.ringSheaf (gradedAlgebraSheaf X B hcB)).obj.obj (op U) =>
        ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraIsoCone X hcB pzB hpzB hzB).inv).hom.app
          (op U)).hom z)
      (ringSheafMap_gradedAlgebraSheafMap_ungradedIncl X hcA hcB φ n U x))

/-- **The morphism induced by `φ` realizes `φ` on homogeneous local sections**: pulling back the
function a homogeneous section of `𝒜` is gives the function its image under `φ` is. -/
theorem ringSheafMap_coneOverHom_ι (n : ℤ) (U : X.Opens) (x : (A.piece n).val.obj (op U)) :
    ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap
        (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB))).hom.app (op U)).hom
        (((cone X A hcA pzA hpzA hzA).ι n).val.app (op U) x) =
      ((cone X B hcB pzB hpzB hzB).ι n).val.app (op U) ((φ.app n).val.app (op U) x) :=
  ((congrArg (fun y => ((AlgebraSheaf.ringSheafMap (pushforwardAlgebraMap
      (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB))).hom.app (op U)).hom y)
      (ι_cone_app X hcA pzA hpzA hzA n U x)).trans
    (ringSheafMap_coneOverHom_ungradedIncl X hcA hcB φ pzA hpzA hzA pzB hpzB hzB n U x)).trans
    (ι_cone_app X hcB pzB hpzB hzB n U _).symm

/-- **The morphism `Spec_S(ℬ) ⟶ Spec_S(𝒜)` induced by a unital homomorphism `φ : 𝒜 ⟶ ℬ` of
graded algebras is a morphism of cones**, in the sense of Tag 062R, from the cone `Spec_S(ℬ)` to
the cone `Spec_S(𝒜)`, with graded part `φ`. -/
def coneHom :
    AbstractCone.Hom (cone X B hcB pzB hpzB hzB) (cone X A hcA pzA hpzA hzA) :=
  AbstractCone.homOfOverHom (cone X A hcA pzA hpzA hzA) (cone X B hcB pzB hpzB hzB)
    (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB) φ.toHom
    (ringSheafMap_coneOverHom_ι X hcA hcB φ pzA hpzA hzA pzB hpzB hzB)

/-- The morphism of total spaces of `AlgebraicGeometry.GradedAlgebraCone.coneHom` is the
morphism of relative spectra induced by `φ`. -/
@[simp] theorem coneHom_f :
    (coneHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB).f =
      (coneOverHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB).left := rfl

/-- The graded part of `AlgebraicGeometry.GradedAlgebraCone.coneHom` is `φ`. -/
@[simp] theorem coneHom_graded :
    (coneHom X hcA hcB φ pzA hpzA hzA pzB hpzB hzB).graded = φ.toHom := rfl

end GradedAlgebraCone

end AlgebraicGeometry

end
