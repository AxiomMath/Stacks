module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTrivialization
public import StacksFrontier.CategoryTheory.Functor.IsIsoMapOfHypothesis

/-!
# The cocone of the reflexive powers over the pushforward of the structure sheaf

Let `X` be an integral locally Noetherian scheme, `ℱ` a coherent reflexive `𝒪_X`-module and
`σ : 𝒪_X ⟶ ℱ` a global section of it.  Let `U ⊆ X` be an open on which `σ` is a stalkwise
isomorphism and on which `ℱ` is trivial, `ℱ|_U ≅ 𝒪_U`, and write `j : U ⟶ X` for the inclusion.
This file builds the cocone

`𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯ ⟶ j_*𝒪_U`

on the directed system `AlgebraicGeometry.CoherentReflexive.reflexivePowerModules` of reflexive
powers of [Stacks, Tag 0EBN] under multiplication by `σ`.

The open `U` of the tag is `AlgebraicGeometry.sectionIsomorphismOpen`, for which both hypotheses
hold: membership of it *is* invertibility of the stalk of `σ`, and
`AlgebraicGeometry.sectionIsomorphismOpenTrivialization` is the trivialization.  `U` is empty
exactly when `σ` generates no stalk, for instance when the section is zero.

## Main definitions

* `Stacks.CategoryTheory.invSeqLeg`: the morphisms out of the terms of a sequence obtained by
  inverting the transition maps and composing down to the first term.
* `Stacks.CategoryTheory.coconeOfSequence`: a cocone on a functor out of `ℕ`, from legs
  compatible with the steps `n ⟶ n + 1` only.
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerRestrictLeg`: the trivializations
  `ℱ^{[n]}|_U ⟶ 𝒪_U`, defined by inverting the restricted multiplication maps.
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerCocone`: **the cocone
  `ℱ^{[n]} ⟶ j_*𝒪_U`.**
* `AlgebraicGeometry.CoherentReflexive.sectionIsomorphismOpenCocone`: the same cocone on the open
  `U` of [Stacks, Tag 0EBN] attached to a global section.

## Main results

* `Stacks.SheafOfModules.TensorStalkRingedSpace.isIso_stalk_tensorSheafMap`: the stalk of the
  ordinary tensor product of two morphisms is an isomorphism as soon as the stalks of both are.
* `AlgebraicGeometry.CoherentReflexive.isIso_restrict_tensorObjMap`: **the hull tensor product of
  `σ` with an identity restricts to an isomorphism on `U`**, when both factors are trivial on
  `U`.
* `AlgebraicGeometry.CoherentReflexive.isIso_restrict_reflexivePowerStep`: **multiplication by
  `σ` restricts to an isomorphism `ℱ^{[n]}|_U ⟶ ℱ^{[n + 1]}|_U`.**

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive toDoubleDual unitModule
  reflexiveHullFunctor)
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules inclusion)

universe u v₁ u₁ u₂ v₂

/-! ### Generic steps about functors, invertibility and sequences -/

namespace Stacks.CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- **A functor carries a composite of two morphisms whose images it inverts to an
isomorphism.** -/
theorem isIso_map_comp {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D) {A B E : C} (f : A ⟶ B)
    (g : B ⟶ E) (hf : IsIso (G.map f)) (hg : IsIso (G.map g)) : IsIso (G.map (f ≫ g)) := by
  rw [G.map_comp]
  exact IsIso.comp_isIso' hf hg

/-- **A functor which inverts the images of three edges of a commuting square inverts the image
of the fourth**: the images of `f`, `g` and `k` in a square `g ≫ h = f ≫ k` being invertible, so
is the image of `h`. -/
theorem isIso_map_of_isIso_square {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D) {A B A' B' : C}
    (f : A ⟶ B) (g : A ⟶ A') (h : A' ⟶ B') (k : B ⟶ B') (hsq : g ≫ h = f ≫ k)
    (hf : IsIso (G.map f)) (hk : IsIso (G.map k)) (hg : IsIso (G.map g)) : IsIso (G.map h) := by
  have := hg
  have : IsIso (G.map g ≫ G.map h) := by
    rw [← G.map_comp, hsq]
    exact isIso_map_comp G f k hf hk
  exact IsIso.of_isIso_comp_left (G.map g) (G.map h)

/-- **Morphisms out of the terms of a sequence of isomorphisms.**  Given invertible transition
maps `f n : Z n ⟶ Z (n + 1)` and a morphism `t` out of the first term, the `n`-th morphism is
obtained by inverting the transition maps down to the first term and following `t`. -/
def invSeqLeg {Z : ℕ → C} (f : ∀ n, Z n ⟶ Z (n + 1)) (hf : ∀ n, IsIso (f n)) {Q : C}
    (t : Z 0 ⟶ Q) : ∀ n : ℕ, Z n ⟶ Q :=
  Nat.rec (motive := fun n => Z n ⟶ Q) t fun n a => (@asIso _ _ _ _ _ (hf n)).inv ≫ a

/-- In degree zero the morphism of `invSeqLeg` is the given one. -/
@[simp] theorem invSeqLeg_zero {Z : ℕ → C} (f : ∀ n, Z n ⟶ Z (n + 1)) (hf : ∀ n, IsIso (f n))
    {Q : C} (t : Z 0 ⟶ Q) : invSeqLeg f hf t 0 = t := rfl

/-- In degree `n + 1` the morphism of `invSeqLeg` is the inverse of the `n`-th transition map
followed by the morphism in degree `n`. -/
@[simp] theorem invSeqLeg_succ {Z : ℕ → C} (f : ∀ n, Z n ⟶ Z (n + 1)) (hf : ∀ n, IsIso (f n))
    {Q : C} (t : Z 0 ⟶ Q) (n : ℕ) :
    invSeqLeg f hf t (n + 1) = (@asIso _ _ _ _ _ (hf n)).inv ≫ invSeqLeg f hf t n := rfl

/-- **The morphisms of `invSeqLeg` are compatible with the transition maps.** -/
theorem comp_invSeqLeg {Z : ℕ → C} (f : ∀ n, Z n ⟶ Z (n + 1)) (hf : ∀ n, IsIso (f n)) {Q : C}
    (t : Z 0 ⟶ Q) (n : ℕ) : f n ≫ invSeqLeg f hf t (n + 1) = invSeqLeg f hf t n :=
  (@asIso _ _ _ _ _ (hf n)).hom_inv_id_assoc _

/-- **A cocone on a functor out of `ℕ`, from legs compatible with the one-step transitions.** -/
def coconeOfSequence (D : ℕ ⥤ C) (P : C) (a : ∀ n : ℕ, D.obj n ⟶ P)
    (ha : ∀ n : ℕ, D.map (homOfLE (n.le_add_right 1)) ≫ a (n + 1) = a n) :
    Limits.Cocone D where
  pt := P
  ι := NatTrans.ofSequence a fun n => (ha n).trans (Category.comp_id (a n)).symm

/-- The cocone point of `coconeOfSequence D P a ha` is `P`. -/
@[simp] theorem coconeOfSequence_pt (D : ℕ ⥤ C) (P : C) (a : ∀ n : ℕ, D.obj n ⟶ P)
    (ha : ∀ n : ℕ, D.map (homOfLE (n.le_add_right 1)) ≫ a (n + 1) = a n) :
    (coconeOfSequence D P a ha).pt = P := rfl

/-- The leg of `coconeOfSequence D P a ha` at `n` is `a n`. -/
@[simp] theorem coconeOfSequence_ι_app (D : ℕ ⥤ C) (P : C) (a : ∀ n : ℕ, D.obj n ⟶ P)
    (ha : ∀ n : ℕ, D.map (homOfLE (n.le_add_right 1)) ≫ a (n + 1) = a n) (n : ℕ) :
    (coconeOfSequence D P a ha).ι.app n = a n := rfl

end Stacks.CategoryTheory

/-! ### The stalk of a tensor product of morphisms -/

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- **The stalk of the ordinary tensor product of two morphisms of `𝒪_X`-modules is an
isomorphism as soon as the stalks of both factors are.** -/
theorem isIso_stalk_tensorSheafMap
    {F F' G G' : SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ F') (ψ : G ⟶ G')
    (x : X.carrier)
    (hφ : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map φ.val)))
    (hψ : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map ψ.val))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
            ((φ, ψ) : (_, _) ⟶ (_, _)))).val)) := by
  let sourceTensor := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G
  let targetTensor := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F').obj G'
  let tensorMorphism :=
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
      ((φ, ψ) : (F, G) ⟶ (F', G'))
  let := stalkModule X sourceTensor.val x
  let := stalkModule X targetTensor.val x
  have ha : Function.Bijective (stalkMapL X F.val F'.val φ.val x) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hφ
  have hb : Function.Bijective (stalkMapL X G.val G'.val ψ.val x) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hψ
  let ea : grpStalk X F.val x ≃ₗ[ringStalk X x] grpStalk X F'.val x :=
    LinearEquiv.ofBijective (stalkMapL X F.val F'.val φ.val x) ha
  let eb : grpStalk X G.val x ≃ₗ[ringStalk X x] grpStalk X G'.val x :=
    LinearEquiv.ofBijective (stalkMapL X G.val G'.val ψ.val x) hb
  have hmapbij : Function.Bijective (TensorProduct.map
      (stalkMapL X F.val F'.val φ.val x) (stalkMapL X G.val G'.val ψ.val x)) :=
    (TensorProduct.congr ea eb).bijective
  have hpt : ∀ z, (tensorStalkIso X x F' G')
        (stalkMapL X sourceTensor.val targetTensor.val tensorMorphism.val x z)
      = TensorProduct.map (stalkMapL X F.val F'.val φ.val x)
          (stalkMapL X G.val G'.val ψ.val x) ((tensorStalkIso X x F G) z) := fun z =>
    (LinearMap.congr_fun (tensorStalkIso_natural X x F G F' G' φ ψ) z).symm
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  change Function.Bijective
    (stalkMapL X sourceTensor.val targetTensor.val tensorMorphism.val x)
  refine ((tensorStalkIso X x F' G').bijective.of_comp_iff' _).1 ?_
  convert hmapbij.comp (tensorStalkIso X x F G).bijective using 1
  exact funext hpt

/-- **The stalk of the ordinary tensor product of a morphism with an identity is an isomorphism
as soon as the stalk of the morphism is.** -/
theorem isIso_stalk_tensorSheafMap_id_right
    {F F' : SheafOfModules.{u} (structureSheafRing X)} (φ : F ⟶ F')
    (B : SheafOfModules.{u} (structureSheafRing X)) (x : X.carrier)
    (hφ : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map φ.val))) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf (O X)).map
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
            ((φ, (𝟙 B : B ⟶ B)) : (_, _) ⟶ (_, _)))).val)) :=
  isIso_stalk_tensorSheafMap X φ (𝟙 B : B ⟶ B) x hφ
    (Functor.isIso_map_of_isIso (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _
      (Functor.isIso_map_of_isIso (PresheafOfModules.toPresheaf (O X)) (𝟙 B.val) inferInstance))

end Stacks.SheafOfModules.TensorStalkRingedSpace

/-! ### Multiplication by a section restricts to an isomorphism -/

namespace AlgebraicGeometry.CoherentReflexive

open Stacks.CategoryTheory (isIso_map_comp isIso_map_of_isIso_square invSeqLeg comp_invSeqLeg
  coconeOfSequence)
open Stacks.SheafOfModules.TensorStalkRingedSpace (isIso_stalk_tensorSheafMap_id_right)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (U : X.Opens)
  (F : CoherentReflexiveModules X) (σ : unitObj X ⟶ F)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The underlying `𝒪_X`-module morphism of a morphism of coherent reflexive modules which is an
isomorphism is an isomorphism. -/
theorem isIso_hom_hom {A B : CoherentReflexiveModules X} (f : A ⟶ B) (h : IsIso f) :
    IsIso f.hom.hom :=
  Functor.isIso_map_of_isIso (inclusion X ⋙ ObjectProperty.ι _) f h

/-- **The underlying `𝒪_X`-module morphism of the hull tensor product of a morphism with an
identity is the double dual of the ordinary one.** -/
theorem tensorObjMap_id_right_hom_hom {A A' : CoherentReflexiveModules X} (f : A ⟶ A')
    (B : CoherentReflexiveModules X) :
    (tensorObjMap f (𝟙 B)).hom.hom
      = (reflexiveHullFunctor X).map
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            (X := (A.obj.obj, B.obj.obj)) (Y := (A'.obj.obj, B.obj.obj))
            (f.hom.hom, 𝟙 B.obj.obj)) :=
  hullReflection_map_hom_hom X (S := ordinaryTensor A B) (S' := ordinaryTensor A' B)
    (ObjectProperty.homMk
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          (X := (A.obj.obj, B.obj.obj)) (Y := (A'.obj.obj, B.obj.obj))
          (f.hom.hom, 𝟙 B.obj.obj)))

/-- **Multiplication by a section is the left unit constraint followed by the hull tensor product
with an identity**, on underlying `𝒪_X`-module morphisms. -/
theorem reflexivePowerStep_hom_hom (n : ℕ) :
    (reflexivePowerStep F σ n).hom.hom
      = ((unitTensorObj (reflexivePower F n)).inv).hom.hom
        ≫ (tensorObjMap σ (𝟙 (reflexivePower F n))).hom.hom := rfl

omit [IsIntegral X] in
/-- **The *ordinary* tensor product of a section with an identity restricts to an isomorphism on
an open on which the section is a stalkwise isomorphism.** -/
theorem isIso_restrict_ordinaryTensorMap (P : CoherentReflexiveModules X)
    (hσ : ∀ x : X, x ∈ U → IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map σ.hom.hom))) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (X := ((unitObj X).obj.obj, P.obj.obj)) (Y := (F.obj.obj, P.obj.obj))
        (σ.hom.hom, 𝟙 P.obj.obj)))) :=
  isIso_restrictFunctor_map_of_forall_mem_isIso U _ fun x hx =>
    isIso_stalk_tensorSheafMap_id_right X.toRingedSpace σ.hom.hom P.obj.obj x (hσ x hx)

omit [IsIntegral X] in
/-- **The canonical map to the double dual of an ordinary tensor product restricts to an
isomorphism on an open on which both factors are trivial.** -/
theorem isIso_restrict_toDoubleDual_ordinaryTensor (A B : CoherentReflexiveModules X)
    (eA : Scheme.Modules.restrict A.obj.obj U.ι ≅ unitModule U.toScheme)
    (eB : Scheme.Modules.restrict B.obj.obj U.ι ≅ unitModule U.toScheme) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (toDoubleDual (ordinaryTensor A B).obj)) :=
  have : _root_.SheafOfModules.IsCoherent (ordinaryTensor A B).obj :=
    (ordinaryTensor A B).property
  Stacks.AlgebraicGeometry.ReflexiveEquivalence.isIso_restrict_toDoubleDual U _
    (isReflexive_restrict_tensorObj_of_unitIso U A B eA eB)

/-- **The naturality square of the canonical map to the double dual, with its bottom edge written
as the hull tensor product of `σ` with an identity.** -/
theorem toDoubleDual_naturality_tensorObjMap (P : CoherentReflexiveModules X) :
    toDoubleDual (ordinaryTensor (unitObj X) P).obj ≫ (tensorObjMap σ (𝟙 P)).hom.hom
      = ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (X := ((unitObj X).obj.obj, P.obj.obj)) (Y := (F.obj.obj, P.obj.obj))
        (σ.hom.hom, 𝟙 P.obj.obj))
        ≫ toDoubleDual (ordinaryTensor F P).obj :=
  (congrArg
    (fun m : (reflexiveHullFunctor X).obj (ordinaryTensor (unitObj X) P).obj ⟶
        (reflexiveHullFunctor X).obj (ordinaryTensor F P).obj =>
      toDoubleDual (ordinaryTensor (unitObj X) P).obj ≫ m)
    (tensorObjMap_id_right_hom_hom σ P)).symm.trans
    (Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_naturality _).symm

/-- **The hull tensor product of a section with an identity restricts to an isomorphism on an
open on which both factors are trivial.** -/
theorem isIso_restrict_tensorObjMap (P : CoherentReflexiveModules X)
    (hσ : ∀ x : X, x ∈ U → IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map σ.hom.hom)))
    (eF : Scheme.Modules.restrict F.obj.obj U.ι ≅ unitModule U.toScheme)
    (eP : Scheme.Modules.restrict P.obj.obj U.ι ≅ unitModule U.toScheme) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (tensorObjMap σ (𝟙 P)).hom.hom) :=
  isIso_map_of_isIso_square (Scheme.Modules.restrictFunctor U.ι)
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (X := ((unitObj X).obj.obj, P.obj.obj)) (Y := (F.obj.obj, P.obj.obj))
        (σ.hom.hom, 𝟙 P.obj.obj)))
    (toDoubleDual (ordinaryTensor (unitObj X) P).obj)
    (tensorObjMap σ (𝟙 P)).hom.hom
    (toDoubleDual (ordinaryTensor F P).obj)
    (toDoubleDual_naturality_tensorObjMap F σ P)
    (isIso_restrict_ordinaryTensorMap U F σ P hσ)
    (isIso_restrict_toDoubleDual_ordinaryTensor U F P eF eP)
    (isIso_restrict_toDoubleDual_ordinaryTensor U (unitObj X) P
      (Scheme.Modules.restrictUnitIso U.ι) eP)

/-- **Multiplication by `σ` restricts to an isomorphism `ℱ^{[n]}|_U ⟶ ℱ^{[n + 1]}|_U`** on an
open on which `σ` is a stalkwise isomorphism and `ℱ` is trivial. -/
theorem isIso_restrict_reflexivePowerStep
    (hσ : ∀ x : X, x ∈ U → IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map σ.hom.hom)))
    (eF : Scheme.Modules.restrict F.obj.obj U.ι ≅ unitModule U.toScheme) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (reflexivePowerStep F σ n).hom.hom) :=
  Eq.mpr (congrArg
    (fun k : (reflexivePower F n).obj.obj ⟶ (reflexivePower F (n + 1)).obj.obj =>
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map k))
    (reflexivePowerStep_hom_hom F σ n))
    (isIso_map_comp (Scheme.Modules.restrictFunctor U.ι)
      ((unitTensorObj (reflexivePower F n)).inv).hom.hom
      (tensorObjMap σ (𝟙 (reflexivePower F n))).hom.hom
      (Functor.isIso_map_of_isIso (Scheme.Modules.restrictFunctor U.ι) _
        (isIso_hom_hom _ (Iso.isIso_inv (unitTensorObj (reflexivePower F n)))))
      (isIso_restrict_tensorObjMap U F σ (reflexivePower F n) hσ eF
        (reflexivePowerRestrictUnitIso U F eF n)))

/-! ### The cocone -/

variable (hstep : ∀ n : ℕ, IsIso ((Scheme.Modules.restrictFunctor U.ι).map
  (reflexivePowerStep F σ n).hom.hom))

/-- **The trivializations `ℱ^{[n]}|_U ⟶ 𝒪_U`, compatible with multiplication by `σ`.**  In
degree zero it is the canonical identification `𝒪_X|_U ≅ 𝒪_U` of
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, and each further one is the inverse of the
restricted multiplication map followed by the previous one. -/
def reflexivePowerRestrictLeg (n : ℕ) :
    Scheme.Modules.restrict (reflexivePower F n).obj.obj U.ι ⟶ unitModule U.toScheme :=
  invSeqLeg (Z := fun n => Scheme.Modules.restrict (reflexivePower F n).obj.obj U.ι)
    (fun n => (Scheme.Modules.restrictFunctor U.ι).map (reflexivePowerStep F σ n).hom.hom)
    hstep (Scheme.Modules.restrictUnitIso U.ι).hom n

/-- **The trivializations are compatible with multiplication by `σ`.** -/
theorem reflexivePowerStep_comp_reflexivePowerRestrictLeg (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (reflexivePowerStep F σ n).hom.hom ≫
        reflexivePowerRestrictLeg U F σ hstep (n + 1)
      = reflexivePowerRestrictLeg U F σ hstep n :=
  comp_invSeqLeg (Z := fun n => Scheme.Modules.restrict (reflexivePower F n).obj.obj U.ι)
    (fun n => (Scheme.Modules.restrictFunctor U.ι).map (reflexivePowerStep F σ n).hom.hom)
    hstep (Scheme.Modules.restrictUnitIso U.ι).hom n

/-- **The legs `ℱ^{[n]} ⟶ j_*𝒪_U` of the cocone**, the adjoints of the trivializations under the
restriction–pushforward adjunction `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`. -/
def reflexivePowerPushforwardLeg (n : ℕ) :
    (reflexivePower F n).obj.obj ⟶
      (Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme) :=
  (Scheme.Modules.restrictAdjunction U.ι).homEquiv _ _ (reflexivePowerRestrictLeg U F σ hstep n)

/-- **The legs are compatible with multiplication by `σ`.** -/
theorem reflexivePowerStep_comp_reflexivePowerPushforwardLeg (n : ℕ) :
    (reflexivePowerStep F σ n).hom.hom ≫ reflexivePowerPushforwardLeg U F σ hstep (n + 1)
      = reflexivePowerPushforwardLeg U F σ hstep n :=
  ((Scheme.Modules.restrictAdjunction U.ι).homEquiv_naturality_left
      (reflexivePowerStep F σ n).hom.hom
      (reflexivePowerRestrictLeg U F σ hstep (n + 1))).symm.trans
    (congrArg (fun t : Scheme.Modules.restrict (reflexivePower F n).obj.obj U.ι ⟶
          unitModule U.toScheme =>
        (Scheme.Modules.restrictAdjunction U.ι).homEquiv (reflexivePower F n).obj.obj
          (unitModule U.toScheme) t)
      (reflexivePowerStep_comp_reflexivePowerRestrictLeg U F σ hstep n))

/-- The transition map of the directed system read in `X.Modules` is the underlying morphism of
multiplication by `σ`. -/
theorem reflexivePowerModules_map_succ (n : ℕ) :
    (reflexivePowerModules F σ).map (homOfLE (n.le_add_right 1))
      = (reflexivePowerStep F σ n).hom.hom :=
  congrArg (fun k : reflexivePower F n ⟶ reflexivePower F (n + 1) => k.hom.hom)
    (Functor.ofSequence_map_homOfLE_succ (reflexivePowerStep F σ) n)

/-- **The cocone `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯ ⟶ j_*𝒪_U`** of the colimit assertion of
[Stacks, Tag 0EBN], on the directed system `reflexivePowerModules` of reflexive powers under
multiplication by `σ`.  Its legs are the adjoints of the trivializations
`reflexivePowerRestrictLeg`. -/
def reflexivePowerCocone : Limits.Cocone (reflexivePowerModules F σ) :=
  coconeOfSequence (reflexivePowerModules F σ)
    ((Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme))
    (fun n => reflexivePowerPushforwardLeg U F σ hstep n) fun n =>
      (congrArg
        (fun k : (reflexivePower F n).obj.obj ⟶ (reflexivePower F (n + 1)).obj.obj =>
          k ≫ reflexivePowerPushforwardLeg U F σ hstep (n + 1))
        (reflexivePowerModules_map_succ F σ n)).trans
      (reflexivePowerStep_comp_reflexivePowerPushforwardLeg U F σ hstep n)

/-- The point of the cocone is `j_*𝒪_U`. -/
theorem reflexivePowerCocone_pt :
    (reflexivePowerCocone U F σ hstep).pt
      = (Scheme.Modules.pushforward U.ι).obj (unitModule U.toScheme) := rfl

/-- The `n`-th leg of the cocone is the adjoint of the `n`-th trivialization. -/
theorem reflexivePowerCocone_ι_app (n : ℕ) :
    (reflexivePowerCocone U F σ hstep).ι.app n = reflexivePowerPushforwardLeg U F σ hstep n := rfl

/-! ### The cocone on the open of [Stacks, Tag 0EBN] -/

/-- The morphism `𝒪_X ⟶ ℱ` of coherent reflexive modules attached to a global section of a
coherent reflexive module, through Mathlib's `SheafOfModules.unitHomEquiv`. -/
def sectionObjHom (s : F.obj.obj.sections) : unitObj X ⟶ F :=
  ObjectProperty.homMk (ObjectProperty.homMk (F.obj.obj.unitHomEquiv.symm s))

omit [IsIntegral X] in
/-- The underlying `𝒪_X`-module morphism of `sectionObjHom` is the one
`SheafOfModules.unitHomEquiv` attaches to the section. -/
theorem sectionObjHom_hom_hom (s : F.obj.obj.sections) :
    (sectionObjHom F s).hom.hom = F.obj.obj.unitHomEquiv.symm s := rfl

variable [IsNormal X] [_root_.SheafOfModules.IsCoherent F.obj.obj]

/-- **At a point of its isomorphism locus the section is a stalkwise isomorphism.** -/
theorem isIso_stalk_sectionObjHom (s : F.obj.obj.sections) (x : X)
    (hx : x ∈ sectionIsomorphismOpen X F.obj.obj s) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((Scheme.Modules.toPresheaf X).map (sectionObjHom F s).hom.hom)) := hx

/-- **Multiplication by a section restricts to an isomorphism on the open `U` of
[Stacks, Tag 0EBN]**, the isomorphism locus of the section itself. -/
theorem isIso_restrict_reflexivePowerStep_sectionIsomorphismOpen (s : F.obj.obj.sections)
    (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionIsomorphismOpen X F.obj.obj s).ι).map
      (reflexivePowerStep F (sectionObjHom F s) n).hom.hom) :=
  isIso_restrict_reflexivePowerStep (sectionIsomorphismOpen X F.obj.obj s) F (sectionObjHom F s)
    (isIso_stalk_sectionObjHom F s) (sectionIsomorphismOpenTrivialization F.obj.obj s).symm n

/-- **The cocone `ℱ^{[n]} ⟶ j_*𝒪_U` on the open `U` of [Stacks, Tag 0EBN]** attached to a global
section `s` of a coherent reflexive module `ℱ`, `U` being the locus where `s` induces an
isomorphism on stalks. -/
def sectionIsomorphismOpenCocone (s : F.obj.obj.sections) :
    Limits.Cocone (reflexivePowerModules F (sectionObjHom F s)) :=
  reflexivePowerCocone (sectionIsomorphismOpen X F.obj.obj s) F (sectionObjHom F s)
    (isIso_restrict_reflexivePowerStep_sectionIsomorphismOpen F s)

end AlgebraicGeometry.CoherentReflexive

end
