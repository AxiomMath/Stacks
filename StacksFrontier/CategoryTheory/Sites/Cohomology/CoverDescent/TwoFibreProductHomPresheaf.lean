module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheaf
public import StacksFrontier.CategoryTheory.Sites.PushforwardSections
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# The presheaf represented by the 2-fibre product with a slice is a Hom presheaf

Let `p𝒳 : 𝒳 ⥤ 𝒞` and `p𝒴 : 𝒴 ⥤ 𝒞` be categories over `𝒞` with `p𝒴` fibred in groupoids, let
`f : 𝒳 ⥤ 𝒴` be a functor over `𝒞` and let `y` be an object of `𝒴` lying over `V`, presented by a
cartesian slice datum `D` (a 1-morphism `𝒞/V ⥤ 𝒴` with a cone of strongly cartesian lifts to `y`,
for instance the 1-morphism `y : (Sch/V) ⟶ 𝒴` of the 2-Yoneda lemma). The projection of the
2-fibre product `(𝒞/V) ×_𝒴 𝒳` to `𝒳` represents, in the sense of
`Stacks.Sites.CoverDescent.componentPresheaf`, the presheaf

`x ↦ Hom_𝒴(f(x), y)`

on `𝒳`. The class of an arrow `φ : x ⟶ ζ.y` into the second component of an object `ζ` of the
2-fibre product goes to `f(φ)` followed by the comparison arrow `f(ζ.y) ⟶ y` of `ζ`; the inverse
sends `g : f(x) ⟶ y` to the class of the identity of `x`, read as an arrow into the object of the
2-fibre product that `g` determines.

This is the presheaf whose free abelian sheaf corepresents the sections over `y` of the direct
image along a cocontinuous functor, so the identification is what places that sheaf in the
Čech dévissage of Stacks 07AK.

## Main definitions

* `Stacks.Sites.CoverDescent.twoFibreProductHomPresheafIso`: the isomorphism
  `Ψ(pr₂) ≅ f^{op} ⋙ Hom(-, y)`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Presheaf

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace Stacks.Sites.CoverDescent

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) {y : 𝒴} (D : p𝒴.CartesianSliceDatum y)

/-- The projection of the 2-fibre product `(𝒞/V) ×_𝒴 𝒳` to `𝒳`. -/
abbrev sliceTwoFibreProductSnd :
    TwoFibreProductOver (Over.forget (p𝒴.obj y)) p𝒳 p𝒴 D.sliceMor f ⥤ 𝒳 :=
  TwoFibreProductOver.snd (Over.forget (p𝒴.obj y)) p𝒳 p𝒴 D.sliceMor f

/-- The arrow `f(x) ⟶ y` attached to an arrow `x ⟶ ζ.y` into an object of the 2-fibre product. -/
abbrev sliceArrowHom {x : 𝒳}
    (a : StructuredArrow x (sliceTwoFibreProductSnd p𝒳 p𝒴 f D)) : f.obj x ⟶ y :=
  f.map a.hom ≫ ((Presheaf.pushforwardIndexFunctor p𝒳 p𝒴 f D).obj a.right).hom

/-- The arrow attached to an arrow into the 2-fibre product is constant along morphisms. -/
lemma sliceArrowHom_eq_of_hom {x : 𝒳}
    {a b : StructuredArrow x (sliceTwoFibreProductSnd p𝒳 p𝒴 f D)} (m : a ⟶ b) :
    sliceArrowHom p𝒳 p𝒴 f D a = sliceArrowHom p𝒳 p𝒴 f D b := by
  have hw' : f.map b.hom =
      f.map a.hom ≫ f.map ((sliceTwoFibreProductSnd p𝒳 p𝒴 f D).map m.right) := by
    rw [← StructuredArrow.w m, Functor.map_comp]
  have hc := CostructuredArrow.w ((Presheaf.pushforwardIndexFunctor p𝒳 p𝒴 f D).map m.right)
  exact (congrArg (fun t => f.map a.hom ≫ t) hc.symm).trans ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ ((Presheaf.pushforwardIndexFunctor p𝒳 p𝒴 f D).obj b.right).hom) hw'.symm))

/-- The arrow attached to an arrow into the 2-fibre product is constant on components. -/
lemma sliceArrowHom_eq_of_zigzag {x : 𝒳}
    {a b : StructuredArrow x (sliceTwoFibreProductSnd p𝒳 p𝒴 f D)} (h : Zigzag a b) :
    sliceArrowHom p𝒳 p𝒴 f D a = sliceArrowHom p𝒳 p𝒴 f D b := by
  induction h with
  | refl => rfl
  | tail _ hzag ih =>
    rcases hzag with ⟨⟨m⟩⟩ | ⟨⟨m⟩⟩
    · exact ih.trans (sliceArrowHom_eq_of_hom p𝒳 p𝒴 f D m)
    · exact ih.trans (sliceArrowHom_eq_of_hom p𝒳 p𝒴 f D m).symm

/-- **The map `Ψ(pr₂) ⟶ f^{op} ⋙ Hom(-, y)`**: the class of `φ : x ⟶ ζ.y` goes to `f(φ)` followed
by the comparison arrow of `ζ`. -/
def twoFibreProductHomPresheafHom :
    componentPresheaf (sliceTwoFibreProductSnd p𝒳 p𝒴 f D) ⟶
      f.op ⋙ uliftYoneda.{max u₁ u₂ v₁ v₂}.obj y where
  app x := ↾fun c => Quotient.liftOn c (fun a => ULift.up (sliceArrowHom p𝒳 p𝒴 f D a))
    (fun _ _ h => congrArg ULift.up (sliceArrowHom_eq_of_zigzag p𝒳 p𝒴 f D h))
  naturality x x' g := TypeCat.homEquiv.injective (funext fun c => by
    induction c using Quotient.inductionOn with
    | h a =>
      change ULift.up (f.map (g.unop ≫ a.hom) ≫ _) =
        ULift.up (f.map g.unop ≫ sliceArrowHom p𝒳 p𝒴 f D a)
      rw [Functor.map_comp]
      exact congrArg ULift.up (Category.assoc _ _ _))

/-- The map `twoFibreProductHomPresheafHom` sends the class of `φ : x ⟶ ζ.y` to `f(φ)` followed by
the comparison arrow of `ζ`. -/
@[simp]
lemma twoFibreProductHomPresheafHom_mk {x : 𝒳} {ζ}
    (φ : x ⟶ (sliceTwoFibreProductSnd p𝒳 p𝒴 f D).obj ζ) :
    (twoFibreProductHomPresheafHom p𝒳 p𝒴 f D).app (op x)
      (componentMk (sliceTwoFibreProductSnd p𝒳 p𝒴 f D) φ) =
      ULift.up (f.map φ ≫ ((Presheaf.pushforwardIndexFunctor p𝒳 p𝒴 f D).obj ζ).hom) := rfl

variable (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳)

/-- The object of the 2-fibre product attached to an arrow `g : f(x) ⟶ y`, with the identity of
`x` as the arrow into its second component. -/
def sliceArrowOfHom {x : 𝒳} (g : f.obj x ⟶ y) :
    StructuredArrow x (sliceTwoFibreProductSnd p𝒳 p𝒴 f D) :=
  StructuredArrow.mk (Y := Presheaf.pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf
    (CostructuredArrow.mk g)) (𝟙 x)

/-- The arrow attached to the object of the 2-fibre product determined by `g` is `g`. -/
lemma sliceArrowHom_sliceArrowOfHom {x : 𝒳} (g : f.obj x ⟶ y) :
    sliceArrowHom p𝒳 p𝒴 f D (sliceArrowOfHom p𝒳 p𝒴 f D h𝒴 hf g) = g := by
  change f.map (𝟙 x) ≫ (Presheaf.pushforwardIndexInverseObj p𝒳 p𝒴 f D h𝒴 hf
      (CostructuredArrow.mk g)).iso.inv ≫ D.cone (Presheaf.pushforwardIndexInverseObj p𝒳 p𝒴 f D
        h𝒴 hf (CostructuredArrow.mk g)).x = g
  simpa using Presheaf.pushforwardIndexInverseObj_iso_inv_comp_cone p𝒳 p𝒴 f D h𝒴 hf
    (CostructuredArrow.mk g)

/-- Every arrow into the 2-fibre product is connected to the one determined by its attached
arrow `f(x) ⟶ y`: the inverse functor of the index equivalence carries the morphism of the index
category given by the arrow itself to a morphism of the 2-fibre product, which the unit of the
index equivalence completes. -/
lemma componentMk_eq_sliceArrowOfHom {x : 𝒳}
    (a : StructuredArrow x (sliceTwoFibreProductSnd p𝒳 p𝒴 f D)) :
    Quotient.mk (Zigzag.setoid _) a =
      Quotient.mk (Zigzag.setoid _)
        (sliceArrowOfHom p𝒳 p𝒴 f D h𝒴 hf (sliceArrowHom p𝒳 p𝒴 f D a)) := by
  let ψ : CostructuredArrow.mk (sliceArrowHom p𝒳 p𝒴 f D a) ⟶
      (Presheaf.pushforwardIndexFunctor p𝒳 p𝒴 f D).obj a.right :=
    CostructuredArrow.homMk a.hom rfl
  let m : (sliceArrowOfHom p𝒳 p𝒴 f D h𝒴 hf (sliceArrowHom p𝒳 p𝒴 f D a)).right ⟶ a.right :=
    (Presheaf.pushforwardIndexInverse p𝒳 p𝒴 f D h𝒴 hf).map ψ ≫
      Presheaf.pushforwardIndexUnitHom p𝒳 p𝒴 f D h𝒴 hf a.right
  have hm : (sliceArrowOfHom p𝒳 p𝒴 f D h𝒴 hf (sliceArrowHom p𝒳 p𝒴 f D a)).hom ≫
      (sliceTwoFibreProductSnd p𝒳 p𝒴 f D).map m = a.hom :=
    (Category.id_comp _).trans (Category.comp_id a.hom)
  exact (Quot.sound (Zigzag.of_hom (StructuredArrow.homMk m hm))).symm

/-- **The presheaf represented by the projection of `(𝒞/V) ×_𝒴 𝒳` to `𝒳` is
`x ↦ Hom_𝒴(f(x), y)`.** -/
def twoFibreProductHomPresheafIso :
    componentPresheaf (sliceTwoFibreProductSnd p𝒳 p𝒴 f D) ≅
      f.op ⋙ uliftYoneda.{max u₁ u₂ v₁ v₂}.obj y :=
  NatIso.ofComponents (fun x => Equiv.toIso
    { toFun := (twoFibreProductHomPresheafHom p𝒳 p𝒴 f D).app x
      invFun := fun g => Quotient.mk (Zigzag.setoid _)
        (sliceArrowOfHom p𝒳 p𝒴 f D h𝒴 hf g.down)
      left_inv := fun c => by
        induction c using Quotient.inductionOn with
        | h a => exact (componentMk_eq_sliceArrowOfHom p𝒳 p𝒴 f D h𝒴 hf a).symm
      right_inv := fun g =>
        congrArg ULift.up (sliceArrowHom_sliceArrowOfHom p𝒳 p𝒴 f D h𝒴 hf g.down) })
    (fun g => (twoFibreProductHomPresheafHom p𝒳 p𝒴 f D).naturality g)

section Swap

variable {𝒮 : Type u₅} [Category.{v₅} 𝒮] {𝒵 : Type u₄} [Category.{v₄} 𝒵]
  (pA : 𝒳 ⥤ 𝒞) (pB : 𝒵 ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒵 ⥤ 𝒮)

/-- **Exchanging the factors of a 2-fibre product does not change the presheaf it represents
on its first factor**: the presheaf of components of the first projection of `𝒳 ×_𝒮 𝒵` is that of
the second projection of `𝒵 ×_𝒮 𝒳`, the exchange of factors being an isomorphism of categories
compatible with the two projections on the nose. -/
def componentPresheafSwapIso :
    componentPresheaf (TwoFibreProductOver.fst pA pB pS F G) ≅
      componentPresheaf (TwoFibreProductOver.snd pB pA pS G F) where
  hom := componentPresheafMap (TwoFibreProductOver.snd pB pA pS G F)
    (TwoFibreProductOver.swap pA pB pS F G)
  inv := componentPresheafMap (TwoFibreProductOver.fst pA pB pS F G)
    (TwoFibreProductOver.swap pB pA pS G F)
  hom_inv_id := by
    ext x c
    induction c using Quotient.inductionOn
    rfl
  inv_hom_id := by
    ext x c
    induction c using Quotient.inductionOn
    rfl

end Swap

/-- **The presheaf represented by the projection of `𝒳 ×_𝒴 (𝒞/V)` to `𝒳` is
`x ↦ Hom_𝒴(f(x), y)`**, for the 2-fibre product written with `𝒳` as its first factor. -/
def twoFibreProductFstHomPresheafIso :
    componentPresheaf (TwoFibreProductOver.fst p𝒳 (Over.forget (p𝒴.obj y)) p𝒴 f D.sliceMor) ≅
      f.op ⋙ uliftYoneda.{max u₁ u₂ v₁ v₂}.obj y :=
  componentPresheafSwapIso p𝒳 (Over.forget (p𝒴.obj y)) p𝒴 f D.sliceMor ≪≫
    twoFibreProductHomPresheafIso p𝒳 p𝒴 f D h𝒴 hf

end Stacks.Sites.CoverDescent
