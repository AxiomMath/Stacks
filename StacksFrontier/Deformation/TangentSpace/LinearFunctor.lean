module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.Grp.LeftExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute

/-!
# Lifting product-preserving functors to linear functors

A set-valued functor on finite-dimensional vector spaces that
preserves finite products lifts uniquely to a linear functor, and that lift is compatible with
morphisms.

## Main definitions

* `LinearFunctorLift` packages an additive, `R`-linear module-valued functor whose
  underlying set-valued functor is a specified functor.
* `fgModuleCatLinearFunctorLift` and
  `moduleCatLinearFunctorLift` are the canonical lifts in the two cases.

## Main results

* `fgModuleCat_linearFunctorLift_unique` gives existence and uniqueness for functors
  on finitely generated modules.
* `moduleCat_linearFunctorLift_unique` gives existence and uniqueness for functors
  on all modules.
* `CategoryTheory.Functor.preservesFiniteProductsOfAdditive` gives preservation of finite
  products.
* `CategoryTheory.Functor.map_isZero` shows that zero objects are carried to zero objects.
* `fgModuleCat_linearFunctorLift_unique` gives the converse unique-lift assertion.
* `fgModuleCat_linearFunctorLift_natTrans`: a natural transformation of the
  underlying set-valued functors uniquely lifts to the module-valued functors.
* `linearFunctor_iso_tensorLeft` identifies a linear functor with tensoring by its
  value on the one-dimensional vector space.

## Implementation notes

### Lifting product-preserving set-valued functors to linear functors

The commuting triangle is expressed by equality after composition with the forgetful functor.
The source's two alternatives are separate results. A `LinearFunctorLift` includes additivity,
linearity, and the commuting condition, so `Nonempty (Unique (LinearFunctorLift R F))` states
precisely that there exists a unique lift. The zero module is represented by the one-element
module `PUnit`.

### Linear functors preserve finite products and zero objects

In Mathlib, an `R`-linear functor is represented by the conjunction of `Functor.Additive` and
`Functor.Linear R`; the conclusions here only use its additive part. We register the more
general existing results for additive functors between preadditive categories. The converse
is exactly the finitely generated case of Stacks Project, Tag 06I6, so that declaration is
also registered here rather than duplicated.

### Morphisms of product-preserving functors are linear

The equality of underlying natural transformations includes the transports along the equalities
which identify the underlying set-valued functors of the canonical lifts with the original
functors. Thus, componentwise, the lifted morphism is exactly the given map of sets.

### Linear functors on finite-dimensional vector spaces

The inclusion of finitely generated modules into all modules is composed with the monoidal
tensor-left functor. Thus the left-hand functor sends `V` to `L(K) ⊗[K] V`. Naturality is
part of the categorical isomorphism, and `Nonempty` records existence without choosing an
isomorphism.

## References

* [Stacks Project, Tag 06I5](https://stacks.math.columbia.edu/tag/06I5)
* [Stacks Project, Tag 06I6](https://stacks.math.columbia.edu/tag/06I6)
* [Stacks Project, Tag 06I7](https://stacks.math.columbia.edu/tag/06I7)
* [Stacks Project, Tag 06I8](https://stacks.math.columbia.edu/tag/06I8)
-/

@[expose] public section

namespace Deformation

/-! ### Lifting product-preserving set-valued functors to linear functors -/

section
open CategoryTheory CategoryTheory.Limits
universe uR uC vC uM vM

private noncomputable def productGroupFunctor
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasTerminal C] [HasBinaryProducts C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] : C ⥤ AddCommGrpCat.{uM} := by
  letI : CartesianMonoidalCategory C :=
    CartesianMonoidalCategory.ofChosenFiniteProducts (getLimitCone (Functor.empty C))
      (fun X Y => getLimitCone (pair X Y))
  letI : BraidedCategory C := BraidedCategory.ofCartesianMonoidalCategory
  letI : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  exact Preadditive.commGrpEquivalence.functor ⋙ F.mapCommGrp ⋙
    CommGrpTypeEquivalenceCommGrp.functor ⋙ commGroupAddCommGroupEquivalence.functor

private theorem productGroupFunctor_preservesFiniteProducts
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasTerminal C] [HasBinaryProducts C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] :
    PreservesFiniteProducts (productGroupFunctor F) := by
  let : PreservesFiniteProducts (productGroupFunctor F ⋙ forget AddCommGrpCat) := by
    show PreservesFiniteProducts F
    infer_instance
  exact preservesFiniteProducts_of_reflects_of_preserves
    (productGroupFunctor F) (forget AddCommGrpCat)

private theorem productGroupFunctor_additive
    {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] :
    (productGroupFunctor F).Additive := by
  let : PreservesFiniteProducts (productGroupFunctor F) :=
    productGroupFunctor_preservesFiniteProducts F
  let : (productGroupFunctor F).PreservesZeroMorphisms := inferInstance
  exact Functor.additive_of_preserves_binary_products (productGroupFunctor F)

private def scalarRingHom
    {R : Type uR} [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    (G : C ⥤ AddCommGrpCat.{uM}) [G.Additive] (X : C) :
    R →+* End (G.obj X) where
  toFun r := .of (G.map (r • 𝟙 X))
  map_one' := by
    ext1
    change G.map ((1 : R) • 𝟙 X) = 𝟙 _
    simp
  map_mul' r s := by
    ext1
    change G.map ((r * s) • (𝟙 X)) =
      G.map (s • (𝟙 X)) ≫ G.map (r • (𝟙 X))
    rw [← Functor.map_comp]
    congr 1
    rw [Linear.smul_comp, Linear.comp_smul]
    simp [smul_smul, mul_comm]
  map_zero' := by
    ext1
    change G.map ((0 : R) • 𝟙 X) = 0
    simp
  map_add' r s := by
    ext1
    change G.map ((r + s) • 𝟙 X) = G.map (r • 𝟙 X) + G.map (s • 𝟙 X)
    rw [add_smul, Functor.map_add]

private lemma scalarRingHom_natural
    {R : Type uR} [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    (G : C ⥤ AddCommGrpCat.{uM}) [G.Additive] {X Y : C}
    (f : X ⟶ Y) (r : R) :
    G.map f ≫ (scalarRingHom G Y r).asHom = (scalarRingHom G X r).asHom ≫ G.map f := by
  show G.map f ≫ G.map (r • 𝟙 Y) = G.map (r • 𝟙 X) ≫ G.map f
  rw [← Functor.map_comp, ← Functor.map_comp,
    Linear.comp_smul, Linear.smul_comp]
  simp

@[instance_reducible]
private def moduleOfSMul
    {R : Type uR} [CommRing R] {A : AddCommGrpCat.{uM}}
    (φ : R →+* End A) : Module R A where
  smul r x := ConcreteCategory.hom (φ r).asHom x
  smul_zero r := (ConcreteCategory.hom (φ r).asHom).map_zero
  smul_add r x y := (ConcreteCategory.hom (φ r).asHom).map_add x y
  one_smul x := by
    change ConcreteCategory.hom (φ 1).asHom x = x
    simp
  mul_smul r s x := by
    change ConcreteCategory.hom (φ (r * s)).asHom x =
      ConcreteCategory.hom (φ r).asHom (ConcreteCategory.hom (φ s).asHom x)
    simp [End.mul_asHom]
  zero_smul x := by
    change ConcreteCategory.hom (φ 0).asHom x = 0
    simp
  add_smul r s x := by
    change ConcreteCategory.hom (φ (r + s)).asHom x =
      ConcreteCategory.hom (φ r).asHom x + ConcreteCategory.hom (φ s).asHom x
    rw [map_add]
    change ConcreteCategory.hom ((φ r).asHom + (φ s).asHom) x = _
    rw [AddCommGrpCat.hom_add_apply]

private lemma moduleOfSMul_smul
    {R : Type uR} [CommRing R] {A : AddCommGrpCat.{uM}}
    (φ : R →+* End A) (r : R) :
    letI : Module R A := moduleOfSMul φ
    (ModuleCat.of R A).smul r = φ r := by
  let : Module R A := moduleOfSMul φ
  ext1
  apply AddCommGrpCat.hom_ext
  ext x
  rfl

private noncomputable def productPreimage
    {C : Type uC} [Category.{vC} C] [HasBinaryProducts C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F]
    (X : C) (x y : F.obj X) : F.obj (X ⨯ X) := by
  let hF := isLimitOfHasBinaryProductOfPreservesLimit F X X
  let s : BinaryFan (F.obj X) (F.obj X) :=
    BinaryFan.mk (↾fun _ : PUnit.{uM + 1} => x)
      (↾fun _ : PUnit.{uM + 1} => y)
  exact hF.lift s PUnit.unit

private lemma productPreimage_fst
    {C : Type uC} [Category.{vC} C] [HasBinaryProducts C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F]
    (X : C) (x y : F.obj X) :
    F.map (Limits.prod.fst (X := X) (Y := X)) (productPreimage F X x y) = x := by
  let hF := isLimitOfHasBinaryProductOfPreservesLimit F X X
  let s : BinaryFan (F.obj X) (F.obj X) :=
    BinaryFan.mk (↾fun _ : PUnit.{uM + 1} => x)
      (↾fun _ : PUnit.{uM + 1} => y)
  show (F.map (Limits.prod.fst (X := X) (Y := X))) ((hF.lift s) PUnit.unit) = x
  exact ConcreteCategory.congr_hom (hF.fac s ⟨WalkingPair.left⟩) PUnit.unit

private lemma productPreimage_snd
    {C : Type uC} [Category.{vC} C] [HasBinaryProducts C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F]
    (X : C) (x y : F.obj X) :
    F.map (Limits.prod.snd (X := X) (Y := X)) (productPreimage F X x y) = y := by
  let hF := isLimitOfHasBinaryProductOfPreservesLimit F X X
  let s : BinaryFan (F.obj X) (F.obj X) :=
    BinaryFan.mk (↾fun _ : PUnit.{uM + 1} => x)
      (↾fun _ : PUnit.{uM + 1} => y)
  show (F.map (Limits.prod.snd (X := X) (Y := X))) ((hF.lift s) PUnit.unit) = y
  exact ConcreteCategory.congr_hom (hF.fac s ⟨WalkingPair.right⟩) PUnit.unit

public lemma eqToHom_app_apply_cast
    {C : Type uC} [Category.{vC} C]
    {H K : C ⥤ Type uM} (e : H = K) (X : C) (x : H.obj X) :
    (eqToHom e).app X x = cast (congrArg (fun T : C ⥤ Type uM => T.obj X) e) x := by
  cases e
  rfl

/-- Naturality of `eqToHom h` for `L ⋙ forget = F`, stated on elements with `cast`. -/
private lemma cast_map_eq_of_forget_comp
    {R : Type uR} [CommRing R]
    {C : Type uC} [Category.{vC} C] {F : C ⥤ Type uM}
    (L : C ⥤ ModuleCat.{uM} R) (h : L ⋙ forget (ModuleCat.{uM} R) = F)
    {X Y : C} (f : X ⟶ Y) (a : L.obj X) :
    cast (congrArg (fun K : C ⥤ Type uM => K.obj Y) h) (L.map f a) =
      F.map f (cast (congrArg (fun K : C ⥤ Type uM => K.obj X) h) a) := by
  have hn := ConcreteCategory.congr_hom ((eqToHom h).naturality f) a
  change (eqToHom h).app Y (L.map f a) = F.map f ((eqToHom h).app X a) at hn
  rwa [eqToHom_app_apply_cast, eqToHom_app_apply_cast] at hn

private lemma lift_add_characterization
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryProducts C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F]
    (L : C ⥤ ModuleCat.{uM} R) [L.Additive]
    (h : L ⋙ forget (ModuleCat.{uM} R) = F)
    (X : C) (a b : L.obj X) :
    cast (congrArg (fun K : C ⥤ Type uM => K.obj X) h) (a + b) =
      F.map (Limits.prod.fst (X := X) (Y := X) + Limits.prod.snd (X := X) (Y := X))
        (productPreimage F X
          (cast (congrArg (fun K : C ⥤ Type uM => K.obj X) h) a)
          (cast (congrArg (fun K : C ⥤ Type uM => K.obj X) h) b)) := by
  let hX := congrArg (fun K : C ⥤ Type uM => K.obj X) h
  let hP := congrArg (fun K : C ⥤ Type uM => K.obj (X ⨯ X)) h
  let zF := productPreimage F X (cast hX a) (cast hX b)
  let zL : L.obj (X ⨯ X) := cast hP.symm zF
  have hz : cast hP zL = zF := by simp [zL]
  have key (g : X ⨯ X ⟶ X) : cast hX (L.map g zL) = F.map g zF := by
    rw [cast_map_eq_of_forget_comp L h g zL, hz]
  have hfst : L.map (Limits.prod.fst (X := X) (Y := X)) zL = a :=
    (Equiv.cast hX).injective ((key _).trans (productPreimage_fst F X (cast hX a) (cast hX b)))
  have hsnd : L.map (Limits.prod.snd (X := X) (Y := X)) zL = b :=
    (Equiv.cast hX).injective ((key _).trans (productPreimage_snd F X (cast hX a) (cast hX b)))
  have hcodiag : L.map (Limits.prod.fst (X := X) (Y := X) + Limits.prod.snd (X := X) (Y := X))
      zL = a + b := by
    rw [Functor.map_add]
    exact congrArg₂ (· + ·) hfst hsnd
  exact (congrArg (cast hX) hcodiag.symm).trans (key _)

private lemma lift_smul_characterization
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    (F : C ⥤ Type uM)
    (L : C ⥤ ModuleCat.{uM} R) [L.Linear R]
    (h : L ⋙ forget (ModuleCat.{uM} R) = F)
    (X : C) (r : R) (a : L.obj X) :
    cast (congrArg (fun K : C ⥤ Type uM => K.obj X) h) (r • a) =
      F.map (r • (𝟙 X)) (cast (congrArg (fun K : C ⥤ Type uM => K.obj X) h) a) := by
  simpa only [Functor.map_smul, L.map_id, ModuleCat.hom_smul,
    ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply] using
    cast_map_eq_of_forget_comp L h (r • (𝟙 X)) a

private lemma moduleCat_ext_of_cast
    (R : Type uR) [CommRing R] {A B : ModuleCat.{uM} R}
    (e : (A : Type uM) = (B : Type uM))
    (hadd : ∀ x y : A, cast e (x + y) = (cast e x : B) + cast e y)
    (hsmul : ∀ (r : R) (x : A), cast e (r • x) = r • (cast e x : B)) :
    A = B := by
  cases A
  cases B
  dsimp at e
  cases e
  rename_i carrier addA moduleA addB moduleB
  have hAdd : addA = addB := by
    apply AddCommGroup.ext
    funext x y
    exact hadd x y
  cases hAdd
  have hModule : moduleA = moduleB := Module.ext' _ _ hsmul
  cases hModule
  rfl

private lemma eqToHom_moduleCat_apply_cast
    (R : Type uR) [CommRing R] {A B : ModuleCat.{uM} R}
    (e : A = B) (x : A) :
    ConcreteCategory.hom (eqToHom e) x =
      cast (congrArg (fun M : ModuleCat.{uM} R => (M : Type uM)) e) x := by
  cases e
  rfl

private theorem moduleFunctor_ext
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F]
    (L K : C ⥤ ModuleCat.{uM} R) [L.Additive] [K.Additive]
    [L.Linear R] [K.Linear R]
    (hL : L ⋙ forget (ModuleCat.{uM} R) = F)
    (hK : K ⋙ forget (ModuleCat.{uM} R) = F) : L = K := by
  let hobj : ∀ X, L.obj X = K.obj X := fun X => by
    let hLX := congrArg (fun H : C ⥤ Type uM => H.obj X) hL
    let hKX := congrArg (fun H : C ⥤ Type uM => H.obj X) hK
    change ((L.obj X : ModuleCat.{uM} R) : Type uM) = F.obj X at hLX
    change ((K.obj X : ModuleCat.{uM} R) : Type uM) = F.obj X at hKX
    let eX := hLX.trans hKX.symm
    have hcast (x : L.obj X) : cast hKX (cast eX x) = cast hLX x := by
      simp
    have hadd : ∀ a b : L.obj X,
        cast eX (a + b) = (cast eX a : K.obj X) + cast eX b := by
      intro a b
      apply (Equiv.cast hKX).injective
      have hleft := lift_add_characterization R F L hL X a b
      have hright := lift_add_characterization R F K hK X (cast eX a) (cast eX b)
      show cast hKX (cast eX (a + b)) =
        cast hKX (cast eX a + cast eX b)
      rw [hcast a, hcast b] at hright
      rw [hcast, hleft, hright]
    have hsmul : ∀ (r : R) (a : L.obj X),
        cast eX (r • a) = r • (cast eX a : K.obj X) := by
      intro r a
      apply (Equiv.cast hKX).injective
      have hleft := lift_smul_characterization R F L hL X r a
      have hright := lift_smul_characterization R F K hK X r (cast eX a)
      show cast hKX (cast eX (r • a)) = cast hKX (r • cast eX a)
      rw [hcast a] at hright
      rw [hcast, hleft, hright]
    exact moduleCat_ext_of_cast R eX hadd hsmul
  refine CategoryTheory.Functor.ext hobj ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let hLX := congrArg (fun H : C ⥤ Type uM => H.obj X) hL
  let hLY := congrArg (fun H : C ⥤ Type uM => H.obj Y) hL
  let hKX := congrArg (fun H : C ⥤ Type uM => H.obj X) hK
  let hKY := congrArg (fun H : C ⥤ Type uM => H.obj Y) hK
  change ((L.obj X : ModuleCat.{uM} R) : Type uM) = F.obj X at hLX
  change ((L.obj Y : ModuleCat.{uM} R) : Type uM) = F.obj Y at hLY
  change ((K.obj X : ModuleCat.{uM} R) : Type uM) = F.obj X at hKX
  change ((K.obj Y : ModuleCat.{uM} R) : Type uM) = F.obj Y at hKY
  let eX := hLX.trans hKX.symm
  let eY := hLY.trans hKY.symm
  have hobjX : congrArg (fun M : ModuleCat.{uM} R => (M : Type uM)) (hobj X) = eX :=
    Subsingleton.elim _ _
  have hobjY : congrArg (fun M : ModuleCat.{uM} R => (M : Type uM)) (hobj Y) = eY :=
    Subsingleton.elim _ _
  have hobjYsymm :
      congrArg (fun M : ModuleCat.{uM} R => (M : Type uM)) (hobj Y).symm = eY.symm := by
    simp
  have hLmap : cast hLY (L.map f a) = F.map f (cast hLX a) :=
    cast_map_eq_of_forget_comp L hL f a
  have hKmap : cast hKY (K.map f (cast eX a)) = F.map f (cast hLX a) := by
    rw [cast_map_eq_of_forget_comp K hK f (cast eX a)]
    simp
  have hcastY (x : L.obj Y) : cast hKY (cast eY x) = cast hLY x := by
    simp
  simp only [ConcreteCategory.comp_apply, eqToHom_moduleCat_apply_cast]
  rw [hobjX, hobjYsymm]
  apply (Equiv.cast eY).injective
  simp only [Equiv.cast_apply, cast_cast, cast_eq]
  apply (Equiv.cast hKY).injective
  show cast hKY (cast eY (L.map f a)) = cast hKY (K.map f (cast eX a))
  rw [hcastY, hLmap, hKmap]

private noncomputable def moduleFunctorLift
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] :
    C ⥤ ModuleCat.{uM} R := by
  let G := productGroupFunctor F
  letI : G.Additive := productGroupFunctor_additive F
  refine
    { obj := fun X => by
        letI : Module R (G.obj X) := moduleOfSMul (scalarRingHom (R := R) G X)
        exact ModuleCat.of R (G.obj X)
      map := fun {X Y} f => by
        letI : Module R (G.obj X) := moduleOfSMul (scalarRingHom (R := R) G X)
        letI : Module R (G.obj Y) := moduleOfSMul (scalarRingHom (R := R) G Y)
        exact ModuleCat.homMk (G.map f) (by
          intro r
          rw [moduleOfSMul_smul (scalarRingHom (R := R) G X) r,
            moduleOfSMul_smul (scalarRingHom (R := R) G Y) r]
          exact scalarRingHom_natural (R := R) G f r)
      map_id := ?_
      map_comp := ?_ }
  · intro X
    let : Module R (G.obj X) := moduleOfSMul (scalarRingHom (R := R) G X)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (G.map (𝟙 X) : G.obj X ⟶ G.obj X) x = x
    simp
  · intro X Y Z f g
    let : Module R (G.obj X) := moduleOfSMul (scalarRingHom (R := R) G X)
    let : Module R (G.obj Y) := moduleOfSMul (scalarRingHom (R := R) G Y)
    let : Module R (G.obj Z) := moduleOfSMul (scalarRingHom (R := R) G Z)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (G.map (f ≫ g) : G.obj X ⟶ G.obj Z) x =
      ((G.map f : G.obj X ⟶ G.obj Y) ≫ (G.map g : G.obj Y ⟶ G.obj Z)) x
    simp

private theorem moduleFunctorLift_forget
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] :
    moduleFunctorLift R F ⋙ forget (ModuleCat.{uM} R) = F := rfl

private theorem moduleFunctorLift_additive
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] :
    (moduleFunctorLift R F).Additive := by
  let G := productGroupFunctor F
  let : G.Additive := productGroupFunctor_additive F
  constructor
  intro X Y f g
  apply ModuleCat.hom_ext
  ext x
  show (G.map (f + g) : G.obj X ⟶ G.obj Y) x =
    ((G.map f + G.map g : G.obj X ⟶ G.obj Y)) x
  rw [Functor.map_add]

private theorem moduleFunctorLift_linear
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] :
    (moduleFunctorLift R F).Linear R := by
  let G := productGroupFunctor F
  let L := moduleFunctorLift R F
  let : G.Additive := productGroupFunctor_additive F
  let : L.Additive := moduleFunctorLift_additive R F
  rw [Functor.linear_iff]
  intro X r
  apply ModuleCat.hom_ext
  ext x
  simp only [ModuleCat.hom_smul, ModuleCat.hom_id]
  show (G.map (r • (𝟙 X)) : G.obj X ⟶ G.obj X) x =
    AddCommGrpCat.Hom.hom (scalarRingHom (R := R) G X r).asHom x
  rfl

/-- An additive, `R`-linear lift of a set-valued functor `F` is a module-valued functor whose
underlying set-valued functor is exactly `F`. -/
structure LinearFunctorLift (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [CategoryTheory.Linear R C]
    (F : C ⥤ Type uM) where
  /-- The module-valued lift. -/
  functor : C ⥤ ModuleCat.{uM} R
  /-- The lift is additive. -/
  [additive : functor.Additive]
  /-- The lift is `R`-linear. -/
  [linear : functor.Linear R]
  /-- Forgetting the module structure recovers the original functor. -/
  forget_comp : functor ⋙ forget (ModuleCat.{uM} R) = F

namespace LinearFunctorLift

attribute [instance] additive linear

end LinearFunctorLift

private lemma linearFunctorLift_ext
    {R : Type uR} [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [CategoryTheory.Linear R C]
    {F : C ⥤ Type uM} {A B : LinearFunctorLift R F}
    (h : A.functor = B.functor) : A = B := by
  cases A
  cases B
  cases h
  rfl

@[instance_reducible]
private noncomputable def moduleFunctorLift_unique
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] : Unique (LinearFunctorLift R F) := by
  let L := moduleFunctorLift R F
  let K : LinearFunctorLift R F :=
    { functor := L
      additive := moduleFunctorLift_additive R F
      linear := moduleFunctorLift_linear R F
      forget_comp := moduleFunctorLift_forget R F }
  refine ⟨⟨K⟩, fun A => ?_⟩
  let : A.functor.Additive := A.additive
  let : A.functor.Linear R := A.linear
  let : K.functor.Additive := K.additive
  let : K.functor.Linear R := K.linear
  exact linearFunctorLift_ext
    (moduleFunctor_ext R F A.functor K.functor A.forget_comp K.forget_comp)

private theorem fgModuleCat_zeroObject
    (R : Type uR) [CommRing R] : HasZeroObject (FGModuleCat.{vM} R) := by
  apply (show IsZero (FGModuleCat.of R PUnit.{vM + 1}) from ?_).hasZeroObject
  refine ⟨?_, ?_⟩
  · intro Y
    refine ⟨Unique.mk ⟨FGModuleCat.ofHom (0 : PUnit.{vM + 1} →ₗ[R] (Y : Type vM))⟩ ?_⟩
    intro f
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    calc
      f.hom.hom PUnit.unit = f.hom.hom 0 := by
        congr 1
      _ = 0 := map_zero _
      _ = (0 : PUnit.{vM + 1} →ₗ[R] (Y : Type vM)) PUnit.unit := by simp
  · intro Y
    refine ⟨Unique.mk ⟨FGModuleCat.ofHom (0 : (Y : Type vM) →ₗ[R] PUnit.{vM + 1})⟩ ?_⟩
    intro f
    apply FGModuleCat.hom_ext
    ext x

private theorem fgModuleCat_hasBinaryProduct
    (R : Type uR) [CommRing R] (X Y : FGModuleCat.{vM} R) :
    HasBinaryProduct X Y := by
  let : AddCommGroup X.obj.carrier := X.obj.isAddCommGroup
  let : Module R X.obj.carrier := X.obj.isModule
  let : AddCommGroup Y.obj.carrier := Y.obj.isAddCommGroup
  let : Module R Y.obj.carrier := Y.obj.isModule
  let : Module.Finite R X.obj.carrier := X.property
  let : Module.Finite R Y.obj.carrier := Y.property
  let : Module.Finite R (X.obj.carrier × Y.obj.carrier) := inferInstance
  let P : FGModuleCat.{vM} R := FGModuleCat.of R (X.obj.carrier × Y.obj.carrier)
  let fst : P ⟶ X := FGModuleCat.ofHom (LinearMap.fst R X.obj.carrier Y.obj.carrier)
  let snd : P ⟶ Y := FGModuleCat.ofHom (LinearMap.snd R X.obj.carrier Y.obj.carrier)
  let fan : BinaryFan X Y := BinaryFan.mk fst snd
  let lim : IsLimit fan := BinaryFan.isLimitMk
    (fun s => FGModuleCat.ofHom (LinearMap.prod s.fst.hom.hom s.snd.hom.hom))
    (by
      intro s
      apply FGModuleCat.hom_ext
      ext x
      show (LinearMap.fst R X.obj.carrier Y.obj.carrier)
        ((LinearMap.prod s.fst.hom.hom s.snd.hom.hom) x) = s.fst.hom.hom x
      simp [LinearMap.prod_apply])
    (by
      intro s
      apply FGModuleCat.hom_ext
      ext x
      show (LinearMap.snd R X.obj.carrier Y.obj.carrier)
        ((LinearMap.prod s.fst.hom.hom s.snd.hom.hom) x) = s.snd.hom.hom x
      simp [LinearMap.prod_apply])
    (by
      intro s m hfst hsnd
      apply FGModuleCat.hom_ext
      ext x
      · have h := congrArg (fun q : s.pt ⟶ X => q.hom.hom x) hfst
        change (LinearMap.fst R X.obj.carrier Y.obj.carrier) (m.hom.hom x) =
          s.fst.hom.hom x at h
        have h' : (m.hom.hom x).1 = s.fst.hom.hom x := by
          simpa only [LinearMap.fst_apply] using h
        show (m.hom.hom x).1 =
          (LinearMap.prod s.fst.hom.hom s.snd.hom.hom x).1
        exact h'
      · have h := congrArg (fun q : s.pt ⟶ Y => q.hom.hom x) hsnd
        change (LinearMap.snd R X.obj.carrier Y.obj.carrier) (m.hom.hom x) =
          s.snd.hom.hom x at h
        have h' : (m.hom.hom x).2 = s.snd.hom.hom x := by
          simpa only [LinearMap.snd_apply] using h
        show (m.hom.hom x).2 =
          (LinearMap.prod s.fst.hom.hom s.snd.hom.hom x).2
        exact h')
  exact HasLimit.mk ⟨fan, lim⟩

private theorem fgModuleCat_hasBinaryProducts
    (R : Type uR) [CommRing R] : HasBinaryProducts (FGModuleCat.{vM} R) := by
  let : ∀ {X Y : FGModuleCat.{vM} R}, HasBinaryProduct X Y :=
    fun {X Y} => fgModuleCat_hasBinaryProduct R X Y
  exact hasBinaryProducts_of_hasLimit_pair (FGModuleCat.{vM} R)

/-- **Stacks Project, Tag 06I6, general source category.** A finite-product-preserving
set-valued functor on any preadditive `R`-linear category with a terminal object, binary
products and a zero object has a unique `R`-linear lift to `R`-modules. The two cases of the
source are the instances of this for the category of all modules and for the category of
finitely generated ones; it is also what applies to the full subcategories of the module
category that arise as the domain of a tangent functor. -/
@[stacks 06I6 "arbitrary linear source category"]
theorem linearFunctorLift_unique
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] :
    Nonempty (Unique (LinearFunctorLift R F)) :=
  ⟨moduleFunctorLift_unique R F⟩

/-- The canonical `R`-linear lift of a finite-product-preserving set-valued functor on a
preadditive `R`-linear category with finite products and a zero object. -/
noncomputable def linearFunctorLift
    (R : Type uR) [CommRing R]
    {C : Type uC} [Category.{vC} C] [Preadditive C] [Linear R C]
    [HasTerminal C] [HasBinaryProducts C] [HasZeroObject C]
    (F : C ⥤ Type uM) [PreservesFiniteProducts F] : LinearFunctorLift R F :=
  (Classical.choice (linearFunctorLift_unique R F)).default

/-- **Stacks Project, Tag 06I6, finitely generated case.** A finite-product-preserving
set-valued functor on finitely generated `R`-modules which takes the zero module to a singleton
has a unique `R`-linear lift to `R`-modules. -/
@[stacks 06I6 "finitely generated modules"]
theorem fgModuleCat_linearFunctorLift_unique
    (R : Type uR) [CommRing R] (F : FGModuleCat.{vM} R ⥤ Type uM)
    [PreservesFiniteProducts F] [Unique (F.obj (FGModuleCat.of R PUnit))] :
    Nonempty (Unique (LinearFunctorLift R F)) := by
  let : HasZeroObject (FGModuleCat.{vM} R) := fgModuleCat_zeroObject R
  let : HasBinaryProducts (FGModuleCat.{vM} R) := fgModuleCat_hasBinaryProducts R
  exact ⟨moduleFunctorLift_unique R F⟩

/-- The canonical linear lift of a product-preserving set-valued functor on finitely generated
modules. -/
noncomputable def fgModuleCatLinearFunctorLift
    (R : Type uR) [CommRing R] (F : FGModuleCat.{vM} R ⥤ Type uM)
    [PreservesFiniteProducts F] [Unique (F.obj (FGModuleCat.of R PUnit))] :
    LinearFunctorLift R F :=
  (Classical.choice (fgModuleCat_linearFunctorLift_unique R F)).default

/-- **Stacks Project, Tag 06I6, unrestricted case.** A finite-product-preserving set-valued
functor on `R`-modules which takes the zero module to a singleton has a unique `R`-linear lift
to `R`-modules. -/
@[stacks 06I6 "all modules"]
theorem moduleCat_linearFunctorLift_unique
    (R : Type uR) [CommRing R] (F : ModuleCat.{vM} R ⥤ Type uM)
    [PreservesFiniteProducts F] [Unique (F.obj (ModuleCat.of R PUnit))] :
    Nonempty (Unique (LinearFunctorLift R F)) :=
  ⟨moduleFunctorLift_unique R F⟩

/-- The canonical linear lift of a product-preserving set-valued functor on all modules. -/
noncomputable def moduleCatLinearFunctorLift
    (R : Type uR) [CommRing R] (F : ModuleCat.{vM} R ⥤ Type uM)
    [PreservesFiniteProducts F] [Unique (F.obj (ModuleCat.of R PUnit))] :
    LinearFunctorLift R F :=
  (Classical.choice (moduleCat_linearFunctorLift_unique R F)).default

end

/-! ### Linear functors preserve finite products and zero objects -/

section

open CategoryTheory.Functor

add_to_stacks 06I5 "preservation of finite products" preservesFiniteProductsOfAdditive

add_to_stacks 06I5 "zero modules are sent to zero modules" map_isZero

add_to_stacks 06I5 "unique linear lift" fgModuleCat_linearFunctorLift_unique

end

/-! ### Morphisms of product-preserving functors are linear -/

section
open CategoryTheory CategoryTheory.Limits
universe uR uM vM

private noncomputable def natTransAppLinearMap
    (R : Type uR) [CommRing R]
    (A B : FGModuleCat.{vM} R ⥤ ModuleCat.{uM} R)
    [A.Additive] [A.Linear R] [B.Additive] [B.Linear R]
    (α : A ⋙ forget (ModuleCat.{uM} R) ⟶ B ⋙ forget (ModuleCat.{uM} R))
    (X : FGModuleCat.{vM} R) : A.obj X →ₗ[R] B.obj X where
  toFun := α.app X
  map_add' x y := by
    let := fgModuleCat_hasBinaryProduct R X X
    let z : A.obj (X ⨯ X) :=
      (asIso (prodComparison A X X)).inv
        ((biprod.isoProd (A.obj X) (A.obj X)).hom
          ((ModuleCat.biprodIsoProd (A.obj X) (A.obj X)).inv (x, y)))
    have hz₁ : (A.map (prod.fst : X ⨯ X ⟶ X)) z = x := by
      change ((inv (prodComparison A X X) ≫ A.map prod.fst) _ = x)
      rw [inv_prodComparison_map_fst, biprod.isoProd_hom, ← ConcreteCategory.comp_apply,
        prod.lift_fst]
      change ((ModuleCat.biprodIsoProd _ _).inv ≫ biprod.fst) (x, y) = x
      rw [ModuleCat.biprodIsoProd_inv_comp_fst]; rfl
    have hz₂ : (A.map (prod.snd : X ⨯ X ⟶ X)) z = y := by
      change ((inv (prodComparison A X X) ≫ A.map prod.snd) _ = y)
      rw [inv_prodComparison_map_snd, biprod.isoProd_hom, ← ConcreteCategory.comp_apply,
        prod.lift_snd]
      change ((ModuleCat.biprodIsoProd _ _).inv ≫ biprod.snd) (x, y) = y
      rw [ModuleCat.biprodIsoProd_inv_comp_snd]; rfl
    have hα₁ := ConcreteCategory.congr_hom
      (NatTrans.naturality α (prod.fst : X ⨯ X ⟶ X)) z
    have hα₂ := ConcreteCategory.congr_hom
      (NatTrans.naturality α (prod.snd : X ⨯ X ⟶ X)) z
    have hαadd := ConcreteCategory.congr_hom (NatTrans.naturality α
      ((prod.fst : X ⨯ X ⟶ X) + prod.snd)) z
    dsimp at hα₁ hα₂ hαadd ⊢
    rw [A.map_add, B.map_add] at hαadd
    simp only [ModuleCat.hom_add, LinearMap.add_apply] at hαadd
    rw [hz₁] at hα₁; rw [hz₂] at hα₂
    rw [hz₁, hz₂] at hαadd
    exact hαadd.trans (congrArg₂ (· + ·) hα₁ hα₂).symm
  map_smul' r x := by
    have h := ConcreteCategory.congr_hom (NatTrans.naturality α (r • (𝟙 X))) x
    dsimp at h ⊢
    rw [A.map_smul, B.map_smul] at h
    simpa using h

private noncomputable def liftNatTrans
    (R : Type uR) [CommRing R]
    (A B : FGModuleCat.{vM} R ⥤ ModuleCat.{uM} R)
    [A.Additive] [A.Linear R] [B.Additive] [B.Linear R]
    (α : A ⋙ forget (ModuleCat.{uM} R) ⟶ B ⋙ forget (ModuleCat.{uM} R)) : A ⟶ B where
  app X := ModuleCat.ofHom (natTransAppLinearMap R A B α X)
  naturality {X Y} f := by
    ext x; exact ConcreteCategory.congr_hom (NatTrans.naturality α f) x

/-- **Stacks Project, Tag 06I7.** A natural transformation between product-preserving
set-valued functors on finitely generated modules uniquely lifts to a natural transformation
between their canonical linear lifts. Its underlying natural transformation is the original
one. -/
@[stacks 06I7]
theorem fgModuleCat_linearFunctorLift_natTrans
    (R : Type uR) [CommRing R]
    (F G : FGModuleCat.{vM} R ⥤ Type uM)
    [PreservesFiniteProducts F] [Unique (F.obj (FGModuleCat.of R PUnit))]
    [PreservesFiniteProducts G] [Unique (G.obj (FGModuleCat.of R PUnit))]
    (t : F ⟶ G) :
    ∃! τ : (fgModuleCatLinearFunctorLift R F).functor ⟶
        (fgModuleCatLinearFunctorLift R G).functor,
      Functor.whiskerRight τ (forget (ModuleCat.{uM} R)) =
        eqToHom (fgModuleCatLinearFunctorLift R F).forget_comp ≫
          t ≫
            eqToHom (fgModuleCatLinearFunctorLift R G).forget_comp.symm := by
  let A := (fgModuleCatLinearFunctorLift R F).functor
  let B := (fgModuleCatLinearFunctorLift R G).functor
  let α : A ⋙ forget (ModuleCat.{uM} R) ⟶ B ⋙ forget (ModuleCat.{uM} R) :=
    eqToHom (fgModuleCatLinearFunctorLift R F).forget_comp ≫ t ≫
      eqToHom (fgModuleCatLinearFunctorLift R G).forget_comp.symm
  refine ⟨liftNatTrans R A B α, ?_, ?_⟩
  · ext X x; rfl
  · intro τ hτ
    ext X x; exact ConcreteCategory.congr_hom (NatTrans.congr_app hτ X) x

end

/-! ### Linear functors on finite-dimensional vector spaces -/

section
open CategoryTheory
universe u

private lemma fg_add_apply {K : Type u} [Field K] {V W : FGModuleCat.{u} K}
    (f g : V ⟶ W) (x : V) : (f + g).hom x = f.hom x + g.hom x := by
  show (((forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)).map (f + g)).hom) x = _
  simp only [CategoryTheory.Functor.map_add, ModuleCat.hom_add, LinearMap.add_apply]
  rfl

private def fromUnit (K : Type u) [Field K] (V : FGModuleCat.{u} K) :
    V →ₗ[K] (FGModuleCat.of K K ⟶ V) where
  toFun v := FGModuleCat.ofHom (LinearMap.toSpanSingleton K V v)
  map_add' x y := FGModuleCat.hom_ext (LinearMap.toSpanSingleton_add x y)
  map_smul' r x := FGModuleCat.hom_ext (LinearMap.toSpanSingleton_smul r x)

private def tensorComparison (K : Type u) [Field K]
    (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.Additive] [L.Linear K]
    (V : FGModuleCat.{u} K) :
    (MonoidalCategory.tensorLeft (L.obj (FGModuleCat.of K K))).obj V.obj ⟶ L.obj V :=
  ModuleCat.ofHom <| TensorProduct.lift <| LinearMap.mk₂ K
    (fun x v ↦ (L.map (fromUnit K V v)).hom x)
    (fun _ _ _ ↦ map_add _ _ _)
    (fun _ _ _ ↦ map_smul _ _ _)
    (fun x v w ↦ by
      rw [map_add, L.map_add]
      rfl)
    (fun r x v ↦ by
      rw [map_smul, L.map_smul]
      rfl)

private lemma tensorComparison_natural (K : Type u) [Field K]
    (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.Additive] [L.Linear K]
    {V W : FGModuleCat.{u} K} (f : V ⟶ W) :
    ((MonoidalCategory.tensorLeft (L.obj (FGModuleCat.of K K))).map
      ((forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)).map f)) ≫
        tensorComparison K L W = tensorComparison K L V ≫ L.map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
      show (L.map (fromUnit K W (f.hom v))).hom x =
        (L.map f).hom ((L.map (fromUnit K V v)).hom x)
      have h : fromUnit K W (f.hom v) = fromUnit K V v ≫ f :=
        FGModuleCat.hom_ext (LinearMap.comp_toSpanSingleton f.hom.hom v).symm
      rw [h, L.map_comp]
      rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

private noncomputable def tensorComparisonInv (K : Type u) [Field K]
    (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.Additive] [L.Linear K]
    (V : FGModuleCat.{u} K) :
    L.obj V ⟶ (MonoidalCategory.tensorLeft (L.obj (FGModuleCat.of K K))).obj V.obj :=
  let b := Module.finBasis K V
  ModuleCat.ofHom
    { toFun := fun y ↦ ∑ i, (L.map (FGModuleCat.ofHom (b.coord i))).hom y ⊗ₜ[K] b i
      map_add' := fun x y ↦ by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
      map_smul' := fun r x ↦ by simp [TensorProduct.smul_tmul, Finset.smul_sum] }

private lemma tensorComparison_comp_inv (K : Type u) [Field K]
    (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.Additive] [L.Linear K]
    (V : FGModuleCat.{u} K) :
    tensorComparisonInv K L V ≫ tensorComparison K L V = 𝟙 (L.obj V) := by
  let b := Module.finBasis K V
  ext y
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply]
  dsimp [tensorComparisonInv]
  rw [map_sum]
  simp only [tensorComparison, ModuleCat.hom_ofHom]
  show (∑ i, (L.map (fromUnit K V (b i))).hom
    ((L.map (FGModuleCat.ofHom (b.coord i))).hom y)) = y
  have heq (i) : (L.map (fromUnit K V (b i))).hom
      ((L.map (FGModuleCat.ofHom (b.coord i))).hom y) =
      (L.map ((FGModuleCat.ofHom (b.coord i) : V ⟶ FGModuleCat.of K K) ≫
        fromUnit K V (b i))).hom y := by
    rw [L.map_comp]
    rfl
  simp_rw [heq]
  have h : (∑ i, (FGModuleCat.ofHom (b.coord i) : V ⟶ FGModuleCat.of K K) ≫
      fromUnit K V (b i)) = 𝟙 V := by
    apply FGModuleCat.hom_ext
    ext v
    have eval_sum (s : Finset (Fin (Module.finrank K V))) :
        (ModuleCat.Hom.hom (∑ i ∈ s,
          (FGModuleCat.ofHom (b.coord i) : V ⟶ FGModuleCat.of K K) ≫
            fromUnit K V (b i)).hom) v = ∑ i ∈ s, b.repr v i • b i := by
      classical
      induction s using Finset.induction with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, fg_add_apply, ih]
          have hterm : ((FGModuleCat.ofHom (b.coord i) : V ⟶ FGModuleCat.of K K) ≫
              fromUnit K V (b i)).hom v = b.repr v i • b i := by
            show b.coord i v • b i = b.repr v i • b i
            rfl
          rw [hterm]
    rw [eval_sum Finset.univ, b.sum_repr]
    rfl
  calc
    _ = (L.map (∑ i, (FGModuleCat.ofHom (b.coord i) : V ⟶ FGModuleCat.of K K) ≫
        fromUnit K V (b i))).hom y := by
          rw [L.map_sum]
          simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
    _ = y := by rw [h, L.map_id]; rfl

private lemma tensorComparison_inv_comp (K : Type u) [Field K]
    (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.Additive] [L.Linear K]
    (V : FGModuleCat.{u} K) :
    tensorComparison K L V ≫ tensorComparisonInv K L V =
      𝟙 ((MonoidalCategory.tensorLeft (L.obj (FGModuleCat.of K K))).obj V.obj) := by
  let b := Module.finBasis K V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x v =>
      show (∑ i, (L.map (FGModuleCat.ofHom (b.coord i))).hom
        ((L.map (fromUnit K V v)).hom x) ⊗ₜ[K] b i) = x ⊗ₜ[K] v
      have h (i) : fromUnit K V v ≫ FGModuleCat.ofHom (b.coord i) =
          (b.repr v i) • 𝟙 (FGModuleCat.of K K) := by
        apply FGModuleCat.hom_ext
        apply LinearMap.ext
        intro r
        show b.coord i (r • v) = b.repr v i * r
        simp [b.coord_apply, mul_comm]
      have heq (i) : (L.map (FGModuleCat.ofHom (b.coord i))).hom
          ((L.map (fromUnit K V v)).hom x) = b.repr v i • x := by
        rw [← ModuleCat.comp_apply, ← L.map_comp, h, L.map_smul, L.map_id]
        rfl
      simp_rw [heq, TensorProduct.smul_tmul]
      rw [← TensorProduct.tmul_sum, b.sum_repr]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- **Stacks Project, Tag 06I8.** A linear functor from finite-dimensional vector spaces over
a field to vector spaces is naturally isomorphic to tensoring with its value on the ground
field. -/
@[stacks 06I8]
theorem linearFunctor_iso_tensorLeft (K : Type u) [Field K]
    (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.Additive] [L.Linear K] :
    Nonempty
      (((forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)) ⋙
          MonoidalCategory.tensorLeft (L.obj (FGModuleCat.of K K))) ≅ L) :=
  ⟨NatIso.ofComponents (fun V ↦
    { hom := tensorComparison K L V
      inv := tensorComparisonInv K L V
      hom_inv_id := tensorComparison_inv_comp K L V
      inv_hom_id := tensorComparison_comp_inv K L V })
    (tensorComparison_natural K L)⟩

end

end Deformation
