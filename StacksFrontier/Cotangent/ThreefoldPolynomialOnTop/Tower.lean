module

public import StacksFrontier.Cotangent.ThreefoldPolynomialOnTop.AdjoinVariables

/-!
# The tower of a resolution when the top ring is a polynomial algebra

Let `A → B → C` be ring maps with `C = B[E]` a polynomial algebra over `B`, and let
`ε : P_• → B` be a resolution of `B` over `A`. This file builds the towers
`U_n = (P_n → B, P_n[E] → C)` of the threefold site `C_{C/B/A}` of Tag 08QT and the cosimplicial
object `U_•` they form, identifies `u₃(U_•)` with the constant simplicial object at the identity
augmentation `C → C`, and shows that the augmentation `P_•[E] → C` is a trivial Kan fibration
when `ε` is one.

## Main definitions

* `CommAlgCat.towerVariablesAugmentation` and `CommAlgCat.towerCommaOfResolution`: the
  augmentation `P_n[E] → C` and the tower `(P_n → B, P_n[E] → C)` it belongs to.
* `CommAlgCat.towerCosimplicialObject`: the cosimplicial object `U_•` of `C_{C/B/A}`.
* `CommAlgCat.towerThirdSimplicialConstIso`: `u₃(U_•)` is constant at `C → C`.

## Main results

* `CommAlgCat.trivialKanFibrations_towerVariablesAugmentationNatTrans`: `P_•[E] → C` is a
  trivial Kan fibration, `C = B[E]` identifying it with the coefficientwise `ε`.

## References

* [Stacks Project, Tag 08QV](https://stacks.math.columbia.edu/tag/08QV)
* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CommAlgCat

/-! ### The tower attached to a resolution -/

section Tower

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)

/-- The augmentation `P_n[E] → C` of the tower attached to a degree of a resolution: the
`A`-algebra map restricting on the coefficients to `P_n → B → C` and sending the variable `X_e`
to the image of `X_e` under a presentation `C = B[E]`. -/
def towerVariablesAugmentation (m : SimplexCategoryᵒᵖ) :
    MvPolynomial E (P.obj m) →ₐ[A] C :=
  MvPolynomial.aevalTower
    ((IsScalarTower.toAlgHom A B C).comp (CommAlgCat.Hom.hom (ε.app m)))
    fun e => eqv (MvPolynomial.X e)

/-- On the coefficients the augmentation `P_n[E] → C` is `P_n → B → C`. -/
@[simp]
lemma towerVariablesAugmentation_C (m : SimplexCategoryᵒᵖ) (p : P.obj m) :
    towerVariablesAugmentation ε eqv m (MvPolynomial.C p) =
      algebraMap B C ((CommAlgCat.Hom.hom (ε.app m)) p) :=
  MvPolynomial.aevalTower_C _ _ p

/-- On a variable the augmentation `P_n[E] → C` is the presentation `C = B[E]`. -/
@[simp]
lemma towerVariablesAugmentation_X (m : SimplexCategoryᵒᵖ) (e : E) :
    towerVariablesAugmentation ε eqv m (MvPolynomial.X e) = eqv (MvPolynomial.X e) :=
  MvPolynomial.aevalTower_X _ _ e

/-- **The augmentation `P_n[E] → C` is the presentation `C = B[E]` applied coefficientwise to
the augmentation `P_n → B`.** -/
lemma towerVariablesAugmentation_eq_eqv_map (m : SimplexCategoryᵒᵖ)
    (p : MvPolynomial E (P.obj m)) :
    towerVariablesAugmentation ε eqv m p =
      eqv (MvPolynomial.map (CommAlgCat.Hom.hom (ε.app m)).toRingHom p) := by
  have key : towerVariablesAugmentation ε eqv m =
      ((eqv.toAlgHom.restrictScalars A).comp
        (MvPolynomial.mapAlgHom (CommAlgCat.Hom.hom (ε.app m)))) := by
    refine MvPolynomial.algHom_ext' ?_ ?_
    · refine AlgHom.ext fun q => ?_
      show towerVariablesAugmentation ε eqv m (MvPolynomial.C q) =
        eqv (MvPolynomial.map (CommAlgCat.Hom.hom (ε.app m)).toRingHom (MvPolynomial.C q))
      rw [towerVariablesAugmentation_C, MvPolynomial.map_C]
      exact (eqv.commutes ((CommAlgCat.Hom.hom (ε.app m)) q)).symm
    · intro e
      show towerVariablesAugmentation ε eqv m (MvPolynomial.X e) =
        eqv (MvPolynomial.map (CommAlgCat.Hom.hom (ε.app m)).toRingHom (MvPolynomial.X e))
      rw [towerVariablesAugmentation_X, MvPolynomial.map_X]
  exact AlgHom.congr_fun key p

/-- **The augmentations `P_n[E] → C` are compatible with the simplicial operators**, which act
on the coefficients: on a coefficient this is the compatibility of `ε` with them, and a variable
has the same image in every degree. -/
lemma mvPolynomialMap_comp_towerVariablesAugmentation {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m') :
    (mvPolynomialFunctor A E).map (P.map f) ≫
        CommAlgCat.ofHom (towerVariablesAugmentation ε eqv m') =
      CommAlgCat.ofHom (towerVariablesAugmentation ε eqv m) := by
  apply CommAlgCat.hom_ext
  refine MvPolynomial.algHom_ext' ?_ ?_
  · refine AlgHom.ext fun q => ?_
    show towerVariablesAugmentation ε eqv m'
        (MvPolynomial.map (CommAlgCat.Hom.hom (P.map f)).toRingHom
          (MvPolynomial.C q)) = towerVariablesAugmentation ε eqv m (MvPolynomial.C q)
    rw [MvPolynomial.map_C, towerVariablesAugmentation_C, towerVariablesAugmentation_C]
    refine congrArg (algebraMap B C) ?_
    have h := ε.naturality f
    rw [show ((SimplicialObject.const (CommAlgCat.{u} A)).obj
      (towerBaseAlgebra A B)).map f = 𝟙 _ from rfl, Category.comp_id] at h
    exact ConcreteCategory.congr_hom h q
  · intro e
    show towerVariablesAugmentation ε eqv m'
        (MvPolynomial.map (CommAlgCat.Hom.hom (P.map f)).toRingHom
          (MvPolynomial.X e)) = towerVariablesAugmentation ε eqv m (MvPolynomial.X e)
    rw [MvPolynomial.map_X, towerVariablesAugmentation_X, towerVariablesAugmentation_X]

/-- The tower `(P_n → B, P_n[E] → C)` attached to a degree of a resolution, as an object of the
comma category underlying the site `C_{C/B/A}`. -/
def towerCommaOfResolution (hP : ∀ m, IsPolynomialAlgebra A (P.obj m)) (m : SimplexCategoryᵒᵖ) :
    TowerComma A B C where
  left := ⟨Over.mk (ε.app m), hP m⟩
  right := Over.mk (CommAlgCat.ofHom (towerVariablesAugmentation ε eqv m))
  hom := CommAlgCat.ofHom (IsScalarTower.toAlgHom A (P.obj m) (MvPolynomial E (P.obj m)))

/-- The towers `(P_n → B, P_n[E] → C)` of the degrees of a resolution form a simplicial object
of the comma category underlying `C_{C/B/A}`: the simplicial operators of `P_•` act on the
coefficients. -/
def towerCommaSimplicialOfResolution (hP : ∀ m, IsPolynomialAlgebra A (P.obj m)) :
    SimplicialObject (TowerComma A B C) where
  obj m := towerCommaOfResolution ε eqv hP m
  map {m m'} f :=
    { left := ObjectProperty.homMk (Over.homMk (P.map f) (by
        have h := ε.naturality f
        rw [show ((SimplicialObject.const (CommAlgCat.{u} A)).obj
          (towerBaseAlgebra A B)).map f = 𝟙 _ from rfl, Category.comp_id] at h
        exact h))
      right := Over.homMk ((mvPolynomialFunctor A E).map (P.map f))
        (mvPolynomialMap_comp_towerVariablesAugmentation ε eqv f)
      w := by
        apply CommAlgCat.hom_ext
        refine AlgHom.ext fun q => ?_
        change MvPolynomial.C ((CommAlgCat.Hom.hom (P.map f)) q) =
          MvPolynomial.map (CommAlgCat.Hom.hom (P.map f)).toRingHom (MvPolynomial.C q)
        exact (MvPolynomial.map_C _ _).symm }
  map_id m := by
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact P.map_id m
    · apply Over.OverMorphism.ext
      change (mvPolynomialFunctor A E).map (P.map (𝟙 m)) = 𝟙 _
      rw [P.map_id, (mvPolynomialFunctor A E).map_id]
  map_comp f g := by
    apply Comma.hom_ext
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact P.map_comp f g
    · apply Over.OverMorphism.ext
      change (mvPolynomialFunctor A E).map (P.map (f ≫ g)) =
        (mvPolynomialFunctor A E).map (P.map f) ≫ (mvPolynomialFunctor A E).map (P.map g)
      rw [P.map_comp, (mvPolynomialFunctor A E).map_comp]

/-- The towers `(P_n → B, P_n[E] → C)` of a resolution are polynomial towers: `P_n[E]` is a
polynomial algebra over `P_n` and the composite `P_n → P_n[E] → C` is `P_n → B → C`. -/
lemma isPolynomialTower_towerCommaOfResolution (hP : ∀ m, IsPolynomialAlgebra A (P.obj m))
    (m : SimplexCategoryᵒᵖ) :
    IsPolynomialTower A B C (towerCommaOfResolution ε eqv hP m) := by
  refine ⟨⟨E, ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) fun _ => rfl⟩⟩, ?_⟩
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun q => ?_
  show towerVariablesAugmentation ε eqv m (MvPolynomial.C q) = _
  exact towerVariablesAugmentation_C ε eqv m q

/-- The towers `(P_n → B, P_n[E] → C)` of a resolution, as a simplicial object of the category
of polynomial towers. -/
def towerSimplicialOfResolution (hP : ∀ m, IsPolynomialAlgebra A (P.obj m)) :
    SimplicialObject (PolynomialTower A B C) :=
  (IsPolynomialTower A B C).lift (towerCommaSimplicialOfResolution ε eqv hP)
    (isPolynomialTower_towerCommaOfResolution ε eqv hP)

/-- The towers `(P_n → B, P_n[E] → C)` of a resolution, as a cosimplicial object of the site
`C_{C/B/A}`: the site is the opposite of the category of polynomial towers. -/
def towerCosimplicialObject (hP : ∀ m, IsPolynomialAlgebra A (P.obj m)) :
    CosimplicialObject (polynomialTowerSite A B C) :=
  (towerSimplicialOfResolution ε eqv hP).rightOp

end Tower

/-! ### `u₃` of the tower of a resolution -/

section Third

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)
  (hP : ∀ m, IsPolynomialAlgebra A (P.obj m))

include eqv in
/-- A presentation `C = B[E]` makes `C` a polynomial algebra over `B`. -/
lemma isPolynomialAlgebra_towerRelativeAlgebra :
    IsPolynomialAlgebra B (towerRelativeAlgebra B C) :=
  ⟨E, ⟨eqv⟩⟩

/-- The identity augmentation `C → C`, an object of the site `C_{C/B}`. -/
abbrev towerIdentityAugmentation : PolynomialAugmentation B (towerRelativeAlgebra B C) :=
  polynomialIdentityAugmentation B (towerRelativeAlgebra B C)
    (isPolynomialAlgebra_towerRelativeAlgebra eqv)

/-- The algebra `Q = P_n[E]` of the tower of a degree of a resolution is the polynomial algebra
on `E` over its `P_n`: the identity, read for the `P_n`-algebra structure the tower carries. -/
def towerRightAlgebraEquivOfResolution (m : SimplexCategoryᵒᵖ) :
    MvPolynomial E ↑(towerLeftAlgebra (towerCommaOfResolution ε eqv hP m))
      ≃ₐ[↑(towerLeftAlgebra (towerCommaOfResolution ε eqv hP m))]
        ↑(towerRightAlgebra (towerCommaOfResolution ε eqv hP m)) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) fun _ => rfl

/-- The base change `B ⊗_{P_n} P_n[E]` of the tower of a degree of a resolution is `B[E]`. -/
def towerBaseChangeMvPolynomialEquiv (m : SimplexCategoryᵒᵖ) :
    MvPolynomial E B ≃ₐ[B]
      ↑(towerBaseChangeAlgebra (towerCommaOfResolution ε eqv hP m)) :=
  have hf : Function.Bijective (Algebra.TensorProduct.map (S := B) (AlgHom.id B B)
      (towerRightAlgebraEquivOfResolution ε eqv hP m).toAlgHom) :=
    Algebra.TensorProduct.map_bijective
      (f := (AlgHom.id B B).restrictScalars
        ↑(towerLeftAlgebra (towerCommaOfResolution ε eqv hP m)))
      (g := (towerRightAlgebraEquivOfResolution ε eqv hP m).toAlgHom)
      Function.bijective_id (towerRightAlgebraEquivOfResolution ε eqv hP m).bijective
  (MvPolynomial.algebraTensorAlgEquiv
      (↑(towerLeftAlgebra (towerCommaOfResolution ε eqv hP m)) : Type u) B).symm.trans
    (AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id B B)
      (towerRightAlgebraEquivOfResolution ε eqv hP m).toAlgHom) hf)

/-- The base change `B ⊗_{P_n} P_n[E]` of the tower of a degree of a resolution is `C`: it is
`B[E]`, which the presentation identifies with `C`. -/
def towerBaseChangeAlgEquiv (m : SimplexCategoryᵒᵖ) :
    ↑(towerBaseChangeAlgebra (towerCommaOfResolution ε eqv hP m)) ≃ₐ[B] C :=
  (towerBaseChangeMvPolynomialEquiv ε eqv hP m).symm.trans eqv

/-- The identification `B ⊗_{P_n} P_n[E] = B[E]` sends a variable to `1 ⊗ X_e`. -/
lemma towerBaseChangeMvPolynomialEquiv_X (m : SimplexCategoryᵒᵖ) (e : E) :
    towerBaseChangeMvPolynomialEquiv ε eqv hP m (MvPolynomial.X e) =
      (1 : B) ⊗ₜ[↑(towerLeftAlgebra (towerCommaOfResolution ε eqv hP m))]
        (towerRightAlgebraEquivOfResolution ε eqv hP m (MvPolynomial.X e)) := by
  show Algebra.TensorProduct.map (AlgHom.id B B)
      (towerRightAlgebraEquivOfResolution ε eqv hP m).toAlgHom
      ((MvPolynomial.algebraTensorAlgEquiv
        (↑(towerLeftAlgebra (towerCommaOfResolution ε eqv hP m)) : Type u) B).symm
          (MvPolynomial.X e)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_symm_X, Algebra.TensorProduct.map_tmul]
  rfl

/-- The augmentation of `u₃` of the tower of a degree of a resolution, read through the
identification `B ⊗_{P_n} P_n[E] = B[E]`, is the presentation `B[E] = C`: the two `B`-algebra
maps out of `B[E]` agree on the variables. -/
lemma towerBaseChangeAugmentation_apply_equiv (m : SimplexCategoryᵒᵖ) (x : MvPolynomial E B) :
    towerBaseChangeAugmentation ((towerSimplicialOfResolution ε eqv hP).obj m)
        (towerBaseChangeMvPolynomialEquiv ε eqv hP m x) = eqv x := by
  have key : (towerBaseChangeAugmentation ((towerSimplicialOfResolution ε eqv hP).obj m)).comp
      (towerBaseChangeMvPolynomialEquiv ε eqv hP m).toAlgHom = eqv.toAlgHom := by
    refine MvPolynomial.algHom_ext fun e => ?_
    show towerBaseChangeAugmentation ((towerSimplicialOfResolution ε eqv hP).obj m)
      (towerBaseChangeMvPolynomialEquiv ε eqv hP m (MvPolynomial.X e)) = eqv (MvPolynomial.X e)
    rw [towerBaseChangeMvPolynomialEquiv_X]
    refine Eq.trans (towerBaseChangeAugmentation_tmul _ 1 _) ?_
    rw [map_one, one_mul]
    exact towerVariablesAugmentation_X ε eqv m e
  exact AlgHom.congr_fun key x

/-- **The augmentation of `u₃` of the tower of a degree of a resolution is the identification
`B ⊗_{P_n} P_n[E] = C`.** -/
lemma towerBaseChangeAugmentation_eq_algEquiv (m : SimplexCategoryᵒᵖ)
    (z : ↑(towerBaseChangeAlgebra (towerCommaOfResolution ε eqv hP m))) :
    towerBaseChangeAugmentation ((towerSimplicialOfResolution ε eqv hP).obj m) z =
      towerBaseChangeAlgEquiv ε eqv hP m z := by
  obtain ⟨x, rfl⟩ := (towerBaseChangeMvPolynomialEquiv ε eqv hP m).surjective z
  show _ = eqv ((towerBaseChangeMvPolynomialEquiv ε eqv hP m).symm
    (towerBaseChangeMvPolynomialEquiv ε eqv hP m x))
  rw [AlgEquiv.symm_apply_apply]
  exact towerBaseChangeAugmentation_apply_equiv ε eqv hP m x

/-- `u₃` of the tower of a degree of a resolution is the identity augmentation `C → C`. -/
def towerThirdObjIso (m : SimplexCategoryᵒᵖ) :
    (polynomialTowerThirdAugmentations A B C).obj
        ((towerSimplicialOfResolution ε eqv hP).obj m) ≅
      towerIdentityAugmentation eqv :=
  ObjectProperty.isoMk _
    (Over.isoMk (CommAlgCat.isoMk (towerBaseChangeAlgEquiv ε eqv hP m)) (by
      apply CommAlgCat.hom_ext
      refine AlgHom.ext fun z => ?_
      exact (towerBaseChangeAugmentation_eq_algEquiv ε eqv hP m z).symm))

/-- **`u₃(U_•)` is the constant simplicial object with value the identity augmentation
`C → C`.** Each component is the augmentation `B ⊗_{P_n} P_n[E] → C`, an isomorphism because
`B ⊗_{P_n} P_n[E] = B[E] = C`; naturality is the uniqueness of a map to a terminal object. -/
def towerThirdSimplicialConstIso :
    towerSimplicialOfResolution ε eqv hP ⋙ polynomialTowerThirdAugmentations A B C ≅
      (SimplicialObject.const
          (PolynomialAugmentation B (towerRelativeAlgebra B C))).obj
        (towerIdentityAugmentation eqv) :=
  NatIso.ofComponents (fun m => towerThirdObjIso ε eqv hP m) fun _ =>
    (polynomialIdentityAugmentation_isTerminal B (towerRelativeAlgebra B C)
      (isPolynomialAlgebra_towerRelativeAlgebra eqv)).hom_ext _ _

end Third

/-! ### The augmentation `P_•[E] → C` is a trivial Kan fibration -/

section Fibration

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B))
  {E : Type u} (eqv : MvPolynomial E B ≃ₐ[B] C)

/-- Adjoining `E` to the constant simplicial algebra `B` gives the constant simplicial algebra
`B[E]`, which a presentation identifies with `C`. -/
def mvPolynomialConstIso :
    (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerBaseAlgebra A B) ⋙
        mvPolynomialFunctor A E ≅
      (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerTotalAlgebra A C) :=
  Functor.constComp SimplexCategoryᵒᵖ (towerBaseAlgebra A B) (mvPolynomialFunctor A E) ≪≫
    (SimplicialObject.const (CommAlgCat.{u} A)).mapIso
      (CommAlgCat.isoMk (AlgEquiv.restrictScalars A eqv))

/-- The augmentations `P_n[E] → C` of the towers of a resolution, as a morphism of simplicial
`A`-algebras into the constant one at `C`: the coefficientwise augmentation `P_• → B` followed
by the presentation `B[E] = C`. -/
def towerVariablesAugmentationNatTrans :
    P ⋙ mvPolynomialFunctor A E ⟶
      (SimplicialObject.const (CommAlgCat.{u} A)).obj (towerTotalAlgebra A C) where
  app m := CommAlgCat.ofHom (towerVariablesAugmentation ε eqv m)
  naturality m m' f := by
    change (mvPolynomialFunctor A E).map (P.map f) ≫
      CommAlgCat.ofHom (towerVariablesAugmentation ε eqv m') =
        CommAlgCat.ofHom (towerVariablesAugmentation ε eqv m) ≫ 𝟙 _
    rw [Category.comp_id]
    exact mvPolynomialMap_comp_towerVariablesAugmentation ε eqv f

/-- `CommAlgCat.towerVariablesAugmentationNatTrans` is the coefficientwise augmentation
`P_• → B` followed by the presentation `B[E] = C`. -/
lemma towerVariablesAugmentationNatTrans_eq :
    towerVariablesAugmentationNatTrans ε eqv =
      Functor.whiskerRight ε (mvPolynomialFunctor A E) ≫ (mvPolynomialConstIso eqv).hom := by
  refine NatTrans.ext (funext fun m => ?_)
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun p => ?_
  exact towerVariablesAugmentation_eq_eqv_map ε eqv m p

/-- **The augmentation `P_•[E] → C` is a trivial Kan fibration** on underlying simplicial sets,
for `ε : P_• → B` a trivial Kan fibration: it is the coefficientwise `ε`, which adjoining
variables preserves, followed by an isomorphism. -/
theorem trivialKanFibrations_towerVariablesAugmentationNatTrans
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    SSet.trivialKanFibrations (Functor.whiskerRight
      (towerVariablesAugmentationNatTrans ε eqv) (forget (CommAlgCat.{u} A))) := by
  rw [towerVariablesAugmentationNatTrans_eq]
  have h : Functor.whiskerRight (Functor.whiskerRight ε (mvPolynomialFunctor A E) ≫
          (mvPolynomialConstIso eqv).hom) (forget (CommAlgCat.{u} A)) =
      Functor.whiskerRight (Functor.whiskerRight ε (mvPolynomialFunctor A E))
          (forget (CommAlgCat.{u} A)) ≫
        (Functor.isoWhiskerRight (mvPolynomialConstIso eqv)
          (forget (CommAlgCat.{u} A))).hom :=
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (CommAlgCat.{u} A) (Type u)).obj
      (forget (CommAlgCat.{u} A))).map_comp _ _
  rw [h]
  exact MorphismProperty.RespectsIso.postcomp SSet.trivialKanFibrations _ _
    (trivialKanFibrations_mvPolynomialWhiskerRight E ε hε)

end Fibration

end CommAlgCat

end
