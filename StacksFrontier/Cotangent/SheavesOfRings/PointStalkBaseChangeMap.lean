module

public import StacksFrontier.Cotangent.SheavesOfRings.PointStalkTowerBaseChange
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposTransitivityTriangleDerived
public import StacksFrontier.Cotangent.LocalizationSquareQuasiIso

/-!
# Stalks of changes of the base ring of the cotangent complex at a point of a site

Let `D` be a sheaf of commutative rings on a site, `f₁ : A₁ ⟶ D` and `f₂ : A₂ ⟶ D` two
homomorphisms into it and `a : A₁ ⟶ A₂` a homomorphism over `D`. A map of complexes
`φ : L_{D/A₁} ⟶ L_{D/A₂}` of `D`-modules is said to *change the base along `a` at the point `Φ`*
when its stalk at `Φ`, read through the identifications `(L_{D/Aᵢ})_Φ ≅ L_{D_Φ/(Aᵢ)_Φ}` of
Tag 08T0 (`CategoryTheory.Sheaf.pointStalkCotangentComplexIso`), is the change-of-base map of
Tag 08PN of the ring maps of stalks, the map of cotangent complexes of the square
`((A₁)_Φ → (A₂)_Φ, 𝟙 D_Φ)` (`CategoryTheory.Sheaf.IsPointStalkBaseMap`).

This file proves that the property holds for the map of cotangent complexes of the square
`(a, 𝟙 D)`, for identities, for the isomorphism of cotangent complexes of an isomorphism `a`
followed by the identification of restriction of scalars along the identity with the identity,
and that it is stable under composition and inversion. Combined with the stalk of the first arrow
of Tag 08SZ (`CategoryTheory.Sheaf.stalk_towerCotangentBaseChange`) it computes the stalk of the
first arrow of 08SZ followed by any such change of base
(`CategoryTheory.Sheaf.stalk_towerCotangentBaseChange_comp_apply`).

This is the form in which the proof of [Stacks, Tag 09DM] reads the right column of the diagram
of Tag 09DK at a geometric point: that column is the first arrow of the tower of the second
projection, followed by a string of changes of base and of identifications of cotangent
complexes.

## Main definitions

* `CategoryTheory.Sheaf.pointBaseSquare`: the square `((A₁)_Φ → (A₂)_Φ, 𝟙 D_Φ)` of stalk rings.
* `CategoryTheory.Sheaf.IsPointStalkBaseMap`: the property above.

## Main results

* `CategoryTheory.Sheaf.isPointStalkBaseMap_squareCotangentComplexMap`,
  `CategoryTheory.Sheaf.isPointStalkBaseMap_id`,
  `CategoryTheory.Sheaf.isPointStalkBaseMap_squareCotangentComplexIso`,
  `CategoryTheory.Sheaf.IsPointStalkBaseMap.comp`,
  `CategoryTheory.Sheaf.IsPointStalkBaseMap.inverse` and
  `CategoryTheory.Sheaf.IsPointStalkBaseMap.iso_inv`: the closure properties.
* `CategoryTheory.Sheaf.stalk_towerCotangentBaseChange_comp_apply`: the stalk of the first arrow
  of Tag 08SZ followed by a change of base.

## References

* [Stacks Project, Tag 08T0](https://stacks.math.columbia.edu/tag/08T0)
* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 09DM](https://stacks.math.columbia.edu/tag/09DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- `SheafOfModules.restrictScalarsIdIso` is the identity on sections. -/
theorem restrictScalarsIdIso_hom_val_app_apply (α : R ⟶ R) (hα : α = 𝟙 R)
    (M : SheafOfModules.{w} R) (U : Cᵒᵖ) (x : M.val.obj U) :
    (restrictScalarsIdIso α hα M).hom.val.app U x = x := by
  subst hα
  rfl

end SheafOfModules

namespace CommAlgCat

universe t

/-- The map of cotangent complexes of abelian groups of a square is, elementwise, the map of
cotangent complexes of modules. -/
theorem cotangentComplexAbMap_f_apply {R R' : Type t} [CommRing R] [CommRing R']
    {B : CommAlgCat.{t} R} {B' : CommAlgCat.{t} R'} (sq : AlgebraSquare.{t, t, t} R R' B B')
    (n : ℤ) (x : (cotangentComplex.{t, t} R B).X n) :
    (cotangentComplexAbMap.{t, t, t} sq).f n x = (squareCotangentComplexMap.{t, t, t} sq).f n x :=
  rfl

/-- The map of cotangent complexes of the identity square is the identity, elementwise. -/
theorem squareCotangentComplexMap_algebraSquareId_apply {R : Type t} [CommRing R]
    (B : CommAlgCat.{t} R) (n : ℤ) (x : (cotangentComplex.{t, t} R B).X n) :
    (squareCotangentComplexMap.{t, t, t} (AlgebraSquare.id.{t, t} R B)).f n x = x := by
  have h := congrArg (fun k => (k.f n) x) (cotangentComplexAbMap_algebraSquareId.{t} R B)
  simp only [HomologicalComplex.id_f] at h
  exact h

end CommAlgCat

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [LocallySmall.{max u v w} C] (Φ : J.Point.{max u v w})
  {A₁ A₂ A₃ D : Sheaf J CommRingCat.{max u v w}} {f₁ : A₁ ⟶ D} {f₂ : A₂ ⟶ D} {f₃ : A₃ ⟶ D}

/-- The square `((A₁)_Φ → (A₂)_Φ, 𝟙 D_Φ)` of stalk rings attached to a homomorphism `a : A₁ ⟶ A₂`
over `D`. -/
def pointBaseSquare (a : A₁ ⟶ A₂) (hsq : f₁ ≫ 𝟙 D = a ≫ f₂) :
    CommAlgCat.AlgebraSquare.{max u v w, max u v w, max u v w}
      ((Φ.presheafFiber (A := CommRingCat)).obj A₁.obj)
      ((Φ.presheafFiber (A := CommRingCat)).obj A₂.obj) (pointStalkAlgebra J Φ f₁)
      (pointStalkAlgebra J Φ f₂) where
  base := ((Φ.presheafFiber (A := CommRingCat)).map a.hom).hom
  map := RingHom.id _
  map_algebraMap z := by
    change ((Φ.presheafFiber (A := CommRingCat)).map f₁.hom).hom z =
      ((Φ.presheafFiber (A := CommRingCat)).map a.hom ≫
        (Φ.presheafFiber (A := CommRingCat)).map f₂.hom).hom z
    rw [← Functor.map_comp]
    exact congrArg (fun k : A₁ ⟶ D => ((Φ.presheafFiber (A := CommRingCat)).map k.hom).hom z)
      ((Category.comp_id f₁).symm.trans hsq)

/-- The square of stalk maps of `(a, 𝟙 D)` is the base square. -/
theorem pointStalkSquare_eq_pointBaseSquare (a : A₁ ⟶ A₂) (hsq : f₁ ≫ 𝟙 D = a ≫ f₂) :
    pointStalkSquare J Φ f₁ a (𝟙 D) hsq = pointBaseSquare J Φ a hsq := by
  refine (CommAlgCat.AlgebraSquare.mk.injEq _ _ _ _ _ _).mpr ⟨rfl, ?_⟩
  show ((Φ.presheafFiber (A := CommRingCat)).map (𝟙 D.obj)).hom = RingHom.id _
  rw [Functor.map_id]
  rfl

/-- The base squares compose. -/
theorem pointBaseSquare_comp (a : A₁ ⟶ A₂) (hsq : f₁ ≫ 𝟙 D = a ≫ f₂) (a' : A₂ ⟶ A₃)
    (hsq' : f₂ ≫ 𝟙 D = a' ≫ f₃) (hsq'' : f₁ ≫ 𝟙 D = (a ≫ a') ≫ f₃) :
    (pointBaseSquare J Φ a hsq).comp (pointBaseSquare J Φ a' hsq') =
      pointBaseSquare J Φ (a ≫ a') hsq'' := by
  refine (CommAlgCat.AlgebraSquare.mk.injEq _ _ _ _ _ _).mpr ⟨?_, rfl⟩
  show ((Φ.presheafFiber (A := CommRingCat)).map a.hom ≫
    (Φ.presheafFiber (A := CommRingCat)).map a'.hom).hom =
      ((Φ.presheafFiber (A := CommRingCat)).map (a ≫ a').hom).hom
  rw [← Functor.map_comp]
  rfl

/-- The base square of the identity is the identity square. -/
theorem pointBaseSquare_id (hsq : f₁ ≫ 𝟙 D = 𝟙 A₁ ≫ f₁) :
    pointBaseSquare J Φ (𝟙 A₁) hsq = CommAlgCat.AlgebraSquare.id _ (pointStalkAlgebra J Φ f₁) := by
  refine (CommAlgCat.AlgebraSquare.mk.injEq _ _ _ _ _ _).mpr ⟨?_, rfl⟩
  show ((Φ.presheafFiber (A := CommRingCat)).map (𝟙 A₁.obj)).hom = RingHom.id _
  rw [Functor.map_id]
  rfl

/-- The map of cotangent complexes of the base square is the identity for the identity. -/
theorem squareCotangentComplexMap_pointBaseSquare_id_apply (hsq : f₁ ≫ 𝟙 D = 𝟙 A₁ ≫ f₁) (n : ℤ)
    (x : (CommAlgCat.cotangentComplex.{max u v w, max u v w} _ (pointStalkAlgebra J Φ f₁)).X n) :
    (CommAlgCat.squareCotangentComplexMap (pointBaseSquare J Φ (𝟙 A₁) hsq)).f n x = x := by
  rw [pointBaseSquare_id]
  exact CommAlgCat.squareCotangentComplexMap_algebraSquareId_apply _ n x

attribute [local instance] moduleOfSections in
/-- **A change of base along `a` at the point `Φ`.** The stalk at `Φ` of the map
`φ : L_{D/A₁} ⟶ L_{D/A₂}`, read through the identifications of Tag 08T0, is the map of cotangent
complexes of the square `((A₁)_Φ → (A₂)_Φ, 𝟙 D_Φ)` of stalk rings. -/
def IsPointStalkBaseMap (a : A₁ ⟶ A₂) (hsq : f₁ ≫ 𝟙 D = a ≫ f₂)
    (φ : cotangentComplex J f₁ ⟶ cotangentComplex J f₂) : Prop :=
  ∀ (n : ℤ) (m : (Stacks.sheafModuleFiberOfCommRing Φ D).obj ((cotangentComplex J f₁).X n)),
    (pointStalkCotangentComplexIso J Φ f₂).hom.f n
        ((Stacks.sheafModuleFiberOfCommRing Φ D).map (φ.f n) m) =
      (CommAlgCat.squareCotangentComplexMap (pointBaseSquare J Φ a hsq)).f n
        ((pointStalkCotangentComplexIso J Φ f₁).hom.f n m)

attribute [local instance] moduleOfSections in
/-- **The map of cotangent complexes of the square `(a, 𝟙 D)` changes the base along `a`.** -/
theorem isPointStalkBaseMap_squareCotangentComplexMap (a : A₁ ⟶ A₂) (hsq : f₁ ≫ 𝟙 D = a ≫ f₂) :
    IsPointStalkBaseMap J Φ a hsq
      (squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a (𝟙 D) hsq)) := by
  intro n m
  obtain ⟨U, x, s, rfl⟩ := exists_pointCotangentGerm_eq J Φ f₁ n m
  have e := sheafModuleFiberOfCommRing_map_squareCotangentComplexMap_germ J Φ f₁ a (𝟙 D) hsq n U x s
  refine (congrArg ((pointStalkCotangentComplexIso J Φ f₂).hom.f n) e).trans ?_
  rw [pointStalkCotangentComplexIso_hom_germ]
  refine (pointStalkCotangentComplexIso_hom_germ J Φ f₂ n U x _).trans ?_
  have k := cotangentComplexAbMap_pointGermSquare_pointStalkSquare J Φ f₁ a (𝟙 D) hsq U x n s
  rw [pointStalkSquare_eq_pointBaseSquare, CommAlgCat.cotangentComplexAbMap_f_apply] at k
  exact k.symm






attribute [local instance] moduleOfSections in
/-- **Changes of base compose.** -/
theorem IsPointStalkBaseMap.comp {a : A₁ ⟶ A₂} {hsq : f₁ ≫ 𝟙 D = a ≫ f₂} {a' : A₂ ⟶ A₃}
    {hsq' : f₂ ≫ 𝟙 D = a' ≫ f₃} {φ : cotangentComplex J f₁ ⟶ cotangentComplex J f₂}
    {φ' : cotangentComplex J f₂ ⟶ cotangentComplex J f₃}
    (h : IsPointStalkBaseMap J Φ a hsq φ) (h' : IsPointStalkBaseMap J Φ a' hsq' φ')
    (hsq'' : f₁ ≫ 𝟙 D = (a ≫ a') ≫ f₃) :
    IsPointStalkBaseMap J Φ (a ≫ a') hsq'' (φ ≫ φ') := by
  intro n m
  refine (congrArg ((pointStalkCotangentComplexIso J Φ f₃).hom.f n)
    (ConcreteCategory.congr_hom
      (Functor.map_comp (Stacks.sheafModuleFiberOfCommRing Φ D) (φ.f n) (φ'.f n)) m)).trans ?_
  rw [ConcreteCategory.comp_apply, h' n, h n, ← CommAlgCat.squareCotangentComplexMap_comp_apply,
    pointBaseSquare_comp J Φ a hsq a' hsq' hsq'']

attribute [local instance] moduleOfSections in
/-- **The identity changes the base along the identity.** -/
theorem isPointStalkBaseMap_id (hsq : f₁ ≫ 𝟙 D = 𝟙 A₁ ≫ f₁) :
    IsPointStalkBaseMap J Φ (𝟙 A₁) hsq (𝟙 (cotangentComplex J f₁)) := by
  intro n m
  rw [squareCotangentComplexMap_pointBaseSquare_id_apply, HomologicalComplex.id_f]
  exact congrArg ((pointStalkCotangentComplexIso J Φ f₁).hom.f n) (ConcreteCategory.congr_hom
    (CategoryTheory.Functor.map_id (Stacks.sheafModuleFiberOfCommRing Φ D)
      ((cotangentComplex J f₁).X n)) m)

/-- A change of base along `a` with a two-sided-inverse pair `(a', φ')` changes the base along `a'`
by `φ'`. -/
private theorem isPointStalkBaseMap_of_comp_eq_id {a : A₁ ⟶ A₂} {a' : A₂ ⟶ A₁}
    {hsq : f₁ ≫ 𝟙 D = a ≫ f₂} {hsq' : f₂ ≫ 𝟙 D = a' ≫ f₁}
    {φ : cotangentComplex J f₁ ⟶ cotangentComplex J f₂}
    {φ' : cotangentComplex J f₂ ⟶ cotangentComplex J f₁}
    (ha : a ≫ a' = 𝟙 A₁) (hφ : φ' ≫ φ = 𝟙 _) (h : IsPointStalkBaseMap J Φ a hsq φ) :
    IsPointStalkBaseMap J Φ a' hsq' φ' := by
  intro n m
  have e : (pointBaseSquare J Φ a hsq).comp (pointBaseSquare J Φ a' hsq') =
      CommAlgCat.AlgebraSquare.id _ (pointStalkAlgebra J Φ f₁) := by
    rw [pointBaseSquare_comp J Φ a hsq a' hsq' (by rw [ha, Category.id_comp, Category.comp_id]),
      ← pointBaseSquare_id J Φ (f₁ := f₁) ((Category.comp_id _).trans (Category.id_comp _).symm)]
    congr 1
  have key := CommAlgCat.squareCotangentComplexMap_comp_apply.{max u v w}
    (pointBaseSquare J Φ a hsq) (pointBaseSquare J Φ a' hsq') n
    ((pointStalkCotangentComplexIso J Φ f₁).hom.f n
      ((Stacks.sheafModuleFiberOfCommRing Φ D).map (φ'.f n) m))
  have hm : (Stacks.sheafModuleFiberOfCommRing Φ D).map (φ.f n)
      ((Stacks.sheafModuleFiberOfCommRing Φ D).map (φ'.f n) m) = m := by
    have := ConcreteCategory.congr_hom (Functor.map_comp (Stacks.sheafModuleFiberOfCommRing Φ D)
      (φ'.f n) (φ.f n)) m
    have hf : φ'.f n ≫ φ.f n = 𝟙 _ := by rw [← HomologicalComplex.comp_f, hφ]; rfl
    erw [hf, Functor.map_id] at this
    exact this.symm
  rw [e, ← h n, hm] at key
  exact (CommAlgCat.squareCotangentComplexMap_algebraSquareId_apply _ n _).symm.trans key

attribute [local instance] moduleOfSections in
/-- **The inverse of a change of base along an isomorphism changes the base along the inverse.** -/
theorem IsPointStalkBaseMap.inverse {a : A₁ ⟶ A₂} [IsIso a] {hsq : f₁ ≫ 𝟙 D = a ≫ f₂}
    {φ : cotangentComplex J f₁ ⟶ cotangentComplex J f₂} [IsIso φ]
    (h : IsPointStalkBaseMap J Φ a hsq φ) (hsq' : f₂ ≫ 𝟙 D = CategoryTheory.inv a ≫ f₁) :
    IsPointStalkBaseMap J Φ (CategoryTheory.inv a) hsq' (CategoryTheory.inv φ) :=
  isPointStalkBaseMap_of_comp_eq_id J Φ (IsIso.hom_inv_id a) (IsIso.inv_hom_id φ) h

/-- The isomorphism of cotangent complexes of an isomorphism of base rings `a`, followed by the
identification of restriction of scalars along the identity with the identity, is the map of
cotangent complexes of the square `(a, 𝟙 D)`. -/
theorem squareCotangentComplexIso_trans_restrictScalarsIdComplexIso_hom (a : A₁ ⟶ A₂) [IsIso a]
    (hsq : f₁ ≫ 𝟙 D = a ≫ f₂) :
    (squareCotangentComplexIso.{u, v, w} (J := J) (a := a) (b := 𝟙 D) hsq ≪≫
        SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _).hom =
      squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a (𝟙 D) hsq) := by
  refine HomologicalComplex.hom_ext _ _ fun n =>
    SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext x
  exact SheafOfModules.restrictScalarsIdIso_hom_val_app_apply
    ((sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map (𝟙 D))
    (CategoryTheory.Functor.map_id _ _) ((cotangentComplex J f₂).X n) U
    (((squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a (𝟙 D) hsq)).f n).val.app U x)

/-- **A change of base along an isomorphism `a`**: the isomorphism of cotangent complexes of the
square `(a, 𝟙 D)` read in `L_{D/A₂}`. -/
theorem isPointStalkBaseMap_squareCotangentComplexIso (a : A₁ ⟶ A₂) [IsIso a]
    (hsq : f₁ ≫ 𝟙 D = a ≫ f₂) :
    IsPointStalkBaseMap J Φ a hsq
      (squareCotangentComplexIso.{u, v, w} (J := J) (a := a) (b := 𝟙 D) hsq ≪≫
        SheafOfModules.restrictScalarsIdComplexIso _
          (CategoryTheory.Functor.map_id _ _) _).hom := by
  rw [squareCotangentComplexIso_trans_restrictScalarsIdComplexIso_hom]
  exact isPointStalkBaseMap_squareCotangentComplexMap J Φ a hsq

attribute [local instance] moduleOfSections in
/-- **The inverse of a change of base along an isomorphism of base rings changes the base along
the inverse isomorphism.** -/
theorem IsPointStalkBaseMap.iso_inv {e : A₁ ≅ A₂} {hsq : f₁ ≫ 𝟙 D = e.hom ≫ f₂}
    {Y : cotangentComplex J f₁ ≅ cotangentComplex J f₂}
    (h : IsPointStalkBaseMap J Φ e.hom hsq Y.hom) (hsq' : f₂ ≫ 𝟙 D = e.inv ≫ f₁) :
    IsPointStalkBaseMap J Φ e.inv hsq' Y.inv :=
  isPointStalkBaseMap_of_comp_eq_id J Φ e.hom_inv_id Y.inv_hom_id h

/-- The stalk functor on a composite of maps of complexes, in one degree, elementwise. -/
theorem sheafModuleFiberOfCommRing_map_comp_f_apply
    {K₁ K₂ K₃ : CochainComplex (targetModules J D) ℤ}
    (φ : K₁ ⟶ K₂) (φ' : K₂ ⟶ K₃) (n : ℤ)
    (m : (Stacks.sheafModuleFiberOfCommRing Φ D).obj (K₁.X n)) :
    (Stacks.sheafModuleFiberOfCommRing Φ D).map ((φ ≫ φ').f n) m =
      (Stacks.sheafModuleFiberOfCommRing Φ D).map (φ'.f n)
        ((Stacks.sheafModuleFiberOfCommRing Φ D).map (φ.f n) m) :=
  ConcreteCategory.congr_hom (Functor.map_comp (Stacks.sheafModuleFiberOfCommRing Φ D)
    (φ.f n) (φ'.f n)) m

/-- Changes of base compose, with the composite square proof supplied. -/
theorem IsPointStalkBaseMap.comp' {a : A₁ ⟶ A₂} {hsq : f₁ ≫ 𝟙 D = a ≫ f₂} {a' : A₂ ⟶ A₃}
    {hsq' : f₂ ≫ 𝟙 D = a' ≫ f₃} {φ : cotangentComplex J f₁ ⟶ cotangentComplex J f₂}
    {φ' : cotangentComplex J f₂ ⟶ cotangentComplex J f₃}
    (h : IsPointStalkBaseMap J Φ a hsq φ) (h' : IsPointStalkBaseMap J Φ a' hsq' φ') :
    IsPointStalkBaseMap J Φ (a ≫ a')
      (by rw [hsq, Category.assoc, ← hsq', Category.comp_id])
      (φ ≫ φ') :=
  h.comp J Φ h' _

/-- A change of base along `a` is a change of base along any `a'` equal to it. -/
theorem IsPointStalkBaseMap.congr_base {a a' : A₁ ⟶ A₂} (e : a = a') {hsq : f₁ ≫ 𝟙 D = a ≫ f₂}
    {φ : cotangentComplex J f₁ ⟶ cotangentComplex J f₂} (h : IsPointStalkBaseMap J Φ a hsq φ)
    (hsq' : f₁ ≫ 𝟙 D = a' ≫ f₂) : IsPointStalkBaseMap J Φ a' hsq' φ := by
  subst e
  exact h

/-- `CategoryTheory.Sheaf.isPointStalkBaseMap_squareCotangentComplexIso` for the forward map of
an isomorphism of base rings. -/
theorem isPointStalkBaseMap_squareCotangentComplexIso_hom (e : A₁ ≅ A₂)
    (hsq : f₁ ≫ 𝟙 D = e.hom ≫ f₂) :
    IsPointStalkBaseMap J Φ e.hom hsq
      (squareCotangentComplexIso.{u, v, w} (J := J) (a := e.hom) (b := 𝟙 D) hsq ≪≫
        SheafOfModules.restrictScalarsIdComplexIso _ (CategoryTheory.Functor.map_id _ _) _).hom :=
  isPointStalkBaseMap_squareCotangentComplexIso J Φ e.hom hsq

section Tower

variable {A B : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

attribute [local instance] moduleOfSections in
/-- **The stalk of the first arrow of Tag 08SZ followed by a change of base.** If
`Θ : L_{D/A} ⟶ L_{D/A₂}` changes the base along `a : A ⟶ A₂` at `Φ`, then through the interchange
`(L_{B/A} ⊗_B D)_Φ ≅ D_Φ ⊗_{B_Φ} (L_{B/A})_Φ` and the identifications of Tag 08T0 the stalk of
`L_{B/A} ⊗_B D ⟶ L_{D/A} ⟶ L_{D/A₂}` is the first displayed morphism of the fundamental triangle
of the stalk rings `A_Φ → B_Φ → D_Φ`, followed by the change of base of the stalk rings;
elementwise in every degree. -/
theorem stalk_towerCotangentBaseChange_comp_apply (a : A ⟶ A₂)
    (hsq : (g ≫ h) ≫ 𝟙 D = a ≫ f₂) (Θ : cotangentComplex J (g ≫ h) ⟶ cotangentComplex J f₂)
    (hΘ : IsPointStalkBaseMap J Φ a hsq Θ) (n : ℤ)
    (y : (((ModuleCat.extendScalars
          (Stacks.SitePointBaseChange.stalkRingHom h.hom Φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((Stacks.sheafModuleFiberOfCommRing Φ B).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex J g))).X n) :
    letI : Algebra ((Φ.presheafFiber (A := CommRingCat)).obj A.obj)
        (pointStalkAlgebra J Φ (g ≫ h)) := CommAlgCat.algebra _
    (pointStalkCotangentComplexIso J Φ f₂).hom.f n
        ((Stacks.sheafModuleFiberOfCommRing Φ D).map
          ((towerCotangentBaseChange.{u, v, w} J g h ≫ Θ).f n)
          ((stalkBaseChangedCotangentComplexIso Φ g h).inv.f n y)) =
      (CommAlgCat.squareCotangentComplexMap (pointBaseSquare J Φ a hsq)).f n
        ((CommAlgCat.cotangentExtendScalarsComplexMap
          (A := (Φ.presheafFiber (A := CommRingCat)).obj A.obj)
          (A' := (Φ.presheafFiber (A := CommRingCat)).obj A.obj) (B := pointStalkAlgebra J Φ g)
          (B' := pointStalkAlgebra J Φ (g ≫ h)) (pointStalkAlgHom J g h Φ).hom).f n
          ((((ModuleCat.extendScalars
              (Stacks.SitePointBaseChange.stalkRingHom h.hom Φ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (pointStalkCotangentComplexIso J Φ g).hom).f n y)) := by
  have key := stalk_towerCotangentBaseChange J g h Φ
  have ky := ConcreteCategory.congr_hom (congrArg (fun k => HomologicalComplex.Hom.f k n) key) y
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at ky
  refine (congrArg ((pointStalkCotangentComplexIso J Φ f₂).hom.f n)
    (ConcreteCategory.congr_hom (Functor.map_comp (Stacks.sheafModuleFiberOfCommRing Φ D)
      ((towerCotangentBaseChange.{u, v, w} J g h).f n) (Θ.f n)) _)).trans ?_
  rw [ConcreteCategory.comp_apply, hΘ n]
  exact congrArg _ ky

end Tower

end CategoryTheory.Sheaf

end
