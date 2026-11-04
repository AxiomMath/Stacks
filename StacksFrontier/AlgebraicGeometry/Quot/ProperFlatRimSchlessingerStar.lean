module

public import StacksFrontier.AlgebraicGeometry.Quot.FlatLfpPushoutGluing
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFibreSections
public import StacksFrontier.Deformation.Artin.RimSchlessinger.RestrictionData
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.PrestackBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecSchemeThickening

/-!
# (RS\*) for the stack of proper flat families from Stacks 0D1J

Stacks 0D1J says that finitely presented, flat and proper algebraic spaces glue across a pushout
of schemes along a thickening and an affine morphism, restriction being an equivalence onto the
compatible pairs; in this library its statement is `AlgebraicGeometry.Space.ProperPushoutRS`,
phrased with the categories `AlgebraicGeometry.Space.FpFlatProperOver` of all morphisms over the
algebraic space of a base scheme and with base-change functors of its own. Condition (RS\*) of
Stacks 07Y8, `Deformation.Artin.SatisfiesRSStar`, is stated for the fibred category
`AlgebraicGeometry.cartesianProperFlatProjection`, whose fibres have only the isomorphisms of
families as morphisms and whose comparison is built from a choice of pullbacks. The first implies
the second, as in the proof of Stacks 0D3X.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.toOver` and `AlgebraicGeometry.ProperFlatFibre.ofOver`: the
  passage between the fibre of the stack over `U` and `FpFlatProperOver U`; the fibre is the
  groupoid of isomorphisms of the latter (`AlgebraicGeometry.ProperFlatFibre.liftIso`).
* `AlgebraicGeometry.ProperFlatFibre.toFiberBaseChange`: a base-change functor of
  `FpFlatProperOver` with its cartesian comparison, as a base-change functor between fibres.
* `AlgebraicGeometry.ProperFlatFibre.restriction`: the restriction functor of Stacks 0D1J, on
  the fibres of the stack; it is an equivalence.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isEquivalence_fiberSquareComparison`: the canonical
  comparison of a square of fibres is an equivalence given the data of Stacks 0D1J for it.
* `AlgebraicGeometry.isThickening_of_appTop_surjective`: a morphism of affine schemes surjective on
  global sections with square-zero kernel is a thickening.
* `AlgebraicGeometry.satisfiesRSStar_cartesianProperFlat`: (RS\*) for `Spaces'_{fp, flat, proper}`
  from the statement of Stacks 0D1J.

## Implementation notes

An object of `FpFlatProperOver U` is an object of the fibre over `U` on the nose
(`AlgebraicGeometry.ProperFlatFibre.ofOver`), and the image of `ofOver Z` is `Z` definitionally,
so every functor of Stacks 0D1J is carried to the fibres by conjugation without comparison
isomorphisms. The comparison with the canonical (RS\*) functor is
`Deformation.Artin.isEquivalence_fiberSquareComparison_of_restriction`.

## References

* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Deformation.Artin

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure morphism of an object of the fibre over `U`, transported to `U` along the
fibre condition. -/
def strT {U : BigFppfOver B S hS} (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    space x ⟶ yoneda.obj U :=
  Eq.rec (motive := fun V _ => space x ⟶ yoneda.obj V) ((comma B S hS).obj x.val).hom x.property

/-- `AlgebraicGeometry.ProperFlatFibre.strT` is `AlgebraicGeometry.ProperFlatFibre.str`. -/
theorem strT_eq {U : BigFppfOver B S hS} (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    strT x = str x := by
  obtain ⟨x, rfl⟩ := x
  change _ = _ ≫ _
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- An object of the fibre over `U` as a finitely presented, flat and proper algebraic space
over the algebraic space of `U`. -/
def toOverObj {U : BigFppfOver B S hS} (x : (cartesianProperFlatProjection B S hS).Fiber U) :
    Space.FpFlatProperOver B S hS U :=
  ⟨Over.mk (ObjectProperty.homMk (strT x) : ((comma B S hS).obj x.val).left ⟶ schemeSpace U), by
    obtain ⟨x, rfl⟩ := x
    exact x.obj.property⟩

/-- A finitely presented, flat and proper algebraic space over the algebraic space of `U`, as an
object of the fibre over `U`. -/
def ofOver {U : BigFppfOver B S hS} (Z : Space.FpFlatProperOver B S hS U) :
    (cartesianProperFlatProjection B S hS).Fiber U :=
  ⟨⟨⟨⟨Z.obj.left, U, Z.obj.hom.hom⟩, Z.property⟩⟩, rfl⟩

/-- The fibres of the stack are groupoids. -/
theorem fiber_isIso {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U} (φ : x ⟶ y) : IsIso φ := by
  have : IsIso φ.val :=
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isIso_of_isHomLift_id
      φ.val φ.property
  have : (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 U) φ.val := φ.property
  exact ⟨⟨⟨inv φ.val, inferInstance⟩, Fiber.hom_ext (IsIso.hom_inv_id φ.val),
    Fiber.hom_ext (IsIso.inv_hom_id φ.val)⟩⟩

/-- A morphism of the fibre over `U` as a morphism of algebraic spaces over the algebraic space
of `U`. -/
def toOver (U : BigFppfOver B S hS) :
    (cartesianProperFlatProjection B S hS).Fiber U ⥤ Space.FpFlatProperOver B S hS U where
  obj := toOverObj
  map {x y} φ := ObjectProperty.homMk (Over.homMk ((comma B S hS).map φ.val).left (by
    apply ObjectProperty.hom_ext
    change map φ.val ≫ strT y = strT x
    rw [strT_eq, strT_eq]
    have : (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 U) φ.val := φ.property
    have h := map_str φ.val (𝟙 U)
    rwa [CategoryTheory.Functor.map_id, Category.comp_id] at h))
  map_id x := rfl
  map_comp φ ψ := rfl

/-- A morphism of the stack of proper flat families is determined by its morphism of algebraic
spaces and its morphism of base schemes. -/
theorem total_hom_ext {X Y : CartesianProperFlatSpaces B S hS} {a b : X ⟶ Y}
    (h₁ : ((comma B S hS).map a).left = ((comma B S hS).map b).left)
    (h₂ : (cartesianProperFlatProjection B S hS).map a =
      (cartesianProperFlatProjection B S hS).map b) : a = b :=
  (comma B S hS).map_injective (Comma.hom_ext _ _ h₁ h₂)

/-- Two mutually inverse `eqToHom`s compose to the identity. -/
private theorem eqToHom_comp_eqToHom_self {C : Type*} [Category C] {X Y : C} (h : X = Y)
    (h' : Y = X) :
    eqToHom h ≫ eqToHom h' = 𝟙 X := by
  subst h
  simp

/-- Reassociating `eqToHom`s after a morphism. -/
private theorem comp_eqToHom_aux {C : Type*} [Category C] {U V X Y : C} (e : U ⟶ V) (hx : X = V)
    (hy : Y = V) :
    e ≫ eqToHom hy.symm = (e ≫ eqToHom hx.symm) ≫ eqToHom hx ≫ eqToHom hy.symm := by
  subst hx hy
  simp

/-- A morphism of a fibre lies over the identity. -/
theorem map_fiber_val {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U} (φ : x ⟶ y) :
    (cartesianProperFlatProjection B S hS).map φ.val =
      eqToHom x.property ≫ eqToHom y.property.symm := by
  have : (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 U) φ.val := φ.property
  rw [IsHomLift.fac' (cartesianProperFlatProjection B S hS) (𝟙 U) φ.val, Category.id_comp]

/-- `AlgebraicGeometry.ProperFlatFibre.toOver` is faithful. -/
theorem toOver_map_injective {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U} {φ ψ : x ⟶ y}
    (h : (toOver U).map φ = (toOver U).map ψ) : φ = ψ :=
  map_injective (congrArg (fun k => k.hom.left.hom) h)

/-- An isomorphism of algebraic spaces over the algebraic space of `U` between the images of two
objects of the fibre over `U` is the image of an isomorphism of the fibre. -/
def liftIso {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U}
    (n : (toOver U).obj x ≅ (toOver U).obj y) : x ≅ y :=
  isoOfUnderlying x y
    ((ObjectProperty.ι _).mapIso ((Over.forget _).mapIso ((ObjectProperty.ι _).mapIso n)))
    (by
      rw [← strT_eq, ← strT_eq]
      exact congrArg (fun k => k.hom) (Over.w n.hom.hom))

/-- The image of `AlgebraicGeometry.ProperFlatFibre.liftIso n` is `n`. -/
@[simp]
theorem toOver_map_liftIso_hom {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U}
    (n : (toOver U).obj x ≅ (toOver U).obj y) : (toOver U).map (liftIso n).hom = n.hom := rfl

/-- The comparison of an object of the fibre with the object rebuilt from its image over the
algebraic space of `U`; its underlying morphism of algebraic spaces is the identity. -/
def ofOverToOverIso {U : BigFppfOver B S hS}
    (x : (cartesianProperFlatProjection B S hS).Fiber U) : ofOver ((toOver U).obj x) ≅ x :=
  liftIso (Iso.refl _)

/-- The image of a morphism of the fibre is an isomorphism. -/
theorem isIso_toOver_map {U : BigFppfOver B S hS}
    {x y : (cartesianProperFlatProjection B S hS).Fiber U}
    (φ : x ⟶ y) : IsIso ((toOver U).map φ) :=
  have := fiber_isIso φ
  inferInstance

/-- The image of a morphism of the fibre is an isomorphism. -/
instance {U : BigFppfOver B S hS} {x y : (cartesianProperFlatProjection B S hS).Fiber U}
    (φ : x ⟶ y) : IsIso ((toOver U).map φ) :=
  isIso_toOver_map φ

variable {U V : BigFppfOver B S hS} {e : U ⟶ V}

/-- The base-change functor between fibres attached to a base-change functor of finitely
presented, flat and proper algebraic spaces. -/
def baseChangeFunctor (F : Space.ProperPushoutBaseChange B S hS e) :
    (cartesianProperFlatProjection B S hS).Fiber V ⥤
      (cartesianProperFlatProjection B S hS).Fiber U where
  obj x := ofOver (F.functor.obj ((toOver V).obj x))
  map φ := (liftIso (x := ofOver _) (y := ofOver _)
    (F.functor.mapIso (asIso ((toOver V).map φ)))).hom
  map_id x := toOver_map_injective (by
    change F.functor.map ((toOver V).map (𝟙 x)) = 𝟙 (F.functor.obj ((toOver V).obj x))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
  map_comp φ ψ := toOver_map_injective (by
    change F.functor.map ((toOver V).map (φ ≫ ψ)) =
      F.functor.map ((toOver V).map φ) ≫ F.functor.map ((toOver V).map ψ)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp])

/-- The square of structure morphisms of the comparison of a base-change functor commutes. -/
theorem baseChange_w (F : Space.ProperPushoutBaseChange B S hS e)
    (x : (cartesianProperFlatProjection B S hS).Fiber V) :
    (F.comparison.app ((toOver V).obj x)).hom ≫ ((comma B S hS).obj x.val).hom =
      (F.functor.obj ((toOver V).obj x)).obj.hom.hom ≫
        yoneda.map (e ≫ eqToHom x.property.symm) := by
  obtain ⟨x, rfl⟩ := x
  rw [eqToHom_refl, Category.comp_id]
  exact congrArg (fun k => k.hom) (F.cartesian ((toOver _).obj ⟨x, rfl⟩)).w

/-- The square of structure morphisms of the comparison of a base-change functor is cartesian. -/
theorem baseChange_isPullback (F : Space.ProperPushoutBaseChange B S hS e)
    (x : (cartesianProperFlatProjection B S hS).Fiber V) :
    IsPullback (F.functor.obj ((toOver V).obj x)).obj.hom.hom
      (F.comparison.app ((toOver V).obj x)).hom
      (yoneda.map (e ≫ eqToHom x.property.symm)) ((comma B S hS).obj x.val).hom := by
  obtain ⟨x, rfl⟩ := x
  rw [eqToHom_refl, Category.comp_id]
  exact (AlgebraicSpaces.isPullback_hom B S hS (F.cartesian ((toOver _).obj ⟨x, rfl⟩))).flip

/-- The comparison morphism of `AlgebraicGeometry.ProperFlatFibre.baseChangeFunctor`, a
morphism of the stack lying over `e`. -/
def baseChangeComparison (F : Space.ProperPushoutBaseChange B S hS e)
    (x : (cartesianProperFlatProjection B S hS).Fiber V) :
    ((baseChangeFunctor F).obj x).val ⟶ x.val :=
  ⟨ObjectProperty.homMk
    { left := F.comparison.app ((toOver V).obj x)
      right := e ≫ eqToHom x.property.symm
      w := baseChange_w F x },
    AlgebraicGeometry.isStronglyCartesian_of_isPullback B S hS _ (baseChange_isPullback F x)⟩

/-- A base-change functor of finitely presented, flat and proper algebraic spaces, as a
base-change functor between the fibres of the stack. -/
def toFiberBaseChange (F : Space.ProperPushoutBaseChange B S hS e) :
    FiberBaseChange (cartesianProperFlatProjection B S hS) e where
  functor := baseChangeFunctor F
  comparison :=
    { app x := baseChangeComparison F x
      naturality x y φ := by
        apply total_hom_ext
        · exact F.comparison.naturality ((toOver V).map φ)
        · change (cartesianProperFlatProjection B S hS).map ((baseChangeFunctor F).map φ).val ≫
              (e ≫ eqToHom y.property.symm) =
            (e ≫ eqToHom x.property.symm) ≫ (cartesianProperFlatProjection B S hS).map φ.val
          have h1 : (cartesianProperFlatProjection B S hS).map
              ((baseChangeFunctor F).map φ).val = 𝟙 U := by
            rw [map_fiber_val]
            exact eqToHom_comp_eqToHom_self _ _
          rw [h1, map_fiber_val φ]
          exact (Category.id_comp _).trans (comp_eqToHom_aux e x.property y.property) }
  comparison_isHomLift x := by
    apply IsHomLift.of_fac' _ _ _ rfl x.property
    change e ≫ eqToHom x.property.symm = eqToHom rfl ≫ e ≫ eqToHom x.property.symm
    rw [eqToHom_refl, Category.id_comp]

/-- The image of a morphism under the fibre base-change functor. -/
@[simp]
theorem toOver_map_baseChangeFunctor_map (F : Space.ProperPushoutBaseChange B S hS e)
    {x y : (cartesianProperFlatProjection B S hS).Fiber V} (φ : x ⟶ y) :
    (toOver U).map ((baseChangeFunctor F).map φ) = F.functor.map ((toOver V).map φ) := rfl

/-- Two morphisms of the stack lying over the same morphism of base schemes have the same image
in the base. -/
theorem map_eq_of_isHomLift {X Y : CartesianProperFlatSpaces B S hS} {R R' : BigFppfOver B S hS}
    (k : R ⟶ R') {a b : X ⟶ Y} (ha : (cartesianProperFlatProjection B S hS).IsHomLift k a)
    (hb : (cartesianProperFlatProjection B S hS).IsHomLift k b) :
    (cartesianProperFlatProjection B S hS).map a =
      (cartesianProperFlatProjection B S hS).map b := by
  rw [IsHomLift.fac' (cartesianProperFlatProjection B S hS) k a,
    IsHomLift.fac' (cartesianProperFlatProjection B S hS) k b]

end AlgebraicGeometry.ProperFlatFibre

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {T T' Y Y' : BigFppfOver B S hS} {i : T ⟶ T'} {f : T ⟶ Y} {g : T' ⟶ Y'} {h : Y ⟶ Y'}
  (D : Space.ProperPushoutEquivalenceData B S hS i f g h)

/-- The identification of the two base changes to the overlap, on the fibres of the stack. -/
def overlapIso :
    baseChangeFunctor D.fromPushoutToS ⋙ baseChangeFunctor D.toOverlapFromS ≅
      baseChangeFunctor D.fromPushoutToT' ⋙ baseChangeFunctor D.toOverlapFromT' :=
  NatIso.ofComponents
    (fun s => liftIso (x := ofOver _) (y := ofOver _) (D.overlapComparison.app ((toOver Y').obj s)))
    (fun φ => toOver_map_injective (D.overlapComparison.hom.naturality ((toOver Y').map φ)))

/-- The image of the overlap identification is that of Stacks 0D1J's data. -/
@[simp]
theorem toOver_map_overlapIso_hom_app (s : (cartesianProperFlatProjection B S hS).Fiber Y') :
    (toOver T).map ((overlapIso D).hom.app s) =
      D.overlapComparison.hom.app ((toOver Y').obj s) := rfl

/-- The overlap identification is compatible with the cartesian comparisons. -/
theorem overlapIso_canonical (w : f ≫ h = i ≫ g)
    (s : (cartesianProperFlatProjection B S hS).Fiber Y') :
    Fiber.fiberInclusion.map ((overlapIso D).hom.app s) ≫
        (toFiberBaseChange D.toOverlapFromT').comparison.app
          ((toFiberBaseChange D.fromPushoutToT').functor.obj s) ≫
        (toFiberBaseChange D.fromPushoutToT').comparison.app s =
      (toFiberBaseChange D.toOverlapFromS).comparison.app
          ((toFiberBaseChange D.fromPushoutToS).functor.obj s) ≫
        (toFiberBaseChange D.fromPushoutToS).comparison.app s := by
  apply total_hom_ext
  · exact D.overlapComparison_canonical ((toOver Y').obj s)
  · have hθ : (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 T)
        (Fiber.fiberInclusion.map ((overlapIso D).hom.app s)) := ((overlapIso D).hom.app s).property
    have h1 := (toFiberBaseChange D.toOverlapFromT').comparison_isHomLift
      ((toFiberBaseChange D.fromPushoutToT').functor.obj s)
    have h2 := (toFiberBaseChange D.fromPushoutToT').comparison_isHomLift s
    have h3 := (toFiberBaseChange D.toOverlapFromS).comparison_isHomLift
      ((toFiberBaseChange D.fromPushoutToS).functor.obj s)
    have h4 := (toFiberBaseChange D.fromPushoutToS).comparison_isHomLift s
    have hl : (cartesianProperFlatProjection B S hS).IsHomLift (𝟙 T ≫ i ≫ g)
        (Fiber.fiberInclusion.map ((overlapIso D).hom.app s) ≫
          (toFiberBaseChange D.toOverlapFromT').comparison.app
            ((toFiberBaseChange D.fromPushoutToT').functor.obj s) ≫
          (toFiberBaseChange D.fromPushoutToT').comparison.app s) :=
      @IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ (𝟙 T) (i ≫ g) _ _ hθ
        (@IsHomLift.comp _ _ _ _ _ _ _ _ _ _ _ i g _ _ h1 h2)
    have hr : (cartesianProperFlatProjection B S hS).IsHomLift (f ≫ h)
        ((toFiberBaseChange D.toOverlapFromS).comparison.app
          ((toFiberBaseChange D.fromPushoutToS).functor.obj s) ≫
        (toFiberBaseChange D.fromPushoutToS).comparison.app s) := inferInstance
    rw [Category.id_comp, ← w] at hl
    exact map_eq_of_isHomLift _ hl hr

/-- The restriction functor of Stacks 0D1J, on the fibres of the stack. -/
def restriction :
    (cartesianProperFlatProjection B S hS).Fiber Y' ⥤
      CategoricalPullback (baseChangeFunctor D.toOverlapFromS)
        (baseChangeFunctor D.toOverlapFromT') where
  obj s :=
    ⟨ofOver (D.restrictionFunctor.obj ((toOver Y').obj s)).fst,
      ofOver (D.restrictionFunctor.obj ((toOver Y').obj s)).snd,
      liftIso (x := ofOver _) (y := ofOver _) (D.restrictionFunctor.obj ((toOver Y').obj s)).iso⟩
  map {s t} φ :=
    ⟨(liftIso (x := ofOver _) (y := ofOver _) ((CategoricalPullback.π₁ _ _).mapIso
        (D.restrictionFunctor.mapIso (asIso ((toOver Y').map φ))))).hom,
      (liftIso (x := ofOver _) (y := ofOver _) ((CategoricalPullback.π₂ _ _).mapIso
        (D.restrictionFunctor.mapIso (asIso ((toOver Y').map φ))))).hom,
      toOver_map_injective (D.restrictionFunctor.map ((toOver Y').map φ)).w⟩
  map_id s := CategoricalPullback.hom_ext
    (toOver_map_injective (by
      change (D.restrictionFunctor.map ((toOver Y').map (𝟙 s))).fst = 𝟙 _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl))
    (toOver_map_injective (by
      change (D.restrictionFunctor.map ((toOver Y').map (𝟙 s))).snd = 𝟙 _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl))
  map_comp φ ψ := CategoricalPullback.hom_ext
    (toOver_map_injective (by
      change (D.restrictionFunctor.map ((toOver Y').map (φ ≫ ψ))).fst =
        (D.restrictionFunctor.map ((toOver Y').map φ)).fst ≫
          (D.restrictionFunctor.map ((toOver Y').map ψ)).fst
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl))
    (toOver_map_injective (by
      change (D.restrictionFunctor.map ((toOver Y').map (φ ≫ ψ))).snd =
        (D.restrictionFunctor.map ((toOver Y').map φ)).snd ≫
          (D.restrictionFunctor.map ((toOver Y').map ψ)).snd
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl))

/-- The first projection of the restriction functor is the base change to `Y`. -/
def restrictionToS :
    restriction D ⋙ CategoricalPullback.π₁ _ _ ≅ baseChangeFunctor D.fromPushoutToS :=
  NatIso.ofComponents
    (fun s => liftIso (x := ofOver _) (y := ofOver _) (D.restriction_toS.app ((toOver Y').obj s)))
    (fun φ => toOver_map_injective (D.restriction_toS.hom.naturality ((toOver Y').map φ)))

/-- The second projection of the restriction functor is the base change to `T'`. -/
def restrictionToT' :
    restriction D ⋙ CategoricalPullback.π₂ _ _ ≅ baseChangeFunctor D.fromPushoutToT' :=
  NatIso.ofComponents
    (fun s => liftIso (x := ofOver _) (y := ofOver _) (D.restriction_toT'.app ((toOver Y').obj s)))
    (fun φ => toOver_map_injective (D.restriction_toT'.hom.naturality ((toOver Y').map φ)))

/-- The projections of the restriction functor are compatible with the overlap identification. -/
theorem restriction_overlap (s : (cartesianProperFlatProjection B S hS).Fiber Y') :
    (baseChangeFunctor D.toOverlapFromS).map ((restrictionToS D).hom.app s) ≫
        (overlapIso D).hom.app s =
      ((restriction D).obj s).iso.hom ≫
        (baseChangeFunctor D.toOverlapFromT').map ((restrictionToT' D).hom.app s) :=
  toOver_map_injective (D.restriction_overlap ((toOver Y').obj s))

/-- The restriction functor is faithful. -/
theorem restriction_faithful : (restriction D).Faithful := by
  have := D.equivalence
  refine ⟨fun {s t} φ ψ hφψ => toOver_map_injective (D.restrictionFunctor.map_injective ?_)⟩
  exact CategoricalPullback.hom_ext
    (congrArg (fun k : (restriction D).obj s ⟶ (restriction D).obj t =>
      (toOver Y).map k.fst) hφψ)
    (congrArg (fun k : (restriction D).obj s ⟶ (restriction D).obj t =>
      (toOver T').map k.snd) hφψ)

/-- The restriction functor is full. -/
theorem restriction_full : (restriction D).Full := by
  have := D.equivalence
  refine ⟨fun {s t} ψ => ?_⟩
  let M : D.restrictionFunctor.obj ((toOver Y').obj s) ≅
      D.restrictionFunctor.obj ((toOver Y').obj t) :=
    CategoricalPullback.mkIso (@asIso _ _ _ _ ((toOver Y).map ψ.fst) (isIso_toOver_map ψ.fst))
      (@asIso _ _ _ _ ((toOver T').map ψ.snd) (isIso_toOver_map ψ.snd))
      (congrArg (toOver T).map ψ.w)
  let n := D.restrictionFunctor.preimage M.hom
  have hn : D.restrictionFunctor.map n = M.hom := D.restrictionFunctor.map_preimage _
  have : IsIso (D.restrictionFunctor.map n) := by rw [hn]; infer_instance
  have : IsIso n := isIso_of_reflects_iso n D.restrictionFunctor
  exact ⟨(liftIso (asIso n)).hom, CategoricalPullback.hom_ext
    (toOver_map_injective (congrArg (fun k => CategoricalPullback.Hom.fst k) hn))
    (toOver_map_injective (congrArg (fun k => CategoricalPullback.Hom.snd k) hn))⟩

/-- The restriction functor is essentially surjective. -/
theorem restriction_essSurj : (restriction D).EssSurj := by
  have := D.equivalence
  refine ⟨fun y => ?_⟩
  let Q : CategoricalPullback D.toOverlapFromS.functor D.toOverlapFromT'.functor :=
    ⟨(toOver Y).obj y.fst, (toOver T').obj y.snd, (toOver T).mapIso y.iso⟩
  let ε := D.restrictionFunctor.objObjPreimageIso Q
  exact ⟨ofOver (D.restrictionFunctor.objPreimage Q),
    ⟨CategoricalPullback.mkIso (liftIso (x := ofOver _) ((CategoricalPullback.π₁ _ _).mapIso ε))
      (liftIso (x := ofOver _) ((CategoricalPullback.π₂ _ _).mapIso ε))
      (toOver_map_injective ε.hom.w)⟩⟩

/-- The restriction functor is an equivalence. -/
instance : (restriction D).IsEquivalence where
  faithful := restriction_faithful D
  full := restriction_full D
  essSurj := restriction_essSurj D

include D in
/-- **The comparison of the square of fibres is an equivalence, from Stacks 0D1J's data.** Given
the data of Stacks 0D1J for a commutative square of the site, the canonical comparison of the
fibre of the stack over the fourth corner with the two-fibre product of the fibres over the two
middle corners is an equivalence, for any choice of pullbacks. -/
theorem isEquivalence_fiberSquareComparison (w : f ≫ h = i ≫ g)
    (c : (cartesianProperFlatProjection B S hS).ChoiceOfPullbacks) :
    (fiberSquareComparison (cartesianProperFlatProjection B S hS) c f i h g w).IsEquivalence := by
  let R : (cartesianProperFlatProjection B S hS).Fiber Y' ⥤
      CategoricalPullback (toFiberBaseChange D.toOverlapFromS).functor
        (toFiberBaseChange D.toOverlapFromT').functor := restriction D
  have : R.IsEquivalence := inferInstanceAs (restriction D).IsEquivalence
  exact isEquivalence_fiberSquareComparison_of_restriction (cartesianProperFlatProjection B S hS)
    (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) c f i h g w
    (toFiberBaseChange D.toOverlapFromS) (toFiberBaseChange D.toOverlapFromT')
    (toFiberBaseChange D.fromPushoutToS) (toFiberBaseChange D.fromPushoutToT')
    (overlapIso D) (overlapIso_canonical D w) R (restrictionToS D)
    (restrictionToT' D) (restriction_overlap D)


end AlgebraicGeometry.ProperFlatFibre

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of affine schemes surjective on global sections with square-zero kernel is a
thickening. -/
theorem isThickening_of_appTop_surjective {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (g : X ⟶ Y) (hsurj : Function.Surjective g.appTop)
    (hsq : RingHom.ker g.appTop.hom ^ 2 = ⊥) : Stacks.Thickenings.IsThickening g := by
  have hspec : Stacks.Thickenings.IsThickening (Spec.map g.appTop) :=
    Stacks.Thickenings.specMap_isThickening_of_nilKernel g.appTop.hom hsurj fun x hx =>
      ⟨2, by
        have h2 : x ^ 2 ∈ RingHom.ker g.appTop.hom ^ 2 := Ideal.pow_mem_pow hx 2
        rwa [hsq, Ideal.mem_bot] at h2⟩
  have : Surjective (Spec.map g.appTop) := ⟨hspec.2⟩
  have : Surjective g :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine g)).2 this
  exact ⟨IsClosedImmersion.of_surjective_of_isAffine g hsurj, this.surj⟩

/-- **(RS\*) for the stack of finitely presented, flat and proper algebraic spaces, from the
statement of Stacks 0D1J.**  If finitely presented, flat and proper algebraic spaces glue across
every affine thickening pushout of the big fppf site, with restriction as the canonical
equivalence (`AlgebraicGeometry.Space.ProperPushoutRS`), then the stack
`Spaces'_{fp, flat, proper}` satisfies condition (RS\*) of Stacks 07Y8. -/
theorem satisfiesRSStar_cartesianProperFlat (rs : Space.ProperPushoutRS B S hS) :
    SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) := by
  intro U V W Z f g i j h hpb hsurj hsq
  let T := BigAffineFppf.toScheme B S hS
  have hthick : Stacks.Thickenings.IsThickening (T.map g) :=
    isThickening_of_appTop_surjective (T.map g) hsurj hsq
  have hpo : IsPushout (T.map g) (T.map f) (T.map j) (T.map i) :=
    (Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _ hpb hsurj).of_iso'
      (T.obj U).isoSpec (T.obj W).isoSpec (T.obj V).isoSpec (T.obj Z).isoSpec
      (Scheme.isoSpec_hom_naturality _) (Scheme.isoSpec_hom_naturality _)
      (Scheme.isoSpec_hom_naturality _) (Scheme.isoSpec_hom_naturality _)
  let D := rs ((BigAffineFppf.inclusion B S hS).map g) ((BigAffineFppf.inclusion B S hS).map f)
    ((BigAffineFppf.inclusion B S hS).map j) ((BigAffineFppf.inclusion B S hS).map i) hthick
    (isAffineHom_of_isAffine (T.map f)) hpo
  exact ProperFlatFibre.isEquivalence_fiberSquareComparison D _ _

/-- (RS\*) for `Spaces'_{fp, flat, proper}`, given that étale charts lift across thickenings
(`AlgebraicGeometry.Space.HasEtaleChartLifts`). -/
theorem satisfiesRSStar_cartesianProperFlat_of_hasEtaleChartLifts
    (hlift : Space.HasEtaleChartLifts B S hS) :
    SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) :=
  satisfiesRSStar_cartesianProperFlat B S hS (Space.properPushoutRS_of_hasEtaleChartLifts hlift)

end AlgebraicGeometry

end
