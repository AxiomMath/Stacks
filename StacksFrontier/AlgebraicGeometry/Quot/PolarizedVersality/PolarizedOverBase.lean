module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.PolarizedTowerLimit
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesOverSpace

/-!
# The stack `S-𝒫olarized` over the big fppf site of a scheme `S`

Remark 0D1N of the Stacks project considers, for an algebraic space `B`, the category
`B-𝒫olarized` of triples `(X ⟶ T, ℒ, h : T ⟶ B)` with `(X ⟶ T, ℒ)` a polarized family
(Stacks 0D1M), fibred over `(Sch/B)_{fppf}`; this is the category over which Stacks 0D4V asserts
openness of versality "after base change". For `B` the scheme `S` underlying the base of a big fppf
site, the library's `AlgebraicGeometry.PolarizedFamilyOver` (Stacks 0D1N) at the functor of points
of `S` over itself is that category: its objects are polarized families together with a morphism of
their base to `S`, and its morphisms are morphisms of polarized families over `S`.

This file reads it as a category over the big fppf site of `S`, through the structure morphisms,
proves that it is fibred in groupoids, and that its square-zero systems are effective (condition
(4) of Stacks 0CXU, from Stacks 0D4T,
`AlgebraicGeometry.PolarizedVersality.Polarized.exists_cocone_of_squareZeroTower`).

## Main definitions

* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.Family`: the category `S-𝒫olarized`.
* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.projection`: its structure functor to the
  big fppf site of `S`.
* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.stack`: `S-𝒫olarized` as a category fibred in
  groupoids over the big fppf site of `S`.
* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.ofBase`,
  `AlgebraicGeometry.PolarizedVersality.PolarizedOver.homMk`: an object and a morphism of
  `S-𝒫olarized` from a polarized family over an object of the site and from a morphism of
  polarized families over `S`.

## Main results

* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.isFiberedInGroupoids_projection`.
* `AlgebraicGeometry.PolarizedVersality.PolarizedOver.isSquareZeroEffective_projection`.

## References

* [Stacks Project, Tag 0D1N](https://stacks.math.columbia.edu/tag/0D1N)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 0D4V](https://stacks.math.columbia.edu/tag/0D4V)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin

namespace AlgebraicGeometry.PolarizedVersality.PolarizedOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme `S` as an algebraic space over itself: the functor of points of the terminal object
`S/S` of the big fppf site of `S`. -/
abbrev point : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  yoneda.obj (Over.mk (𝟙 (B.obj hS)))

/-- **The category `S-𝒫olarized` of Stacks 0D1N**: polarized families with a morphism of their
base to `S`. -/
abbrev Family : Type (u + 1) :=
  PolarizedFamilyOver B S hS (point B S hS)

/-- The structure functor of `S-𝒫olarized` to the big fppf site of `S`: a family goes to its base
with its morphism to `S`. -/
def projection : Family B S hS ⥤ BigFppfOver B S hS where
  obj x := Over.mk x.toBase
  map f := PolarizedFamilyOver.Hom.over f
  map_id _ := Over.OverMorphism.ext rfl
  map_comp _ _ := Over.OverMorphism.ext rfl

variable {B S hS}

/-- The base of the image of `x` under `projection` is the base of its polarized family. -/
@[simp]
theorem projection_obj_left (x : Family B S hS) :
    ((projection B S hS).obj x).left = x.polarized.base := rfl

/-- The underlying morphism of schemes of the image of `f` under `projection` is the base morphism
of its morphism of polarized families. -/
@[simp]
theorem projection_map_left {x y : Family B S hS} (f : x ⟶ y) :
    ((projection B S hS).map f).left = f.polarizedHom.baseMap := rfl

/-- The point of `S` over a scheme of the site with a morphism to `S`. -/
def pointOf (T : B.Schemes) (s : T ⟶ B.obj hS) : (point B S hS).obj (op (Over.mk s)) :=
  Over.homMk s

/-- Two points of `S` over the same scheme agree: `S/S` is terminal. -/
theorem point_ext {V : BigFppfOver B S hS} (a b : (point B S hS).obj (op V)) : a = b :=
  Over.mkIdTerminal.hom_ext a b

/-- **An object of `S-𝒫olarized` from a polarized family over an object of the site of `S`.** -/
def ofBase (z : PolarizedFamily B) (V : BigFppfOver B S hS) (h : z.base = V.left) :
    Family B S hS where
  polarized := z
  toBase := eqToHom h ≫ V.hom
  point := pointOf z.base (eqToHom h ≫ V.hom)

/-- An object of a slice with structure morphism transported along an equality is the object
itself. -/
theorem over_mk_eqToHom_comp {C : Type*} [Category C] {X A : C} (V : Over X) (h : A = V.left) :
    Over.mk (eqToHom h ≫ V.hom) = V := by
  subst h
  rw [eqToHom_refl, Category.id_comp]
  rfl

/-- The polarized family of `ofBase z V h` is `z`. -/
@[simp]
theorem ofBase_polarized (z : PolarizedFamily B) (V : BigFppfOver B S hS) (h : z.base = V.left) :
    (ofBase z V h).polarized = z := rfl

/-- The object `ofBase z V h` lies over `V`. -/
theorem projection_obj_ofBase (z : PolarizedFamily B) (V : BigFppfOver B S hS)
    (h : z.base = V.left) : (projection B S hS).obj (ofBase z V h) = V :=
  over_mk_eqToHom_comp V h

/-- A morphism over the underlying morphism of a morphism `f` of a slice, up to equalities of
objects, commutes with the structure morphisms. -/
theorem comp_eqToHom_hom_eq {C : Type*} [Category C] {X : C} {V U : Over X} (f : V ⟶ U)
    {A A' : C} (k : A ⟶ A') (hA : A = V.left) (hA' : A' = U.left)
    (hk : k = eqToHom hA ≫ f.left ≫ eqToHom hA'.symm) :
    k ≫ eqToHom hA' ≫ U.hom = eqToHom hA ≫ V.hom := by
  subst hk
  simp

/-- The structure morphism of an object lying over `U` is that of `U`. -/
theorem toBase_eq {x : Family B S hS} {U : BigFppfOver B S hS}
    (hx : (projection B S hS).obj x = U) :
    x.toBase = eqToHom (congrArg Comma.left hx) ≫ U.hom := by
  subst hx
  exact (Category.id_comp _).symm

/-- **A morphism of `S-𝒫olarized` from a morphism of polarized families over `S`.** -/
def homMk {x y : Family B S hS} (φ : x.polarized ⟶ y.polarized)
    (hφ : φ.baseMap ≫ y.toBase = x.toBase) : x ⟶ y where
  polarizedHom := φ
  base_comm := hφ
  point_comm := point_ext _ _

/-- The morphism of polarized families underlying `homMk φ hφ` is `φ`. -/
@[simp]
theorem homMk_polarizedHom {x y : Family B S hS} (φ : x.polarized ⟶ y.polarized)
    (hφ : φ.baseMap ≫ y.toBase = x.toBase) : (homMk φ hφ).polarizedHom = φ := rfl

/-- A morphism of `S-𝒫olarized` lying over a morphism of the site lies, as a morphism of
polarized families, over its underlying morphism of schemes. -/
theorem isHomLift_polarizedProjection {V W : BigFppfOver B S hS} (f : V ⟶ W)
    {x y : Family B S hS} (φ : x ⟶ y) (h : (projection B S hS).IsHomLift f φ) :
    (polarizedProjection B).IsHomLift f.left φ.polarizedHom := by
  have hf := IsHomLift.fac' (projection B S hS) f φ
  have hl := congrArg CommaMorphism.left hf
  simp only [Over.comp_left, Over.eqToHom_left, projection_map_left] at hl
  exact IsHomLift.of_fac' (polarizedProjection B) f.left φ.polarizedHom
    (congrArg Comma.left (IsHomLift.domain_eq (projection B S hS) f φ))
    (congrArg Comma.left (IsHomLift.codomain_eq (projection B S hS) f φ)) hl

/-- A morphism of `S-𝒫olarized` between objects over `V` and `W` lies over a morphism `f` of the
site as soon as its morphism of polarized families lies over the underlying morphism of `f`. -/
theorem isHomLift_projection {V W : BigFppfOver B S hS} (f : V ⟶ W) {x y : Family B S hS}
    (φ : x ⟶ y) (hx : (projection B S hS).obj x = V) (hy : (projection B S hS).obj y = W)
    (h : (polarizedProjection B).IsHomLift f.left φ.polarizedHom) :
    (projection B S hS).IsHomLift f φ := by
  refine IsHomLift.of_fac' _ f φ hx hy ?_
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left, projection_map_left]
  exact IsHomLift.fac' (polarizedProjection B) f.left φ.polarizedHom

/-- A base morphism of polarized families equal to the underlying morphism of a morphism over `S`
is compatible with the structure morphisms. -/
private theorem baseMap_comp_toBase {x y : Family B S hS} (φ : x.polarized ⟶ y.polarized)
    (g : (projection B S hS).obj x ⟶ (projection B S hS).obj y) (h : φ.baseMap = g.left) :
    φ.baseMap ≫ y.toBase = x.toBase := by
  rw [h]
  exact Over.w g

variable (B S hS) in
/-- **`S-𝒫olarized` is fibred in groupoids over the big fppf site of `S`**: lifts are the lifts of
`𝒫olarized` with the composite morphism to `S`, and fill-ins are those of `𝒫olarized`. -/
theorem isFiberedInGroupoids_projection : (projection B S hS).IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    have hp := (polarizedProjection_isFiberedInGroupoids_unconditional (B := B))
    have hxl : (polarizedProjection B).obj x.polarized = U.left := congrArg Comma.left hx
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f.left x.polarized hxl
    have hy : y.base = V.left := IsHomLift.domain_eq (polarizedProjection B) f.left φ
    have hb : φ.baseMap ≫ x.toBase = (ofBase y V hy).toBase := by
      rw [toBase_eq hx]
      exact comp_eqToHom_hom_eq f φ.baseMap hy (congrArg Comma.left hx)
        (IsHomLift.fac' (polarizedProjection B) f.left φ)
    exact ⟨ofBase y V hy, homMk φ hb, isHomLift_projection f _ (projection_obj_ofBase y V hy) hx hφ⟩
  unique_lift {x y z} φ ψ f hcomm := by
    have hp := (polarizedProjection_isFiberedInGroupoids_unconditional (B := B))
    have hcomm' : f.left ≫ (polarizedProjection B).map φ.polarizedHom =
        (polarizedProjection B).map ψ.polarizedHom :=
      congrArg CommaMorphism.left hcomm
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, huniq⟩ := hp.unique_lift φ.polarizedHom ψ.polarizedHom f.left hcomm'
    refine ⟨homMk χ (baseMap_comp_toBase χ f hχ₁),
      ⟨Over.OverMorphism.ext hχ₁, PolarizedFamilyOver.Hom.ext hχ₂⟩, ?_⟩
    rintro χ' ⟨h₁, h₂⟩
    exact PolarizedFamilyOver.Hom.ext
      (huniq χ'.polarizedHom ⟨congrArg CommaMorphism.left h₁,
        congrArg PolarizedFamilyOver.Hom.polarizedHom h₂⟩)

variable (B S hS) in
/-- **`S-𝒫olarized`** as a category fibred in groupoids over the big fppf site of `S`. -/
def stack : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (projection B S hS))
    (isFiberedInGroupoids_projection B S hS)

/-- The structure functor of `S-𝒫olarized` to the big fppf site of `S` is fibred. -/
instance : (projection B S hS).IsFibered := (isFiberedInGroupoids_projection B S hS).isFibered

variable (B S hS) in
/-- **Square-zero systems in `S-𝒫olarized` are effective** (condition (4) of Stacks 0CXU), by
Stacks 0D4T: the limit polarized family lies over the given scheme over `S`. -/
theorem isSquareZeroEffective_projection :
    IsSquareZeroEffective B S hS (projection B S hS) (isFiberedInGroupoids_projection B S hS) := by
  rintro Λ _ _ _ R cR hcR hsurj hsq ξ ⟨⟨T, ⟨⟨⟩⟩, hV⟩, cι⟩ e eLimit he heLimit -
  have := Space.ComplexesSituation.preservesLimitsOfShape_forget₂_commAlgCat Λ
  obtain ⟨x, hx, ι, hι, hιa⟩ := Polarized.exists_cocone_of_squareZeroTower (R ⋙ forget₂ _ _)
    (fun _ => hsurj _) (fun _ => hsq _) ((forget₂ _ _).mapCone cR) (isLimitOfPreserves _ hcR)
    (fun n => (ξ.obj n).polarized) (fun n => (ξ.map (homOfLE (Nat.le_succ n))).polarizedHom) T
    (fun n => (cι.app n).left)
    (fun n => congrArg CommaMorphism.left
      (Cocone.w (⟨_, cι⟩ : Cocone (ξ ⋙ projection B S hS)) (homOfLE (Nat.le_succ n))))
    e eLimit (fun n => he (homOfLE (Nat.le_succ n))) heLimit
  subst hx
  have hι' : ∀ n, (ι n).baseMap = (cι.app n).left := fun n =>
    (Category.comp_id _).symm.trans (hιa n)
  let xS : Family B S hS :=
    { polarized := x
      toBase := hV
      point := pointOf x.base hV }
  have hb := fun n => baseMap_comp_toBase (y := xS) (ι n) (cι.app n) (hι' n)
  refine ⟨⟨xS, NatTrans.ofSequence (fun n => homMk (ι n) (hb n)) fun n =>
    (PolarizedFamilyOver.Hom.ext (hι n) : _ = homMk (ι n) (hb n)).trans
      (Category.comp_id _).symm⟩, ?_⟩
  exact Space.ComplexesSituation.coconeEq_of_pt_eq rfl fun n => Over.OverMorphism.ext
    ((congrArg CommaMorphism.left (Category.comp_id _ : _ ≫ 𝟙 _ = _)).trans (hι' n))

end AlgebraicGeometry.PolarizedVersality.PolarizedOver

end
