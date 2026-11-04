module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSplitThickening
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackArtinAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackIsomEqualizer

/-!
# The 1-morphism from `Coh_{X/Y}` to the algebraic space `Y`

Let `D` be the situation of Stacks 08KB. Forgetting the module of an object `(T, g, ℱ)` of
`Coh_{X/Y}` and keeping the point `g ∈ Y(T)` is a functor from `Coh_{X/Y}` to the category of
elements of `Y`, the category fibred in groupoids `S_Y` of the algebraic space `Y`, over the big
fppf site. It induces, at a finite-type field point, a `1`-morphism of predeformation categories
`𝓕_{Coh_{X/Y}, k, x₀} ⟶ 𝓕_{Y, k, y₀}`, whose tangent map is the map
`T𝓕_{Coh} ⟶ T𝓕_Y` of Stacks 08W8.

This file also records the identification of the global functions on a test scheme whose
underlying scheme is an affine spectrum, and how pullback of functions along a morphism whose
underlying morphism of schemes is a spectrum map acts.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.toBaseElements`: the functor
  `Coh_{X/Y} ⥤ S_Y`.
* `AlgebraicGeometry.Space.CoherentSituation.testRingOfSpec`: the identification
  `A ⟶ Γ(T, 𝒪_T)` for a test scheme whose scheme is `Spec A`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.toBaseElements_comp_p`: the functor is over the
  site.
* `AlgebraicGeometry.Space.CoherentSituation.siteΓ_testRingOfSpec`: pullback of functions along
  a spectrum map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : CoherentSituation B S hS)

attribute [local instance] cohCategory

/-- The morphism of `Coh_{X/Y}` read as a morphism of the structure
`AlgebraicGeometry.Space.CoherentHom`. -/
abbrev homOf {A A' : CoherentObject D} (m : A ⟶ A') : CoherentHom A A' :=
  Equiv.cast (D.categoryData.hom_type A A') m

/-- The point `g ∈ Y(T)` of an object of `Coh_{X/Y}`. -/
abbrev basePoint (A : CoherentObject D) : D.Y.1.obj (op A.T.left) :=
  yonedaEquiv A.T.hom.hom

/-- The point of the source of a morphism is the restriction of the point of the target. -/
theorem basePoint_eq_map {T T' : SchemesOver D.Y} (g : T ⟶ T') :
    yonedaEquiv T.hom.hom = D.Y.1.map g.left.op (yonedaEquiv T'.hom.hom) :=
  ((yonedaEquiv_naturality T'.hom.hom g.left).trans
    (congrArg yonedaEquiv (congrArg (fun f => f.hom) (CostructuredArrow.w g)))).symm

/-- **The functor `Coh_{X/Y} ⥤ S_Y`** forgetting the module. -/
def toBaseElements :
    CoherentObject D ⥤ (Stack.fibredCategory B S hS D.Y.1).val.obj where
  obj A := ⟨A.T.left, Discrete.mk (yonedaEquiv A.T.hom.hom)⟩
  map {A A'} m :=
    { base := (D.homOf m).base.left
      fiber := Discrete.eqToHom (D.basePoint_eq_map (D.homOf m).base) }
  map_id A := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ (by apply Discrete.hom_eq)
    change (D.homOf (𝟙 A)).base.left = 𝟙 _
    rw [homOf, D.categoryData.identity]
    rfl
  map_comp {A A' A''} m n := by
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ (by apply Discrete.hom_eq)
    change (D.homOf (m ≫ n)).base.left = (D.homOf m).base.left ≫ (D.homOf n).base.left
    rw [homOf, D.categoryData.composition]
    rfl

/-- The functor `Coh_{X/Y} ⥤ S_Y` lies over the site. -/
theorem toBaseElements_comp_p :
    D.toBaseElements ⋙ (Stack.fibredCategory B S hS D.Y.1).val.p =
      coherentSiteProjection D.categoryData :=
  rfl

/-! ### Global functions on a test scheme which is a spectrum -/

/-- The maps on global sections induced by `eqToHom e` and `eqToHom e.symm` compose to the
identity. -/
theorem appTop_eqToHom_comp {X Y : Scheme.{u}} (e : X = Y) :
    (eqToHom e).appTop ≫ (eqToHom e.symm).appTop = 𝟙 _ := by
  subst e
  rfl

/-- The identification `A ⟶ Γ(T, 𝒪_T)` for a test scheme whose underlying scheme is `Spec A`. -/
def testRingOfSpec (T : SchemesOver D.Y) {A : CommRingCat.{u}}
    (e : (BigFppfOver.toScheme B S hS).obj T.left = Spec A) : A ⟶ D.testRing T :=
  ((Scheme.ΓSpecIso A).symm ≪≫ Scheme.Γ.mapIso (eqToIso e).op).hom

/-- `testRingOfSpec T e` is the inverse of `Scheme.ΓSpecIso A` followed by the map on global
sections induced by `eqToHom e`. -/
theorem testRingOfSpec_eq (T : SchemesOver D.Y) {A : CommRingCat.{u}}
    (e : (BigFppfOver.toScheme B S hS).obj T.left = Spec A) :
    D.testRingOfSpec T e = (Scheme.ΓSpecIso A).inv ≫ (eqToHom e).appTop := rfl

/-- The map `testRingOfSpec T e : A ⟶ D.testRing T` is bijective. -/
theorem bijective_testRingOfSpec (T : SchemesOver D.Y) {A : CommRingCat.{u}}
    (e : (BigFppfOver.toScheme B S hS).obj T.left = Spec A) :
    Function.Bijective (D.testRingOfSpec T e) :=
  ConcreteCategory.bijective_of_isIso (Iso.hom _ : A ⟶ D.testRing T)

/-- **Pullback of functions along a morphism whose underlying morphism of schemes is the spectrum
of a ring map is that ring map**, read through the identifications of the two rings of global
functions. -/
theorem siteΓ_testRingOfSpec {T₁ T₀ : SchemesOver D.Y} (g : T₁.left ⟶ T₀.left)
    {A₀ A₁ : CommRingCat.{u}} (e₀ : (BigFppfOver.toScheme B S hS).obj T₀.left = Spec A₀)
    (e₁ : (BigFppfOver.toScheme B S hS).obj T₁.left = Spec A₁) (φ : A₀ ⟶ A₁)
    (hg : (BigFppfOver.toScheme B S hS).map g = eqToHom e₁ ≫ Spec.map φ ≫ eqToHom e₀.symm) :
    D.testRingOfSpec T₀ e₀ ≫ siteΓ g = φ ≫ D.testRingOfSpec T₁ e₁ := by
  rw [testRingOfSpec_eq, testRingOfSpec_eq, siteΓ, hg]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  rw [reassoc_of% (appTop_eqToHom_comp e₀), ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc]

end CoherentSituation

end AlgebraicGeometry.Space

end
