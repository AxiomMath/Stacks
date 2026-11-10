module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeStratificationQuotientStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationExistence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coordinates on the weighted multiplicative-group quotient

Let `k` be a commutative ring, `p` a natural number, `U = Spec k[x_0, x_1, …]` with the action
of `𝐆_m` in which `x_i` has weight `p^i`, and `X = [U/𝐆_m]` the quotient stack of
**Stacks 06RE** (`AlgebraicGeometry.PPowerWeighted.quotientStack`).  This file reads the
presenting groupoid `𝐆_m × U ⇉ U` of `X` in coordinates, on the points of `U` with values in an
arbitrary object `W` of the big fppf site over `Spec ℤ`, and describes the strata `X_i`,
`X_∞` of 06RE as subfunctors of `U` together with their coarse spaces.

## Main definitions

* `AlgebraicGeometry.PPowerWeighted.actionGroupoid`: the action groupoid presenting
  `quotientStack`, and `AlgebraicGeometry.PPowerWeighted.actionGroupoidOverBase` the same
  groupoid over `AlgebraicGeometry.Stack.baseSpace`.
* `AlgebraicGeometry.PPowerWeighted.totalSiteObject`: `U` as an object of the site, and
  `AlgebraicGeometry.PPowerWeighted.objectsIso` the identification of the objects of the
  groupoid with the points of `U`.
* `AlgebraicGeometry.PPowerWeighted.coord`: the coordinates of a `W`-point of `U`, and
  `AlgebraicGeometry.PPowerWeighted.scalarMap` the `k`-algebra structure it induces on `Γ(W)`.
* `AlgebraicGeometry.PPowerWeighted.actMap`: the action of a unit of `Γ(W)` on the `W`-points
  of `U`, and `AlgebraicGeometry.PPowerWeighted.arrowsEquiv` the identification of the arrows of
  the groupoid with pairs (unit, point).
* `AlgebraicGeometry.PPowerWeighted.stratumSubfunctor`: the strata `X_a`, `a : WithTop ℕ`, as
  subfunctors of the functor of points of `U`.
* `AlgebraicGeometry.PPowerWeighted.stratumTopSubobject`,
  `AlgebraicGeometry.PPowerWeighted.basicOpenSiteObject`,
  `AlgebraicGeometry.PPowerWeighted.basicOpenι` and
  `AlgebraicGeometry.PPowerWeighted.stratumSubobject`: the strata as subschemes.
* `AlgebraicGeometry.PPowerWeighted.coarseSiteObject`,
  `AlgebraicGeometry.PPowerWeighted.coarseMap` and
  `AlgebraicGeometry.PPowerWeighted.coarseSection`: the coarse spaces of the strata, the coarse
  maps and their sections.

## Main results

* `AlgebraicGeometry.PPowerWeighted.quotientStack_eq`,
  `AlgebraicGeometry.PPowerWeighted.quotientStack_actionGroupoidOverBase` and
  `AlgebraicGeometry.PPowerWeighted.isSmooth_actionGroupoidOverBase`.
* `AlgebraicGeometry.PPowerWeighted.objectsIso_inv_source` and
  `AlgebraicGeometry.PPowerWeighted.objectsIso_inv_target`: the arrow `(γ, h)` goes from `h` to
  `γ • h`, where `coord (γ • h) j = γ ^ p ^ j * coord h j`
  (`AlgebraicGeometry.PPowerWeighted.coord_actMap`).
* `AlgebraicGeometry.PPowerWeighted.actMap_mem_stratumSubfunctor_iff`: the strata are invariant;
  `AlgebraicGeometry.PPowerWeighted.isSheaf_stratumSubfunctor`: they are fppf sheaves.
* `AlgebraicGeometry.PPowerWeighted.subschemePoints_stratumTopSubobject` and
  `AlgebraicGeometry.PPowerWeighted.mem_stratumSubfunctor_coe_iff_exists`: the strata are the
  functors of points of the closed subscheme `X_∞ ⊆ U` and of the closed subschemes
  `X_i ⊆ D(x_i)`, which are reduced over a domain.
* `AlgebraicGeometry.PPowerWeighted.coarseMap_actMapStratum`,
  `AlgebraicGeometry.PPowerWeighted.coarseMap_coarseSection` and
  `AlgebraicGeometry.PPowerWeighted.exists_covering_actMap_eq`: the coarse maps are invariant,
  have sections, and two points with the same image are fppf locally in the same orbit.
* `AlgebraicGeometry.PPowerWeighted.actMap_eq_self_iff_coe` and
  `AlgebraicGeometry.PPowerWeighted.actMap_eq_self_of_top`: the stabilizer along `X_i` is
  `μ_{p^i}` and along `X_∞` it is `𝐆_m`.

## Implementation notes

A morphism `W ⟶ U` of the site over `Spec ℤ` is the same thing as a ring map
`k[x_0, x_1, …] → Γ(W, ⊤)` (`AlgebraicGeometry.PPowerWeighted.siteHomEquiv`): the structure
morphisms to `Spec ℤ` agree automatically, `Spec ℤ` being terminal.  Such a ring map is
determined by the `k`-algebra structure it induces on `Γ(W)` and by the coordinates, so two
points of `U` are equal when both agree (`AlgebraicGeometry.PPowerWeighted.hom_ext_coord`).

The action groupoid is `AlgebraicGeometry.Space.groupoidOfAction`, which records its spaces and
structure maps only up to heterogeneous equalities; these are turned into equalities with
`eqToHom` (`AlgebraicGeometry.PPowerWeighted.actionGroupoid_source_hom`), and the arrows are read
through the Yoneda lemma, so that the target formula reduces to the coaction formula
`AlgebraicGeometry.PPowerWeighted.action_μ_X` on points of schemes
(`AlgebraicGeometry.PPowerWeighted.specRingHom_lift_smul`).

The local transitivity of `exists_covering_actMap_eq` assumes `0 < p`: for `p = 0` the weight of
`x_i` with `i > 0` is `0` and the coarse map of `X_i` forgets `x_i`, so it fails.  The source
takes `p` prime.

## References

* [Stacks Project, Tag 06RE](https://stacks.math.columbia.edu/tag/06RE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PPowerWeighted

attribute [local instance 100] ULift.algebra'

variable (𝒞 : BigFppfSite.{u}) (k : Type u) [CommRing k] (p : ℕ)

/-- The base `Spec ℤ` of the site. -/
local macro "𝒵" : term => `(Spec (CommRingCat.of (ULift ℤ)))

/-- `U = Spec k[x_0, x_1, …]` as an object of the big fppf site over `Spec ℤ`. -/
noncomputable abbrev totalSiteObject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hU
    (Spec (.of (MvPolynomial ℕ k)) ↘ 𝒵)

/-- The base algebraic space. -/
noncomputable abbrev baseAlgebraicSpace : AlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  schemeSpace (Over.mk (𝟙 (𝒞.obj (Space.contains_specULiftZ 𝒞))))

/-- The base algebraic space is terminal among presheaves on the site. -/
noncomputable def isTerminalBaseAlgebraicSpace : IsTerminal (baseAlgebraicSpace 𝒞).obj :=
  (IsTerminal.ofUniqueHom (fun F => { app := fun W => ↾ fun _ => Over.mkIdTerminal.from W.unop })
    (fun F m => by ext W x; exact Over.mkIdTerminal.hom_ext _ _) :
      IsTerminal (yoneda.obj (Over.mk (𝟙 (𝒞.obj (Space.contains_specULiftZ 𝒞)))))).ofIso
    (eqToIso (schemeSpace_obj _).symm)

/-- The presheaf of points of `𝐆_m` on the site. -/
noncomputable abbrev gmPoints : (BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))ᵒᵖ ⥤ Type u :=
  Space.pointsOnSite 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (Space.multiplicativeGroupULiftSiteObject 𝒞)
    (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞) ⋙ forget GrpCat

/-- The presheaf of points of `U` on the site, as the restriction of the functor of points of
`U` in the slice of all schemes over `Spec ℤ`. -/
noncomputable abbrev totalPoints (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    (BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))ᵒᵖ ⥤ Type u :=
  (Space.toSchemeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).op ⋙
    yoneda.obj ((Space.toSchemeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU))

/-- The group algebraic space `𝐆_m` over the base, as an object of the slice of presheaves. -/
noncomputable abbrev groupOver : Over (baseAlgebraicSpace 𝒞).obj :=
  Over.mk (prod.fst : (baseAlgebraicSpace 𝒞).obj ⨯ gmPoints 𝒞 ⟶ (baseAlgebraicSpace 𝒞).obj)

/-- `U` over the base, as an object of the slice of presheaves. -/
noncomputable abbrev spaceOver (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    Over (baseAlgebraicSpace 𝒞).obj :=
  Over.mk (prod.fst : (baseAlgebraicSpace 𝒞).obj ⨯ totalPoints 𝒞 k hU ⟶
    (baseAlgebraicSpace 𝒞).obj)

/-- The weighted action of `𝐆_m` on `U`, read in the slice of presheaves over the base. -/
@[instance_reducible]
noncomputable def spaceOverModObj (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    ModObj (groupOver 𝒞) (spaceOver 𝒞 k hU) :=
  letI := Space.pointsOnSiteModObj 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (Space.multiplicativeGroupULiftSiteObject 𝒞)
    (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞)
    ((Space.toSchemeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (totalSiteObject 𝒞 k hU))
    (action k p).action
  overProdFstModObj _ _ _

/-- The group `𝐆_m` over the base is an algebraic space. -/
theorem isAlgebraicSpace_groupOver :
    IsAlgebraicSpace 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (groupOver 𝒞).left :=
  Space.isAlgebraicSpace_prod_compForget_of_representableBy 𝒞 𝒵
    (Space.contains_specULiftZ 𝒞) (baseAlgebraicSpace 𝒞).obj (baseAlgebraicSpace 𝒞).property _
    (Space.pointsOnSiteRepresentableBy 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Space.multiplicativeGroupULiftSiteObject 𝒞)
      (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞))

/-- `U` over the base is an algebraic space. -/
theorem isAlgebraicSpace_spaceOver (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    IsAlgebraicSpace 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (spaceOver 𝒞 k hU).left :=
  Space.isAlgebraicSpace_prod_toSchemeOverYoneda 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (baseAlgebraicSpace 𝒞).obj (baseAlgebraicSpace 𝒞).property (totalSiteObject 𝒞 k hU)

/-- The action groupoid of Stacks 0444 for the weighted action, with its identifications. -/
noncomputable abbrev actionGroupoidConstruction
    (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    @Space.ActionGroupoidConstruction _ _ _ (baseAlgebraicSpace 𝒞) (groupOver 𝒞)
      (spaceOver 𝒞 k hU) _ (spaceOverModObj 𝒞 k p hU)
      (isAlgebraicSpace_groupOver 𝒞) (isAlgebraicSpace_spaceOver 𝒞 k hU) :=
  @Space.groupoidOfAction _ _ _ (baseAlgebraicSpace 𝒞) (groupOver 𝒞)
      (spaceOver 𝒞 k hU) _ (spaceOverModObj 𝒞 k p hU)
      (isAlgebraicSpace_groupOver 𝒞) (isAlgebraicSpace_spaceOver 𝒞 k hU)

/-- The action groupoid `𝐆_m ×_{Spec ℤ} U ⇉ U` of the weighted action, as a groupoid in
algebraic spaces over the terminal object of the site; its quotient stack is
`AlgebraicGeometry.PPowerWeighted.quotientStack`. -/
noncomputable def actionGroupoid (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    GroupoidInAlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (baseAlgebraicSpace 𝒞) :=
  letI := spaceOverModObj 𝒞 k p hU
  (actionGroupoidConstruction 𝒞 k p hU).groupoid

/-- The quotient stack of 06RE is the quotient stack of
`AlgebraicGeometry.PPowerWeighted.actionGroupoid`, by definition. -/
theorem quotientStack_eq (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    quotientStack 𝒞 k p hU = Stack.quotientStack (actionGroupoid 𝒞 k p hU) :=
  rfl

/-- The comparison from the base algebraic space to `AlgebraicGeometry.Stack.baseSpace`, the
algebraic space of the terminal object. -/
noncomputable def toBaseSpace :
    baseAlgebraicSpace 𝒞 ⟶ Stack.baseSpace 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  schemeSpaceMap (terminal.from _)

/-- The action groupoid read over `AlgebraicGeometry.Stack.baseSpace`. -/
noncomputable def actionGroupoidOverBase (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    GroupoidInAlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Stack.baseSpace 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) :=
  GroupoidInAlgebraicSpaces.changeBase (toBaseSpace 𝒞) (actionGroupoid 𝒞 k p hU)

/-- Changing the base leaves the underlying groupoid in presheaves unchanged. -/
theorem toGroupoidInFunctors_actionGroupoidOverBase
    (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    (actionGroupoidOverBase 𝒞 k p hU).toGroupoidInFunctors =
      (actionGroupoid 𝒞 k p hU).toGroupoidInFunctors :=
  rfl

/-- The groupoid over `AlgebraicGeometry.Stack.baseSpace` presents the quotient stack of 06RE, by
definition. -/
theorem quotientStack_actionGroupoidOverBase
    (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    Stack.quotientStack (actionGroupoidOverBase 𝒞 k p hU) = quotientStack 𝒞 k p hU :=
  rfl

/-- The action groupoid is smooth: its source and target are smooth, `𝐆_m` being smooth. -/
theorem isSmooth_actionGroupoid (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    GroupoidInAlgebraicSpaces.IsSmooth 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (actionGroupoid 𝒞 k p hU) :=
  @Space.isSmooth_groupoidOfAction _ _ _ (baseAlgebraicSpace 𝒞) (groupOver 𝒞)
      (spaceOver 𝒞 k hU) _ (spaceOverModObj 𝒞 k p hU)
      (isAlgebraicSpace_groupOver 𝒞) (isAlgebraicSpace_spaceOver 𝒞 k hU)
    (Space.isSmooth_prod_fst_multiplicativeGroupULift 𝒞 _ (baseAlgebraicSpace 𝒞).property)

/-- The action groupoid read over `AlgebraicGeometry.Stack.baseSpace` is smooth. -/
theorem isSmooth_actionGroupoidOverBase (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    GroupoidInAlgebraicSpaces.IsSmooth 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (actionGroupoidOverBase 𝒞 k p hU) :=
  isSmooth_actionGroupoid 𝒞 k p hU

/-! ### Morphisms into an affine scheme -/

section SpecDictionary

variable {X : Scheme.{u}} {R : CommRingCat.{u}}

/-- The ring map `R → Γ(X, ⊤)` of a morphism `X ⟶ Spec R`: the pullback of functions. -/
noncomputable def specRingHom (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

/-- `AlgebraicGeometry.PPowerWeighted.specRingHom` turns precomposition into restriction of
functions. -/
theorem specRingHom_comp {Y : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ Spec R) :
    specRingHom (g ≫ f) = specRingHom f ≫ g.appTop := by
  simp [specRingHom]

/-- `AlgebraicGeometry.PPowerWeighted.specRingHom` turns postcomposition with `Spec.map φ` into
precomposition with `φ`. -/
theorem specRingHom_comp_specMap {S : CommRingCat.{u}} (f : X ⟶ Spec R) (φ : S ⟶ R) :
    specRingHom (f ≫ Spec.map φ) = φ ≫ specRingHom f := by
  rw [specRingHom_comp, specRingHom, specRingHom, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- The ring map of `f ≫ g ≫ Spec.map φ` is `φ` followed by the ring map of `f ≫ g`. -/
theorem specRingHom_comp_comp_specMap {Y : Scheme.{u}} {S : CommRingCat.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Spec R) (φ : S ⟶ R) :
    specRingHom (f ≫ g ≫ Spec.map φ) = φ ≫ specRingHom (f ≫ g) := by
  rw [← Category.assoc, specRingHom_comp_specMap]

/-- The morphism `X ⟶ Spec Γ(X) ⟶ Spec R` defined by a ring map `φ` pulls functions back by `φ`. -/
theorem specRingHom_toSpecΓ_comp (φ : R ⟶ Γ(X, ⊤)) :
    specRingHom (X.toSpecΓ ≫ Spec.map φ) = φ := by
  rw [specRingHom_comp_specMap, specRingHom, Scheme.toSpecΓ_appTop, Iso.inv_hom_id,
    Category.comp_id]

/-- A morphism into an affine scheme is determined by its ring map. -/
theorem specRingHom_injective : Function.Injective (specRingHom (X := X) (R := R)) := by
  intro f g h
  apply ext_of_isAffine
  have := congrArg ((Scheme.ΓSpecIso R).hom ≫ ·) h
  simpa [specRingHom] using this

/-- Morphisms into `Spec R` are ring maps out of `R` into the global sections. -/
noncomputable def specHomEquiv : (X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤)) where
  toFun := specRingHom
  invFun φ := X.toSpecΓ ≫ Spec.map φ
  left_inv _ := specRingHom_injective (specRingHom_toSpecΓ_comp _)
  right_inv := specRingHom_toSpecΓ_comp

end SpecDictionary

/-! ### Morphisms into an affine object of the site -/

section SiteDictionary

variable {𝒞} {R : CommRingCat.{u}} (hR : 𝒞.Contains (Spec R)) (b : Spec R ⟶ 𝒵)

/-- Morphisms of the site over `Spec ℤ` into an object whose underlying scheme is `Spec R` are
ring maps out of `R` into the global sections: the structure morphisms to `Spec ℤ` agree
automatically, `Spec ℤ` being terminal. -/
noncomputable def siteHomEquiv (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) :
    (W ⟶ siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR b) ≃
      (R ⟶ Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)) where
  toFun h := specRingHom ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h)
  invFun φ := Over.homMk (ObjectProperty.homMk (specHomEquiv.symm φ)) (by
    ext
    exact specULiftZIsTerminal.hom_ext _ _)
  left_inv h := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact specHomEquiv.symm_apply_apply
      ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map h)
  right_inv φ := specHomEquiv.apply_symm_apply φ

variable {hR b}

/-- The ring map of a composite of morphisms of the site. -/
theorem siteHomEquiv_comp {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (h : W ⟶ siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) hR b) :
    siteHomEquiv hR b V (g ≫ h) = siteHomEquiv hR b W h ≫
      ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map g).appTop := by
  change specRingHom (_ ≫ _) = _
  rw [specRingHom_comp]
  rfl

end SiteDictionary

/-! ### Coordinates -/

section Coordinates

variable {𝒞 k} {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- The ring map `Γ(W) → Γ(V)` of a morphism `V ⟶ W` of the site: restriction of functions. -/
noncomputable abbrev restrict {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) :
    Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤) →+*
      Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤) :=
  ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).map g).appTop.hom

/-- The ring map `k[x_0, x_1, …] → Γ(W)` of a `W`-point of `U`. -/
noncomputable abbrev pointRingHom {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    MvPolynomial ℕ k →+* Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤) :=
  (siteHomEquiv hU _ W h).hom

/-- The `j`-th coordinate of a `W`-point `h` of `U`: the pullback of `x_j` along `h`. -/
noncomputable def coord {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) (j : ℕ) :
    Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤) :=
  pointRingHom h (MvPolynomial.X j)

/-- The `k`-algebra structure on `Γ(W)` which a `W`-point of `U` induces. -/
noncomputable def scalarMap {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    k →+* Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤) :=
  (pointRingHom h).comp MvPolynomial.C

/-- The ring map of the restriction of a point of `U`. -/
theorem pointRingHom_comp {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    pointRingHom (g ≫ h) = (restrict g).comp (pointRingHom h) := by
  simp only [pointRingHom]
  rw [siteHomEquiv_comp]
  rfl

/-- **The coordinates are natural**: the coordinates of `g ≫ h` are the restrictions along `g` of
the coordinates of `h`. -/
theorem coord_comp {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (h : W ⟶ totalSiteObject 𝒞 k hU) (j : ℕ) :
    coord (g ≫ h) j = restrict g (coord h j) := by
  rw [coord, pointRingHom_comp]
  rfl

/-- The coordinates of `g ≫ h`, as a function of the index. -/
private theorem coord_comp_eq {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (h : W ⟶ totalSiteObject 𝒞 k hU) : coord (g ≫ h) = fun j => restrict g (coord h j) :=
  funext (coord_comp g h)

/-- The `k`-algebra structure of the restriction of a point of `U`. -/
theorem scalarMap_comp {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    scalarMap (g ≫ h) = (restrict g).comp (scalarMap h) := by
  rw [scalarMap, pointRingHom_comp]
  rfl

/-- Two `W`-points of `U` which induce the same `k`-algebra structure on `Γ(W)` and have the
same coordinates are equal. -/
theorem hom_ext_coord {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {h h' : W ⟶ totalSiteObject 𝒞 k hU} (hk : scalarMap h = scalarMap h')
    (hx : ∀ j, coord h j = coord h' j) : h = h' := by
  apply (siteHomEquiv hU _ W).injective
  ext1
  exact MvPolynomial.ringHom_ext (fun r => RingHom.congr_fun hk r) hx

/-- The `W`-point of `U` with prescribed `k`-algebra structure and coordinates. -/
noncomputable def pointOfCoords {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (φ : k →+* Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (a : ℕ → Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)) :
    W ⟶ totalSiteObject 𝒞 k hU :=
  (siteHomEquiv hU _ W).symm (CommRingCat.ofHom (MvPolynomial.eval₂Hom φ a))

/-- The ring map of the point with prescribed coordinates. -/
@[simp]
theorem pointRingHom_pointOfCoords {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (φ : k →+* Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (a : ℕ → Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)) :
    pointRingHom (pointOfCoords (hU := hU) φ a) = MvPolynomial.eval₂Hom φ a := by
  rw [pointRingHom, pointOfCoords, Equiv.apply_symm_apply]
  rfl

/-- The coordinates of the point with prescribed coordinates. -/
@[simp]
theorem coord_pointOfCoords {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (φ : k →+* Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (a : ℕ → Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)) (j : ℕ) :
    coord (pointOfCoords (hU := hU) φ a) j = a j := by
  simp [coord]

/-- The `k`-algebra structure of the point with prescribed coordinates. -/
@[simp]
theorem scalarMap_pointOfCoords {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (φ : k →+* Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (a : ℕ → Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)) :
    scalarMap (pointOfCoords (hU := hU) φ a) = φ := by
  ext r
  simp [scalarMap]

/-- The restriction of the point with prescribed coordinates. -/
theorem comp_pointOfCoords {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W)
    (φ : k →+* Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (a : ℕ → Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)) :
    g ≫ pointOfCoords (hU := hU) φ a =
      pointOfCoords ((restrict g).comp φ) (fun j => restrict g (a j)) :=
  hom_ext_coord (by rw [scalarMap_comp]; simp) (fun j => by rw [coord_comp]; simp)

/-- The action of a unit `γ` of `Γ(W)`, that is of a `W`-point of `𝐆_m`, on the `W`-points of
`U`: the `j`-th coordinate is multiplied by `γ ^ p ^ j`. -/
noncomputable def actMap {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) : W ⟶ totalSiteObject 𝒞 k hU :=
  pointOfCoords (scalarMap h) (smulPoint p γ (coord h))

/-- **The coordinates of `γ • h`**: the `j`-th one is `γ ^ p ^ j` times that of `h`. -/
@[simp]
theorem coord_actMap {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) (j : ℕ) :
    coord (actMap p γ h) j = γ.val ^ p ^ j * coord h j := by
  simp [actMap]

/-- The action does not change the `k`-algebra structure. -/
@[simp]
theorem scalarMap_actMap {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    scalarMap (actMap p γ h) = scalarMap h := by
  simp [actMap]

/-- The coordinates of `γ • h` are `AlgebraicGeometry.PPowerWeighted.smulPoint` of those of `h`. -/
theorem coord_actMap_eq_smulPoint {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    coord (actMap p γ h) = smulPoint p γ (coord h) :=
  funext fun j => by simp [smulPoint]

/-- The action is natural in the test object. -/
theorem comp_actMap {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    g ≫ actMap p γ h = actMap p (Units.map (restrict g).toMonoidHom γ) (g ≫ h) :=
  hom_ext_coord (by rw [scalarMap_comp]; simp [scalarMap_comp])
    (fun j => by simp [coord_comp])

/-- The unit acts trivially. -/
theorem actMap_one {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) : actMap p 1 h = h :=
  hom_ext_coord (by simp) (fun j => by simp)

/-- The action is an action. -/
theorem actMap_mul {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ δ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) : actMap p (γ * δ) h = actMap p γ (actMap p δ h) :=
  hom_ext_coord (by simp) (fun j => by simp [mul_pow, mul_assoc])

end Coordinates

/-! ### The action on points of schemes -/

section ActionOnPoints

open scoped TensorProduct

/-- The ring map of a morphism into `Spec (S ⊗[R] T)` given by two morphisms into `Spec S` and
`Spec T`, on a pure tensor. -/
theorem specRingHom_lift_pullbackSpecIso_hom_tmul {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] {W : Scheme.{u}} (f : W ⟶ Spec (.of S))
    (g : W ⟶ Spec (.of T))
    (w : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap R T))) (a : S) (b : T) :
    (specRingHom (pullback.lift f g w ≫ (pullbackSpecIso R S T).hom)).hom (a ⊗ₜ[R] b) =
      (specRingHom f).hom a * (specRingHom g).hom b := by
  have hl : (specRingHom (pullback.lift f g w ≫ (pullbackSpecIso R S T).hom)).hom (a ⊗ₜ[R] 1) =
      (specRingHom f).hom a := by
    have e := specRingHom_comp_specMap (pullback.lift f g w ≫ (pullbackSpecIso R S T).hom)
      (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst] at e
    exact (congrArg (fun φ => φ.hom a) e).symm
  have hr : (specRingHom (pullback.lift f g w ≫ (pullbackSpecIso R S T).hom)).hom (1 ⊗ₜ[R] b) =
      (specRingHom g).hom b := by
    have e := specRingHom_comp_specMap (pullback.lift f g w ≫ (pullbackSpecIso R S T).hom)
      (CommRingCat.ofHom (R := T) (S := S ⊗[R] T)
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T))
    rw [Category.assoc, pullbackSpecIso_hom_snd, pullback.lift_snd] at e
    exact (congrArg (fun φ => φ.hom b) e).symm
  rw [← hl, ← hr, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The weighted action read on the points of a scheme: acting by a point `m` of `𝐆_m` on a
point `q` of `U` multiplies the `j`-th coordinate by `t ^ p ^ j`, where `t` is the pullback of
the coordinate of `𝐆_m` along `m`, and keeps the `k`-algebra structure. -/
theorem specRingHom_lift_smul {W : Scheme.{u}} (m : W ⟶ multiplicativeGroupULift.{u})
    (q : W ⟶ Spec (.of (MvPolynomial ℕ k)))
    (w : m ≫ (multiplicativeGroupULift ↘ 𝒵) = q ≫ (Spec (.of (MvPolynomial ℕ k)) ↘ 𝒵)) :
    specRingHom (pullback.lift m q w ≫ (action k p).action.smul.left) =
      CommRingCat.ofHom (MvPolynomial.eval₂Hom ((specRingHom q).hom.comp MvPolynomial.C)
        (smulPoint p ((LaurentPolynomial.isUnit_T (R := ULift.{u} ℤ) 1).map
          (specRingHom m).hom).unit (fun j => (specRingHom q).hom (MvPolynomial.X j)))) := by
  rw [(action k p).action_eq_spec_map]
  refine (specRingHom_comp_comp_specMap _ _ _).trans ?_
  ext1
  apply MvPolynomial.ringHom_ext
  · intro r
    have hC : (MvPolynomial.C r : MvPolynomial ℕ k) ∈ grading k p 0 :=
      (MvPolynomial.mem_weightedHomogeneousSubmodule k _ _ _).2
        (MvPolynomial.isWeightedHomogeneous_C _ r)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      (action k p).μ_homogeneous 0 _ hC, gradedActionTensorMap_tmul_T,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.comm_tmul, MvPolynomial.eval₂Hom_C]
    refine (specRingHom_lift_pullbackSpecIso_hom_tmul m q w _ _).trans ?_
    rw [LaurentPolynomial.T_zero, map_one, one_mul]
  · intro j
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, action_μ_X,
      gradedActionTensorMap_tmul_T, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv,
      Algebra.TensorProduct.comm_tmul, MvPolynomial.eval₂Hom_X', smulPoint_apply,
      IsUnit.unit_spec]
    refine (specRingHom_lift_pullbackSpecIso_hom_tmul m q w _ _).trans ?_
    rw [← map_pow, LaurentPolynomial.T_pow, mul_one]
    norm_cast

end ActionOnPoints

/-! ### Points of `𝐆_m` -/

section GmPoints

/-- Ring maps out of `ℤ[T, T⁻¹]` agree as soon as they agree on `T`. -/
theorem laurentPolynomial_ringHom_ext {S : Type*} [CommRing S]
    {f g : LaurentPolynomial (ULift.{u} ℤ) →+* S}
    (h : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  have hC : ∀ x, f (LaurentPolynomial.C x) = g (LaurentPolynomial.C x) := by
    intro x
    have hx : x = ((x.down : ℤ) : ULift.{u} ℤ) := by ext; simp
    rw [hx, map_intCast, map_intCast, map_intCast]
  have hinv : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    have hf : f (LaurentPolynomial.T (-1)) * f (LaurentPolynomial.T 1) = 1 := by
      rw [← map_mul, ← LaurentPolynomial.T_add]
      simp
    have hg : g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1)) = 1 := by
      rw [← map_mul, ← LaurentPolynomial.T_add]
      simp
    rw [h] at hf
    exact left_inv_eq_right_inv hf hg
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [LaurentPolynomial.T_add, map_mul, map_mul, ih, h]
    | pred n ih => rw [sub_eq_add_neg, LaurentPolynomial.T_add, map_mul, map_mul, ih, hinv]
  refine RingHom.ext fun a => ?_
  induction a using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | C_mul_T n a => rw [map_mul, map_mul, hT n, hC a]

/-- Ring maps out of `ℤ[T, T⁻¹]` are units. -/
noncomputable def laurentHomEquiv (S : CommRingCat.{u}) :
    (CommRingCat.of (LaurentPolynomial (ULift.{u} ℤ)) ⟶ S) ≃ Sˣ where
  toFun φ := ((LaurentPolynomial.isUnit_T (R := ULift.{u} ℤ) 1).map φ.hom).unit
  invFun γ := CommRingCat.ofHom
    (LaurentPolynomial.eval₂ ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom) γ)
  left_inv φ := by
    ext1
    apply laurentPolynomial_ringHom_ext
    simp
  right_inv γ := Units.ext (by simp)

variable {𝒞}

/-- Morphisms over `Spec ℤ` are morphisms of schemes, `Spec ℤ` being terminal. -/
noncomputable def overSpecULiftZHomEquiv (X Y : Over 𝒵) : (X ⟶ Y) ≃ (X.left ⟶ Y.left) where
  toFun f := f.left
  invFun f := Over.homMk f (specULiftZIsTerminal.hom_ext _ _)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `W`-points of `𝐆_m` are the units of `Γ(W)`. -/
@[ega "II 8.3.9" "Bijection Hom_Y(Z"]
noncomputable def gmUnitsEquiv (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) :
    (gmPoints 𝒞).obj (Opposite.op W) ≃
      (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ :=
  ((Equiv.refl _ : (gmPoints 𝒞).obj (Opposite.op W) ≃
      ((Space.toSchemeOver 𝒞 𝒵 _).obj W ⟶ (multiplicativeGroupULift : Scheme.{u}).asOver 𝒵)).trans
    (overSpecULiftZHomEquiv _ _)).trans
    (specHomEquiv.trans (laurentHomEquiv _))

/-- A `W`-point of `𝐆_m`, read as a morphism over `Spec ℤ`. -/
abbrev gmHom {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (m : (gmPoints 𝒞).obj (Opposite.op W)) :
    (Space.toSchemeOver 𝒞 𝒵 _).obj W ⟶
      (Space.toSchemeOver 𝒞 𝒵 _).obj (Space.multiplicativeGroupULiftSiteObject 𝒞) :=
  m

/-- The unit attached to a point of `𝐆_m` is the pullback of the coordinate `T`. -/
@[ega "II 8.3.9" "partial"]
theorem gmUnitsEquiv_val {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (m : (gmPoints 𝒞).obj (Opposite.op W)) :
    (gmUnitsEquiv W m).val = (specRingHom (gmHom m).left).hom (LaurentPolynomial.T 1) :=
  rfl

/-- Restriction of points of `𝐆_m` is precomposition. -/
theorem gmHom_map {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (m : (gmPoints 𝒞).obj (Opposite.op W)) :
    gmHom ((gmPoints 𝒞).map g.op m) = (Space.toSchemeOver 𝒞 𝒵 _).map g ≫ gmHom m :=
  rfl

/-- The identification of the points of `𝐆_m` with units is natural. -/
@[ega "II 8.3.9" "Naturality of Hom(Z"]
theorem gmUnitsEquiv_naturality {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (m : (gmPoints 𝒞).obj (Opposite.op W)) :
    gmUnitsEquiv V ((gmPoints 𝒞).map g.op m) =
      Units.map (restrict g).toMonoidHom (gmUnitsEquiv W m) := by
  apply Units.ext
  rw [gmUnitsEquiv_val, gmHom_map, Over.comp_left]
  exact congrArg (fun φ => (CommRingCat.Hom.hom φ) (LaurentPolynomial.T 1))
    (specRingHom_comp _ (gmHom m).left)

end GmPoints

/-! ### The objects and the arrows of the action groupoid -/

section ActionGroupoidPoints

variable (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))

/-- The objects of the action groupoid are the points of `U` over the base. -/
theorem actionGroupoid_objects_obj :
    (actionGroupoid 𝒞 k p hU).objects.obj = (spaceOver 𝒞 k hU).left :=
  let := spaceOverModObj 𝒞 k p hU
  congrArg (fun Z : AlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) => Z.obj)
    (actionGroupoidConstruction 𝒞 k p hU).objects_eq

open MonoidalCategory in
/-- The arrows of the action groupoid are the points of `𝐆_m × U` over the base. -/
theorem actionGroupoid_arrows_obj :
    (actionGroupoid 𝒞 k p hU).arrows.obj = (groupOver 𝒞 ⊗ spaceOver 𝒞 k hU).left :=
  let := spaceOverModObj 𝒞 k p hU
  congrArg (fun Z : AlgebraicSpaces 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) => Z.obj)
    (actionGroupoidConstruction 𝒞 k p hU).arrows_eq

open MonoidalCategory CartesianMonoidalCategory in
/-- The source of the action groupoid is the second projection. -/
theorem actionGroupoid_source_hom :
    (actionGroupoid 𝒞 k p hU).source.hom = eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
      (snd (groupOver 𝒞) (spaceOver 𝒞 k hU)).left ≫
        eqToHom (actionGroupoid_objects_obj 𝒞 k p hU).symm :=
  let := spaceOverModObj 𝒞 k p hU
  (conj_eqToHom_iff_heq (actionGroupoid 𝒞 k p hU).source.hom _
    (actionGroupoid_arrows_obj 𝒞 k p hU) (actionGroupoid_objects_obj 𝒞 k p hU)).2
    (actionGroupoidConstruction 𝒞 k p hU).source_eq

open MonoidalCategory in
/-- The target of the action groupoid is the action morphism. -/
theorem actionGroupoid_target_hom :
    (actionGroupoid 𝒞 k p hU).target.hom = eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
      (letI := spaceOverModObj 𝒞 k p hU;
        ModObj.smul (M := groupOver 𝒞) (X := spaceOver 𝒞 k hU)).left ≫
        eqToHom (actionGroupoid_objects_obj 𝒞 k p hU).symm :=
  let := spaceOverModObj 𝒞 k p hU
  (conj_eqToHom_iff_heq (actionGroupoid 𝒞 k p hU).target.hom _
    (actionGroupoid_arrows_obj 𝒞 k p hU) (actionGroupoid_objects_obj 𝒞 k p hU)).2
    (actionGroupoidConstruction 𝒞 k p hU).target_eq

/-- The product with the terminal presheaf is the identity. -/
noncomputable def baseProdIso (F : (BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))ᵒᵖ ⥤ Type u) :
    (baseAlgebraicSpace 𝒞).obj ⨯ F ≅ F where
  hom := prod.snd
  inv := prod.lift ((isTerminalBaseAlgebraicSpace 𝒞).from F) (𝟙 F)
  hom_inv_id := prod.hom_ext ((isTerminalBaseAlgebraicSpace 𝒞).hom_ext _ _) (by simp)
  inv_hom_id := by simp

/-- **The objects of the action groupoid are the points of `U`.** -/
noncomputable def objectsIso :
    yoneda.obj (totalSiteObject 𝒞 k hU) ≅ (actionGroupoid 𝒞 k p hU).objects.obj :=
  Space.toSchemeOverYonedaObjIso 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (totalSiteObject 𝒞 k hU) ≪≫
    (baseProdIso 𝒞 _).symm ≪≫ eqToIso (actionGroupoid_objects_obj 𝒞 k p hU).symm

/-- The source of the action groupoid, read on the points of `U`. -/
theorem source_hom_comp_objectsIso_inv :
    (actionGroupoid 𝒞 k p hU).source.hom ≫ (objectsIso 𝒞 k p hU).inv =
      eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
        pullback.snd (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd ≫
          (Space.toSchemeOverYonedaObjIso 𝒞 𝒵 _ (totalSiteObject 𝒞 k hU)).inv := by
  rw [actionGroupoid_source_hom]
  simp only [objectsIso, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- The target of the action groupoid, read on the points of `U`. -/
theorem target_hom_comp_objectsIso_inv :
    (actionGroupoid 𝒞 k p hU).target.hom ≫ (objectsIso 𝒞 k p hU).inv =
      eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
        (letI := spaceOverModObj 𝒞 k p hU;
        ModObj.smul (M := groupOver 𝒞) (X := spaceOver 𝒞 k hU)).left ≫ prod.snd ≫
          (Space.toSchemeOverYonedaObjIso 𝒞 𝒵 _ (totalSiteObject 𝒞 k hU)).inv := by
  rw [actionGroupoid_target_hom]
  simp only [objectsIso, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

/-- Morphisms from a representable presheaf into the arrows of the action groupoid are pairs of
a point of `𝐆_m` and a point of `U`. -/
noncomputable def arrowsYonedaEquiv (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) :
    (yoneda.obj W ⟶ (actionGroupoid 𝒞 k p hU).arrows.obj) ≃
      (yoneda.obj W ⟶ gmPoints 𝒞) × (W ⟶ totalSiteObject 𝒞 k hU) where
  toFun y := (y ≫ eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
      pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd,
    yonedaEquiv (y ≫ (actionGroupoid 𝒞 k p hU).source.hom ≫ (objectsIso 𝒞 k p hU).inv))
  invFun mh := pullback.lift (prod.lift ((isTerminalBaseAlgebraicSpace 𝒞).from _) mh.1)
      (prod.lift ((isTerminalBaseAlgebraicSpace 𝒞).from _) (yoneda.map mh.2 ≫
        (Space.toSchemeOverYonedaObjIso 𝒞 𝒵 _ (totalSiteObject 𝒞 k hU)).hom))
      ((isTerminalBaseAlgebraicSpace 𝒞).hom_ext _ _) ≫
    eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU).symm
  left_inv y := by
    dsimp only
    rw [← Iso.cancel_iso_hom_right _ _ (eqToIso (actionGroupoid_arrows_obj 𝒞 k p hU)),
      eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply prod.hom_ext
      · exact (isTerminalBaseAlgebraicSpace 𝒞).hom_ext _ _
      · simp
    · rw [pullback.lift_snd]
      apply prod.hom_ext
      · exact (isTerminalBaseAlgebraicSpace 𝒞).hom_ext _ _
      · have : yoneda.map (yonedaEquiv (y ≫ (actionGroupoid 𝒞 k p hU).source.hom ≫
            (objectsIso 𝒞 k p hU).inv)) =
            y ≫ (actionGroupoid 𝒞 k p hU).source.hom ≫ (objectsIso 𝒞 k p hU).inv :=
          yonedaEquiv.injective (yonedaEquiv_yoneda_map _)
        rw [prod.lift_snd, this, source_hom_comp_objectsIso_inv]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  right_inv mh := by
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact (pullback.lift_fst_assoc _ _ _ _).trans (prod.lift_snd _ _)
    · dsimp only
      apply yonedaEquiv.symm.injective
      rw [Equiv.symm_apply_apply, source_hom_comp_objectsIso_inv]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        pullback.lift_snd_assoc, prod.lift_snd_assoc, Iso.hom_inv_id, Category.comp_id]
      exact (yonedaEquiv.symm_apply_eq).2 (yonedaEquiv_yoneda_map _).symm

/-- **The arrows of the action groupoid over `W` are pairs `(γ, h)` of a unit `γ` of `Γ(W)`,
that is a `W`-point of `𝐆_m`, and a `W`-point `h` of `U`.** The source of the arrow is `h`
(`AlgebraicGeometry.PPowerWeighted.objectsIso_inv_source`) and its target is `γ • h`
(`AlgebraicGeometry.PPowerWeighted.objectsIso_inv_target`). -/
noncomputable def arrowsEquiv (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) :
    (actionGroupoid 𝒞 k p hU).arrows.obj.obj (Opposite.op W) ≃
      (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ ×
        (W ⟶ totalSiteObject 𝒞 k hU) :=
  yonedaEquiv.symm.trans ((arrowsYonedaEquiv 𝒞 k p hU W).trans
    (Equiv.prodCongr (yonedaEquiv.trans (gmUnitsEquiv W)) (Equiv.refl _)))

/-- The source of an arrow `(γ, h)` is `h`. -/
theorem objectsIso_inv_source (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (x : (actionGroupoid 𝒞 k p hU).arrows.obj.obj (Opposite.op W)) :
    (objectsIso 𝒞 k p hU).inv.app (Opposite.op W)
        ((actionGroupoid 𝒞 k p hU).source.hom.app (Opposite.op W) x) =
      (arrowsEquiv 𝒞 k p hU W x).2 := by
  have : (arrowsEquiv 𝒞 k p hU W x).2 = yonedaEquiv (yonedaEquiv.symm x ≫
      (actionGroupoid 𝒞 k p hU).source.hom ≫ (objectsIso 𝒞 k p hU).inv) := rfl
  rw [this, ← Category.assoc, yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply]

attribute [local instance] Space.multiplicativeGroupULiftSiteObjectGrpObj in
/-- The weighted action, on `U` read through the site. -/
@[instance_reducible]
noncomputable def totalModObj : ModObj
    ((Space.toSchemeOver 𝒞 𝒵 _).obj (Space.multiplicativeGroupULiftSiteObject 𝒞))
    ((Space.toSchemeOver 𝒞 𝒵 _).obj (totalSiteObject 𝒞 k hU)) :=
  (action k p).action

attribute [local instance] Space.multiplicativeGroupULiftSiteObjectGrpObj

/-- The action of a `W`-point of `𝐆_m` on a `W`-point of `U`, computed in the slice of all
schemes over `Spec ℤ`, is `AlgebraicGeometry.PPowerWeighted.actMap`. -/
theorem gmHom_smul_toSchemeOver_map (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (m : (gmPoints 𝒞).obj (Opposite.op W)) (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (letI := totalModObj 𝒞 k p hU; gmHom m • (Space.toSchemeOver 𝒞 𝒵 _).map h) =
      (Space.toSchemeOver 𝒞 𝒵 _).map (actMap p (gmUnitsEquiv W m) h) := by
  let := totalModObj 𝒞 k p hU
  apply Over.OverMorphism.ext
  apply specRingHom_injective
  refine (specRingHom_lift_smul k p (gmHom m).left
    ((BigFppfOver.toScheme 𝒞 𝒵 _).map h) (specULiftZIsTerminal.hom_ext _ _)).trans ?_
  change _ = CommRingCat.ofHom (pointRingHom (actMap p (gmUnitsEquiv W m) h))
  rw [actMap, pointRingHom_pointOfCoords]
  rfl

open MonoidalCategory CartesianMonoidalCategory in
/-- The action of the presheaf of groups `𝐆_m` on the presheaf of points of `U`, on
representable sections. -/
theorem yoneda_smul_eq (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (m : yoneda.obj W ⟶ gmPoints 𝒞) (h : W ⟶ totalSiteObject 𝒞 k hU) :
    (letI := Space.pointsOnSiteModObj 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Space.multiplicativeGroupULiftSiteObject 𝒞)
      (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞)
      ((Space.toSchemeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (totalSiteObject 𝒞 k hU))
      (action k p).action
    m • (yoneda.map h ≫ (Space.toSchemeOverYonedaObjIso 𝒞 𝒵 _ (totalSiteObject 𝒞 k hU)).hom)) =
      yoneda.map (actMap p (gmUnitsEquiv W (yonedaEquiv m)) h) ≫
        (Space.toSchemeOverYonedaObjIso 𝒞 𝒵 _ (totalSiteObject 𝒞 k hU)).hom := by
  let := Space.pointsOnSiteModObj 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (Space.multiplicativeGroupULiftSiteObject 𝒞)
      (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞)
      ((Space.toSchemeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (totalSiteObject 𝒞 k hU))
      (action k p).action
  apply yonedaEquiv.injective
  rw [Hom.smul_def, yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  let := totalModObj 𝒞 k p hU
  refine (opCompYoneda_smul_app (Space.toSchemeOver 𝒞 𝒵 _) _ _ (Opposite.op W) _ _).trans ?_
  exact gmHom_smul_toSchemeOver_map 𝒞 k p hU W (yonedaEquiv m) h

/-- The target of an arrow `(γ, h)` is `γ • h`. -/
theorem objectsIso_inv_target (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (x : (actionGroupoid 𝒞 k p hU).arrows.obj.obj (Opposite.op W)) :
    (objectsIso 𝒞 k p hU).inv.app (Opposite.op W)
        ((actionGroupoid 𝒞 k p hU).target.hom.app (Opposite.op W) x) =
      actMap p (arrowsEquiv 𝒞 k p hU W x).1 (arrowsEquiv 𝒞 k p hU W x).2 := by
  let := spaceOverModObj 𝒞 k p hU
  obtain ⟨⟨m, h⟩, hx⟩ : ∃ mh, (arrowsYonedaEquiv 𝒞 k p hU W).symm mh = yonedaEquiv.symm x :=
    ⟨_, Equiv.symm_apply_apply _ _⟩
  have hx' : x = yonedaEquiv ((arrowsYonedaEquiv 𝒞 k p hU W).symm (m, h)) := by
    rw [hx, Equiv.apply_symm_apply]
  have he : arrowsEquiv 𝒞 k p hU W x = (gmUnitsEquiv W (yonedaEquiv m), h) := by
    change (Equiv.prodCongr (yonedaEquiv.trans (gmUnitsEquiv W)) (Equiv.refl _))
      (arrowsYonedaEquiv 𝒞 k p hU W (yonedaEquiv.symm x)) = _
    rw [← hx, Equiv.apply_symm_apply]
    rfl
  rw [he, hx', ← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc,
    target_hom_comp_objectsIso_inv]
  change yonedaEquiv ((pullback.lift _ _ _ ≫ eqToHom _) ≫ eqToHom _ ≫ _) = _
  rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  let t := (isTerminalBaseAlgebraicSpace 𝒞).from (yoneda.obj W)
  let ptG : Over.mk t ⟶ groupOver 𝒞 := Over.homMk (prod.lift t m) (prod.lift_fst _ _)
  let ptX : Over.mk t ⟶ spaceOver 𝒞 k hU := Over.homMk (prod.lift t (yoneda.map h ≫
    (Space.toSchemeOverYonedaObjIso 𝒞 𝒵 _ (totalSiteObject 𝒞 k hU)).hom)) (prod.lift_fst _ _)
  let := Space.pointsOnSiteModObj 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
    (Space.multiplicativeGroupULiftSiteObject 𝒞)
    (Space.multiplicativeGroupULiftSiteObjectGrpObj 𝒞)
    ((Space.toSchemeOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (totalSiteObject 𝒞 k hU))
    (action k p).action
  have key := overProdFst_smul_left_comp_snd (B := (baseAlgebraicSpace 𝒞).obj)
    (P := gmPoints 𝒞) (Y := totalPoints 𝒞 k hU) ptG ptX
  simp only [ptG, ptX, Over.homMk_left, prod.lift_snd] at key
  rw [yoneda_smul_eq] at key
  have hl : pullback.lift (prod.lift t m) (prod.lift t (yoneda.map h ≫
      (Space.toSchemeOverYonedaObjIso 𝒞 𝒵 _ (totalSiteObject 𝒞 k hU)).hom))
        ((isTerminalBaseAlgebraicSpace 𝒞).hom_ext _ _) ≫
      (ModObj.smul (M := groupOver 𝒞) (X := spaceOver 𝒞 k hU)).left = (ptG • ptX).left := rfl
  rw [← Category.assoc, hl, ← Category.assoc, key, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, yonedaEquiv_yoneda_map]

/-- The two components of `AlgebraicGeometry.PPowerWeighted.arrowsEquiv`. -/
theorem arrowsEquiv_apply (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
    (x : (actionGroupoid 𝒞 k p hU).arrows.obj.obj (Opposite.op W)) :
    arrowsEquiv 𝒞 k p hU W x =
      (gmUnitsEquiv W ((eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
          pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd).app _ x),
        ((actionGroupoid 𝒞 k p hU).source.hom ≫ (objectsIso 𝒞 k p hU).inv).app _ x) := by
  have : arrowsEquiv 𝒞 k p hU W x =
      (gmUnitsEquiv W (yonedaEquiv (yonedaEquiv.symm x ≫
          (eqToHom (actionGroupoid_arrows_obj 𝒞 k p hU) ≫
            pullback.fst (groupOver 𝒞).hom (spaceOver 𝒞 k hU).hom ≫ prod.snd))),
        yonedaEquiv (yonedaEquiv.symm x ≫
          ((actionGroupoid 𝒞 k p hU).source.hom ≫ (objectsIso 𝒞 k p hU).inv))) := rfl
  rw [this, yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The description of the arrows is natural in the test object. -/
theorem arrowsEquiv_naturality {V W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (x : (actionGroupoid 𝒞 k p hU).arrows.obj.obj (Opposite.op W)) :
    arrowsEquiv 𝒞 k p hU V ((actionGroupoid 𝒞 k p hU).arrows.obj.map g.op x) =
      (Units.map (restrict g).toMonoidHom (arrowsEquiv 𝒞 k p hU W x).1,
        g ≫ (arrowsEquiv 𝒞 k p hU W x).2) := by
  rw [arrowsEquiv_apply, arrowsEquiv_apply, NatTrans.naturality_apply,
    NatTrans.naturality_apply, gmUnitsEquiv_naturality]
  rfl

end ActionGroupoidPoints

/-! ### The strata as subfunctors -/

section Strata

/-- The stratum `X_a` read on points, for `a : WithTop ℕ`: for `a = i` the coordinates before
the `i`-th vanish and the `i`-th one is invertible, for `a = ⊤` all coordinates vanish. -/
def IsPointInStratumAt {R : Type*} [CommRing R] : WithTop ℕ → (ℕ → R) → Prop
  | ⊤ => IsPointInStratumInf
  | (i : ℕ) => IsPointInStratum i

/-- The predicate `IsPointInStratumAt ⊤` is `IsPointInStratumInf`. -/
@[simp] theorem isPointInStratumAt_top {R : Type*} [CommRing R] (c : ℕ → R) :
    IsPointInStratumAt ⊤ c ↔ IsPointInStratumInf c := Iff.rfl

/-- The predicate `IsPointInStratumAt i` is `IsPointInStratum i`. -/
@[simp] theorem isPointInStratumAt_coe {R : Type*} [CommRing R] (i : ℕ) (c : ℕ → R) :
    IsPointInStratumAt (i : WithTop ℕ) c ↔ IsPointInStratum i c := Iff.rfl

/-- The strata are preserved by ring maps. -/
theorem IsPointInStratumAt.map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {a : WithTop ℕ} {c : ℕ → R} (h : IsPointInStratumAt a c) :
    IsPointInStratumAt a (fun j => f (c j)) := by
  induction a using WithTop.recTopCoe with
  | top => exact fun j => show f (c j) = 0 by rw [show c j = 0 from h j, map_zero]
  | coe i => exact ⟨fun j hj => show f (c j) = 0 by rw [h.1 j hj, map_zero], h.2.map f⟩

/-- The strata are invariant under the action on points. -/
theorem isPointInStratumAt_smulPoint {R : Type*} [CommRing R] (p : ℕ) (a : WithTop ℕ)
    (t : Rˣ) (c : ℕ → R) :
    IsPointInStratumAt a (smulPoint p t c) ↔ IsPointInStratumAt a c := by
  induction a using WithTop.recTopCoe with
  | top => exact isPointInStratumInf_smulPoint p t c
  | coe i => exact isPointInStratum_smulPoint p i t c

variable {𝒞 k}

/-- **The strata of `U` as subfunctors of its functor of points.** For `i : ℕ` the `W`-points
of `X_i` are those whose coordinates before the `i`-th vanish and whose `i`-th coordinate is a
unit of `Γ(W)`; the `W`-points of `X_∞` are those all of whose coordinates vanish. -/
def stratumSubfunctor (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) (a : WithTop ℕ) :
    Subfunctor (yoneda.obj (totalSiteObject 𝒞 k hU)) where
  obj W := {h | IsPointInStratumAt a (coord h)}
  map {W V} g h hh := by
    change IsPointInStratumAt a (coord (g.unop ≫ h))
    rw [show coord (g.unop ≫ h) = fun j => restrict g.unop (coord h j) from
      funext (coord_comp g.unop h)]
    exact hh.map (restrict g.unop)

variable {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- Membership in a stratum is the stratum condition on the coordinates. -/
theorem mem_stratumSubfunctor_iff {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (a : WithTop ℕ) (h : W ⟶ totalSiteObject 𝒞 k hU) :
    h ∈ (stratumSubfunctor hU a).obj (Opposite.op W) ↔ IsPointInStratumAt a (coord h) :=
  Iff.rfl

/-- Membership in `X_i`: the coordinates before the `i`-th vanish and the `i`-th is a unit. -/
theorem mem_stratumSubfunctor_coe_iff {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (i : ℕ) (h : W ⟶ totalSiteObject 𝒞 k hU) :
    h ∈ (stratumSubfunctor hU i).obj (Opposite.op W) ↔
      (∀ j < i, coord h j = 0) ∧ IsUnit (coord h i) :=
  Iff.rfl

/-- Membership in `X_∞`: all the coordinates vanish. -/
theorem mem_stratumSubfunctor_top_iff {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    h ∈ (stratumSubfunctor hU ⊤).obj (Opposite.op W) ↔ ∀ j, coord h j = 0 :=
  Iff.rfl

/-- **The strata are invariant under the action.** -/
theorem actMap_mem_stratumSubfunctor_iff {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (a : WithTop ℕ)
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    actMap p γ h ∈ (stratumSubfunctor hU a).obj (Opposite.op W) ↔
      h ∈ (stratumSubfunctor hU a).obj (Opposite.op W) := by
  rw [mem_stratumSubfunctor_iff, mem_stratumSubfunctor_iff, coord_actMap_eq_smulPoint,
    isPointInStratumAt_smulPoint]

/-- **Stacks 06RE, the stabilizer along `X_i`.** A unit `γ` fixes a `W`-point of the stratum
`X_i` exactly when `γ ^ p ^ i = 1`, that is when `γ` is a `W`-point of `μ_{p^i}`. -/
theorem actMap_eq_self_iff_coe {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} {i : ℕ}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    {h : W ⟶ totalSiteObject 𝒞 k hU} (hh : h ∈ (stratumSubfunctor hU i).obj (Opposite.op W)) :
    actMap p γ h = h ↔ γ ∈ rootsUnitsSubgroup (p ^ i) := by
  rw [← pointStabilizer_eq_rootsUnitsSubgroup p i _ hh]
  constructor
  · intro he
    change smulPoint p γ (coord h) = coord h
    rw [← coord_actMap_eq_smulPoint, he]
  · intro hγ
    exact hom_ext_coord (scalarMap_actMap p γ h)
      (fun j => by rw [coord_actMap_eq_smulPoint]; exact congrFun hγ j)

/-- **Stacks 06RE, the stabilizer along `X_∞`.** Every unit fixes every `W`-point of `X_∞`. -/
theorem actMap_eq_self_of_top {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    {h : W ⟶ totalSiteObject 𝒞 k hU} (hh : h ∈ (stratumSubfunctor hU ⊤).obj (Opposite.op W)) :
    actMap p γ h = h :=
  hom_ext_coord (scalarMap_actMap p γ h) (fun j => by
    rw [coord_actMap, show coord h j = 0 from hh j, mul_zero])

/-- **Comparison with the strata of the spectrum.** If `Γ(W)` is a field, a `W`-point of `U`
lies in `X_i` exactly when the prime ideal it defines lies in the stratum
`AlgebraicGeometry.PPowerWeighted.stratum`. -/
theorem mem_stratumSubfunctor_coe_iff_mem_stratum
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (i : ℕ)
    (hK : IsField Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    h ∈ (stratumSubfunctor hU i).obj (Opposite.op W) ↔
      (⟨RingHom.ker (pointRingHom h), letI := hK.toField; RingHom.ker_isPrime _⟩ :
        PrimeSpectrum (MvPolynomial ℕ k)) ∈ stratum k i := by
  let := hK.toField
  exact (mem_stratum_ker_iff k (pointRingHom h) i).symm

/-- **Comparison with the strata of the spectrum.** If `Γ(W)` is a field, a `W`-point of `U`
lies in `X_∞` exactly when the prime ideal it defines lies in
`AlgebraicGeometry.PPowerWeighted.stratumInf`. -/
theorem mem_stratumSubfunctor_top_iff_mem_stratumInf
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (hK : IsField Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    h ∈ (stratumSubfunctor hU ⊤).obj (Opposite.op W) ↔
      (⟨RingHom.ker (pointRingHom h), letI := hK.toField; RingHom.ker_isPrime _⟩ :
        PrimeSpectrum (MvPolynomial ℕ k)) ∈ stratumInf k := by
  let := hK.toField
  exact (mem_stratumInf_ker_iff k (pointRingHom h)).symm

end Strata

/-! ### The strata as subschemes -/

section Subschemes

/-- `Spec` of a surjective ring map is a monomorphism of schemes. -/
theorem mono_specMap_of_surjective {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Surjective φ) : Mono (Spec.map φ) := by
  have : Epi φ := ConcreteCategory.epi_of_surjective φ hφ
  exact inferInstanceAs (Mono (Scheme.Spec.map φ.op))

/-- A morphism into `Spec A` factors through the closed subscheme `Spec (A ⧸ I)` exactly when
the pullback of functions kills `I`. -/
theorem exists_comp_specMap_quotient_iff {X : Scheme.{u}} {A : Type u} [CommRing A]
    (I : Ideal A) (g : X ⟶ Spec (.of A)) :
    (∃ f : X ⟶ Spec (.of (A ⧸ I)), f ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      I ≤ RingHom.ker (specRingHom g).hom := by
  constructor
  · rintro ⟨f, rfl⟩ a ha
    rw [RingHom.mem_ker, specRingHom_comp_specMap]
    change (specRingHom f).hom (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  · intro hI
    refine ⟨specHomEquiv.symm (CommRingCat.ofHom (Ideal.Quotient.lift I (specRingHom g).hom hI)),
      specRingHom_injective ?_⟩
    rw [specRingHom_comp_specMap]
    change _ ≫ specHomEquiv (specHomEquiv.symm _) = _
    rw [Equiv.apply_symm_apply]
    ext a
    rfl

/-- A ring map kills the ideal generated by some coordinates exactly when it kills those
coordinates. -/
theorem coordinateIdeal_le_ker_iff {R : Type*} [CommRing R] (s : Set ℕ)
    (φ : MvPolynomial ℕ k →+* R) :
    coordinateIdeal k s ≤ RingHom.ker φ ↔ ∀ j ∈ s, φ (MvPolynomial.X j) = 0 := by
  rw [coordinateIdeal, Ideal.span_le, Set.image_subset_iff]
  exact Iff.rfl

/-- The closed subscheme `Spec (A ⧸ I)` of `Spec A`. -/
private noncomputable abbrev specQuotientSubobject {A : Type u} [CommRing A] (I : Ideal A) :
    Subobject (Spec (.of A)) :=
  haveI := mono_specMap_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
  Subobject.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- The closed subscheme `Spec (A ⧸ I)` of `Spec A` is a closed immersion. -/
private theorem isClosedImmersion_specQuotientSubobject_arrow {A : Type u} [CommRing A]
    (I : Ideal A) : IsClosedImmersion (specQuotientSubobject I).arrow := by
  have := mono_specMap_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
  rw [specQuotientSubobject, ← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- The closed subscheme `Spec (A ⧸ I)` of `Spec A` is reduced when `A ⧸ I` is a domain. -/
private theorem isReduced_specQuotientSubobject {A : Type u} [CommRing A] (I : Ideal A)
    [IsDomain (A ⧸ I)] : IsReduced (specQuotientSubobject I : Scheme.{u}) :=
  haveI := mono_specMap_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
  @isReduced_of_isOpenImmersion _ _ (Subobject.underlyingIso (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk I)))).hom (@IsOpenImmersion.of_isIso _ _ _ (Iso.isIso_hom _)) _

/-- A morphism into `Spec A` factors through `Spec (A ⧸ I)` exactly when `I` is killed. -/
private theorem factors_specQuotientSubobject_iff {X : Scheme.{u}} {A : Type u} [CommRing A]
    (I : Ideal A) (g : X ⟶ Spec (.of A)) :
    (specQuotientSubobject I).Factors g ↔ I ≤ RingHom.ker (specRingHom g).hom := by
  have := mono_specMap_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk I))
    Ideal.Quotient.mk_surjective
  rw [specQuotientSubobject, Subobject.mk_factors_iff]
  exact exists_comp_specMap_quotient_iff I g

variable {𝒞 k}

/-- **The closed subscheme `X_∞` of `U`**, cut out by all the coordinates: it is
`Spec k = Spec (k[x_0, x_1, …] ⧸ (x_0, x_1, …))`. -/
noncomputable def stratumTopSubobject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    Subobject ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU)) :=
  haveI := mono_specMap_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (coordinateIdeal k Set.univ)))
    Ideal.Quotient.mk_surjective
  Subobject.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (coordinateIdeal k Set.univ))) :
    Spec (.of (MvPolynomial ℕ k ⧸ coordinateIdeal k Set.univ)) ⟶ Spec (.of (MvPolynomial ℕ k)))

variable {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}

/-- `X_∞` is a closed subscheme of `U`. -/
theorem isClosedImmersion_stratumTopSubobject_arrow :
    IsClosedImmersion (stratumTopSubobject hU).arrow := by
  exact isClosedImmersion_specQuotientSubobject_arrow (coordinateIdeal k Set.univ)

/-- `X_∞` is reduced, being the spectrum of the field `k`, or more generally of a domain. -/
theorem isReduced_stratumTopSubobject [IsDomain k] :
    IsReduced (stratumTopSubobject hU : Scheme.{u}) := by
  have := isDomain_quotient_coordinateIdeal_univ k
  exact isReduced_specQuotientSubobject (coordinateIdeal k Set.univ)

/-- **The `W`-points of `X_∞` are the points of the closed subscheme `X_∞`.** -/
theorem subschemePoints_stratumTopSubobject :
    Space.subschemePoints 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (stratumTopSubobject hU) =
      stratumSubfunctor hU ⊤ := by
  ext W h
  rw [Space.mem_subschemePoints_iff]
  refine (factors_specQuotientSubobject_iff _
    ((BigFppfOver.toScheme 𝒞 𝒵 _).map h)).trans ((coordinateIdeal_le_ker_iff k _ _).trans ?_)
  exact ⟨fun H j => H j trivial, fun H j _ => H j⟩

variable (k) in
/-- The coordinate ring `k[x_0, x_1, …][1/x_i]` of the basic open `D(x_i)` of `U`. -/
noncomputable abbrev basicOpenRing (i : ℕ) : Type u :=
  Localization.Away (MvPolynomial.X i : MvPolynomial ℕ k)

variable (k) in
/-- The ideal of `D(x_i)` generated by `x_0, …, x_{i-1}`, cutting out `X_i`. -/
noncomputable abbrev basicOpenIdeal (i : ℕ) : Ideal (basicOpenRing k i) :=
  Ideal.map (algebraMap (MvPolynomial ℕ k) (basicOpenRing k i)) (coordinateIdeal k {j | j < i})

/-- The basic open `D(x_i)` belongs to the site. -/
theorem contains_basicOpen (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) (i : ℕ) :
    𝒞.Contains (Spec (.of (basicOpenRing k i))) :=
  have := Scheme.isOpenImmersion_SpecMap_localizationAway
    (R := CommRingCat.of (MvPolynomial ℕ k)) (MvPolynomial.X i)
  Scheme.size_lt_of_isOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ℕ k) (basicOpenRing k i)))) hU

/-- The basic open `D(x_i)` of `U`, as an object of the site. -/
noncomputable abbrev basicOpenSiteObject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))
    (i : ℕ) : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (contains_basicOpen hU i)
    (specULiftZIsTerminal.from _)

/-- The open immersion `D(x_i) ⟶ U`. -/
noncomputable def basicOpenι (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) (i : ℕ) :
    basicOpenSiteObject hU i ⟶ totalSiteObject 𝒞 k hU :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ℕ k) (basicOpenRing k i)))))
    (by ext; exact specULiftZIsTerminal.hom_ext _ _)

/-- `D(x_i) ⟶ U` is an open immersion. -/
theorem isOpenImmersion_basicOpenι (i : ℕ) :
    IsOpenImmersion ((BigFppfOver.toScheme 𝒞 𝒵 _).map (basicOpenι hU i)) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway
    (R := CommRingCat.of (MvPolynomial ℕ k)) (MvPolynomial.X i)

/-- The ring map of a point of `U` which factors through `D(x_i)`. -/
theorem pointRingHom_comp_basicOpenι {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    {i : ℕ} (h' : W ⟶ basicOpenSiteObject hU i) :
    pointRingHom (h' ≫ basicOpenι hU i) =
      (siteHomEquiv _ _ W h').hom.comp (algebraMap _ (basicOpenRing k i)) :=
  congrArg CommRingCat.Hom.hom (specRingHom_comp_specMap
    ((BigFppfOver.toScheme 𝒞 𝒵 _).map h')
    (CommRingCat.ofHom (algebraMap (MvPolynomial ℕ k) (basicOpenRing k i))))

/-- **The closed subscheme `X_i` of `D(x_i)`**, cut out by `x_0, …, x_{i-1}`: it is
`Spec (k[x_0, x_1, …][1/x_i] ⧸ (x_0, …, x_{i-1}))`. -/
noncomputable def stratumSubobject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) (i : ℕ) :
    Subobject ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (basicOpenSiteObject hU i)) :=
  haveI := mono_specMap_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (basicOpenIdeal k i))) Ideal.Quotient.mk_surjective
  Subobject.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (basicOpenIdeal k i))))

/-- `X_i` is a closed subscheme of `D(x_i)`. -/
theorem isClosedImmersion_stratumSubobject_arrow (i : ℕ) :
    IsClosedImmersion (stratumSubobject hU i).arrow := by
  exact isClosedImmersion_specQuotientSubobject_arrow (basicOpenIdeal k i)

/-- Over a domain, the ideal of `X_i` in `D(x_i)` is prime. -/
theorem isPrime_basicOpenIdeal [IsDomain k] (i : ℕ) : (basicOpenIdeal k i).IsPrime := by
  refine IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial ℕ k)) _ _
    (isPrime_coordinateIdeal k _) ?_
  rw [Set.disjoint_left]
  rintro _ ⟨n, rfl⟩ hn
  exact X_notMem_coordinateIdeal k (s := {j | j < i}) (i := i) (lt_irrefl i)
    ((isPrime_coordinateIdeal k _).mem_of_pow_mem n hn)

/-- `X_i` is reduced: its coordinate ring is a domain. -/
theorem isReduced_stratumSubobject [IsDomain k] (i : ℕ) :
    IsReduced (stratumSubobject hU i : Scheme.{u}) := by
  have := (Ideal.Quotient.isDomain_iff_prime _).mpr (isPrime_basicOpenIdeal (k := k) i)
  exact isReduced_specQuotientSubobject (basicOpenIdeal k i)

/-- A point of `D(x_i)` is a point of `X_i` exactly when its coordinates before the `i`-th
vanish. -/
theorem mem_subschemePoints_stratumSubobject_iff
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} {i : ℕ}
    (h' : W ⟶ basicOpenSiteObject hU i) :
    h' ∈ (Space.subschemePoints 𝒞 𝒵 _ (stratumSubobject hU i)).obj (Opposite.op W) ↔
      ∀ j < i, coord (h' ≫ basicOpenι hU i) j = 0 := by
  rw [Space.mem_subschemePoints_iff]
  refine (factors_specQuotientSubobject_iff _
    ((BigFppfOver.toScheme 𝒞 𝒵 _).map h')).trans ?_
  rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
  refine (coordinateIdeal_le_ker_iff k _ _).trans ?_
  simp only [coord, pointRingHom_comp_basicOpenι]
  exact Iff.rfl

/-- **Stacks 06RE, `X_i` as a subscheme.** A `W`-point of `U` lies in `X_i` exactly when it
factors through the basic open `D(x_i)` by a point of the closed subscheme `X_i` of `D(x_i)`. -/
theorem mem_stratumSubfunctor_coe_iff_exists
    {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (i : ℕ)
    (h : W ⟶ totalSiteObject 𝒞 k hU) :
    h ∈ (stratumSubfunctor hU i).obj (Opposite.op W) ↔
      ∃ h' : W ⟶ basicOpenSiteObject hU i, h' ≫ basicOpenι hU i = h ∧
        h' ∈ (Space.subschemePoints 𝒞 𝒵 _ (stratumSubobject hU i)).obj (Opposite.op W) := by
  constructor
  · rintro ⟨h0, hi⟩
    let φ : basicOpenRing k i →+* _ := IsLocalization.Away.lift _ (g := pointRingHom h) hi
    let h' : W ⟶ basicOpenSiteObject hU i := (siteHomEquiv _ _ W).symm (CommRingCat.ofHom φ)
    have hφ : pointRingHom (h' ≫ basicOpenι hU i) = pointRingHom h := by
      rw [pointRingHom_comp_basicOpenι, Equiv.apply_symm_apply]
      exact IsLocalization.Away.lift_comp _ hi
    have he : h' ≫ basicOpenι hU i = h :=
      (siteHomEquiv _ _ W).injective (CommRingCat.hom_ext hφ)
    refine ⟨h', he, (mem_subschemePoints_stratumSubobject_iff h').2 ?_⟩
    rw [he]
    exact h0
  · rintro ⟨h', rfl, hm⟩
    refine ⟨(mem_subschemePoints_stratumSubobject_iff h').1 hm, ?_⟩
    simp only [coord, pointRingHom_comp_basicOpenι, RingHom.comp_apply]
    exact (IsLocalization.Away.algebraMap_isUnit _).map _

/-- The `i`-th stratum as an immersed subscheme of `U`: the closed subscheme `X_i` of `D(x_i)`
followed by the open immersion `D(x_i) ⟶ U`. -/
noncomputable def stratumImmersedSubobject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k))))
    (i : ℕ) : Subobject ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj
      (totalSiteObject 𝒞 k hU)) :=
  haveI := isOpenImmersion_basicOpenι (hU := hU) i
  Subobject.mk ((stratumSubobject hU i).arrow ≫
    (BigFppfOver.toScheme 𝒞 𝒵 _).map (basicOpenι hU i))

/-- `X_i ⟶ U` is an immersion. -/
theorem isImmersion_stratumImmersedSubobject_arrow (i : ℕ) :
    IsImmersion (stratumImmersedSubobject hU i).arrow := by
  have := isClosedImmersion_stratumSubobject_arrow (hU := hU) i
  have := isOpenImmersion_basicOpenι (hU := hU) i
  rw [stratumImmersedSubobject, ← Subobject.underlyingIso_hom_comp_eq_mk]
  infer_instance

/-- **The `W`-points of `X_i` are the points of the immersed subscheme `X_i`.** -/
theorem subschemePoints_stratumImmersedSubobject (i : ℕ) :
    Space.subschemePoints 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (stratumImmersedSubobject hU i) =
      stratumSubfunctor hU i := by
  have := isOpenImmersion_basicOpenι (hU := hU) i
  ext W h
  rw [Space.mem_subschemePoints_iff, stratumImmersedSubobject, Subobject.mk_factors_iff,
    mem_stratumSubfunctor_coe_iff_exists]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨Over.homMk (ObjectProperty.homMk (f ≫ (stratumSubobject hU i).arrow))
      (by ext; exact specULiftZIsTerminal.hom_ext _ _), ?_, ?_⟩
    · apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact (Category.assoc _ _ _).trans hf
    · rw [Space.mem_subschemePoints_iff]
      exact (Subobject.factors_iff _ _).2 ⟨f, rfl⟩
  · rintro ⟨h', rfl, hm⟩
    rw [Space.mem_subschemePoints_iff] at hm
    obtain ⟨f, hf⟩ := (Subobject.factors_iff _ _).1 hm
    exact ⟨f, ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hf)).trans
      (Functor.map_comp _ _ _).symm⟩

/-- **The strata are sheaves for the big fppf topology.** Each is the functor of points of an
immersed subscheme of `U`, and the big fppf site is subcanonical. -/
theorem isSheaf_stratumSubfunctor (a : WithTop ℕ) :
    Presheaf.IsSheaf (BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞))
      (stratumSubfunctor hU a).toFunctor := by
  induction a using WithTop.recTopCoe with
  | top =>
    rw [← subschemePoints_stratumTopSubobject]
    have := isClosedImmersion_stratumTopSubobject_arrow (hU := hU)
    obtain ⟨V, ι, e, he⟩ := Space.exists_presentation 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (stratumTopSubobject hU) inferInstance
    exact Space.isSheaf_subschemePoints 𝒞 𝒵 _ ι e he
  | coe i =>
    obtain ⟨V, ι, e, he⟩ := Space.exists_presentation 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
      (stratumImmersedSubobject hU i) (isImmersion_stratumImmersedSubobject_arrow i)
    have := Space.isSheaf_subschemePoints 𝒞 𝒵 _ ι e he
    rwa [subschemePoints_stratumImmersedSubobject] at this

end Subschemes

/-! ### The coarse maps -/

section CoarseCoordinates

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The invariants of a point `c` of the stratum `X_i` with `i`-th coordinate the unit `u`:
`y_m = c_{i+1+m} / u ^ p ^ (m + 1)`. -/
def coarseCoords (p i : ℕ) (c : ℕ → R) (u : Rˣ) : ℕ → R :=
  fun m => c (i + 1 + m) * ((u⁻¹ ^ p ^ (m + 1) : Rˣ) : R)

/-- The invariants are invariant. -/
theorem coarseCoords_smulPoint (p i : ℕ) (c : ℕ → R) (u γ : Rˣ) :
    coarseCoords p i (smulPoint p γ c) (γ ^ p ^ i * u) = coarseCoords p i c u := by
  funext m
  simp only [coarseCoords, smulPoint_apply]
  have hN : p ^ (i + 1 + m) = p ^ i * p ^ (m + 1) := by rw [← pow_add]; ring_nf
  have key : (γ : R) ^ p ^ (i + 1 + m) * (((γ ^ p ^ i)⁻¹ ^ p ^ (m + 1) : Rˣ) : R) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, ← pow_mul, ← hN,
      mul_inv_cancel, Units.val_one]
  rw [mul_inv, mul_pow, Units.val_mul]
  linear_combination (c (i + 1 + m) * ((u⁻¹ ^ p ^ (m + 1) : Rˣ) : R)) * key

/-- The invariants commute with ring maps. -/
theorem map_coarseCoords (f : R →+* S) (p i : ℕ) (c : ℕ → R) (u : Rˣ) (m : ℕ) :
    f (coarseCoords p i c u m) =
      coarseCoords p i (fun j => f (c j)) (Units.map f.toMonoidHom u) m := by
  simp [coarseCoords]

end CoarseCoordinates

section Coarse

variable {𝒞 k}

/-- `Spec k` belongs to the site as soon as `U` does: it is a closed subscheme of `U`. -/
theorem contains_specField (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    𝒞.Contains (Spec (.of k)) :=
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (MvPolynomial.constantCoeff : MvPolynomial ℕ k →+* k))
    (fun a => ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C _ a⟩)
  Scheme.size_lt_of_isClosedImmersion (Spec.map (CommRingCat.ofHom MvPolynomial.constantCoeff)) hU

/-- `Spec k` as an object of the site: the coarse space of the last stratum `X_∞`. -/
noncomputable abbrev specFieldSiteObject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (contains_specField hU)
    (specULiftZIsTerminal.from _)

/-- The coarse space of the stratum `X_a`: for `a = i` it is `U` again, with coordinates
`y_m = x_{i+1+m} / x_i ^ p ^ (m + 1)`, and for `a = ⊤` it is `Spec k`. -/
noncomputable def coarseSiteObject (hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))) :
    WithTop ℕ → BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)
  | ⊤ => specFieldSiteObject hU
  | (_ : ℕ) => totalSiteObject 𝒞 k hU

variable {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}
variable {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}

/-- The `i`-th coordinate of a point of `X_i`, as a unit. -/
noncomputable def stratumUnit {i : ℕ} (x : (stratumSubfunctor hU i).obj (Opposite.op W)) :
    (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ :=
  x.2.2.unit

/-- The value of `AlgebraicGeometry.PPowerWeighted.stratumUnit`. -/
@[simp] theorem stratumUnit_val {i : ℕ} (x : (stratumSubfunctor hU i).obj (Opposite.op W)) :
    (stratumUnit x).val = coord x.1 i :=
  x.2.2.unit_spec

/-- The coarse map of the stratum `X_i`: `y_m = x_{i+1+m} / x_i ^ p ^ (m + 1)`. -/
noncomputable def coarseMapCoe {i : ℕ} (x : (stratumSubfunctor hU i).obj (Opposite.op W)) :
    W ⟶ totalSiteObject 𝒞 k hU :=
  pointOfCoords (scalarMap x.1) (coarseCoords p i (coord x.1) (stratumUnit x))

/-- The coarse map of the stratum `X_∞`: the structure morphism to `Spec k`. -/
noncomputable def coarseMapTop (x : (stratumSubfunctor hU ⊤).obj (Opposite.op W)) :
    W ⟶ specFieldSiteObject hU :=
  (siteHomEquiv (contains_specField hU) _ W).symm (CommRingCat.ofHom (scalarMap x.1))

/-- **The coarse maps `X_a ⟶ M_a`.** -/
noncomputable def coarseMap : (a : WithTop ℕ) →
    (stratumSubfunctor hU a).obj (Opposite.op W) → (W ⟶ coarseSiteObject hU a)
  | ⊤ => coarseMapTop
  | (_ : ℕ) => coarseMapCoe p

/-- The coarse map of `X_i`. -/
theorem coarseMap_coe (i : ℕ) (x : (stratumSubfunctor hU i).obj (Opposite.op W)) :
    coarseMap p (i : WithTop ℕ) x = coarseMapCoe p x := rfl

/-- The coarse map of `X_∞`. -/
theorem coarseMap_top (x : (stratumSubfunctor hU ⊤).obj (Opposite.op W)) :
    coarseMap p ⊤ x = coarseMapTop x := rfl

/-- The coarse map of `X_i` keeps the `k`-algebra structure. -/
theorem scalarMap_coarseMapCoe {i : ℕ} (x : (stratumSubfunctor hU i).obj (Opposite.op W)) :
    scalarMap (coarseMapCoe p x) = scalarMap x.1 := by
  simp [coarseMapCoe]

/-- The coordinates of the coarse map of `X_i`. -/
theorem coord_coarseMapCoe {i : ℕ} (x : (stratumSubfunctor hU i).obj (Opposite.op W)) (m : ℕ) :
    coord (coarseMapCoe p x) m =
      coord x.1 (i + 1 + m) * ((stratumUnit x)⁻¹ ^ p ^ (m + 1) : _ˣ) := by
  simp [coarseMapCoe, coarseCoords]

/-- The point of `X_a` obtained by acting on a point of `X_a`. -/
noncomputable def actMapStratum (a : WithTop ℕ)
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (x : (stratumSubfunctor hU a).obj (Opposite.op W)) :
    (stratumSubfunctor hU a).obj (Opposite.op W) :=
  ⟨actMap p γ x.1, (actMap_mem_stratumSubfunctor_iff p a γ x.1).2 x.2⟩

/-- The `i`-th coordinate of `γ • x` is `γ ^ p ^ i` times that of `x`. -/
theorem stratumUnit_actMapStratum {i : ℕ}
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (x : (stratumSubfunctor hU i).obj (Opposite.op W)) :
    stratumUnit (actMapStratum p (i : WithTop ℕ) γ x) = γ ^ p ^ i * stratumUnit x := by
  apply Units.ext
  rw [stratumUnit_val, Units.val_mul, Units.val_pow_eq_pow_val, stratumUnit_val]
  exact coord_actMap p γ x.1 i

/-- **The coarse maps are invariant under the action.** -/
theorem coarseMap_actMapStratum (a : WithTop ℕ)
    (γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)
    (x : (stratumSubfunctor hU a).obj (Opposite.op W)) :
    coarseMap p a (actMapStratum p a γ x) = coarseMap p a x := by
  induction a using WithTop.recTopCoe with
  | top =>
    change (siteHomEquiv _ _ W).symm (CommRingCat.ofHom (scalarMap (actMap p γ x.1))) =
      (siteHomEquiv _ _ W).symm (CommRingCat.ofHom (scalarMap x.1))
    rw [scalarMap_actMap]
  | coe i =>
    change pointOfCoords (scalarMap (actMap p γ x.1))
        (coarseCoords p i (coord (actMap p γ x.1))
          (stratumUnit (actMapStratum p (i : WithTop ℕ) γ x))) =
      pointOfCoords (scalarMap x.1) (coarseCoords p i (coord x.1) (stratumUnit x))
    rw [stratumUnit_actMapStratum, scalarMap_actMap, coord_actMap_eq_smulPoint,
      coarseCoords_smulPoint]

/-- The restriction of a point of `X_a` along a morphism of the site. -/
noncomputable def restrictStratum {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    {a : WithTop ℕ} (x : (stratumSubfunctor hU a).obj (Opposite.op W)) :
    (stratumSubfunctor hU a).obj (Opposite.op V) :=
  ⟨g ≫ x.1, (stratumSubfunctor hU a).map g.op x.2⟩

/-- `AlgebraicGeometry.PPowerWeighted.restrictStratum` is the restriction map of the subfunctor. -/
theorem restrictStratum_eq {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    {a : WithTop ℕ} (x : (stratumSubfunctor hU a).obj (Opposite.op W)) :
    restrictStratum g x = (stratumSubfunctor hU a).toFunctor.map g.op x :=
  rfl

/-- **The coarse maps are natural in the test object.** -/
theorem coarseMap_restrictStratum {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (a : WithTop ℕ) (x : (stratumSubfunctor hU a).obj (Opposite.op W)) :
    coarseMap p a (restrictStratum g x) = g ≫ coarseMap p a x := by
  induction a using WithTop.recTopCoe with
  | top =>
    change (siteHomEquiv _ _ V).symm (CommRingCat.ofHom (scalarMap (g ≫ x.1))) =
      g ≫ (siteHomEquiv _ _ W).symm (CommRingCat.ofHom (scalarMap x.1))
    apply (siteHomEquiv (contains_specField hU) _ V).injective
    rw [siteHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext1
    exact scalarMap_comp g x.1
  | coe i =>
    change pointOfCoords (scalarMap (g ≫ x.1))
        (coarseCoords p i (coord (g ≫ x.1)) (stratumUnit (restrictStratum g x))) =
      g ≫ pointOfCoords (scalarMap x.1) (coarseCoords p i (coord x.1) (stratumUnit x))
    have hu : stratumUnit (restrictStratum g x) =
        Units.map (restrict g).toMonoidHom (stratumUnit x) := by
      apply Units.ext
      rw [stratumUnit_val, Units.coe_map, stratumUnit_val]
      exact coord_comp g x.1 i
    rw [comp_pointOfCoords, scalarMap_comp, hu, coord_comp_eq]
    congr 1
    funext m
    rw [map_coarseCoords]

/-- **The coarse maps are natural**, in the form of the restriction maps of the subfunctor. -/
theorem coarseMap_naturality {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V ⟶ W)
    (a : WithTop ℕ) (x : (stratumSubfunctor hU a).obj (Opposite.op W)) :
    coarseMap p a ((stratumSubfunctor hU a).toFunctor.map g.op x) = g ≫ coarseMap p a x :=
  coarseMap_restrictStratum p g a x

/-- The section of the coarse map of `X_i`: the point `(0, …, 0, 1, y_0, y_1, …)`. -/
noncomputable def coarseSectionCoe (i : ℕ) (y : W ⟶ totalSiteObject 𝒞 k hU) :
    (stratumSubfunctor hU i).obj (Opposite.op W) :=
  ⟨pointOfCoords (scalarMap y)
      (fun j => if j < i then 0 else if j = i then 1 else coord y (j - (i + 1))),
    (mem_stratumSubfunctor_coe_iff i _).2 ⟨fun j hj => by simp [hj], by simp⟩⟩

/-- The section of the coarse map of `X_∞`: the origin. -/
noncomputable def coarseSectionTop (y : W ⟶ specFieldSiteObject hU) :
    (stratumSubfunctor hU ⊤).obj (Opposite.op W) :=
  ⟨pointOfCoords (siteHomEquiv (contains_specField hU) _ W y).hom 0, fun j => by simp⟩

/-- **The sections of the coarse maps.** -/
noncomputable def coarseSection : (a : WithTop ℕ) →
    (W ⟶ coarseSiteObject hU a) → (stratumSubfunctor hU a).obj (Opposite.op W)
  | ⊤ => coarseSectionTop
  | (i : ℕ) => coarseSectionCoe i

/-- **The sections are sections.** -/
theorem coarseMap_coarseSection (a : WithTop ℕ) (y : W ⟶ coarseSiteObject hU a) :
    coarseMap p a (coarseSection a y) = y := by
  induction a using WithTop.recTopCoe with
  | top =>
    apply (siteHomEquiv (contains_specField hU) _ W).injective
    change (siteHomEquiv _ _ W) ((siteHomEquiv _ _ W).symm _) = _
    rw [Equiv.apply_symm_apply]
    ext1
    exact scalarMap_pointOfCoords _ _
  | coe i =>
    change coarseMapCoe p (coarseSectionCoe i y) = y
    have hu : stratumUnit (coarseSectionCoe (hU := hU) i y) = 1 :=
      Units.ext (by simp [coarseSectionCoe])
    refine hom_ext_coord ?_ (fun m => ?_)
    · rw [scalarMap_coarseMapCoe]
      exact scalarMap_pointOfCoords _ _
    · rw [coord_coarseMapCoe, hu]
      simp only [coarseSectionCoe, coord_pointOfCoords, inv_one, one_pow, Units.val_one,
        mul_one]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1
      omega

/-- The section of the coarse map of `X_∞` is natural. -/
theorem coarseSectionTop_naturality {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (y : W ⟶ specFieldSiteObject hU) :
    coarseSectionTop (g ≫ y) = restrictStratum g (coarseSectionTop y) := by
  apply Subtype.ext
  change pointOfCoords _ _ = g ≫ pointOfCoords _ _
  rw [comp_pointOfCoords, siteHomEquiv_comp]
  congr 1
  funext j
  simp

/-- The section of the coarse map of `X_i` is natural. -/
theorem coarseSectionCoe_naturality {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (i : ℕ) (y : W ⟶ totalSiteObject 𝒞 k hU) :
    coarseSectionCoe i (g ≫ y) = restrictStratum g (coarseSectionCoe i y) := by
  apply Subtype.ext
  change pointOfCoords _ _ = g ≫ pointOfCoords _ _
  rw [comp_pointOfCoords, scalarMap_comp]
  congr 1
  funext j
  split_ifs <;> simp [coord_comp]

/-- **The sections are natural in the test object.** -/
theorem coarseSection_naturality {V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}
    (g : V ⟶ W) (a : WithTop ℕ) (y : W ⟶ coarseSiteObject hU a) :
    coarseSection a (g ≫ y) = (stratumSubfunctor hU a).toFunctor.map g.op (coarseSection a y) := by
  induction a using WithTop.recTopCoe with
  | top => exact coarseSectionTop_naturality g y
  | coe i => exact coarseSectionCoe_naturality g i y

end Coarse

/-! ### Local transitivity on the fibres of the coarse maps -/

section Transitivity

/-- Two points of the stratum `X_i` with the same invariants differ by a unit `γ` as soon as
`γ ^ p ^ i` is the ratio of their `i`-th coordinates. -/
theorem smulPoint_eq_of_coarseCoords_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p i : ℕ) {cx cy : ℕ → R} {ux uy : Rˣ} (hx : IsPointInStratum i cx)
    (hy : IsPointInStratum i cy) (hux : (ux : R) = cx i) (huy : (uy : R) = cy i)
    (h : coarseCoords p i cx ux = coarseCoords p i cy uy) (γ : Sˣ)
    (hγ : (γ : S) ^ p ^ i = f ((uy * ux⁻¹ : Rˣ) : R)) :
    smulPoint p γ (fun j => f (cx j)) = fun j => f (cy j) := by
  funext j
  rw [smulPoint_apply]
  rcases lt_trichotomy j i with hj | rfl | hj
  · rw [hx.1 j hj, hy.1 j hj, map_zero, mul_zero]
  · rw [hγ, ← map_mul, ← hux, ← huy, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - (i + 1), by omega⟩
    have hm := congrFun h m
    simp only [coarseCoords] at hm
    have hN : p ^ (i + 1 + m) = p ^ i * p ^ (m + 1) := by rw [← pow_add]; ring_nf
    have hR : cy (i + 1 + m) = cx (i + 1 + m) * (((uy * ux⁻¹) ^ p ^ (m + 1) : Rˣ) : R) := by
      have e1 : (((uy⁻¹ ^ p ^ (m + 1) : Rˣ) : R)) * ((uy ^ p ^ (m + 1) : Rˣ) : R) = 1 := by
        rw [← Units.val_mul, ← mul_pow, inv_mul_cancel, one_pow, Units.val_one]
      have e2 : ((uy * ux⁻¹) ^ p ^ (m + 1) : Rˣ) =
          ux⁻¹ ^ p ^ (m + 1) * uy ^ p ^ (m + 1) := by rw [mul_pow, mul_comm]
      rw [e2, Units.val_mul, ← mul_assoc, hm, mul_assoc, e1, mul_one]
    rw [hR, map_mul, hN, pow_mul, hγ, ← map_pow, ← Units.val_pow_eq_pow_val, mul_comm]

variable {𝒞 k} {hU : 𝒞.Contains (Spec (.of (MvPolynomial ℕ k)))}
variable {W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)}

/-- Restriction of functions is functorial. -/
theorem restrict_comp {V V' : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)} (g : V' ⟶ V)
    (h : V ⟶ W) (a : Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)) :
    restrict (g ≫ h) a = restrict g (restrict h a) :=
  rfl

/-- The coordinates of the coarse map of `X_i` are the invariants. -/
theorem coord_coarseMapCoe_eq {i : ℕ} (x : (stratumSubfunctor hU i).obj (Opposite.op W)) :
    coord (coarseMapCoe p x) = coarseCoords p i (coord x.1) (stratumUnit x) :=
  funext fun m => by simp [coarseMapCoe]

/-- The ring `Γ(W)[s] ⧸ (s ^ n - c)` adjoining an `n`-th root of a unit `c` of `Γ(W)`. -/
noncomputable abbrev rootRing (W : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)) (n : ℕ)
    (c : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ) : Type u :=
  AdjoinRoot (Polynomial.X ^ n - Polynomial.C (c : Γ(
    (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)))

section RootRing

variable (n : ℕ) (hn : 0 < n)
  (c : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤))ˣ)

include hn in
/-- `Γ(W)[s] ⧸ (s ^ n - c)` is free over `Γ(W)`. -/
theorem module_free_rootRing :
    Module.Free Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)
      (rootRing W n c) :=
  (Polynomial.monic_X_pow_sub_C _ hn.ne').free_adjoinRoot

include hn in
/-- `Γ(W)[s] ⧸ (s ^ n - c)` is finite over `Γ(W)`. -/
theorem module_finite_rootRing :
    Module.Finite Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)
      (rootRing W n c) :=
  (Polynomial.monic_X_pow_sub_C _ hn.ne').finite_adjoinRoot

include hn in
/-- `Γ(W)[s] ⧸ (s ^ n - c)` is faithfully flat over `Γ(W)`. -/
theorem faithfullyFlat_rootRing :
    Module.FaithfullyFlat Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)
      (rootRing W n c) := by
  have := module_free_rootRing n hn c
  rcases subsingleton_or_nontrivial
    Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤) with hR | hR
  · exact ⟨fun m hm => absurd (Subsingleton.elim m ⊤) hm.ne_top⟩
  · have : Nontrivial (rootRing W n c) :=
      (AdjoinRoot.nontrivial_iff_of_monic (Polynomial.monic_X_pow_sub_C _ hn.ne')).2
        (by rw [Polynomial.degree_X_pow_sub_C hn]; exact_mod_cast hn)
    infer_instance

/-- The structure map `Spec Γ(W)[s] ⧸ (s ^ n - c) ⟶ Spec Γ(W)`. -/
noncomputable abbrev rootSpecMap :
    Spec (.of (rootRing W n c)) ⟶
      Spec Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ (rootRing W n c)))

include hn in
/-- `Spec Γ(W)[s] ⧸ (s ^ n - c) ⟶ Spec Γ(W)` is flat and surjective. -/
theorem flat_rootSpecMap : Flat (rootSpecMap n c) ∧ Surjective (rootSpecMap n c) := by
  have := faithfullyFlat_rootRing n hn c
  exact (flat_and_surjective_SpecMap_iff _).2 (RingHom.faithfullyFlat_algebraMap_iff.2 this)

/-- `Spec Γ(W)[s] ⧸ (s ^ n - c) ⟶ Spec Γ(W)` is locally of finite presentation. -/
theorem lfp_rootSpecMap : LocallyOfFinitePresentation (rootSpecMap n c) := by
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.2 inferInstance

include hn in
/-- `Spec Γ(W)[s] ⧸ (s ^ n - c) ⟶ Spec Γ(W)` is finite. -/
theorem isFinite_rootSpecMap : IsFinite (rootSpecMap n c) := by
  have := module_finite_rootRing n hn c
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.2 this

/-- The finite locally free cover of `W` on which `c` acquires an `n`-th root. -/
noncomputable abbrev rootCoverScheme : Scheme.{u} :=
  pullback ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W).toSpecΓ
    (rootSpecMap n c)

/-- The root cover belongs to the site, being finite over `W`. -/
theorem contains_rootCoverScheme : 𝒞.Contains (rootCoverScheme n c) :=
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (pullback.fst ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ (rootSpecMap n c)) W.left.property

/-- The cover of `W` on which `c` has an `n`-th root, as an object of the site. -/
noncomputable abbrev rootCover : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) :=
  siteObject 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) (contains_rootCoverScheme n c)
    (specULiftZIsTerminal.from _)

/-- The covering map. -/
noncomputable def rootCoverMap : rootCover n c ⟶ W :=
  Over.homMk (ObjectProperty.homMk (pullback.fst _ _)) (by
    ext
    exact specULiftZIsTerminal.hom_ext _ _)

include hn in
/-- The root cover is an fppf covering. -/
theorem mem_topology_rootCoverMap :
    Sieve.generate (Presieve.singleton (rootCoverMap n c)) ∈
      BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W := by
  obtain ⟨hf, hs⟩ := flat_rootSpecMap n hn c
  have := lfp_rootSpecMap n c
  refine Space.sieve_generate_singleton_mem_topology_over_of_flat 𝒞 𝒵 _ _ ?_ ?_ ?_
  · exact (inferInstance : Surjective (pullback.fst
      ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ (rootSpecMap n c)))
  · exact (inferInstance : Flat (pullback.fst
      ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ (rootSpecMap n c)))
  · exact (inferInstance : LocallyOfFinitePresentation (pullback.fst
      ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ (rootSpecMap n c)))

/-- The `n`-th root of `c` on the cover. -/
noncomputable def rootCoverRoot :
    Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj (rootCover n c), ⊤) :=
  (specRingHom (pullback.snd _ _ : rootCoverScheme n c ⟶ _)).hom (AdjoinRoot.root _)

/-- The root is an `n`-th root of `c`. -/
theorem rootCoverRoot_pow :
    rootCoverRoot n c ^ n = (pullback.fst ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ
      (rootSpecMap n c)).appTop.hom c.val := by
  have hroot : (AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (c : Γ(
      (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)))) ^ n =
      algebraMap Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)
        (rootRing W n c) c.val := by
    have := AdjoinRoot.mk_self (f := Polynomial.X ^ n - Polynomial.C (c : Γ(
      (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)))
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at this
    exact this
  have h1 : specRingHom (pullback.snd ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ
        (rootSpecMap n c) ≫ rootSpecMap n c) =
      CommRingCat.ofHom (algebraMap _ (rootRing W n c)) ≫ specRingHom
        (pullback.snd ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ (rootSpecMap n c)) :=
    specRingHom_comp_specMap _ _
  have h2 : specRingHom (pullback.fst ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ
        (rootSpecMap n c) ≫ ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ) =
      specRingHom ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ ≫
        (pullback.fst ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ (rootSpecMap n c)).appTop :=
    specRingHom_comp _ _
  have hid : specRingHom ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W).toSpecΓ =
      𝟙 _ := by
    have := specRingHom_toSpecΓ_comp
      (X := (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W) (𝟙 _)
    rwa [Spec.map_id, Category.comp_id] at this
  have h3 := h2.symm.trans ((congrArg specRingHom pullback.condition).trans h1)
  have h4 := congrArg (fun φ => (CommRingCat.Hom.hom φ) c.val) h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h4
  have h5 : (CommRingCat.Hom.hom (specRingHom
      ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W).toSpecΓ)) c.val = c.val := by
    rw [hid]
    rfl
  calc rootCoverRoot n c ^ n
      = (specRingHom (pullback.snd ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ
          (rootSpecMap n c))).hom ((AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (c : Γ(
            (BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj W, ⊤)))) ^ n) :=
        (map_pow _ _ _).symm
    _ = (specRingHom (pullback.snd ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ
          (rootSpecMap n c))).hom (algebraMap Γ((BigFppfOver.toScheme 𝒞 𝒵
            (Space.contains_specULiftZ 𝒞)).obj W, ⊤) (rootRing W n c) c.val) :=
        congrArg (specRingHom (pullback.snd ((BigFppfOver.toScheme 𝒞 𝒵 _).obj W).toSpecΓ
          (rootSpecMap n c))).hom hroot
    _ = _ := h4.symm
    _ = _ := congrArg _ h5

include hn in
/-- The root is a unit. -/
theorem isUnit_rootCoverRoot : IsUnit (rootCoverRoot n c) :=
  (isUnit_pow_iff hn.ne').1 (by rw [rootCoverRoot_pow]; exact c.isUnit.map _)

/-- The root is an `n`-th root of `c`, in terms of restriction along the covering map. -/
theorem rootCoverRoot_pow' :
    rootCoverRoot n c ^ n = restrict (rootCoverMap n c) c :=
  rootCoverRoot_pow n c

end RootRing

/-- **Local transitivity on the fibres of the coarse maps.** Two `W`-points of the stratum
`X_a` with the same image in the coarse space `M_a` are, fppf locally on `W`, in the same orbit
of the action.  For `a = ⊤` they are equal; for `a = i` the ratio of their `i`-th coordinates
acquires a `p^i`-th root on the finite locally free cover `Spec Γ(W)[s] ⧸ (s ^ p ^ i - c)`. -/
theorem exists_covering_actMap_eq (hp : 0 < p) (a : WithTop ℕ)
    (x y : (stratumSubfunctor hU a).obj (Opposite.op W))
    (hxy : coarseMap p a x = coarseMap p a y) :
    ∃ R : Sieve W, R ∈ BigFppfOver.topology 𝒞 𝒵 (Space.contains_specULiftZ 𝒞) W ∧
      ∀ ⦃V : BigFppfOver 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)⦄ (g : V ⟶ W), R.arrows g →
        ∃ γ : (Γ((BigFppfOver.toScheme 𝒞 𝒵 (Space.contains_specULiftZ 𝒞)).obj V, ⊤))ˣ,
          actMap p γ (g ≫ x.1) = g ≫ y.1 := by
  induction a using WithTop.recTopCoe with
  | top =>
    have hs : scalarMap x.1 = scalarMap y.1 := by
      have := congrArg (siteHomEquiv (contains_specField hU) _ W) hxy
      simp only [coarseMap_top, coarseMapTop, Equiv.apply_symm_apply] at this
      exact congrArg CommRingCat.Hom.hom this
    have hxy' : x.1 = y.1 :=
      hom_ext_coord hs (fun j => (x.2 j).trans (y.2 j).symm)
    refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨1, ?_⟩⟩
    rw [actMap_one, hxy']
  | coe i =>
    have hxy₀ : coarseMapCoe p x = coarseMapCoe p y := hxy
    have hs : scalarMap x.1 = scalarMap y.1 := by
      have := congrArg scalarMap hxy₀
      rwa [scalarMap_coarseMapCoe, scalarMap_coarseMapCoe] at this
    have hc : coarseCoords p i (coord x.1) (stratumUnit x) =
        coarseCoords p i (coord y.1) (stratumUnit y) := by
      have := congrArg coord hxy₀
      rwa [coord_coarseMapCoe_eq, coord_coarseMapCoe_eq] at this
    have hn : 0 < p ^ i := pow_pos hp i
    let c := stratumUnit y * (stratumUnit x)⁻¹
    refine ⟨_, mem_topology_rootCoverMap (p ^ i) hn c, ?_⟩
    rintro V g ⟨V', h, g₀, ⟨⟩, rfl⟩
    refine ⟨Units.map (restrict h).toMonoidHom (isUnit_rootCoverRoot (p ^ i) hn c).unit, ?_⟩
    refine hom_ext_coord ?_ (fun j => ?_)
    · rw [scalarMap_actMap, scalarMap_comp, scalarMap_comp, hs]
    · rw [coord_actMap_eq_smulPoint]
      rw [coord_comp_eq, coord_comp_eq]
      refine congrFun (smulPoint_eq_of_coarseCoords_eq _ p i x.2 y.2 (stratumUnit_val x)
        (stratumUnit_val y) hc _ ?_) j
      change (restrict h (isUnit_rootCoverRoot (p ^ i) hn c).unit.val) ^ p ^ i = _
      rw [IsUnit.unit_spec, ← map_pow, rootCoverRoot_pow', restrict_comp]

end Transitivity

end AlgebraicGeometry.PPowerWeighted

end
