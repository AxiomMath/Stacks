module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# The rational functions of a scheme

A rational function on a scheme `X` is a rational map from `X` to the affine line over the
integers [Stacks, Tag 01RT]. A section of the structure sheaf on a *dense* open set is such a
rational map, because a morphism to the affine line is the same thing as a global section of the
structure sheaf; this file records that construction and its three basic properties: it is
unchanged by passing to a smaller dense open set, every rational function arises this way, and
two sections giving the same rational function agree on a smaller dense open set.

Those three properties characterize the ring of rational functions [Stacks, Tag 01RU] among rings
receiving the sections on dense open sets.

## Main definitions

* `AlgebraicGeometry.affineLine`: the affine line over the integers, as a one-dimensional affine
  space over the spectrum of `ULift ℤ`.
* `AlgebraicGeometry.Scheme.rationalFunctions`: the rational maps from `X` to the affine line.
* `AlgebraicGeometry.Scheme.rationalFunctionOfSection`: a section on a dense open set, read as a
  rational function.

## Main results

* `AlgebraicGeometry.Scheme.rationalFunctionOfSection_res`: restriction to a smaller dense open
  set does not change the rational function.
* `AlgebraicGeometry.Scheme.exists_rationalFunctionOfSection_eq`: every rational function comes
  from a section on a dense open set.
* `AlgebraicGeometry.Scheme.exists_dense_res_eq_of_rationalFunctionOfSection_eq`: two sections
  defining the same rational function agree on a smaller dense open set.
* `AlgebraicGeometry.homOfLE_appTop_topIso_inv`: the sections functor of an open subscheme
  identifies the inclusion of a smaller open set with the restriction map of the structure sheaf.

## References

* [Stacks Project, Tag 01RT](https://stacks.math.columbia.edu/tag/01RT)
* [Stacks Project, Tag 01RU](https://stacks.math.columbia.edu/tag/01RU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Morphisms, restriction maps and partial maps -/

/-- The inverse of an isomorphism of commutative rings is injective. -/
private lemma commRingCat_iso_inv_injective {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Injective e.inv.hom :=
  (ConcreteCategory.bijective_of_isIso e.inv).1

/-- Equal morphisms of schemes induce equal maps on a global section. -/
private lemma appTop_congr {Y Z : Scheme.{u}} {k k' : Y ⟶ Z} (he : k = k') (c : Γ(Z, ⊤)) :
    k.appTop c = k'.appTop c := by rw [he]

/-- Any two composites of restriction maps of the structure sheaf with the same source and the
same target agree, because the category of open sets has at most one morphism between any two
objects. -/
private lemma presheaf_map_square {A B B' A' : (Opens X)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ B') (f' : A ⟶ A') (g' : A' ⟶ B') :
    X.presheaf.map f ≫ X.presheaf.map g = X.presheaf.map f' ≫ X.presheaf.map g' := by
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 1

/-- Partial maps with the same rational map agree after restriction to a dense open set. -/
private lemma exists_dense_restrict_hom_eq {Y : Scheme.{u}} {g g' : X.PartialMap Y}
    (h : g.toRationalMap = g'.toRationalMap) :
    ∃ (W : X.Opens) (_ : Dense (W : Set X)) (hWl : W ≤ g.domain) (hWr : W ≤ g'.domain),
      X.homOfLE hWl ≫ g.hom = X.homOfLE hWr ≫ g'.hom :=
  Scheme.PartialMap.toRationalMap_eq_iff.mp h

/-- Partial maps agreeing on a dense open set define the same rational map. -/
private lemma toRationalMap_eq_of_restrict_hom_eq {Y : Scheme.{u}} (g g' : X.PartialMap Y)
    {W : X.Opens} (hW : Dense (W : Set X)) (hWl : W ≤ g.domain) (hWr : W ≤ g'.domain)
    (e : X.homOfLE hWl ≫ g.hom = X.homOfLE hWr ≫ g'.hom) :
    g.toRationalMap = g'.toRationalMap :=
  Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨W, hW, hWl, hWr, e⟩

/-- Partial maps with the same domain and equal underlying morphisms define the same rational
map. -/
private lemma toRationalMap_congr {Y : Scheme.{u}} {U : X.Opens} {hU : Dense (U : Set X)}
    {k k' : U.toScheme ⟶ Y} (he : k = k') :
    (⟨U, hU, k⟩ : X.PartialMap Y).toRationalMap =
      (⟨U, hU, k'⟩ : X.PartialMap Y).toRationalMap := by rw [he]

/-- On an open subscheme, the map on global sections induced by the inclusion of a smaller open
set is the restriction map of the structure sheaf. -/
lemma homOfLE_appTop_topIso_inv {U V : X.Opens} (h : U ≤ V) (f : Γ(X, V)) :
    (X.homOfLE h).appTop (V.topIso.inv f) =
      U.topIso.inv ((X.presheaf.map (homOfLE h).op) f) := by
  refine ConcreteCategory.congr_hom (?_ :
    V.topIso.inv ≫ (X.homOfLE h).appTop = X.presheaf.map (homOfLE h).op ≫ U.topIso.inv) f
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop]
  exact presheaf_map_square _ _ _ _

/-! ### Rational functions -/

/-- The affine line over the integers, as a one-dimensional affine space over the spectrum of
`ULift ℤ`. It is isomorphic, by `AlgebraicGeometry.AffineSpace.SpecIso`, to the spectrum of a
polynomial ring in one variable. -/
noncomputable abbrev affineLine : Scheme.{u} :=
  AffineSpace (ULift.{u} (Fin 1)) (Spec (.of (ULift.{u} ℤ)))

/-- A rational function on a scheme is a rational map to the affine line over the integers. -/
@[stacks 01RT, ega "I 7.1.2", ega "IV 20.2.8" "special case"]
abbrev Scheme.rationalFunctions (X : Scheme.{u}) : Type u :=
  X.RationalMap (affineLine : Scheme.{u})

/-- The standard coordinate on the affine line over the integers. -/
private noncomputable abbrev affineLineCoord : Γ(affineLine.{u}, ⊤) :=
  AffineSpace.coord (Spec (.of (ULift.{u} ℤ))) (ULift.up 0)

/-- The morphism to the affine line given by a section on an open set. -/
private noncomputable abbrev sectionHom (U : X.Opens) (s : Γ(X, U)) : U.toScheme ⟶ affineLine :=
  AffineSpace.homOfVector (specULiftZIsTerminal.from U.toScheme)
    (fun _ : ULift.{u} (Fin 1) ↦ U.topIso.inv s)

/-- The coordinate of the morphism to the affine line given by a section is that section. -/
private lemma sectionHom_appTop_coord (U : X.Opens) (s : Γ(X, U)) :
    (sectionHom U s).appTop affineLineCoord = U.topIso.inv s :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- A morphism to the affine line is the one given by a section as soon as it has that section as
its coordinate. -/
private lemma sectionHom_eq_of_appTop_coord_eq (U : X.Opens) (s : Γ(X, U))
    (k : U.toScheme ⟶ affineLine.{u})
    (hk : k.appTop affineLineCoord = U.topIso.inv s) : k = sectionHom U s := by
  refine AffineSpace.hom_ext (specULiftZIsTerminal.hom_ext _ _) fun i => ?_
  obtain rfl : i = ULift.up 0 := Subsingleton.elim _ _
  rw [hk, sectionHom_appTop_coord]

/-- The coordinate of the restriction of `sectionHom V s` to a smaller open set is the restricted
section. -/
private lemma homOfLE_comp_sectionHom_appTop_coord {U V : X.Opens} (h : U ≤ V) (s : Γ(X, V)) :
    (X.homOfLE h ≫ sectionHom V s).appTop affineLineCoord =
      U.topIso.inv ((X.presheaf.map (homOfLE h).op) s) := by
  rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, sectionHom_appTop_coord,
    homOfLE_appTop_topIso_inv]

/-- A section of the structure sheaf on a dense open set, read as a rational function. -/
@[ega "I 7.1.3" "partial"]
noncomputable def Scheme.rationalFunctionOfSection (X : Scheme.{u}) (U : X.Opens)
    (hU : Dense (U : Set X)) (s : Γ(X, U)) : X.rationalFunctions :=
  (⟨U, hU, AffineSpace.homOfVector (specULiftZIsTerminal.from U.toScheme)
    (fun _ : ULift.{u} (Fin 1) ↦ U.topIso.inv s)⟩ : X.PartialMap affineLine).toRationalMap

/-- The rational function of a section is the rational map of `sectionHom`. -/
private lemma rationalFunctionOfSection_eq (X : Scheme.{u}) (U : X.Opens)
    (hU : Dense (U : Set X)) (s : Γ(X, U)) :
    X.rationalFunctionOfSection U hU s =
      (⟨U, hU, sectionHom U s⟩ : X.PartialMap affineLine).toRationalMap := rfl

/-- Passing to a smaller dense open set does not change the rational function defined by a
section. -/
theorem Scheme.rationalFunctionOfSection_res (X : Scheme.{u}) {P Q : X.Opens}
    (hP : Dense (P : Set X)) (hQ : Dense (Q : Set X)) (hQP : Q ≤ P) (f : Γ(X, P)) :
    X.rationalFunctionOfSection Q hQ ((X.presheaf.map (homOfLE hQP).op) f) =
      X.rationalFunctionOfSection P hP f := by
  rw [rationalFunctionOfSection_eq, rationalFunctionOfSection_eq]
  refine toRationalMap_eq_of_restrict_hom_eq _ _ hQ (le_rfl : Q ≤ Q) hQP ?_
  change X.homOfLE (le_rfl : Q ≤ Q) ≫ sectionHom Q ((X.presheaf.map (homOfLE hQP).op) f) =
    X.homOfLE hQP ≫ sectionHom P f
  rw [Scheme.homOfLE_rfl, Category.id_comp]
  exact (sectionHom_eq_of_appTop_coord_eq Q _ _
    (homOfLE_comp_sectionHom_appTop_coord hQP f)).symm

/-- Every rational function is a section of the structure sheaf on some dense open set. -/
@[ega "I 7.1.3" "partial"]
theorem Scheme.exists_rationalFunctionOfSection_eq (X : Scheme.{u}) (r : X.rationalFunctions) :
    ∃ (U : X.Opens) (hU : Dense (U : Set X)) (s : Γ(X, U)),
      X.rationalFunctionOfSection U hU s = r := by
  obtain ⟨g, hg⟩ := Scheme.RationalMap.exists_rep r
  refine ⟨g.domain, g.dense_domain, g.domain.topIso.hom (g.hom.appTop affineLineCoord), ?_⟩
  rw [rationalFunctionOfSection_eq, ← hg]
  refine (toRationalMap_congr (hU := g.dense_domain) ?_).symm
  refine sectionHom_eq_of_appTop_coord_eq g.domain _ g.hom ?_
  exact (ConcreteCategory.congr_hom g.domain.topIso.hom_inv_id _).symm

/-- Two sections on a dense open set define the same rational function only if they agree on a
possibly smaller dense open set. -/
theorem Scheme.exists_dense_res_eq_of_rationalFunctionOfSection_eq (X : Scheme.{u})
    {P : X.Opens} (hP : Dense (P : Set X)) (f f' : Γ(X, P))
    (h : X.rationalFunctionOfSection P hP f = X.rationalFunctionOfSection P hP f') :
    ∃ (Q : X.Opens) (_ : Dense (Q : Set X)) (hQP : Q ≤ P),
      (X.presheaf.map (homOfLE hQP).op) f = (X.presheaf.map (homOfLE hQP).op) f' := by
  rw [rationalFunctionOfSection_eq, rationalFunctionOfSection_eq] at h
  obtain ⟨W, hW, hWl, hWr, e⟩ := exists_dense_restrict_hom_eq h
  have e' : X.homOfLE (hWl : W ≤ P) ≫ sectionHom P f =
      X.homOfLE (hWr : W ≤ P) ≫ sectionHom P f' := e
  have hc := appTop_congr e' affineLineCoord
  rw [homOfLE_comp_sectionHom_appTop_coord, homOfLE_comp_sectionHom_appTop_coord] at hc
  exact ⟨W, hW, hWl, commRingCat_iso_inv_injective W.topIso hc⟩

end AlgebraicGeometry
