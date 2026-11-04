module

public import Mathlib.GroupTheory.OrderOfElement
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Polynomial.TwistedTranslation
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.PullbackSquare
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation

/-!
# The affine line twisted by an automorphism of the base field

Let `K` be a field with a ring automorphism `σ`, and let `Spec K → S` be a morphism invariant
under `σ`. The integers then act on `Spec K` over `S` through `σ`, and on the affine line
`Spec K[t]` over `S` through the twisted translation of `Polynomial.twistedTranslationEquiv`,
which acts on the coefficients by `σ` and sends `t` to `t + 1`. The inclusion of the constants
and the origin `t = 0` relate the two actions.

Neither action has a nonidentity element fixing a point together with the residue field there:
for the affine line this is because the `n`-th power of the twisted translation adds `n` to
the coordinate, and `n` is invertible in characteristic zero; for the base it is because `σ`
has infinite order. That is the hypothesis under which the graph relation of an action is an
étale equivalence relation, by Stacks 02Z2.

## Main definitions

* `AlgebraicGeometry.Space.twistedBase` is `Spec K` over `S` and
  `AlgebraicGeometry.Space.twistedLine` is `Spec K[t]` over `S`.
* `AlgebraicGeometry.Space.twistedBaseAction` and
  `AlgebraicGeometry.Space.twistedLineAction` are the two integer actions.
* `AlgebraicGeometry.Space.twistedLineToBase` is the inclusion of the constants and
  `AlgebraicGeometry.Space.twistedBaseToLine` is the origin `t = 0`.

## Main results

* `AlgebraicGeometry.Space.twistedBaseAction_actsNontrivially` and
  `AlgebraicGeometry.Space.twistedLineAction_actsNontrivially`: neither action has a
  nonidentity element fixing a point together with the residue field there.
* `AlgebraicGeometry.Space.twistedLineToBase_comp_twistedBaseAction`: the inclusion of the
  constants is equivariant.
* `AlgebraicGeometry.Space.exists_isPullback_toQuotientSheaf_actionQuotient`: Stacks 07S3 for
  two group actions related by an equivariant map — the square formed by the two projections
  onto the quotient sheaves is cartesian. Its input is
  `AlgebraicGeometry.Space.isPullback_actionRelationMap_source`, that the source map of a
  graph relation is stable under base change along an equivariant map.
* `AlgebraicGeometry.Space.exists_smul_of_pointsMap_actionProjection_eq`: two points of an
  object of the site with the same image in the quotient by an action differ by a group
  element, with no algebraicity hypothesis on the quotient — Stacks 03BW for the graph
  relation of an action, whose ingredients are
  `AlgebraicGeometry.Space.exists_rel_of_toQuotientSheaf_app_eq`, the kernel-pair square of a
  quotient sheaf, and `AlgebraicGeometry.Space.exists_sigmaι_factorization_actionRelationScheme`,
  the factorization of a point of the relation scheme through one copy of the object.
* `AlgebraicGeometry.Scheme.spec_hom_eq_id_of_residueFieldMap_eq`: an endomorphism of the
  spectrum of a field fixing a point and inducing the canonical map on the residue field
  there is the identity.

## Implementation notes

The twisted action of the integers on the affine line is the one for which the fibre of
points of Stacks 0AC4 is infinite: the orbit of the origin under the translations is a set of
pairwise distinct points of the affine line all of which have the same image in the quotient
and the same image in `Spec K`.

## References

* [Stacks Project, Tag 0AC4](https://stacks.math.columbia.edu/tag/0AC4)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 03BW](https://stacks.math.columbia.edu/tag/03BW)
* [Stacks Project, Tag 07S3](https://stacks.math.columbia.edu/tag/07S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Multiplicative Opposite Polynomial

universe u v w

namespace AlgebraicGeometry

/-- An endomorphism of the spectrum of a field which fixes a point and induces the canonical
isomorphism of residue fields there is the identity. -/
theorem Scheme.spec_hom_eq_id_of_residueFieldMap_eq {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ Spec (.of K)) (x : Spec (.of K)) (hx : f x = x)
    (hf : f.residueFieldMap x = (Scheme.residueFieldCongr hx).hom) : f = 𝟙 _ := by
  have hx' : f (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hf' : f.residueFieldMap (IsLocalRing.closedPoint K) =
      (Scheme.residueFieldCongr hx').hom := by
    obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    simpa using hf
  apply (Scheme.SpecToEquivOfField K _).injective
  apply Scheme.SpecToEquivOfField_eq_iff.mpr
  refine ⟨Subsingleton.elim _ _, ?_⟩
  have hcomp := Scheme.descResidueField_stalkClosedPointTo_comp (f := f) (g := 𝟙 _)
  change _ = f.residueFieldMap (IsLocalRing.closedPoint K) ≫ _ at hcomp
  grind [Scheme.SpecToEquivOfField_apply_fst,
    Scheme.SpecToEquivOfField_apply_snd, CategoryTheory.id_apply]

namespace Space

variable {K : Type u} [Field K] {S : Scheme.{u}} (s : Spec (.of K) ⟶ S) (σ : K ≃+* K)

/-- The spectrum of `K`, as a scheme over `S`. -/
abbrev twistedBase : Over S := Over.mk s

/-- The affine line `Spec K[t]`, as a scheme over `S` through the inclusion of the
constants. -/
abbrev twistedLine : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫ s)

/-- Taking spectra turns a commuting square of commutative rings into a commuting square of
affine schemes. -/
private theorem spec_map_comp_eq_of_comp_eq {A B C D : Type u} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] (f : A →+* B) (g : B →+* D) (f' : A →+* C) (g' : C →+* D)
    (h : g.comp f = g'.comp f') :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom f') := by
  have hh := congrArg CommRingCat.ofHom h
  rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp] at hh
  simpa only [Spec.map_comp] using congrArg Spec.map hh

/-- Taking spectra turns the compatibility of the twisted translation with `Polynomial.C`
into a commuting square of affine schemes. -/
theorem specMap_twistedTranslationEquiv_comp :
    Spec.map (CommRingCat.ofHom (twistedTranslationEquiv σ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (C : K →+* K[X])) =
      Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫
        Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  spec_map_comp_eq_of_comp_eq _ _ _ _ (twistedTranslationEquiv_comp_C σ)

/-- Taking spectra turns the compatibility of the `n`-th power of the twisted translation
with `Polynomial.C` into a commuting square of affine schemes. -/
theorem specMap_twistedTranslationEquiv_zpow_comp (n : ℤ) :
    Spec.map (CommRingCat.ofHom (twistedTranslationEquiv σ ^ n).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (C : K →+* K[X])) =
      Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫
        Spec.map (CommRingCat.ofHom (σ ^ n).toRingHom) :=
  spec_map_comp_eq_of_comp_eq _ _ _ _ (twistedTranslationEquiv_zpow_comp_C σ n)

/-- The automorphism of `Spec K` over `S` induced by `σ`. -/
def twistedBaseGenerator (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s = s) :
    Aut (twistedBase s) :=
  Over.isoMk (Scheme.Spec.mapIso σ.toCommRingCatIso.op) hs

/-- The action of the integers on `Spec K` over `S` through the powers of `σ`, as in
Stacks 0AC4. -/
def twistedBaseAction (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s = s) :
    Multiplicative ℤ →* Aut (twistedBase s) :=
  zpowersHom _ (twistedBaseGenerator s σ hs)

/-- The automorphism of the affine line over `S` induced by the twisted translation: it acts
on the coefficients by `σ` and sends the coordinate to itself plus one. -/
def twistedLineGenerator (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s = s) :
    Aut (twistedLine s) :=
  Over.isoMk (Scheme.Spec.mapIso (twistedTranslationEquiv σ).toCommRingCatIso.op)
    (show Spec.map (CommRingCat.ofHom (twistedTranslationEquiv σ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫ s =
      Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫ s from by
      rw [← Category.assoc, specMap_twistedTranslationEquiv_comp, Category.assoc, hs])

/-- The action of the integers on the affine line over `S` through the powers of the twisted
translation, as in Stacks 0AC4. -/
def twistedLineAction (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s = s) :
    Multiplicative ℤ →* Aut (twistedLine s) :=
  zpowersHom _ (twistedLineGenerator s σ hs)

/-- The standard coordinate on the affine line `Spec K[t]`. -/
def twistedLineCoord (K : Type u) [Field K] : Γ(Spec (.of K[X]), ⊤) :=
  (Scheme.ΓSpecIso (.of K[X])).inv X

/-- A ring homomorphism `φ` pulls the global section of an affine scheme given by `r` back to
the global section given by `φ r`. -/
private theorem specMap_appTop_ΓSpecIso_inv {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (r : R) :
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of R')).inv (φ r) := by
  change (((Scheme.ΓSpecIso (.of R)).inv ≫
    (Spec.map (CommRingCat.ofHom φ)).appTop).hom) r = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- A ring automorphism `φ` of `K[t]` pulls the standard coordinate back to `φ t`. -/
theorem specMap_appTop_twistedLineCoord (φ : K[X] ≃+* K[X]) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom)).appTop (twistedLineCoord K) =
      (Scheme.ΓSpecIso (.of K[X])).inv (φ X) :=
  specMap_appTop_ΓSpecIso_inv φ.toRingHom X

section Actions

variable (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s = s)

/-- The twisted translation of the affine line is induced by `twistedTranslationEquiv σ`. -/
theorem twistedLineGenerator_hom_left :
    (twistedLineGenerator s σ hs).hom.left =
      Spec.map (CommRingCat.ofHom (twistedTranslationEquiv σ).toRingHom) := rfl

/-- The inverse of the twisted translation of the affine line is induced by the inverse of
`twistedTranslationEquiv σ`. -/
theorem twistedLineGenerator_inv_left :
    (twistedLineGenerator s σ hs).inv.left =
      Spec.map (CommRingCat.ofHom (twistedTranslationEquiv σ).symm.toRingHom) := rfl

/-- The generator of the action on `Spec K` is induced by `σ`. -/
theorem twistedBaseGenerator_hom_left :
    (twistedBaseGenerator s σ hs).hom.left =
      Spec.map (CommRingCat.ofHom σ.toRingHom) := rfl

/-- The inverse of the generator of the action on `Spec K` is induced by `σ⁻¹`. -/
theorem twistedBaseGenerator_inv_left :
    (twistedBaseGenerator s σ hs).inv.left =
      Spec.map (CommRingCat.ofHom σ.symm.toRingHom) := rfl

/-- The `n`-th power of an automorphism of an affine scheme over `S` coming from a ring
automorphism `e` is induced by the `n`-th power of `e`. -/
theorem specZpow_hom_left {R : Type u} [CommRing R] (p : Spec (.of R) ⟶ S)
    (a : Aut (Over.mk p)) (e : R ≃+* R)
    (ha : a.hom.left = Spec.map (CommRingCat.ofHom e.toRingHom))
    (hai : a.inv.left = Spec.map (CommRingCat.ofHom e.symm.toRingHom)) (n : ℤ) :
    (a ^ n).hom.left = Spec.map (CommRingCat.ofHom (e ^ n).toRingHom) := by
  induction n using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      show (𝟙 (Spec (.of R))) = _
      rw [← Spec.map_id, Spec.map_inj]
      rfl
  | succ i ih =>
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, Aut.Aut_mul_def (Over.mk p)]
      show (a ^ (i : ℤ)).hom.left ≫ a.hom.left = _
      rw [ih, ha, ← Spec.map_comp, Spec.map_inj]
      apply CommRingCat.hom_ext
      ext x
      have h := congrArg (fun ψ : R ≃+* R => ψ x) ((Commute.refl e).zpow_right (i : ℤ)).eq
      simpa [zpow_add] using h.symm
  | pred i ih =>
      rw [show -(i : ℤ) - 1 = -1 + (-(i : ℤ)) by omega, zpow_add, zpow_neg_one,
        Aut.Aut_mul_def (Over.mk p)]
      show (a ^ (-(i : ℤ))).hom.left ≫ a.inv.left = _
      rw [ih, hai, ← Spec.map_comp, Spec.map_inj]
      apply CommRingCat.hom_ext
      ext x
      have hinv : e.symm = e⁻¹ := rfl
      have hpow : e ^ (-(i : ℤ)) * e⁻¹ = e ^ (-1 + -(i : ℤ)) := by
        calc
          e ^ (-(i : ℤ)) * e⁻¹ = e ^ (-(i : ℤ) + -1) := by
            simpa only [zpow_neg_one] using (zpow_add e (-(i : ℤ)) (-1)).symm
          _ = _ := by rw [add_comm]
      rw [hinv]
      show (e ^ (-(i : ℤ)) * e⁻¹) x = _
      rw [hpow]
      rfl

/-- The integer `n` acts on `Spec K` through the `n`-th power of `σ`. -/
theorem twistedBaseAction_hom_left (n : ℤ) :
    (twistedBaseAction s σ hs (ofAdd n)).hom.left =
      Spec.map (CommRingCat.ofHom (σ ^ n).toRingHom) :=
  specZpow_hom_left s (twistedBaseGenerator s σ hs) σ
    (twistedBaseGenerator_hom_left s σ hs) (twistedBaseGenerator_inv_left s σ hs) n

/-- The integer `n` acts on the affine line through the `n`-th power of the twisted
translation. -/
theorem twistedLineAction_hom_left (n : ℤ) :
    (twistedLineAction s σ hs (ofAdd n)).hom.left =
      Spec.map (CommRingCat.ofHom (twistedTranslationEquiv σ ^ n).toRingHom) :=
  specZpow_hom_left _ (twistedLineGenerator s σ hs) (twistedTranslationEquiv σ)
    (twistedLineGenerator_hom_left s σ hs) (twistedLineGenerator_inv_left s σ hs) n

/-- The integer `n` sends the standard coordinate of the affine line to that coordinate plus
`n`. -/
theorem twistedLineAction_appTop_coord (n : ℤ) :
    ((twistedLineAction s σ hs (ofAdd n)).hom.left).appTop (twistedLineCoord K) =
      twistedLineCoord K + (n : Γ(Spec (.of K[X]), ⊤)) := by
  rw [twistedLineAction_hom_left, specMap_appTop_twistedLineCoord,
    twistedTranslationEquiv_zpow_X, map_add, twistedLineCoord]
  simp

/-- In characteristic zero no nonidentity twisted translation of the affine
line fixes a point together with the residue field there: the integer it adds to the
coordinate is invertible in the residue field, so it cannot evaluate to zero. -/
theorem twistedLineAction_actsNontrivially [CharZero K] :
    ActsNontriviallyOnFixedResidueFields (twistedLine s) (Multiplicative ℤ)
      (twistedLineAction s σ hs) := by
  intro g x hx hne hres
  have hn : g.toAdd ≠ 0 := mt toAdd_eq_zero.mp hne
  have hg : Multiplicative.ofAdd g.toAdd = g := by simp
  set U : Scheme.{u} := Spec (.of K[X]) with hU
  set f : U ⟶ U := (twistedLineAction s σ hs g).hom.left with hf
  have heval : U.Γevaluation x (f.appTop (twistedLineCoord K)) =
      U.Γevaluation x (twistedLineCoord K) := by
    calc
      U.Γevaluation x (f.appTop (twistedLineCoord K)) =
          (f.residueFieldMap x).hom (U.Γevaluation (f x) (twistedLineCoord K)) :=
        (Scheme.Γevaluation_naturality_apply f x _).symm
      _ = (U.residueFieldCongr hx).hom (U.Γevaluation (f x) (twistedLineCoord K)) :=
        congrArg (fun φ : CommRingCat.Hom _ _ =>
          φ.hom (U.Γevaluation (f x) (twistedLineCoord K))) hres
      _ = U.Γevaluation x (twistedLineCoord K) :=
        Scheme.residueFieldCongr_Γevaluation_apply hx _
  have hformula : f.appTop (twistedLineCoord K) =
      twistedLineCoord K + ((g.toAdd : ℤ) : Γ(U, ⊤)) := by
    rw [hf, ← hg]
    exact twistedLineAction_appTop_coord s σ hs g.toAdd
  have hcoord := congrArg (fun r : Γ(U, ⊤) => U.Γevaluation x r) hformula
  simp only [map_add, map_intCast] at hcoord
  rw [heval] at hcoord
  have hzero : U.Γevaluation x ((g.toAdd : ℤ) : Γ(U, ⊤)) = 0 := by
    simp only [map_intCast]
    linear_combination -hcoord
  have hunit : IsUnit ((g.toAdd : ℤ) : Γ(U, ⊤)) := by
    simpa using IsUnit.map
      (((Scheme.ΓSpecIso (.of K[X])).inv.hom.comp (C : K →+* K[X])) : K →+* Γ(U, ⊤))
      (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn))
  exact (IsUnit.map (U.Γevaluation x).hom hunit).ne_zero hzero

/-- An automorphism of infinite order acts nontrivially on the residue field
at the unique point of `Spec K`: a power of it inducing the canonical map on that residue
field is the identity, and no nonzero power of `σ` is. -/
theorem twistedBaseAction_actsNontrivially (hσ : orderOf σ = 0) :
    ActsNontriviallyOnFixedResidueFields (twistedBase s) (Multiplicative ℤ)
      (twistedBaseAction s σ hs) := by
  intro g x hx hne hres
  have hn : g.toAdd ≠ 0 := mt toAdd_eq_zero.mp hne
  have hg : Multiplicative.ofAdd g.toAdd = g := by simp
  have hspec : Spec.map (CommRingCat.ofHom ((σ ^ g.toAdd)).toRingHom) = 𝟙 (Spec (.of K)) := by
    rw [← twistedBaseAction_hom_left s σ hs g.toAdd, hg]
    exact Scheme.spec_hom_eq_id_of_residueFieldMap_eq _ x hx hres
  have hpow : σ ^ g.toAdd = 1 := by
    have hr : ((σ ^ g.toAdd)).toRingHom = RingHom.id K := by
      simpa using congrArg CommRingCat.Hom.hom (Spec.map_eq_id.mp hspec)
    ext a
    simpa using DFunLike.congr_fun hr a
  exact orderOf_eq_zero_iff.mp hσ ((isOfFinOrder_iff_zpow_eq_one).2 ⟨g.toAdd, hn, hpow⟩)

end Actions

/-- The inclusion of the constants, `Spec K[t] ⟶ Spec K` over `S`. -/
def twistedLineToBase : twistedLine s ⟶ twistedBase s :=
  Over.homMk (Spec.map (CommRingCat.ofHom (C : K →+* K[X])))

/-- The origin `t = 0` of the affine line, a section of the inclusion of the constants. -/
def twistedBaseToLine : twistedBase s ⟶ twistedLine s :=
  Over.homMk (Spec.map (CommRingCat.ofHom (evalRingHom (0 : K))))
    (show Spec.map (CommRingCat.ofHom (evalRingHom (0 : K))) ≫
        Spec.map (CommRingCat.ofHom (C : K →+* K[X])) ≫ s = s from by
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        show (evalRingHom (0 : K)).comp (C : K →+* K[X]) = RingHom.id K from by ext a; simp,
        CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

/-- The underlying morphism of `twistedLineToBase` is induced by the inclusion of the constants
`K → K[t]`. -/
@[simp]
theorem twistedLineToBase_left :
    (twistedLineToBase s).left = Spec.map (CommRingCat.ofHom (C : K →+* K[X])) := rfl

/-- The underlying morphism of `twistedBaseToLine` is induced by evaluation at `0`. -/
@[simp]
theorem twistedBaseToLine_left :
    (twistedBaseToLine s).left = Spec.map (CommRingCat.ofHom (evalRingHom (0 : K))) := rfl

/-- The origin sends the standard coordinate of the affine line to zero. -/
theorem twistedBaseToLine_appTop_coord :
    (twistedBaseToLine s).left.appTop (twistedLineCoord K) = 0 := by
  rw [twistedBaseToLine_left, twistedLineCoord, specMap_appTop_ΓSpecIso_inv]
  simp

/-- The inclusion of the constants is equivariant for the two actions. -/
theorem twistedLineToBase_comp_twistedBaseAction
    (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ s = s) (g : Multiplicative ℤ) :
    (twistedLineAction s σ hs g).hom ≫ twistedLineToBase s =
      twistedLineToBase s ≫ (twistedBaseAction s σ hs g).hom := by
  apply Over.OverMorphism.ext
  have hg : Multiplicative.ofAdd g.toAdd = g := by simp
  show (twistedLineAction s σ hs g).hom.left ≫ (twistedLineToBase s).left =
    (twistedLineToBase s).left ≫ (twistedBaseAction s σ hs g).hom.left
  rw [← hg, twistedBaseAction_hom_left, twistedLineAction_hom_left, twistedLineToBase_left]
  exact specMap_twistedTranslationEquiv_zpow_comp σ g.toAdd

/-! ### Cartesian squares of quotients along an equivariant map -/

section Equivariant

variable {S : Scheme.{u}} {U U' : Over S} (G : Type v) [Group G] [Small.{u} G]

/-- The map of graph relations induced by a map of the schemes acted on: on the copy indexed
by a group element it is the given map into the copy with the same index. -/
def actionRelationMap (q : U ⟶ U') :
    actionRelationScheme U G ⟶ actionRelationScheme U' G :=
  Limits.Sigma.map (fun _ : G ↦ q)

omit [Group G] in
/-- The map of graph relations induced by `q` commutes with the source projections. -/
@[reassoc]
theorem actionRelationMap_comp_source (q : U ⟶ U') :
    actionRelationMap G q ≫ actionRelationSource U' G = actionRelationSource U G ≫ q := by
  refine Sigma.hom_ext _ _ fun g ↦ ?_
  simp [actionRelationMap, actionRelationSource]

/-- For an equivariant map `q`, the induced map of graph relations commutes with the target
projections. -/
@[reassoc]
theorem actionRelationMap_comp_target (a : G →* Aut U) (b : G →* Aut U') (q : U ⟶ U')
    (h : ∀ g : G, (a g).hom ≫ q = q ≫ (b g).hom) :
    actionRelationMap G q ≫ actionRelationTarget U' G b =
      actionRelationTarget U G a ≫ q := by
  refine Sigma.hom_ext _ _ fun g ↦ ?_
  calc
    Sigma.ι (fun _ : G ↦ U) g ≫ actionRelationMap G q ≫ actionRelationTarget U' G b
        = q ≫ (b g).hom := by
          simp [actionRelationMap, actionRelationTarget]
    _ = (a g).hom ≫ q := (h g).symm
    _ = Sigma.ι (fun _ : G ↦ U) g ≫ actionRelationTarget U G a ≫ q := by
          simp [actionRelationTarget]

omit [Group G] in
/-- The source map of a graph relation is stable under base change along a map of the schemes
acted on: the relation scheme of `U` is the fibre product of `U` and the relation scheme of
`U'` over `U'`, because a coproduct of schemes over a base is a universal colimit. -/
theorem isPullback_actionRelationMap_source (q : U ⟶ U') :
    IsPullback (actionRelationMap G q) (actionRelationSource U G)
      (actionRelationSource U' G) q := by
  let c : Cofan (fun _ : G ↦ U') :=
    Cofan.mk (actionRelationScheme U' G) (Sigma.ι (fun _ : G ↦ U'))
  let d : Cofan (fun _ : G ↦ U) :=
    Cofan.mk (actionRelationScheme U G) (Sigma.ι (fun _ : G ↦ U))
  have hd : IsColimit d := coproductIsCoproduct _
  have hU : IsUniversalColimit c := isUniversalColimit_sigmaCofanOver (fun _ : G ↦ U')
  have hpull : IsPullback (Cofan.IsColimit.desc hd (fun _ : G ↦ 𝟙 U))
      (Cofan.IsColimit.desc hd (fun g ↦ q ≫ c.inj g)) q (actionRelationSource U' G) :=
    hU.isPullback_of_isColimit_left (fun _ : G ↦ 𝟙 U') (actionRelationSource U' G) q
      (fun _ : G ↦ 𝟙 U) (fun _ : G ↦ q)
      (fun _ ↦ (IsPullback.of_id_snd (f := q)).flip) hd
      (by intro g; simp [c, actionRelationSource])
  have hleft : Cofan.IsColimit.desc hd (fun _ : G ↦ 𝟙 U) = actionRelationSource U G := by
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    calc
      _ = 𝟙 U := Cofan.IsColimit.fac hd (fun _ : G ↦ 𝟙 U) g
      _ = _ := by simp [actionRelationSource]
  have htop : Cofan.IsColimit.desc hd (fun g ↦ q ≫ c.inj g) = actionRelationMap G q := by
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    calc
      _ = q ≫ c.inj g := Cofan.IsColimit.fac hd (fun g ↦ q ≫ c.inj g) g
      _ = _ := by simp [actionRelationMap, c]
  rw [htop, hleft] at hpull
  exact hpull.flip

end Equivariant

/-! ### The quotients of the twisted actions -/

section Quotient

variable {S : Scheme.{u}} (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u})
  (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- Stacks 07S3 for the graph relations of two group actions. Let a group act on two
objects of a big fppf site over `S` and let `q` be an equivariant map between them. Then the
square formed by the two projections onto the quotient sheaves and by `q` is cartesian: the
functor of points of the source is the fibre product of the functor of points of the target
and of the quotient of the source over the quotient of the target. -/
theorem exists_isPullback_toQuotientSheaf_actionQuotient {V V' : BigFppfOver B S hS}
    (a : G →* Aut (underlyingOver B hS V)) (b : G →* Aut (underlyingOver B hS V'))
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (hb : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V') G b)
    (q : V ⟶ V')
    (hq : ∀ g : G, (a g).hom ≫ (Over.post B.inclusion).map q =
      (Over.post B.inclusion).map q ≫ (b g).hom) :
    ∃ f : (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (actionRelation (underlyingOver B hS V) G a)).obj ⟶
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (actionRelation (underlyingOver B hS V') G b)).obj,
      IsPullback
        (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (actionRelation (underlyingOver B hS V) G a))
        ((Over.post (X := B.obj hS) B.inclusion).op.whiskerLeft
          (yoneda.map ((Over.post B.inclusion).map q)))
        f
        (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) (actionRelation (underlyingOver B hS V') G b)) := by
  have := actionRelation_isEtaleEquivalenceRelation (underlyingOver B hS V) G a ha
  have := actionRelation_isEtaleEquivalenceRelation (underlyingOver B hS V') G b hb
  have hsq : actionRelationMap G ((Over.post B.inclusion).map q) ≫
      (actionRelation (underlyingOver B hS V') G b).source =
        (actionRelation (underlyingOver B hS V) G a).source ≫
          (Over.post B.inclusion).map q := by
    simpa [actionRelation, Stacks.Groupoids.PreRelation.source] using
      actionRelationMap_comp_source G ((Over.post B.inclusion).map q)
  have htq : actionRelationMap G ((Over.post B.inclusion).map q) ≫
      (actionRelation (underlyingOver B hS V') G b).target =
        (actionRelation (underlyingOver B hS V) G a).target ≫
          (Over.post B.inclusion).map q := by
    simpa [actionRelation, Stacks.Groupoids.PreRelation.target] using
      actionRelationMap_comp_target G a b ((Over.post B.inclusion).map q) hq
  have hcart : IsPullback (actionRelationMap G ((Over.post B.inclusion).map q))
      (actionRelation (underlyingOver B hS V) G a).source
      (actionRelation (underlyingOver B hS V') G b).source
      ((Over.post B.inclusion).map q) := by
    simpa [actionRelation, Stacks.Groupoids.PreRelation.source] using
      isPullback_actionRelationMap_source G ((Over.post B.inclusion).map q)
  exact ⟨_, Stacks.Groupoids.isPullback_toQuotientSheaf (BigFppfOver.topology B S hS)
    (Over.post B.inclusion) _ _ _ _ hsq htq hcart
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS _)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS _)⟩

end Quotient


/-! ### Factoring a morphism with one-point source through a summand -/

section Factorization

variable {I : Type v} [Small.{u} I]

/-- A morphism of schemes whose source has at most one point factors through one summand of
a coproduct. -/
theorem exists_sigmaι_factorization_of_subsingleton (Y : I → Scheme.{u}) {X : Scheme.{u}}
    (hsub : Subsingleton (X : Type u)) (x₀ : (X : Type u)) (f : X ⟶ ∐ Y) :
    ∃ (i : I) (g : X ⟶ Y i), f = g ≫ Sigma.ι Y i := by
  obtain ⟨i, x, hx⟩ := (sigmaOpenCover Y).exists_eq (f x₀)
  have hr : Set.range f.base ⊆ Set.range (Sigma.ι Y i).base := by
    rintro _ ⟨y, rfl⟩
    exact ⟨x, hx.trans (congrArg f.base (Subsingleton.elim x₀ y))⟩
  exact ⟨i, IsOpenImmersion.lift (Sigma.ι Y i) f hr,
    (IsOpenImmersion.lift_fac (Sigma.ι Y i) f hr).symm⟩

/-- A morphism into the relation scheme of a group action whose source has at most one point
factors through the copy indexed by one group element. -/
theorem exists_sigmaι_factorization_actionRelationScheme {S : Scheme.{u}} (U : Over S)
    (G : Type v) [Group G] [Small.{u} G] {T : Over S}
    (hsub : Subsingleton (T.left : Type u))
    (x₀ : (T.left : Type u)) (r : T ⟶ actionRelationScheme U G) :
    ∃ (g : G) (w : T ⟶ U), r = w ≫ Sigma.ι (fun _ : G ↦ U) g := by
  let e := actionRelationUnderlyingIso U G
  obtain ⟨g, w, hw⟩ :=
    exists_sigmaι_factorization_of_subsingleton (fun _ : G ↦ U.left) hsub x₀ (r.left ≫ e.hom)
  have hleft : r.left = w ≫ (Sigma.ι (fun _ : G ↦ U) g).left := by
    rw [show (Sigma.ι (fun _ : G ↦ U) g).left = (Over.forget S).map (Sigma.ι (fun _ : G ↦ U) g)
      from rfl, ← actionRelationUnderlyingIso_inv_ι U G g, ← Category.assoc, ← hw,
      Category.assoc, e.hom_inv_id, Category.comp_id]
  have hw' : w ≫ U.hom = T.hom := by
    rw [← (Sigma.ι (fun _ : G ↦ U) g).w, ← Category.assoc, ← hleft]
    exact r.w
  exact ⟨g, Over.homMk w hw', Over.OverMorphism.ext hleft⟩

end Factorization

/-! ### Points of the quotient of a scheme by a group action -/

section Points

variable {S : Scheme.{u}} (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u})
  (hS : B.Contains S) [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (V : BigFppfOver B S hS) (a : G →* Aut (underlyingOver B hS V))

/-- The projection of an object of a big fppf site onto its quotient by a group action, as a
morphism out of the presheaf it represents. -/
def actionProjection : yoneda.obj V ⟶ (actionQuotient G B hS V a) :=
  (Space.pointsYonedaIso (Over.post B.inclusion) V).inv ≫
    Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion)
      (actionRelation (underlyingOver B hS V) G a)

/-- On a morphism `f : T ⟶ V`, the projection onto the quotient is the image of `f` under the
quotient map of the action relation. -/
theorem actionProjection_app {T : BigFppfOver B S hS} (f : T ⟶ V) :
    (actionProjection G B hS V a).app (op T) f =
      (Stacks.Groupoids.toQuotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (actionRelation (underlyingOver B hS V) G a)).app (op T)
        ((Over.post B.inclusion).map f) := rfl

/-- The automorphism of an object of the site realizing the action of a group element, which
exists because the site is a full subcategory of the schemes over `S`. -/
def siteActionHom (g : G) : V ⟶ V := (Over.post B.inclusion).preimage (a g).hom

omit [Small.{u} G] [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The image in the schemes over `S` of the site automorphism of `g` is the automorphism
`a g`. -/
@[simp]
theorem post_map_siteActionHom (g : G) :
    (Over.post B.inclusion).map (siteActionHom G B hS V a g) = (a g).hom :=
  (Over.post (X := B.obj hS) B.inclusion).map_preimage _

/-- The projection onto the quotient is invariant under the action. -/
theorem siteActionHom_comp_actionProjection (g : G) :
    yoneda.map (siteActionHom G B hS V a g) ≫ actionProjection G B hS V a =
      actionProjection G B hS V a := by
  let F : BigFppfOver B S hS ⥤ Over S := Over.post (X := B.obj hS) B.inclusion
  let j := actionRelation (underlyingOver B hS V) G a
  have h := Stacks.Groupoids.sourceMap_toQuotientSheaf
    (BigFppfOver.topology B S hS) F j
  ext T f
  have h' := congrArg (fun k ↦ k (F.map f ≫ Sigma.ι (fun _ : G ↦ F.obj V) g))
    (NatTrans.congr_app h T)
  change (Stacks.Groupoids.toQuotientSheaf _ F j).app T
      ((F.map f ≫ Sigma.ι (fun _ : G ↦ F.obj V) g) ≫ j.source) =
    (Stacks.Groupoids.toQuotientSheaf _ F j).app T
      ((F.map f ≫ Sigma.ι (fun _ : G ↦ F.obj V) g) ≫ j.target) at h'
  simp only [j, Stacks.Groupoids.PreRelation.source, Stacks.Groupoids.PreRelation.target,
    actionRelation, prod.lift_snd, prod.lift_fst, actionRelationSource, actionRelationTarget,
    Category.assoc, Sigma.ι_desc] at h'
  show (Stacks.Groupoids.toQuotientSheaf _ F j).app T
      (F.map (f ≫ siteActionHom G B hS V a g)) = _
  rw [F.map_comp, post_map_siteActionHom]
  exact h'.symm


/-- Two points of `U` over a test object with the same class in the quotient sheaf of an
internal equivalence relation are the target and the source of a point of the relation. The
relation is the kernel pair of the projection onto the quotient sheaf whenever the functors
of points of its two objects are already sheaves; sheafification is left exact, so the
statement is transported from the quotient presheaf, where it is pointwise. -/
theorem exists_rel_of_toQuotientSheaf_app_eq {S : Scheme.{u}} {C : Type v} [Category.{w} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S) {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U)
    [CategoryTheory.IsEquivalenceRelation j.target j.source]
    (hR : Presheaf.IsSheaf J (Stacks.Groupoids.points F R))
    (hU : Presheaf.IsSheaf J (Stacks.Groupoids.points F U))
    (T : C) (x y : F.obj T ⟶ U)
    (h : (Stacks.Groupoids.toQuotientSheaf J F j).app (op T) x =
      (Stacks.Groupoids.toQuotientSheaf J F j).app (op T) y) :
    ∃ r : F.obj T ⟶ R, r ≫ j.target = x ∧ r ≫ j.source = y := by
  have hpre := ((quotientPresheaf_isPullback F j).map (presheafToSheaf J (Type u))).map
    (sheafToPresheaf J (Type u))
  have hsq : IsPullback (Stacks.Groupoids.targetMap F j) (Stacks.Groupoids.sourceMap F j)
      (Stacks.Groupoids.toQuotientSheaf J F j) (Stacks.Groupoids.toQuotientSheaf J F j) :=
    hpre.of_iso' (isoSheafify J hR) (isoSheafify J hU) (isoSheafify J hU) (Iso.refl _)
      (toSheafify_naturality J (Stacks.Groupoids.targetMap F j)).symm
      (toSheafify_naturality J (Stacks.Groupoids.sourceMap F j)).symm (by simp) (by simp)
  exact Types.exists_of_isPullback (hsq.map ((evaluation Cᵒᵖ (Type u)).obj (op T))) x y h

/-- Two morphisms from the spectrum of a field in the site to `V` with the same class in the
quotient by a group action differ by a group element. The point of the relation scheme
witnessing the identification has a one-point source, so it factors through the copy indexed
by a single group element. -/
theorem exists_smul_of_actionProjection_app_eq
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (u : Spec (.of k) ⟶ S)
    (x y : (Over.mk (⟨u⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V)
    (h : (actionProjection G B hS V a).app
        (op (Over.mk (⟨u⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) x =
      (actionProjection G B hS V a).app
        (op (Over.mk (⟨u⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) y) :
    ∃ g : G, x = y ≫ siteActionHom G B hS V a g := by
  classical
  have _ := actionRelation_isEtaleEquivalenceRelation (underlyingOver B hS V) G a ha
  obtain ⟨r, hrt, hrs⟩ := exists_rel_of_toQuotientSheaf_app_eq
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion)
    (actionRelation (underlyingOver B hS V) G a)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS _)
    (BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS _) _
    ((Over.post B.inclusion).map x) ((Over.post B.inclusion).map y) h
  obtain ⟨g, v, hv⟩ := exists_sigmaι_factorization_actionRelationScheme
    (underlyingOver B hS V) G
    (inferInstanceAs (Subsingleton (Spec (CommRingCat.of k) : Type u)))
    (IsLocalRing.closedPoint k) r
  have hsrc0 : (actionRelation (underlyingOver B hS V) G a).source =
      actionRelationSource (underlyingOver B hS V) G := prod.lift_snd _ _
  have htgt0 : (actionRelation (underlyingOver B hS V) G a).target =
      actionRelationTarget (underlyingOver B hS V) G a := prod.lift_fst _ _
  have hsrc : v = (Over.post B.inclusion).map y := by
    rw [← hrs, hv, hsrc0, actionRelationSource, Category.assoc, Sigma.ι_desc, Category.comp_id]
  refine ⟨g, (Over.post (X := B.obj hS) B.inclusion).map_injective ?_⟩
  rw [Functor.map_comp, post_map_siteActionHom, ← hsrc, ← hrt, hv, htgt0,
    actionRelationTarget, Category.assoc, Sigma.ι_desc]

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- A criterion on field-valued points, stated for an arbitrary morphism of presheaves out of
a representable one. If any two morphisms from the spectrum of a field of the site into `V`
with the same image under `π` differ by one of a family of endomorphisms of `V`, then any two
points of `V` with the same image under `π` differ by one of them. -/
theorem exists_eq_pointsMap_of_pointsMap_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : yoneda.obj V ⟶ X) {ι : Type*} (τ : ι → (V ⟶ V))
    (key : ∀ (k : Type u) (_ : Field k) (hk : B.Contains (Spec (.of k)))
      (u : Spec (.of k) ⟶ S)
      (x y : (Over.mk (⟨u⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V),
      π.app (op (Over.mk (⟨u⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) x =
        π.app (op (Over.mk (⟨u⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS)) y →
        ∃ i : ι, x = y ≫ τ i)
    (x y : Space.points B S hS (yoneda.obj V))
    (h : Space.pointsMap B S hS _ π x = Space.pointsMap B S hS _ π y) :
    ∃ i : ι, x = Space.pointsMap B S hS _ (yoneda.map (τ i)) y := by
  classical
  obtain ⟨w₀, rfl⟩ := Quot.exists_rep x
  obtain ⟨z₀, rfl⟩ := Quot.exists_rep y
  rw [Space.pointsMap_class, Space.pointsMap_class] at h
  obtain ⟨c, ⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    (Space.FieldValuedPoint.class_eq_class_iff B S hS X _ _).mp h
  have e₁ : π.app _ (i ≫ w₀.value) = c.value :=
    (π.naturality_apply i.op w₀.value).trans hi
  have e₂ : π.app _ (j ≫ z₀.value) = c.value :=
    (π.naturality_apply j.op z₀.value).trans hj
  obtain ⟨n, hn⟩ := key c.carrier c.field c.contained c.toBase
    (i ≫ w₀.value) (j ≫ z₀.value) (e₁.trans e₂.symm)
  refine ⟨n, ?_⟩
  rw [Space.pointsMap_class]
  apply Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension
  refine ⟨⟨c.carrier, c.contained, c.toBase, i ≫ w₀.value⟩, ⟨i, rfl⟩, ⟨j, ?_⟩⟩
  show j ≫ (z₀.value ≫ τ n) = i ≫ w₀.value
  rw [hn]
  exact (Category.assoc _ _ _).symm

/-- Stacks 03BW for the quotient of a scheme by a group action, with no algebraicity
hypothesis on the quotient — the general statement, which goes through a presentation, is
`AlgebraicGeometry.Space.Presentation.pointsRelation_iff`. Two points of an object of a big
fppf site with the same image in the quotient by a group action whose stabilizers act
faithfully on residue fields differ by a group element. -/
theorem exists_smul_of_pointsMap_actionProjection_eq
    (ha : ActsNontriviallyOnFixedResidueFields (underlyingOver B hS V) G a)
    (x y : Space.points B S hS (yoneda.obj V))
    (h : Space.pointsMap B S hS _ (actionProjection G B hS V a) x =
      Space.pointsMap B S hS _ (actionProjection G B hS V a) y) :
    ∃ g : G, x = Space.pointsMap B S hS _
      (yoneda.map (siteActionHom G B hS V a g)) y :=
  exists_eq_pointsMap_of_pointsMap_eq B hS V (actionProjection G B hS V a)
    (siteActionHom G B hS V a)
    (fun _k _ hk u xx yy hxy =>
      exists_smul_of_actionProjection_app_eq G B hS V a ha hk u xx yy hxy) x y h

end Points

end Space

end AlgebraicGeometry

end
