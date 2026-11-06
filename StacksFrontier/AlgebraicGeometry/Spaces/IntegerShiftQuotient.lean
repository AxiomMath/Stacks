module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.Algebra.MvPolynomial.Rename
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelationSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.RingTheory.MvPolynomial.IntegerShift

/-!
# The quotient of a two-sided polynomial spectrum by the integer shift

Let `K` be a field and write `R = K[y, x_n : n ∈ ℤ]`. The shift of
`MvPolynomial.shiftDown` makes the integers act on `Spec R` over `Spec K` by automorphisms.
In characteristic zero no nonidentity element of the action fixes a point of `Spec R`
together with the residue field there, because the element translates `y` by its own value,
which is invertible. So the graph relation of the action is an étale equivalence relation
(**Stacks 02Z2**) and its fppf sheaf quotient is an algebraic space over `Spec K`.

The action is free, yet it does not separate specializations: the tail primes
`p_n = (x_n, x_{n + 1}, \ldots)` form a single orbit and a decreasing chain at once. That is
what makes this quotient the example of Stacks 06UK, carried out in
`StacksFrontier/Examples/Spaces/EtaleSpecializationInFibre.lean`.

## Main definitions

* `AlgebraicGeometry.IntegerShift.shiftSource` is `Spec R` over `Spec K`, and
  `AlgebraicGeometry.IntegerShift.shiftByOne` the automorphism induced by the shift.
* `AlgebraicGeometry.IntegerShift.shiftAction` is the resulting action of the integers, and
  `AlgebraicGeometry.IntegerShift.coord` the global section `y` that it translates.
* `AlgebraicGeometry.IntegerShift.shiftChart` is `Spec R` as an object of a big fppf site
  over `Spec K`, with `AlgebraicGeometry.IntegerShift.shiftRelationSource` and
  `AlgebraicGeometry.IntegerShift.shiftRelationTarget` the graph relation of the action
  inside that site, and `AlgebraicGeometry.IntegerShift.shiftQuotient` its quotient sheaf.

## Main results

* `AlgebraicGeometry.IntegerShift.shiftAction_appTop_coord`: the integer `n` sends the
  coordinate `y` to `y - n`.
* `AlgebraicGeometry.IntegerShift.shiftAction_residueFieldFaithful`: in characteristic zero
  the action is nontrivial on every residue field it fixes.
* `AlgebraicGeometry.IntegerShift.shiftByOne_shiftPoint`: the shift carries the `n`-th tail
  point to the `(n + 1)`-st.
* `AlgebraicGeometry.IntegerShift.isAlgebraicSpace_shiftQuotient`: the quotient is an
  algebraic space over `Spec K`, conditional on the two effective-descent hypotheses this
  library's Stacks 0265 carries.

## Implementation notes

`Spec R` lies in every big fppf site containing `Spec K`: the ring `R` has cardinality at
most `max ℵ₀ #K`, so `AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le_max` applies even though
`R` is not of finite type over `K`.

The relation scheme is automatically inside the site as well, by
`AlgebraicGeometry.Space.contains_actionRelationScheme`, which needs exactly the
residue-field faithfulness proved here.

Algebraicity of the quotient is `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf`,
this library's form of Stacks 0265; it takes two undischarged instances of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve`, which are therefore
hypotheses of `isAlgebraicSpace_shiftQuotient` as well.

## References

* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 06UK](https://stacks.math.columbia.edu/tag/06UK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal MvPolynomial Multiplicative
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.IntegerShift

variable (K : Type u) [Field K]

/-! ### The shift as an automorphism of a scheme -/

/-- The spectrum of `K[y, x_n : n ∈ ℤ]`, viewed over `Spec K`. -/
abbrev shiftSource : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Option ℤ) K))))

private theorem ofHom_shiftUp_comp_shiftDown :
    CommRingCat.ofHom (shiftUp K).toRingHom ≫ CommRingCat.ofHom (shiftDown K).toRingHom =
      𝟙 _ :=
  CommRingCat.hom_ext <| RingHom.ext fun x ↦ congrArg
    (fun f : MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K ↦ f x)
    (shiftDown_comp_shiftUp K)

private theorem ofHom_shiftDown_comp_shiftUp :
    CommRingCat.ofHom (shiftDown K).toRingHom ≫ CommRingCat.ofHom (shiftUp K).toRingHom =
      𝟙 _ :=
  CommRingCat.hom_ext <| RingHom.ext fun x ↦ congrArg
    (fun f : MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K ↦ f x)
    (shiftUp_comp_shiftDown K)

private theorem ofHom_algebraMap_comp_shiftDown :
    CommRingCat.ofHom (algebraMap K (MvPolynomial (Option ℤ) K)) ≫
        CommRingCat.ofHom (shiftDown K).toRingHom =
      CommRingCat.ofHom (algebraMap K (MvPolynomial (Option ℤ) K)) :=
  CommRingCat.hom_ext <| RingHom.ext fun x ↦ (shiftDown K).commutes x

/-- The automorphism of the scheme `Spec K[y, x_n : n ∈ ℤ]` induced by the shift
`MvPolynomial.shiftDown`. -/
def shiftSpecIso :
    Spec (CommRingCat.of (MvPolynomial (Option ℤ) K)) ≅
      Spec (CommRingCat.of (MvPolynomial (Option ℤ) K)) where
  hom := Spec.map (CommRingCat.ofHom (shiftDown K).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (shiftUp K).toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ofHom_shiftUp_comp_shiftDown, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ofHom_shiftDown_comp_shiftUp, Spec.map_id]

/-- The automorphism of `Spec K[y, x_n : n ∈ ℤ]` over `Spec K` induced by the shift
`MvPolynomial.shiftDown`. It generates the integer action of Stacks 06UK. -/
def shiftByOne : Aut (shiftSource K) := .of <|
  Over.isoMk (shiftSpecIso K)
    (by
      change Spec.map (CommRingCat.ofHom (shiftDown K).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Option ℤ) K))) =
        Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Option ℤ) K)))
      rw [← Spec.map_comp, ofHom_algebraMap_comp_shiftDown])

/-- The underlying morphism of schemes of `shiftByOne` is the spectrum of
`MvPolynomial.shiftDown`. -/
@[simp]
theorem shiftByOne_hom_left :
    (shiftByOne K).asIso.hom.left = Spec.map (CommRingCat.ofHom (shiftDown K).toRingHom) := rfl

/-- The underlying morphism of schemes of the inverse of `shiftByOne` is the spectrum of
`MvPolynomial.shiftUp`. -/
@[simp]
theorem shiftByOne_inv_left :
    (shiftByOne K).asIso.inv.left = Spec.map (CommRingCat.ofHom (shiftUp K).toRingHom) := rfl

/-- **Stacks 06UK.** The action of the integers on `Spec K[y, x_n : n ∈ ℤ]` over `Spec K`
generated by the shift. -/
def shiftAction : Multiplicative ℤ →* Aut (shiftSource K) :=
  zpowersHom _ (shiftByOne K)

/-! ### The translated coordinate -/

/-- The global section `y` of `Spec K[y, x_n : n ∈ ℤ]`, the variable the shift translates. -/
def coord : Γ((shiftSource K).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Option ℤ) K))).inv (X none)

/-- The spectrum of an algebra endomorphism sends the coordinate `y` to the image of `X none`. -/
private theorem specMap_appTop_coord
    (f : MvPolynomial (Option ℤ) K →ₐ[K] MvPolynomial (Option ℤ) K) :
    (Spec.map (CommRingCat.ofHom f.toRingHom)).appTop (coord K) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Option ℤ) K))).inv (f (X none)) := by
  rw [coord, Scheme.specMap_appTop_ΓSpecIso_inv]
  rfl

/-- The generator of the action sends the coordinate `y` to `y - 1`. -/
theorem shiftByOne_appTop_coord :
    (shiftByOne K).asIso.hom.left.appTop (coord K) = coord K - 1 := by
  have h : shiftDown K (X (none : Option ℤ)) = X none - 1 := by simp [shiftDown]
  rw [shiftByOne_hom_left, specMap_appTop_coord, h, map_sub, map_one]
  rfl

/-- The inverse of the generator sends the coordinate `y` to `y + 1`. -/
theorem shiftByOne_symm_appTop_coord :
    (shiftByOne K).asIso.symm.hom.left.appTop (coord K) = coord K + 1 := by
  have h : shiftUp K (X (none : Option ℤ)) = X none + 1 := by simp [shiftUp]
  change (shiftByOne K).asIso.inv.left.appTop (coord K) = _
  rw [shiftByOne_inv_left, specMap_appTop_coord, h, map_add, map_one]
  rfl

/-- **Stacks 06UK.** The integer `n` sends the coordinate `y` to `y - n`. -/
theorem shiftAction_appTop_coord (n : ℤ) :
    ((shiftAction K (Multiplicative.ofAdd n)).asIso.hom.left).appTop (coord K) =
      coord K - (n : Γ((shiftSource K).left, ⊤)) := by
  let a := shiftByOne K
  let c := coord K
  have hgen : a.asIso.hom.left.appTop c = c - 1 := shiftByOne_appTop_coord K
  have hgen_inv : a.asIso.symm.hom.left.appTop c = c + 1 := shiftByOne_symm_appTop_coord K
  show ((a ^ n).asIso.hom.left).appTop c = c - (n : Γ((shiftSource K).left, ⊤))
  induction n using Int.induction_on with
  | zero =>
      rw [zpow_zero]
      have hid : (Iso.hom (1 : Aut (shiftSource K)).asIso) = (Iso.refl (shiftSource K)).hom := rfl
      rw [hid]
      simp
  | succ i ih =>
      rw [add_comm (i : ℤ) 1, zpow_add, zpow_one, Aut.mul_asIso]
      show ((a ^ (i : ℤ)).asIso.hom.left ≫ a.asIso.hom.left).appTop c = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hgen, map_sub, map_one, ih]
      simp only [Int.cast_add, Int.cast_one]
      ring
  | pred i ih =>
      rw [show -(i : ℤ) - 1 = -1 + (-(i : ℤ)) by omega, zpow_add, zpow_neg_one,
        Aut.mul_asIso]
      show ((a ^ (-(i : ℤ))).asIso.hom.left ≫ a.asIso.symm.hom.left).appTop c = _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hgen_inv, map_add, map_one, ih]
      simp only [Int.cast_add, Int.cast_neg, Int.cast_one]
      ring

/-- **Stacks 06UK.** In characteristic zero no nonidentity integer fixes a point of
`Spec K[y, x_n : n ∈ ℤ]` together with the residue field there: the integer translates the
coordinate `y` by its own value, which is invertible in the residue field. -/
theorem shiftAction_residueFieldFaithful [CharZero K] :
    Space.ActsNontriviallyOnFixedResidueFields (shiftSource K) (Multiplicative ℤ)
      (shiftAction K) := by
  intro g x hx hne hres
  have hn : g.toAdd ≠ 0 := by
    intro hzero
    exact hne (by simpa [hzero] using (ofAdd_toAdd g).symm)
  have hnat := (Scheme.Γevaluation_naturality_apply
    (shiftAction K g).asIso.hom.left x (coord K)).symm
  rw [hres, Scheme.residueFieldCongr_Γevaluation_apply hx] at hnat
  have hformula := shiftAction_appTop_coord K g.toAdd
  rw [ofAdd_toAdd] at hformula
  rw [hformula, map_sub, map_intCast] at hnat
  have hzero : ((g.toAdd : ℤ) : (shiftSource K).left.residueField x) = 0 :=
    sub_eq_self.mp hnat
  have hunit : IsUnit ((g.toAdd : ℤ) : Γ((shiftSource K).left, ⊤)) := by
    simpa using IsUnit.map
      (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (shiftSource K).hom.appTop).hom :
        K →+* Γ((shiftSource K).left, ⊤))
      (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn : ((g.toAdd : ℤ) : K) ≠ 0))
  exact (IsUnit.map ((shiftSource K).left.Γevaluation x).hom hunit).ne_zero (by simpa using hzero)

/-! ### The tail points and the orbit of the shift -/

/-- The point of `Spec K[y, x_n : n ∈ ℤ]` cut out by the `n`-th tail prime
`(x_n, x_{n + 1}, \ldots)`. -/
def shiftPoint (n : ℤ) : (shiftSource K).left := tailPrime K n

/-- **Stacks 06UK.** The shift carries the `n`-th tail point to the `(n + 1)`-st, so all
tail points lie in a single orbit of the integer action. -/
theorem shiftByOne_shiftPoint (n : ℤ) :
    (shiftByOne K).asIso.hom.left (shiftPoint K n) = shiftPoint K (n + 1) := by
  rw [shiftByOne_hom_left]
  show PrimeSpectrum.comap (shiftDown K).toRingHom (tailPrime K n) = tailPrime K (n + 1)
  exact comap_shiftDown_tailPrime K n

/-- **Stacks 06UK.** A later tail point specializes to an earlier one. -/
theorem shiftPoint_specializes_of_le {m n : ℤ} (h : m ≤ n) :
    shiftPoint K n ⤳ shiftPoint K m :=
  tailPrime_specializes_of_le K h

/-- **Stacks 06UK.** Tail points at different indices are different. -/
theorem shiftPoint_injective : Function.Injective (shiftPoint K) :=
  tailPrime_injective K

/-! ### The shift inside a big fppf site -/

/-- `Spec K[y, x_n : n ∈ ℤ]` lies in every big fppf site containing `Spec K`: its ring has
cardinality at most `max ℵ₀ #K`. -/
theorem contains_shiftSource (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of K))) :
    B.Contains (shiftSource K).left := by
  show (Spec (CommRingCat.of (MvPolynomial (Option ℤ) K))).size < B.cutoff
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hS ?_
  rw [mk_congr (MvPolynomial.renameEquiv K (Equiv.ulift.{u, 0} (α := Option ℤ)).symm).toEquiv]
  refine (MvPolynomial.cardinalMk_le_max (σ := ULift.{u, 0} (Option ℤ)) (R := K)).trans ?_
  rw [show #(ULift.{u, 0} (Option ℤ)) = ℵ₀ by simp]
  exact sup_le (sup_le (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)

variable (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of K)))

/-- `Spec K[y, x_n : n ∈ ℤ]` as an object of a big fppf site over `Spec K` containing it. -/
def shiftChart : BigFppfOver B (Spec (.of K)) hS :=
  Over.mk (ObjectProperty.homMk (shiftSource K).hom :
    B.obj (contains_shiftSource K B hS) ⟶ B.obj hS)

/-- The image of `shiftChart` in the category of schemes over `Spec K` is `shiftSource`. -/
@[simp]
theorem shiftChart_post :
    (Over.post B.inclusion).obj (shiftChart K B hS) = shiftSource K := rfl

/-- The underlying scheme of `shiftChart` is affine. -/
instance isAffine_shiftChart :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of K)) hS).obj (shiftChart K B hS)) :=
  show IsAffine (Spec (CommRingCat.of (MvPolynomial (Option ℤ) K))) from inferInstance

/-- The point of the chart's underlying scheme cut out by the `n`-th tail prime. -/
def chartPoint (n : ℤ) :
    (BigFppfOver.toScheme B (Spec (.of K)) hS).obj (shiftChart K B hS) :=
  shiftPoint K n

/-- **Stacks 06UK.** A later tail point of the chart specializes to an earlier one. -/
theorem chartPoint_specializes_of_le {m n : ℤ} (h : m ≤ n) :
    chartPoint K B hS n ⤳ chartPoint K B hS m :=
  shiftPoint_specializes_of_le K h

/-- **Stacks 06UK.** Tail points of the chart at different indices are different. -/
theorem chartPoint_injective : Function.Injective (chartPoint K B hS) :=
  shiftPoint_injective K

variable [CharZero K]

/-- The scheme of arrows of the graph relation of the integer shift lies in every big fppf
site containing `Spec K`. -/
theorem contains_shiftRelationScheme :
    B.Contains (Space.actionRelationScheme
      (Space.underlyingOver B hS (shiftChart K B hS)) (Multiplicative ℤ)).left :=
  Space.contains_actionRelationScheme (Multiplicative ℤ) B hS (shiftChart K B hS)
    (shiftAction K) (shiftAction_residueFieldFaithful K)

/-- The scheme of arrows of the graph relation of the integer shift, as an object of the
big fppf site over `Spec K`. -/
def shiftRelationObj : BigFppfOver B (Spec (.of K)) hS :=
  Space.siteActionRelationScheme (Multiplicative ℤ) B hS (shiftChart K B hS)
    (contains_shiftRelationScheme K B hS)

/-- The source map of the graph relation of the integer shift: the identity on each copy of
the chart. -/
def shiftRelationSource : shiftRelationObj K B hS ⟶ shiftChart K B hS :=
  Space.siteActionRelationSource (Multiplicative ℤ) B hS (shiftChart K B hS)
    (contains_shiftRelationScheme K B hS)

/-- The target map of the graph relation of the integer shift: the action of the indexing
integer on each copy of the chart. -/
def shiftRelationTarget : shiftRelationObj K B hS ⟶ shiftChart K B hS :=
  Space.siteActionRelationTarget (Multiplicative ℤ) B hS (shiftChart K B hS)
    (contains_shiftRelationScheme K B hS) (shiftAction K)

/-- The relation given by `shiftRelationSource` and `shiftRelationTarget` is the graph
relation of `shiftAction`. -/
theorem relation_eq_actionRelation :
    Space.relation B (Spec (.of K)) hS (shiftRelationSource K B hS)
        (shiftRelationTarget K B hS) =
      Space.actionRelation (Space.underlyingOver B hS (shiftChart K B hS))
        (Multiplicative ℤ) (shiftAction K) := rfl

/-- **Stacks 02Z2.** The graph relation of the integer shift is an étale equivalence
relation. -/
instance isEtaleEquivalenceRelation_relation :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.relation B (Spec (.of K)) hS (shiftRelationSource K B hS)
        (shiftRelationTarget K B hS)) := by
  rw [relation_eq_actionRelation]
  exact Space.actionRelation_isEtaleEquivalenceRelation _ (Multiplicative ℤ) (shiftAction K)
    (shiftAction_residueFieldFaithful K)

/-- The copy of the chart inside the relation scheme indexed by the generator of the integer
action. It identifies a tail point of the chart with its shift in the quotient. -/
def generatorSummand : shiftChart K B hS ⟶ shiftRelationObj K B hS :=
  Space.siteActionRelationInclusion (Multiplicative ℤ) B hS (shiftChart K B hS)
    (contains_shiftRelationScheme K B hS) (Multiplicative.ofAdd (1 : ℤ))

/-- The generator's copy of the chart is a section of the source map of the relation. -/
theorem generatorSummand_comp_shiftRelationSource :
    generatorSummand K B hS ≫ shiftRelationSource K B hS = 𝟙 (shiftChart K B hS) :=
  Space.siteActionRelationInclusion_comp_source (Multiplicative ℤ) B hS (shiftChart K B hS)
    (contains_shiftRelationScheme K B hS) (Multiplicative.ofAdd (1 : ℤ))

/-- The target map of the relation, restricted to the generator's copy of the chart, is the
generating automorphism of the integer action. -/
theorem toScheme_map_generatorSummand_comp_shiftRelationTarget :
    (BigFppfOver.toScheme B (Spec (.of K)) hS).map
        (generatorSummand K B hS ≫ shiftRelationTarget K B hS) =
      (shiftByOne K).asIso.hom.left := by
  have h : (BigFppfOver.toScheme B (Spec (.of K)) hS).map
      (Space.siteActionRelationInclusion (Multiplicative ℤ) B hS (shiftChart K B hS)
          (contains_shiftRelationScheme K B hS) (Multiplicative.ofAdd (1 : ℤ)) ≫
        Space.siteActionRelationTarget (Multiplicative ℤ) B hS (shiftChart K B hS)
          (contains_shiftRelationScheme K B hS) (shiftAction K)) =
      (shiftAction K (Multiplicative.ofAdd (1 : ℤ))).asIso.hom.left :=
    Space.toScheme_map_siteActionRelationInclusion_comp_target (Multiplicative ℤ) B hS
      (shiftChart K B hS) (contains_shiftRelationScheme K B hS) (shiftAction K)
      (Multiplicative.ofAdd (1 : ℤ))
  rwa [show shiftAction K (Multiplicative.ofAdd (1 : ℤ)) = shiftByOne K from zpow_one _] at h

/-- **Stacks 06UK.** The target map of the relation carries the `n`-th tail point of the
generator's copy of the chart to the `(n + 1)`-st tail point: the two are identified in the
quotient. -/
theorem toScheme_map_shiftRelationTarget_generatorSummand_chartPoint (n : ℤ) :
    (BigFppfOver.toScheme B (Spec (.of K)) hS).map (shiftRelationTarget K B hS)
        ((BigFppfOver.toScheme B (Spec (.of K)) hS).map (generatorSummand K B hS)
          (chartPoint K B hS n)) =
      chartPoint K B hS (n + 1) := by
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp,
    toScheme_map_generatorSummand_comp_shiftRelationTarget]
  exact shiftByOne_shiftPoint K n

/-- **Stacks 06UK.** The fppf sheaf quotient of `Spec K[y, x_n : n ∈ ℤ]` by the integer
shift. -/
abbrev shiftQuotient [HasSheafify (BigFppfOver.topology B (Spec (.of K)) hS) (Type u)] :
    (BigFppfOver B (Spec (.of K)) hS)ᵒᵖ ⥤ Type u :=
  (quotientSheaf (BigFppfOver.topology B (Spec (.of K)) hS) (Over.post B.inclusion)
    (Space.relation B (Spec (.of K)) hS (shiftRelationSource K B hS)
      (shiftRelationTarget K B hS))).obj

/-- The canonical map from the chart to the quotient. -/
abbrev shiftQuotientMap [HasSheafify (BigFppfOver.topology B (Spec (.of K)) hS) (Type u)] :
    yoneda.obj (shiftChart K B hS) ⟶ shiftQuotient K B hS :=
  Space.quotientMap B (Spec (.of K)) hS (shiftRelationSource K B hS)
    (shiftRelationTarget K B hS)

/-- **Stacks 06UK.** The quotient of `Spec K[y, x_n : n ∈ ℤ]` by the integer shift is an
algebraic space over `Spec K`.

The two descent hypotheses are those of
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf`, which is this library's form of
Stacks 0265. -/
theorem isAlgebraicSpace_shiftQuotient
    [HasSheafify (BigFppfOver.topology B (Spec (.of K)) hS) (Type u)]
    (hdiag : Space.IsEffectiveDescentAlongCoveringSieve B (Spec (.of K)) hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType))
    (hchart : Space.IsEffectiveDescentAlongCoveringSieve B (Spec (.of K)) hS
      (@AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓
        @AlgebraicGeometry.Surjective ⊓ @Etale : MorphismProperty Scheme.{u})) :
    IsAlgebraicSpace B (Spec (.of K)) hS (shiftQuotient K B hS) :=
  Space.isAlgebraicSpace_quotientSheaf B (Spec (.of K)) hS (shiftChart K B hS)
    (Space.relation B (Spec (.of K)) hS (shiftRelationSource K B hS)
      (shiftRelationTarget K B hS)) hdiag hchart

end AlgebraicGeometry.IntegerShift

end
