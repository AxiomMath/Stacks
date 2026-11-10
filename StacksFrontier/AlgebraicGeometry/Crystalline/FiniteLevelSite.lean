module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelBase
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecSchemeThickening
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Functoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleComparison

/-!
# The finite level bases `S_e` and the full subcategories `Cris(X/S_e) ⊆ Cris(X/S)`

Let `p` be a prime, let `(A, I, γ)` be a divided power ring with `A` an algebra over `ℤ_(p)` and
`p` nilpotent in `A/I`, and set `S = Spec(A, I, γ)`.  For `e ≫ 0` the ideal `(p^e)` is contained
in `I` and preserved by `γ`, so `A/p^eA` is again a divided power ring and `S_e = Spec(A/p^eA)` is
a divided power scheme with a closed immersion `S_e ⟶ S`.  Because `(p^e) ⊆ I`, the two divided
power schemes have the *same* closed fibre: `(A/p^eA)/(I/p^eA) = A/I`.  Hence a scheme `X` over
`S_0 = Spec(A/I)` is a scheme over the closed fibre of `S_e` as well, and the two crystalline
situations `X/S` and `X/S_e` have the same `X`.  Change of divided power base along the closed
immersion `S_e ⟶ S` and the identity of `X` is then fully faithful, which is the assertion of
[Stacks, Tag 07MV] that `Cris(X/S_e)` is a full subcategory of `Cris(X/S)`; and `F_e` is the
restriction of `F` along it.

## Main definitions

* `Crystalline.DividedPowerScheme.specClosedFiberPresentation` and
  `Crystalline.DividedPowerScheme.specClosedFiberIso` — the closed fibre of `Spec (A, I, γ)` is
  `Spec (A/I)`.
* `Crystalline.pAdicLevelScheme` — the divided power scheme `S_e = Spec(A/p^eA)`, and
  `Crystalline.pAdicLevelSchemeProj` the closed immersion `S_e ⟶ S`.
* `Crystalline.pAdicLevelQuotEquiv` and `Crystalline.pAdicLevelClosedFiberIso` — the
  identification `(A/p^eA)/(I/p^eA) = A/I` of the two closed fibres.
* `Crystalline.specSituation` and `Crystalline.pAdicLevelSituation` — the global crystalline
  situations `X/S` and `X/S_e`.
* `Crystalline.pAdicLevelExtend` — the functor `Cris(X/S_e) ⥤ Cris(X/S)`.
* `Crystalline.pAdicLevelRestriction` and `Crystalline.pAdicLevelModuleRestriction` — the
  restriction `F_e` of a presheaf, respectively of a presheaf of `𝒪_{X/S}`-modules, along it.
* `Crystalline.pAdicLevelBigModuleRestriction` — the restriction of a *sheaf* of
  `𝒪_{X/S}`-modules on the big crystalline site, where change of base is known to be continuous.

## Main results

* `Crystalline.pAdicLevelClosedFiberIso_hom_eq` — the identification of the closed fibres *is* the
  map on closed fibres induced by `S_e ⟶ S`; this is what makes `X/S_e` a situation over the same
  `X` and not a reindexing.
* `Crystalline.isClosedImmersion_pAdicLevelSchemeProj_hom` — `S_e ⟶ S` is a closed immersion.
* `Crystalline.pAdicLevelExtendFullyFaithful` — **`Cris(X/S_e)` is a full subcategory of
  `Cris(X/S)`**, [Stacks, Tag 07MV].

## Implementation notes

The restriction `F_e` is taken here at the level of presheaves of modules on the small site,
together with a sheaf-level version on the big site
(`Crystalline.pAdicLevelBigModuleRestriction`), where change of divided power base is continuous.
On the small site change of base is cocontinuous
(`Crystalline.GlobalCrystallineSituation.smallChangeBase_isCocontinuous`), and the pullback of
sheaves along a cocontinuous functor is the *sheafification* of the restriction rather than the
restriction; the continuity of `Crystalline.pAdicLevelExtend` for the small site is
`Crystalline.GlobalCrystallineSituation.smallChangeBase_isContinuous`, and the small-site
sheaf-level `F_e` is `Crystalline.pAdicLevelSmallModuleRestriction`. The transition functors
`Cris(X/S_m) ⥤ Cris(X/S_e)` for `m ≤ e` are `Crystalline.pAdicLevelStepExtend`.

The conclusion `RΓ(Cris(X/S), F) = R lim_e RΓ(Cris(X/S_e), F_e)` of [Stacks, Tag 07MV] is not
proved here. Its graded form `H^j(Cris(X/S), F) = lim_e H^j(Cris(X/S_e), F_e)` is a different and
in general false statement, `R lim` of a tower not being determined by the cohomologies of its
terms.

## References

* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 07KD](https://stacks.math.columbia.edu/tag/07KD)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline

namespace DividedPowerScheme

/-! ### The closed fibre of `Spec (A, I, γ)` -/

variable (A : DividedPowerRing.{u})

/-- **Over an affine open, the divided power ideal of `Spec (A, I, γ)` is the kernel ideal of the
closed immersion `Spec (A/I) ⟶ Spec A`.**  This is
`Crystalline.DividedPowerScheme.ker_specQuotientImmersion` read on affine opens. -/
theorem specDividedPowerScheme_ideal_obj_eq_ker
    (V : (Spec (CommRingCat.of A)).affineOpens) :
    (specDividedPowerScheme A).ideal.obj (op (V : (Spec (CommRingCat.of A)).Opens)) =
      (specQuotientImmersion A).ker.ideal V :=
  (idealSheafAsSubmodule_obj_affine _ V).trans
    (congrArg (fun d : (Spec (CommRingCat.of A)).IdealSheafData ↦ d.ideal V)
      (ker_specQuotientImmersion A).symm)

/-- **Over an affine open, a section of `𝒪_{Spec A}` killed by the quotient map lies in the
divided power ideal of `Spec (A, I, γ)`.**  This is the second half of the presentation of the
closed fibre below, stated separately so that
`Crystalline.DividedPowerScheme.specDividedPowerScheme_ideal_obj_eq_ker` can be rewritten with
its affine open at the type the field of the presentation hands over. -/
theorem mem_specDividedPowerScheme_ideal_of_app_eq_zero
    (V : (specDividedPowerScheme A).scheme.affineOpens)
    (s : Γ((specDividedPowerScheme A).scheme, (V : (specDividedPowerScheme A).scheme.Opens)))
    (hs : ((specQuotientImmersion A).app (V : (specDividedPowerScheme A).scheme.Opens)).hom s =
      0) :
    s ∈ (specDividedPowerScheme A).ideal.obj
      (op (V : (specDividedPowerScheme A).scheme.Opens)) := by
  rw [specDividedPowerScheme_ideal_obj_eq_ker A V,
    Scheme.Hom.ker_apply (specQuotientImmersion A) V]
  exact hs

/-- **`Spec (A/I)` presents the closed fibre of `Spec (A, I, γ)`.**  The quotient map is a closed
immersion whose kernel ideal sheaf is the divided power ideal, by
`Crystalline.DividedPowerScheme.ker_specQuotientImmersion`; unlike
`Crystalline.DividedPowerScheme.specSchemeThickening`, no nilpotence of `I` is needed, because a
presentation of the closed fibre is not asked to be a thickening. -/
def specClosedFiberPresentation : ClosedFiberPresentation (specDividedPowerScheme A) where
  carrier := Spec (CommRingCat.of (↥A ⧸ A.ideal))
  ι := specQuotientImmersion A
  isClosedImmersion := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  app_eq_zero_of_mem V s hs :=
    (specQuotientImmersion A).app_eq_zero_of_mem_of_le_ker _
      (fun U ↦ (specDividedPowerScheme_ideal_obj_eq_ker A U).le) V s hs
  mem_of_app_eq_zero V s hs := mem_specDividedPowerScheme_ideal_of_app_eq_zero A V s hs

/-- **The closed fibre of `Spec (A, I, γ)` is `Spec (A/I)`.**  Any two presentations of the closed
fibre of a divided power scheme are canonically isomorphic. -/
def specClosedFiberIso :
    closedFiber (specDividedPowerScheme A) ≅ Spec (CommRingCat.of (↥A ⧸ A.ideal)) :=
  ClosedFiberPresentation.isoOfPresentations (closedFiberPresentation (specDividedPowerScheme A))
    (specClosedFiberPresentation A)

/-- The identification of the closed fibre of `Spec (A, I, γ)` with `Spec (A/I)` is compatible
with the two closed immersions into `Spec A`. -/
@[reassoc (attr := simp)]
theorem specClosedFiberIso_hom_specQuotientImmersion :
    (specClosedFiberIso A).hom ≫ specQuotientImmersion A =
      closedFiberι (specDividedPowerScheme A) :=
  ClosedFiberPresentation.isoOfPresentations_hom_comp_ι _ _

/-- The inverse form of
`Crystalline.DividedPowerScheme.specClosedFiberIso_hom_specQuotientImmersion`. -/
@[reassoc]
theorem specClosedFiberIso_inv_closedFiberι :
    (specClosedFiberIso A).inv ≫ closedFiberι (specDividedPowerScheme A) =
      specQuotientImmersion A :=
  (Iso.inv_comp_eq _).mpr (specClosedFiberIso_hom_specQuotientImmersion A).symm

end DividedPowerScheme

/-! ### The finite level base `S_e = Spec(A/p^eA)` -/

section Level

open DividedPowerScheme

attribute [local implicit_reducible] DividedPowerScheme.specDividedPowerScheme

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) (p : ℕ)

/-- **The divided power base `S = Spec(A, I, γ)` of [Stacks, Tag 07MV].** -/
def specBase : DividedPowerScheme.{u} :=
  specDividedPowerScheme (DividedPowerRing.of A I γ)

/-- The divided power base `S_e = Spec(A/p^eA)` at a finite divided power level `e`: the spectrum
of the divided power ring `Crystalline.pAdicLevelRing`. -/
@[stacks 07MV "S_e = Spec(A/p^eA) is a divided power base, for e a finite divided power level"]
def pAdicLevelScheme {e : ℕ} (he : IsPAdicLevel I γ p e) : DividedPowerScheme.{u} :=
  specDividedPowerScheme (pAdicLevelRing I γ p he)

/-- **The projection `S_e ⟶ S` of divided power bases**, `Spec` of the quotient map
`(A, I, γ) ⟶ (A/p^eA, I/p^eA, γ̄)`. -/
def pAdicLevelSchemeProj {e : ℕ} (he : IsPAdicLevel I γ p e) :
    pAdicLevelScheme I γ p he ⟶ specBase I γ :=
  specDividedPowerMap (pAdicLevelProj I γ p he)

/-- The underlying morphism of schemes of `S_e ⟶ S` is `Spec` of the quotient map `A → A/p^eA`. -/
@[simp]
theorem pAdicLevelSchemeProj_hom {e : ℕ} (he : IsPAdicLevel I γ p e) :
    (pAdicLevelSchemeProj I γ p he).hom =
      Spec.map (CommRingCat.ofHom (pAdicLevelProj I γ p he).toRingHom) := rfl

/-- **The projection `S_e ⟶ S` is a closed immersion**, being `Spec` of the surjection
`A → A/p^eA`. -/
instance isClosedImmersion_pAdicLevelSchemeProj_hom {e : ℕ} (he : IsPAdicLevel I γ p e) :
    IsClosedImmersion (pAdicLevelSchemeProj I γ p he).hom := by
  rw [pAdicLevelSchemeProj_hom]
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- **The two closed fibres agree at the level of rings:** `(A/p^eA)/(I/p^eA) = A/I`, because
`(p^e) ⊆ I`.  This is the third isomorphism theorem,
`Ideal.DoubleQuot.quotQuotEquivQuotOfLE`. -/
def pAdicLevelQuotEquiv {e : ℕ} (he : IsPAdicLevel I γ p e) :
    (↥(pAdicLevelRing I γ p he) ⧸ (pAdicLevelRing I γ p he).ideal) ≃+*
      (↥(DividedPowerRing.of A I γ) ⧸ (DividedPowerRing.of A I γ).ideal) :=
  DoubleQuot.quotQuotEquivQuotOfLE he.1

/-- **The identification `(A/p^eA)/(I/p^eA) = A/I` is compatible with the two quotient maps out
of `A`.**  Reading `A ⟶ A/I` through it is `A ⟶ A/p^eA ⟶ (A/p^eA)/(I/p^eA)`. -/
theorem pAdicLevelQuotEquiv_symm_comp_mk {e : ℕ} (he : IsPAdicLevel I γ p e) :
    (pAdicLevelQuotEquiv I γ p he).symm.toRingHom.comp
        (Ideal.Quotient.mk (DividedPowerRing.of A I γ).ideal) =
      (Ideal.Quotient.mk (pAdicLevelRing I γ p he).ideal).comp
        (pAdicLevelProj I γ p he).toRingHom := by
  ext a
  exact DoubleQuot.quotQuotEquivQuotOfLE_symm_mk a he.1

/-- The identification `(A/p^eA)/(I/p^eA) = A/I`, as an isomorphism of `CommRingCat`. -/
def pAdicLevelQuotIso {e : ℕ} (he : IsPAdicLevel I γ p e) :
    CommRingCat.of (↥(DividedPowerRing.of A I γ) ⧸ (DividedPowerRing.of A I γ).ideal) ≅
      CommRingCat.of (↥(pAdicLevelRing I γ p he) ⧸ (pAdicLevelRing I γ p he).ideal) :=
  (pAdicLevelQuotEquiv I γ p he).symm.toCommRingCatIso

/-- The isomorphism `pAdicLevelQuotIso` is the inverse of the ring isomorphism
`pAdicLevelQuotEquiv`. -/
@[simp]
theorem pAdicLevelQuotIso_hom {e : ℕ} (he : IsPAdicLevel I γ p e) :
    (pAdicLevelQuotIso I γ p he).hom =
      CommRingCat.ofHom (pAdicLevelQuotEquiv I γ p he).symm.toRingHom := rfl

/-- **The identification of the two closed fibres, at the level of their defining quotient
maps.**  Reading `Spec(A/I) ⟶ Spec A` through the identification `(A/p^eA)/(I/p^eA) = A/I` gives
`Spec((A/p^eA)/(I/p^eA)) ⟶ Spec(A/p^eA) ⟶ Spec A`. -/
theorem spec_pAdicLevelQuotIso_comp {e : ℕ} (he : IsPAdicLevel I γ p e) :
    Spec.map (pAdicLevelQuotIso I γ p he).hom ≫
        specQuotientImmersion (DividedPowerRing.of A I γ) =
      specQuotientImmersion (pAdicLevelRing I γ p he) ≫
        Spec.map (CommRingCat.ofHom (pAdicLevelProj I γ p he).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map
    (CommRingCat.hom_ext (pAdicLevelQuotEquiv_symm_comp_mk I γ p he))

/-- The closed fibre of `S_e = Spec(A/p^eA)` is the closed fibre `S_0 = Spec(A/I)` of `S`. Both
are the spectrum of a double quotient of `A`, and the two double quotients agree because
`(p^e) ⊆ I`. -/
@[stacks 07MV "S_e has the same closed fibre S₀ = Spec(A/I) as S, since (p^e) ⊆ I"]
def pAdicLevelClosedFiberIso {e : ℕ} (he : IsPAdicLevel I γ p e) :
    closedFiber (pAdicLevelScheme I γ p he) ≅ closedFiber (specBase I γ) :=
  specClosedFiberIso (pAdicLevelRing I γ p he) ≪≫
    Scheme.Spec.mapIso (pAdicLevelQuotIso I γ p he).op ≪≫
      (specClosedFiberIso (DividedPowerRing.of A I γ)).symm

/-- **The identification of the closed fibres of `S_e` and `S` is the map on closed fibres induced
by the projection `S_e ⟶ S`.**  Both become the same morphism into `Spec A` after composing with
the closed immersion of the closed fibre of `S`, which is a monomorphism; at the level of rings
the required identity is
`Crystalline.pAdicLevelQuotEquiv_symm_comp_mk`. -/
theorem pAdicLevelClosedFiberIso_hom_eq {e : ℕ} (he : IsPAdicLevel I γ p e) :
    (pAdicLevelClosedFiberIso I γ p he).hom =
      closedFiberMap (pAdicLevelSchemeProj I γ p he) := by
  refine eq_closedFiberMap _ _ ?_
  change (specClosedFiberIso (pAdicLevelRing I γ p he)).hom ≫
      Spec.map (pAdicLevelQuotIso I γ p he).hom ≫
        (specClosedFiberIso (DividedPowerRing.of A I γ)).inv ≫
          closedFiberι (specDividedPowerScheme (DividedPowerRing.of A I γ)) =
    closedFiberι (specDividedPowerScheme (pAdicLevelRing I γ p he)) ≫
      Spec.map (CommRingCat.ofHom (pAdicLevelProj I γ p he).toRingHom)
  rw [specClosedFiberIso_inv_closedFiberι, spec_pAdicLevelQuotIso_comp, ← Category.assoc,
    specClosedFiberIso_hom_specQuotientImmersion]

/-! ### The crystalline situations `X/S` and `X/S_e` -/

variable [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) A]

/-- The `ℤ_(p)`-algebra structure on the global sections of `Spec` of a divided power ring, read
from the one on the ring through the `Γ`-`Spec` identification. -/
@[instance_reducible]
def specAlgebraAtPrime (R : DividedPowerRing.{u})
    (φ : DividedPowers.IntegersAtPrime p →+* R) :
    Algebra (DividedPowers.IntegersAtPrime p) Γ((specDividedPowerScheme R).scheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp φ).toAlgebra

/-- **The global crystalline situation `X/S` of [Stacks, Tag 07MV]**, for `S = Spec(A, I, γ)` and
`X` a scheme over the closed fibre `S_0 = Spec(A/I)` on which `p` is locally nilpotent. -/
def specSituation (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    GlobalCrystallineSituation.{u} where
  p := p
  S := specBase I γ
  algebraAtPrime :=
    specAlgebraAtPrime p (DividedPowerRing.of A I γ)
      (algebraMap (DividedPowers.IntegersAtPrime p) A)
  X := X
  toClosedFiber := toCF
  prime_locallyNilpotent := hX

/-- The prime of the situation `X/S` is `p`. -/
@[simp]
theorem specSituation_p (X : Scheme.{u}) (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (specSituation I γ p X toCF hX).p = p := rfl

/-- The divided power base of the situation `X/S` is `S = Spec(A, I, γ)`. -/
@[simp]
theorem specSituation_S (X : Scheme.{u}) (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (specSituation I γ p X toCF hX).S = specBase I γ := rfl

/-- The scheme of the situation `X/S` is `X`. -/
@[simp]
theorem specSituation_X (X : Scheme.{u}) (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (specSituation I γ p X toCF hX).X = X := rfl

/-- The structure morphism of the situation `X/S` is the given morphism `X ⟶ S_0`. -/
@[simp]
theorem specSituation_toClosedFiber (X : Scheme.{u}) (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (specSituation I γ p X toCF hX).toClosedFiber = toCF := rfl

/-- The global crystalline situation `X/S_e` at a finite divided power level `e`, on the *same*
scheme `X`: the structure morphism `X ⟶ S_0` of the situation `X/S` is read in the closed fibre
of `S_e` through the identification `Crystalline.pAdicLevelClosedFiberIso` of the two closed
fibres. -/
@[stacks 07MV "X/S_e is a global crystalline situation on the same X, so Cris(X/S_e) is defined"]
def pAdicLevelSituation {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    GlobalCrystallineSituation.{u} where
  p := p
  S := pAdicLevelScheme I γ p he
  algebraAtPrime :=
    specAlgebraAtPrime p (pAdicLevelRing I γ p he)
      ((Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := A) p ^ e)).comp
        (algebraMap (DividedPowers.IntegersAtPrime p) A))
  X := X
  toClosedFiber := toCF ≫ (pAdicLevelClosedFiberIso I γ p he).inv
  prime_locallyNilpotent := hX

/-- The divided power base of the situation `X/S_e` is `S_e = Spec(A/p^eA)`. -/
@[simp]
theorem pAdicLevelSituation_S {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelSituation I γ p he X toCF hX).S = pAdicLevelScheme I γ p he := rfl

/-- The scheme of the situation `X/S_e` is `X`. -/
@[simp]
theorem pAdicLevelSituation_X {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelSituation I γ p he X toCF hX).X = X := rfl

/-- The structure morphism of the situation `X/S_e` is the structure morphism `X ⟶ S_0` of `X/S`
followed by the identification `pAdicLevelClosedFiberIso` of the closed fibres. -/
@[simp]
theorem pAdicLevelSituation_toClosedFiber {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelSituation I γ p he X toCF hX).toClosedFiber =
      toCF ≫ (pAdicLevelClosedFiberIso I γ p he).inv := rfl

/-- **The compatibility of the projection `S_e ⟶ S` with the structure morphisms**, which is the
hypothesis of change of divided power base, [Stacks, Tag 07IC], for the pair
`(S_e ⟶ S, 𝟙 X)`.  It holds because the map on closed fibres induced by `S_e ⟶ S` is the
identification of the two closed fibres,
`Crystalline.pAdicLevelClosedFiberIso_hom_eq`. -/
theorem pAdicLevelSituation_changeBase_condition {e : ℕ} (he : IsPAdicLevel I γ p e)
    (X : Scheme.{u}) (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelSituation I γ p he X toCF hX).toClosedFiber ≫
        closedFiberMap (pAdicLevelSchemeProj I γ p he) =
      (𝟙 X : X ⟶ X) ≫ (specSituation I γ p X toCF hX).toClosedFiber := by
  change (toCF ≫ (pAdicLevelClosedFiberIso I γ p he).inv) ≫
      closedFiberMap (pAdicLevelSchemeProj I γ p he) = (𝟙 X : X ⟶ X) ≫ toCF
  rw [← pAdicLevelClosedFiberIso_hom_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.id_comp]

/-- The identity of `X`, read as a morphism from the thickened space of the situation `X/S_e` to
that of the situation `X/S`, is an open immersion.  Both are `X`, but the two field projections
are not reducible, so the instance is supplied here. -/
instance isOpenImmersion_pAdicLevelId {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    @IsOpenImmersion (pAdicLevelSituation I γ p he X toCF hX).X
      (specSituation I γ p X toCF hX).X (𝟙 X) :=
  inferInstanceAs (IsOpenImmersion (𝟙 X))

/-- The functor `Cris(X/S_e) ⥤ Cris(X/S)`: change of divided power base along the projection
`S_e ⟶ S` and the identity of `X`. An object of `Cris(X/S_e)` is a divided power thickening of `X`
relative to `S_e`, which composed with `S_e ⟶ S` is one relative to `S`. -/
@[stacks 07MV "the functor Cris(X/S_e) ⥤ Cris(X/S)"]
def pAdicLevelExtend {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    GlobalCrystallineSituation.CrystallineThickening
        (pAdicLevelSituation I γ p he X toCF hX) ⥤
      GlobalCrystallineSituation.CrystallineThickening (specSituation I γ p X toCF hX) :=
  GlobalCrystallineSituation.smallChangeBase _ _ (pAdicLevelSchemeProj I γ p he) (𝟙 X)
    (pAdicLevelSituation_changeBase_condition I γ p he X toCF hX)

/-- `Cris(X/S_e)` is a full subcategory of `Cris(X/S)`: change of divided power base along
`S_e ⟶ S` and `𝟙 X` is fully faithful, the projection `S_e ⟶ S` being a closed immersion and
hence a monomorphism. -/
@[stacks 07MV "Cris(X/S_e) is a full subcategory of Cris(X/S)"]
def pAdicLevelExtendFullyFaithful {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelExtend I γ p he X toCF hX).FullyFaithful :=
  GlobalCrystallineSituation.smallChangeBaseFullyFaithfulOfMono
    (S := pAdicLevelSituation I γ p he X toCF hX) (S' := specSituation I γ p X toCF hX)
    (f := pAdicLevelSchemeProj I γ p he) (g := 𝟙 X)
    (h := pAdicLevelSituation_changeBase_condition I γ p he X toCF hX)
    (DividedPowerScheme.mono_of_mono_hom
      (inferInstanceAs (Mono (pAdicLevelSchemeProj I γ p he).hom)))

/-! ### The restriction `F_e` -/

/-- The restriction of a presheaf `F` on `Cris(X/S)` to `Cris(X/S_e)`: its value on an object of
`Cris(X/S_e)` is the value of `F` on the same divided power thickening, read over `S`.  The tag's
`F_e` is the `𝒪_{X/S}`-module form of this, `Crystalline.pAdicLevelModuleRestriction`. -/
def pAdicLevelRestriction {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    {𝒜 : Type*} [Category 𝒜]
    (F : (GlobalCrystallineSituation.CrystallineThickening
      (specSituation I γ p X toCF hX))ᵒᵖ ⥤ 𝒜) :
    (GlobalCrystallineSituation.CrystallineThickening
      (pAdicLevelSituation I γ p he X toCF hX))ᵒᵖ ⥤ 𝒜 :=
  (pAdicLevelExtend I γ p he X toCF hX).op ⋙ F

/-- **The functor `Cris(X/S_e) ⥤ Cris(X/S)` preserves the structure presheaf.**  The structure
presheaf sends an object to the global sections of its ambient divided power scheme, which change
of base leaves untouched; so `𝒪_{X/S}` restricts to `𝒪_{X/S_e}` on the nose. -/
theorem pAdicLevelExtend_op_comp_crisRing {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    (pAdicLevelExtend I γ p he X toCF hX).op ⋙
        GlobalCrystallineSituation.SmallSite.crisRing (specSituation I γ p X toCF hX) =
      GlobalCrystallineSituation.SmallSite.crisRing
        (pAdicLevelSituation I γ p he X toCF hX) := rfl

/-- The restriction `F_e` of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` to a presheaf of
`𝒪_{X/S_e}`-modules on `Cris(X/S_e)`. No comparison of structure presheaves is needed: the
restriction of `𝒪_{X/S}` along the functor is `𝒪_{X/S_e}` itself, by
`Crystalline.pAdicLevelExtend_op_comp_crisRing`. -/
@[stacks 07MV
  "F_e, the restriction of an 𝒪_{X/S}-module F to Cris(X/S_e), as a presheaf of modules"]
def pAdicLevelModuleRestriction {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    (F : PresheafOfModules.{u}
      (GlobalCrystallineSituation.SmallSite.crisRing (specSituation I γ p X toCF hX))) :
    PresheafOfModules.{u}
      (GlobalCrystallineSituation.SmallSite.crisRing
        (pAdicLevelSituation I γ p he X toCF hX)) :=
  (PresheafOfModules.pushforward₀ (pAdicLevelExtend I γ p he X toCF hX)
    (GlobalCrystallineSituation.SmallSite.crisRing (specSituation I γ p X toCF hX))).obj F

/-- **The restriction `F_e` of a sheaf of `𝒪_{X/S}`-modules on the big crystalline site.**  On
the big site change of divided power base is known to be continuous
(`Crystalline.GlobalCrystallineSituation.changeBase_isContinuous`), so the restriction of a sheaf
of modules along it is again one; this is
`Crystalline.GlobalCrystallineSituation.changeBaseModulePullback` for the pair
`(S_e ⟶ S, 𝟙 X)`. -/
def pAdicLevelBigModuleRestriction {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    SheafOfModules.{u} (GlobalCrystallineSituation.crystallineStructureSheaf
        (specSituation I γ p X toCF hX)) ⥤
      SheafOfModules.{u} (GlobalCrystallineSituation.crystallineStructureSheaf
        (pAdicLevelSituation I γ p he X toCF hX)) :=
  GlobalCrystallineSituation.changeBaseModulePullback _ _ (pAdicLevelSchemeProj I γ p he) (𝟙 X)
    (pAdicLevelSituation_changeBase_condition I γ p he X toCF hX)

end Level

end Crystalline

end
