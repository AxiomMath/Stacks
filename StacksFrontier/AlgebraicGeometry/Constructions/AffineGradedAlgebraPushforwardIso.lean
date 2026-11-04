module

public import StacksFrontier.AlgebraicGeometry.Constructions.AffineGradedAlgebraPushforward
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleRealization

/-!
# The comparison `B̃ ⟶ f_* 𝒪_{Spec B}` is an isomorphism

Let `A` be a commutative ring and `B` a graded `A`-algebra, and let `f : Spec B ⟶ Spec A` be the
morphism of affine schemes induced by the structure map.
`Stacks.AffineGradedAlgebra.toPushforwardAlgebra` is the canonical morphism of sheaves of
commutative `𝒪_{Spec A}`-algebras from the algebra sheaf presented by the grading to
`f_* 𝒪_{Spec B}`. **This file proves that it is invertible**, which is the affine graded case of
the comparison of [Stacks, Tag 01LX] (3).

## The hypothesis

Invertibility needs `B` to be the internal direct sum of its homogeneous pieces,
`DirectSum.Decomposition`. This is the notion of [Stacks, Tag 00JL]: a graded ring *is* a ring
with a direct sum decomposition `S = ⨁_{d ≥ 0} S_d` such that `S_d · S_e ⊆ S_{d+e}`, and
[Stacks, Tag 0897] takes its `B` to be a finitely generated graded `A`-algebra.

The hypothesis is necessary. With `A = B = k` a field and `𝒞 n = ⊤` in every degree `n ≥ 0`, the
family of submodules is multiplicative and contains `1` in degree `0`, but the source has a copy
of `k` in every nonnegative degree while `Γ(Spec k, 𝒪) = k`, so the comparison is not injective.
In particular a `SetLike.GradedMonoid`, which is all `Stacks.AffineGradedAlgebra.gradedTilde`
carries, does not suffice.

## Main results

* `Stacks.AffineGradedAlgebra.bijective_totalTildeSec`: **the comparison is bijective on the
  sections over a basic open `D(r)`.** Over `D(r)` it is `⨁ₙ (𝒞 n)_r → B_r`, and the two sides
  are localizations at `r` of `⨁ₙ 𝒞 n` and of `B`, which the decomposition identifies.
* `Stacks.AffineGradedAlgebra.isLocallyInjective_totalPresheafHom` and
  `isLocallySurjective_totalPresheafHom`: the comparison of presheaves of rings is locally
  bijective — bijectivity on basic opens plus the fact that they are a basis.
* `Stacks.AffineGradedAlgebra.isIso_ungradedSheafHom`: **the comparison of sheaves of rings is an
  isomorphism.**
* `Stacks.AffineGradedAlgebra.isIso_toPushforwardAlgebra`: **the comparison of sheaves of
  commutative `𝒪_{Spec A}`-algebras is an isomorphism** — leg (i) of [Stacks, Tag 01LX] in the
  affine graded case.
* `Stacks.AffineGradedAlgebra.isInternal_intPiece`: the `ℤ`-extension by zero of an `ℕ`-grading
  is again an internal direct sum, so the hypothesis transports to `B̃`.
* `Stacks.AffineGradedAlgebra.isIso_gradedTildeToPushforwardAlgebra`,
  `gradedTildeToPushforwardAlgebraIso` and `isIso_gradedTildeOfToPushforwardAlgebra`: the same
  for `B̃`, in the two spellings of the base used by [Stacks, Tag 0897].

## Implementation notes

**The comparison at all of `B`.** The degreewise comparison
`Stacks.AffineGradedAlgebra.pieceToPushforward` factors, by definition, as `tilde` applied to the
inclusion of the graded piece followed by a single morphism
`Stacks.AffineGradedAlgebra.tildeToPushforward` which does not depend on the degree, and that
morphism is invertible because it is a component of `AlgebraicGeometry.pushforwardTildeNatTrans`.
So the argument can be run entirely inside the sections of associated sheaves of `R`-modules,
where the `Module ↑R` and `IsScalarTower ↑R Γ(Spec R, U)` instances on sections exist; the
sections of the pushforward carry no such instance under their own name.

**Instance spellings are the obstacle, not defeq.** `Γ(M, U)` and `M.val.obj (op U)` are the same
type, but the `Module ↑R` instance keys on the first spelling, `(Spec R).Modules` is a `def` and
not an `abbrev`, and `rw` type-checks its motive at `implicit` transparency and so fails on any
goal mentioning either. Every step across that boundary here is a `have`-bound term, as in
`Stacks.AffineGradedAlgebra.pieceToPushforward_app_eq`, never a `rw`.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 00JL](https://stacks.math.columbia.edu/tag/00JL)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AffineBaseChange

/-- **Over a basic open the canonical map is a localization**: `toOpenₗ N (D f)` exhibits the
sections of `Ñ` over `D(f)` as `N_f`. -/
theorem isLocalizedModule_toOpenₗ_specBasicOpen {R : CommRingCat.{u}} (N : ModuleCat.{u} R)
    (f : R) : IsLocalizedModule (Submonoid.powers f) (toOpenₗ N (specBasicOpen f)) :=
  inferInstanceAs (IsLocalizedModule (Submonoid.powers f)
    (tilde.toOpen N (specBasicOpen f)).hom)

end Stacks.AffineBaseChange

namespace Stacks.AffineGradedAlgebra

/-! ### The comparison at all of `B` -/

/-- `B`, read as an `R`-module by restricting scalars along the structure map. -/
abbrev restrictedAlgebra (R : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra R B] :
    ModuleCat.{u} R :=
  (ModuleCat.restrictScalars (specAlgebraMap R B).hom).obj (ModuleCat.of (CommRingCat.of B) B)

/-- **The comparison at all of `B`**: the associated sheaf of `B`, read as an `R`-module, is the
pushforward of the structure sheaf of `Spec B`. This is the component of
`AlgebraicGeometry.pushforwardTildeNatTrans`, [Stacks, Tag 01I9], at `B` over itself. -/
def tildeToPushforward (R : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra R B] :
    tilde (restrictedAlgebra R B) ⟶ pushforwardModule R B :=
  (AlgebraicGeometry.pushforwardTildeNatTrans R (CommRingCat.of B)
    (specAlgebraMap R B)).app (ModuleCat.of (CommRingCat.of B) B)

/-- The comparison at all of `B` is an isomorphism. -/
instance isIso_tildeToPushforward (R : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra R B] :
    IsIso (tildeToPushforward R B) :=
  AlgebraicGeometry.isIso_pushforwardTildeNatTrans_app R (CommRingCat.of B)
    (specAlgebraMap R B) (ModuleCat.of (CommRingCat.of B) B)

/-- The comparison at all of `B` is bijective on the sections over every open. -/
theorem bijective_tildeToPushforward_app (R : CommRingCat.{u}) (B : Type u) [CommRing B]
    [Algebra R B] (U : (Spec R).Opens) :
    Function.Bijective ((tildeToPushforward R B).val.app (op U)).hom :=
  ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)).mapIso
      (@asIso _ _ _ _ (tildeToPushforward R B) (isIso_tildeToPushforward R B))).hom

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒞 : ℤ → Submodule R B)

/-- The degreewise comparison factors through the comparison at all of `B`. -/
theorem pieceToPushforward_eq (n : ℤ) :
    pieceToPushforward 𝒞 n =
      AlgebraicGeometry.tilde.map (pieceIncl 𝒞 n) ≫ tildeToPushforward R B := rfl

/-! ### The comparison on sections, as a map of `R`-modules -/

/-- The degreewise comparison into the associated sheaf of `B`, on sections over an open, as an
`R`-linear map. -/
def pieceTildeSec (n : ℤ) (U : (Spec R).Opens) :
    Γ(pieceSheaf 𝒞 n, U) →ₗ[(R : Type u)] Γ(tilde (restrictedAlgebra R B), U) :=
  LinearMap.restrictScalars (R : Type u) (AffineBaseChange.tildeMapₗ (pieceIncl 𝒞 n) U)

/-- On the image of `x ∈ 𝒞 n` in the sections over `U`, `pieceTildeSec` is the image of `x` in
the sections of the associated sheaf of `B`. -/
theorem pieceTildeSec_toOpen (n : ℤ) (U : (Spec R).Opens) (x : ↥(𝒞 n)) :
    pieceTildeSec 𝒞 n U (AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) U x) =
      AffineBaseChange.toOpenₗ (restrictedAlgebra R B) U (pieceIncl 𝒞 n x) :=
  AffineBaseChange.tildeMapₗ_toOpenₗ (pieceIncl 𝒞 n) U x

/-- **The comparison on the direct sum of the sections of the homogeneous pieces**, into the
sections of the associated sheaf of `B`, as a map of `R`-modules. -/
def totalTildeSec (U : (Spec R).Opens) :
    (DirectSum ℤ fun n => Γ(pieceSheaf 𝒞 n, U)) →ₗ[(R : Type u)]
      Γ(tilde (restrictedAlgebra R B), U) :=
  DirectSum.toModule (R : Type u) ℤ _ fun n => pieceTildeSec 𝒞 n U

/-- On the summand of degree `n`, `totalTildeSec` is `pieceTildeSec` in degree `n`. -/
theorem totalTildeSec_lof (U : (Spec R).Opens) (n : ℤ) (y : Γ(pieceSheaf 𝒞 n, U)) :
    totalTildeSec 𝒞 U
        (DirectSum.lof (R : Type u) ℤ (fun n => Γ(pieceSheaf 𝒞 n, U)) n y) =
      pieceTildeSec 𝒞 n U y := by
  show DirectSum.toModule (R : Type u) ℤ (Γ(tilde (restrictedAlgebra R B), U))
      (fun n => pieceTildeSec 𝒞 n U)
      (DirectSum.lof (R : Type u) ℤ (fun n => Γ(pieceSheaf 𝒞 n, U)) n y) = _
  rw [DirectSum.toModule_lof]

/-- The sum of the inclusions of the homogeneous pieces into `B`, read as an `R`-module. -/
def inclSum : (DirectSum ℤ fun n => ↥(𝒞 n)) →ₗ[(R : Type u)] ↥(restrictedAlgebra R B) :=
  DirectSum.toModule (R : Type u) ℤ _ fun n => (pieceIncl 𝒞 n).hom

/-- On the summand of degree `n`, `inclSum` is the inclusion of `𝒞 n` into `B`. -/
theorem inclSum_lof (n : ℤ) (x : ↥(𝒞 n)) :
    inclSum 𝒞 (DirectSum.lof (R : Type u) ℤ (fun n => ↥(𝒞 n)) n x) = pieceIncl 𝒞 n x := by
  show DirectSum.toModule (R : Type u) ℤ (↥(restrictedAlgebra R B))
      (fun n => (pieceIncl 𝒞 n).hom)
      (DirectSum.lof (R : Type u) ℤ (fun n => ↥(𝒞 n)) n x) = _
  rw [DirectSum.toModule_lof]

/-- `inclSum` has the same underlying function as `DirectSum.coeAddMonoidHom`. -/
theorem inclSum_eq_coeAddMonoidHom (x : DirectSum ℤ fun n => ↥(𝒞 n)) :
    (inclSum 𝒞 x : B) = DirectSum.coeAddMonoidHom 𝒞 x := by
  induction x using DirectSum.induction_on with
  | zero => simp; rfl
  | of n x =>
      rw [DirectSum.coeAddMonoidHom_of]
      exact congrArg (fun y : ↥(restrictedAlgebra R B) => (y : B)) (inclSum_lof 𝒞 n x)
  | add x y hx hy =>
      rw [map_add (DirectSum.coeAddMonoidHom 𝒞), ← hx, ← hy, map_add]
      rfl

/-- **`inclSum` is bijective exactly when `B` is the internal direct sum of its homogeneous
pieces**: the two maps have the same underlying function. -/
theorem bijective_inclSum (hdec : DirectSum.IsInternal 𝒞) :
    Function.Bijective (inclSum 𝒞) := by
  refine ⟨fun a b hab => hdec.1 ?_, fun s => ?_⟩
  · rw [← inclSum_eq_coeAddMonoidHom 𝒞 a, ← inclSum_eq_coeAddMonoidHom 𝒞 b]
    exact congrArg (fun y : ↥(restrictedAlgebra R B) => (y : B)) hab
  · obtain ⟨a, ha⟩ := hdec.2 (s : B)
    exact ⟨a, (inclSum_eq_coeAddMonoidHom 𝒞 a).trans ha⟩

/-- The direct sum of the degreewise canonical maps into the sections over a basic open. -/
def pieceToOpenSum (r : R) :
    (DirectSum ℤ fun n => ↥(𝒞 n)) →ₗ[(R : Type u)]
      DirectSum ℤ fun n => Γ(pieceSheaf 𝒞 n, AffineBaseChange.specBasicOpen r) :=
  DirectSum.lmap fun n =>
    AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) (AffineBaseChange.specBasicOpen r)

/-- On the summand of degree `n`, `pieceToOpenSum` is the canonical map of `𝒞 n` into its sections
over `D(r)`, followed by the inclusion of that summand. -/
theorem pieceToOpenSum_lof (r : R) (n : ℤ) (x : ↥(𝒞 n)) :
    pieceToOpenSum 𝒞 r (DirectSum.lof (R : Type u) ℤ (fun n => ↥(𝒞 n)) n x) =
      DirectSum.lof (R : Type u) ℤ
        (fun n => Γ(pieceSheaf 𝒞 n, AffineBaseChange.specBasicOpen r)) n
        (AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) (AffineBaseChange.specBasicOpen r) x) := by
  show DirectSum.lmap
      (fun n => AffineBaseChange.toOpenₗ (pieceModule 𝒞 n) (AffineBaseChange.specBasicOpen r))
      (DirectSum.lof (R : Type u) ℤ (fun n => ↥(𝒞 n)) n x) = _
  rw [DirectSum.lmap_lof]

/-- **The direct sum of the degreewise canonical maps is a localization**: localization commutes
with direct sums, which is `IsBaseChange.directSum` read through
`isLocalizedModule_iff_isBaseChange`. -/
theorem isLocalizedModule_pieceToOpenSum (r : R) :
    IsLocalizedModule (Submonoid.powers r) (pieceToOpenSum 𝒞 r) := by
  rw [isLocalizedModule_iff_isBaseChange (Submonoid.powers r)
    Γ(Spec R, AffineBaseChange.specBasicOpen r)]
  refine IsBaseChange.directSum fun n => ?_
  rw [← isLocalizedModule_iff_isBaseChange (Submonoid.powers r)
    Γ(Spec R, AffineBaseChange.specBasicOpen r)]
  exact AffineBaseChange.isLocalizedModule_toOpenₗ_specBasicOpen (pieceModule 𝒞 n) r

/-- Over `D(r)`, `totalTildeSec` after `pieceToOpenSum` is `inclSum` followed by the canonical map
of `B` into the sections of its associated sheaf. -/
theorem totalTildeSec_comp_pieceToOpenSum (r : R) :
    (totalTildeSec 𝒞 (AffineBaseChange.specBasicOpen r)).comp (pieceToOpenSum 𝒞 r) =
      (AffineBaseChange.toOpenₗ (restrictedAlgebra R B)
        (AffineBaseChange.specBasicOpen r)).comp (inclSum 𝒞) := by
  refine LinearMap.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n x =>
      have h0 : DirectSum.of (fun n => ↥(𝒞 n)) n x =
          DirectSum.lof (R : Type u) ℤ (fun n => ↥(𝒞 n)) n x := rfl
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h0, pieceToOpenSum_lof, inclSum_lof,
        totalTildeSec_lof, pieceTildeSec_toOpen]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The comparison on the direct sum of the sections of the homogeneous pieces over a basic
open is bijective**, once `B` is the internal direct sum of its pieces: both sides are
localizations of `⨁ₙ 𝒞 n` at `r`, and the comparison is the unique map between them. -/
theorem bijective_totalTildeSec (hdec : DirectSum.IsInternal 𝒞) (r : R) :
    Function.Bijective (totalTildeSec 𝒞 (AffineBaseChange.specBasicOpen r)) := by
  have hsum : IsLocalizedModule (Submonoid.powers r) (pieceToOpenSum 𝒞 r) :=
    isLocalizedModule_pieceToOpenSum 𝒞 r
  have hcomp : IsLocalizedModule (Submonoid.powers r)
      ((totalTildeSec 𝒞 (AffineBaseChange.specBasicOpen r)).comp (pieceToOpenSum 𝒞 r)) := by
    rw [totalTildeSec_comp_pieceToOpenSum]
    exact (IsLocalizedModule.comp_iff_of_bijective_right (S := Submonoid.powers r)
      (inclSum 𝒞) (bijective_inclSum 𝒞 hdec)).2
      (AffineBaseChange.isLocalizedModule_toOpenₗ_specBasicOpen (restrictedAlgebra R B) r)
  have hEq := IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp (Submonoid.powers r)
    (pieceToOpenSum 𝒞 r) (totalTildeSec 𝒞 (AffineBaseChange.specBasicOpen r))
  exact hEq ▸ (IsLocalizedModule.linearEquiv (Submonoid.powers r) (pieceToOpenSum 𝒞 r)
    ((totalTildeSec 𝒞 (AffineBaseChange.specBasicOpen r)).comp
      (pieceToOpenSum 𝒞 r))).bijective

/-! ### Bijectivity of the comparison on a basic open -/

/-- The degreewise comparison on sections, factored through the associated sheaf of `B`. -/
theorem pieceToPushforward_app_eq (n : ℤ) (U : (Spec R).Opens)
    (y : Γ(pieceSheaf 𝒞 n, U)) :
    ((pieceToPushforward 𝒞 n).val.app (op U)).hom y =
      ((tildeToPushforward R B).val.app (op U)).hom
        (((AlgebraicGeometry.tilde.map (pieceIncl 𝒞 n)).val.app (op U)).hom y) :=
  rfl

section Ungraded

variable (hmul : ∀ (i j : ℤ) ⦃x y : B⦄, x ∈ 𝒞 i → y ∈ 𝒞 j → x * y ∈ 𝒞 (i + j))
  (hone : (1 : B) ∈ 𝒞 0)

/-- On the image of the degree-`n` piece in the total presheaf, `totalTildeSec` is the map induced
by the inclusion of `𝒞 n` into `B`. -/
theorem totalTildeSec_incl (U : (Spec R).Opens) (n : ℤ)
    (y : ((algebraSheaf 𝒞 hmul hone).piece n).val.obj (op U)) :
    totalTildeSec 𝒞 U ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.incl n y) =
      ((AlgebraicGeometry.tilde.map (pieceIncl 𝒞 n)).val.app (op U)).hom y :=
  totalTildeSec_lof 𝒞 U n y

/-- **The comparison out of the direct sum of the homogeneous components is the comparison into
the associated sheaf of `B` followed by the comparison at all of `B`.** -/
theorem totalAddSec_eq_tildeToPushforward (U : (Spec R).Opens)
    (z : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.Total (op U)) :
    totalAddSec 𝒞 hmul hone U z =
      ((tildeToPushforward R B).val.app (op U)).hom (totalTildeSec 𝒞 U z) := by
  induction z using Stacks.GradedAlgebra.incl_induction with
  | zero =>
      exact (map_zero _).trans ((map_zero ((tildeToPushforward R B).val.app (op U)).hom).symm.trans
        (congrArg _ (map_zero (totalTildeSec 𝒞 U))).symm)
  | incl n y =>
      have e0 : totalAddSec 𝒞 hmul hone U
            ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.incl n y) =
          ((pieceToPushforward 𝒞 n).val.app (op U)).hom y :=
        totalAddSec_incl 𝒞 hmul hone n U y
      exact e0.trans ((pieceToPushforward_app_eq 𝒞 n U y).trans
        (congrArg (fun w => ((tildeToPushforward R B).val.app (op U)).hom w)
          (totalTildeSec_incl 𝒞 hmul hone U n y)).symm)
  | add a b ha hb =>
      exact (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
        ((map_add ((tildeToPushforward R B).val.app (op U)).hom _ _).symm.trans
          (congrArg _ (map_add (totalTildeSec 𝒞 U) a b)).symm))

/-- **The comparison out of the direct sum of the homogeneous components is bijective on the
sections over a basic open**, once `B` is the internal direct sum of its homogeneous pieces. -/
theorem bijective_totalAddSec_specBasicOpen (hdec : DirectSum.IsInternal 𝒞) (r : R) :
    Function.Bijective (totalAddSec 𝒞 hmul hone (AffineBaseChange.specBasicOpen r)) := by
  have hcomp := (bijective_tildeToPushforward_app R B
    (AffineBaseChange.specBasicOpen r)).comp (bijective_totalTildeSec 𝒞 hdec r)
  have h : ∀ z, totalAddSec 𝒞 hmul hone (AffineBaseChange.specBasicOpen r) z =
      ((tildeToPushforward R B).val.app
        (op (AffineBaseChange.specBasicOpen r))).hom
          (totalTildeSec 𝒞 (AffineBaseChange.specBasicOpen r) z) :=
    totalAddSec_eq_tildeToPushforward 𝒞 hmul hone (AffineBaseChange.specBasicOpen r)
  refine ⟨fun a b hab => hcomp.1 (((h a).symm.trans hab).trans (h b)), fun s => ?_⟩
  obtain ⟨a, ha⟩ := hcomp.2 s
  exact ⟨a, (h a).trans ha⟩

/-! ### Local bijectivity, and the isomorphism of sheaves of rings -/

/-- The comparison of presheaves of rings is locally injective: it is injective on the sections
over a basic open, and the basic opens are a basis. -/
theorem isLocallyInjective_totalPresheafHom (hdec : DirectSum.IsInternal 𝒞) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec R : TopCat))
      (totalPresheafHom 𝒞 hmul hone) := by
  constructor
  intro W x y h
  rw [Opens.mem_grothendieckTopology]
  intro pt hpt
  obtain ⟨r, hrpt, hrW⟩ := AffineBaseChange.exists_basicOpen_le (U := W.unop) hpt
  refine ⟨AffineBaseChange.specBasicOpen r, homOfLE hrW, ?_, hrpt⟩
  have hx := NatTrans.naturality_apply (totalPresheafHom 𝒞 hmul hone) (homOfLE hrW).op x
  have hy := NatTrans.naturality_apply (totalPresheafHom 𝒞 hmul hone) (homOfLE hrW).op y
  rw [h] at hx
  exact (bijective_totalAddSec_specBasicOpen 𝒞 hmul hone hdec r).1 (hx.trans hy.symm)

/-- The comparison of presheaves of rings is locally surjective: it is surjective on the sections
over a basic open, and the basic opens are a basis. -/
theorem isLocallySurjective_totalPresheafHom (hdec : DirectSum.IsInternal 𝒞) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec R : TopCat))
      (totalPresheafHom 𝒞 hmul hone) := by
  constructor
  intro W s
  rw [Opens.mem_grothendieckTopology]
  intro pt hpt
  obtain ⟨r, hrpt, hrW⟩ := AffineBaseChange.exists_basicOpen_le (U := W) hpt
  refine ⟨AffineBaseChange.specBasicOpen r, homOfLE hrW, ?_, hrpt⟩
  exact (bijective_totalAddSec_specBasicOpen 𝒞 hmul hone hdec r).2 _

/-- The sheafification unit of the ungraded realization is locally injective: it is the unit of
a sheafification, read off `CategoryTheory.toSheafify`. -/
theorem isLocallyInjective_toTotalSheaf :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Spec R : TopCat))
      ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.toTotalSheaf
        (Opens.grothendieckTopology (Spec R : TopCat))) :=
  ⟨fun x y h => Presheaf.equalizerSieve_mem (Opens.grothendieckTopology (Spec R : TopCat))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (Spec R : TopCat))
      (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.totalPresheaf) x y h⟩

/-- The sheafification unit of the ungraded realization is locally surjective. -/
theorem isLocallySurjective_toTotalSheaf :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Spec R : TopCat))
      ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.toTotalSheaf
        (Opens.grothendieckTopology (Spec R : TopCat))) :=
  ⟨fun s => Presheaf.imageSieve_mem (Opens.grothendieckTopology (Spec R : TopCat))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (Spec R : TopCat))
      (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.totalPresheaf) s⟩

/-- **The comparison of sheaves of rings is an isomorphism**: the ungraded realization of the
algebra sheaf of a graded algebra is `f_* 𝒪_{Spec B}`, once `B` is the internal direct sum of its
homogeneous pieces. -/
theorem isIso_ungradedSheafHom (hdec : DirectSum.IsInternal 𝒞) :
    IsIso (ungradedSheafHom 𝒞 hmul hone) := by
  have hfac : (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.toTotalSheaf
        (Opens.grothendieckTopology (Spec R : TopCat)) ≫
      (ungradedSheafHom 𝒞 hmul hone).hom = totalPresheafHom 𝒞 hmul hone :=
    Stacks.GradedAlgebra.toTotalSheaf_totalSheafLift
      (algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra
      (Opens.grothendieckTopology (Spec R : TopCat)) _ (totalPresheafHom 𝒞 hmul hone)
  have hti := isLocallyInjective_toTotalSheaf 𝒞 hmul hone
  have hts := isLocallySurjective_toTotalSheaf 𝒞 hmul hone
  have hinj := (Presheaf.comp_isLocallyInjective_iff
    (Opens.grothendieckTopology (Spec R : TopCat))
    ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.toTotalSheaf
      (Opens.grothendieckTopology (Spec R : TopCat)))
    (ungradedSheafHom 𝒞 hmul hone).hom).1
    (hfac ▸ isLocallyInjective_totalPresheafHom 𝒞 hmul hone hdec)
  have hsurj := (Presheaf.comp_isLocallySurjective_iff
    (Opens.grothendieckTopology (Spec R : TopCat))
    ((algebraSheaf 𝒞 hmul hone).toPresheafGradedAlgebra.toTotalSheaf
      (Opens.grothendieckTopology (Spec R : TopCat)))
    (ungradedSheafHom 𝒞 hmul hone).hom).1
    (hfac ▸ isLocallySurjective_totalPresheafHom 𝒞 hmul hone hdec)
  exact (Sheaf.isLocallyBijective_iff_isIso (ungradedSheafHom 𝒞 hmul hone)).1
    ⟨hinj, hsurj⟩

/-- The comparison of sheaves of rings is bijective on the sections over every open. -/
theorem bijective_ungradedSheafHom_app (hdec : DirectSum.IsInternal 𝒞) (U : (Spec R).Opens) :
    Function.Bijective ((ungradedSheafHom 𝒞 hmul hone).hom.app (op U)) := by
  have := isIso_ungradedSheafHom 𝒞 hmul hone hdec
  have : IsIso (ungradedSheafHom 𝒞 hmul hone).hom :=
    (inferInstance : IsIso ((sheafToPresheaf (Opens.grothendieckTopology (Spec R : TopCat))
      RingCat.{u}).map (ungradedSheafHom 𝒞 hmul hone)))
  exact ConcreteCategory.bijective_of_isIso ((ungradedSheafHom 𝒞 hmul hone).hom.app (op U))

section Comm

variable (hc : ∀ (i j : ℤ) (W : ((Spec R).Opens)ᵒᵖ)
  (a : ((algebraSheaf 𝒞 hmul hone).piece i).val.obj W)
  (b : ((algebraSheaf 𝒞 hmul hone).piece j).val.obj W),
  HEq (((algebraSheaf 𝒞 hmul hone).mul i j).app W a b)
    (((algebraSheaf 𝒞 hmul hone).mul j i).app W b a))

/-- **The comparison of sheaves of commutative rings is an isomorphism.** It has the same
sections as `Stacks.AffineGradedAlgebra.ungradedSheafHom`, which is bijective on every open. -/
theorem isIso_commSheafHom (hdec : DirectSum.IsInternal 𝒞) :
    IsIso (commSheafHom 𝒞 hmul hone hc) := by
  have happ : ∀ W, IsIso ((commSheafHom 𝒞 hmul hone hc).hom.app W) := fun W =>
    (ConcreteCategory.isIso_iff_bijective
      ((commSheafHom 𝒞 hmul hone hc).hom.app W)).2
      (bijective_ungradedSheafHom_app 𝒞 hmul hone hdec W.unop)
  have hnat : IsIso ((commSheafHom 𝒞 hmul hone hc).hom) := NatIso.isIso_of_isIso_app _
  exact ⟨⟨ObjectProperty.homMk (inv (commSheafHom 𝒞 hmul hone hc).hom),
    ObjectProperty.hom_ext _ (IsIso.hom_inv_id (commSheafHom 𝒞 hmul hone hc).hom),
    ObjectProperty.hom_ext _ (IsIso.inv_hom_id (commSheafHom 𝒞 hmul hone hc).hom)⟩⟩

/-- **Leg (i) of [Stacks, Tag 01LX] in the affine graded case, as an isomorphism.** -/
theorem isIso_toPushforwardAlgebra (hdec : DirectSum.IsInternal 𝒞) :
    IsIso (toPushforwardAlgebra 𝒞 hmul hone hc) := by
  have hmap : IsIso ((Under.forget (Spec R).sheaf).map
      (toPushforwardAlgebra 𝒞 hmul hone hc)) := isIso_commSheafHom 𝒞 hmul hone hc hdec
  exact isIso_of_reflects_iso _ (Under.forget (Spec R).sheaf)

end Comm

end Ungraded

/-! ### The case of `B̃` -/

section Nat

variable {R : CommRingCat.{u}} {B : Type u} [CommRing B] [Algebra R B]
  (𝒜 : ℕ → Submodule R B)

/-- **An `ℕ`-graded algebra is the internal direct sum of the `ℤ`-extension of its grading**:
extending by zero in negative degrees changes neither the independence of the pieces nor their
supremum. -/
theorem isInternal_intPiece [DirectSum.Decomposition 𝒜] :
    DirectSum.IsInternal (intPiece 𝒜) := by
  obtain ⟨hindep, htop⟩ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top 𝒜).1
      (DirectSum.Decomposition.isInternal 𝒜)
  refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (intPiece 𝒜)).2
    ⟨?_, le_antisymm le_top ?_⟩
  · intro i
    match i with
    | .negSucc k =>
        rw [intPiece_negSucc]
        exact disjoint_bot_left
    | .ofNat n =>
        refine Disjoint.mono_right (iSup₂_le fun j hj => ?_) (hindep n)
        match j with
        | .ofNat m =>
            exact le_iSup₂ (f := fun (k : ℕ) (_ : k ≠ n) => 𝒜 k) m
              fun h => hj (congrArg Int.ofNat h)
        | .negSucc k =>
            rw [intPiece_negSucc]
            exact bot_le
  · rw [← htop]
    exact iSup_le fun n => le_iSup (intPiece 𝒜) ((n : ℕ) : ℤ)

variable [SetLike.GradedMonoid 𝒜] [DirectSum.Decomposition 𝒜]

/-- **Leg (i) of [Stacks, Tag 01LX] for `B̃` is an isomorphism**: the canonical morphism of
sheaves of commutative `𝒪_{Spec R}`-algebras from the algebra sheaf presented by `B̃` to
`f_* 𝒪_{Spec B}` is invertible.

The `DirectSum.Decomposition` hypothesis is the notion of a graded algebra of
[Stacks, Tag 00JL]: a ring with a direct sum decomposition `S = ⨁_{d ≥ 0} S_d` satisfying
`S_d · S_e ⊆ S_{d+e}`. Without it the comparison need not be injective (see
`Stacks.AffineGradedAlgebra.toPushforwardAlgebra`). -/
theorem isIso_gradedTildeToPushforwardAlgebra :
    IsIso (gradedTildeToPushforwardAlgebra 𝒜) :=
  isIso_toPushforwardAlgebra (intPiece 𝒜) (mul_mem_intPiece 𝒜) (one_mem_intPiece 𝒜)
    (gradedTilde_mul_comm 𝒜) (isInternal_intPiece 𝒜)

/-- **The algebra sheaf presented by `B̃` is `f_* 𝒪_{Spec B}`**, as sheaves of commutative
`𝒪_{Spec R}`-algebras, by the canonical morphism of
`Stacks.AffineGradedAlgebra.gradedTildeToPushforwardAlgebra`. -/
def gradedTildeToPushforwardAlgebraIso :
    Stacks.RelativeSpec.gradedAlgebraSheaf (Spec R) (gradedTilde 𝒜) (gradedTilde_mul_comm 𝒜) ≅
      AffineAlgebraEquivalence.pushforwardAlgebra (specOfAlgebra R B) :=
  @asIso _ _ _ _ (gradedTildeToPushforwardAlgebra 𝒜)
    (isIso_gradedTildeToPushforwardAlgebra 𝒜)

end Nat

/-- **Leg (i) of [Stacks, Tag 01LX] for `B̃` over a bare commutative ring, as an isomorphism**,
which is the shape in which [Stacks, Tag 0897] uses it. -/
theorem isIso_gradedTildeOfToPushforwardAlgebra (A : Type u) [CommRing A] {B : Type u}
    [CommRing B] [Algebra A B] (𝒜 : ℕ → Submodule A B) [SetLike.GradedMonoid 𝒜]
    [DirectSum.Decomposition 𝒜] :
    IsIso (gradedTildeOfToPushforwardAlgebra A 𝒜) :=
  isIso_gradedTildeToPushforwardAlgebra (R := CommRingCat.of A) 𝒜

end Stacks.AffineGradedAlgebra

end
