module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LineBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionGysin
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullbackChow
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TautologicalSectionBaseRegular
public import StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Basic

/-!
# The zero section of a line bundle pushes a class forward to minus the Chern class pullback

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module and let

  `p : L = \underline{\Spec}(\Sym^*(ℒ)) ⟶ X`

be the associated line bundle, with zero section `o : X ⟶ L`. Clause (5) of [Stacks, Tag 0F96]
asserts

  `o_* α = - p^*(c₁(ℒ) ∩ α)`  for every  `α ∈ \CH_k(X)`.

## Main definitions

* `Stacks.Chow.tensorObjTensorPowerNegOneIso`: the trivialization `ℒ ⊗_{𝒪_X} ℒ^{⊗ -1} ≅ 𝒪_X`.
* `Stacks.LineBundle.Situation.zeroSectionDivisor`: the image `o(X)`, as the zero scheme of the
  tautological section of `p^*(ℒ^{⊗ -1})`.

## Main results

* `Stacks.Chow.zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow`:
  `o_* α = - p^*(c₁(ℒ) ∩ α)`.
* `Stacks.Chow.flatPullbackChowOfRelativeDimension_of_isIso`: flat pullback of relative
  dimension zero along an isomorphism over the base is proper pushforward along its inverse.
* `Stacks.Chow.flatPullbackChowOfRelativeDimension_firstChernClassCapChow`: flat pullback
  commutes with the first Chern class cap product, on Chow classes.
* `Stacks.Chow.firstChernClassCapChow_eq_neg_of_tensorObj_iso_unit`: if `ℒ ⊗_{𝒪_X} ℳ ≅ 𝒪_X`, then
  `c₁(ℳ) ∩ α = -(c₁(ℒ) ∩ α)` on Chow classes.
* `Stacks.LineBundle.Situation.zeroSectionDivisorIso_hom_comp_zeroSection` and
  `Stacks.LineBundle.Situation.zeroSection_eq_zeroSectionDivisorIso_inv_comp`: the zero section
  is the inclusion of `o(X)` read through the isomorphism `o(X) ≅ X`.
* `Stacks.Chow.zeroSectionChowPushforward_eq_properChowPushforward`: `o_*` is the pushforward
  along `i : o(X) ⟶ L` of the transport along `X ≅ o(X)`.

## References

* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

universe u

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

/-! ### The trivialization of the inverse of an invertible module -/

namespace Stacks.Chow

/-- **`ℒ^{⊗ -1}` is invertible**, in the sense of
`AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem isInvertible_tensorPowerNegOne (X : Scheme.{u}) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
        (isSheaf_structureRingPresheaf X) L (-1)) :=
  have hS : Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (@Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower _ _ _ X.presheaf
      (isSheaf_structureRingPresheaf X) _ _ L hS (-1))

/-- **The trivialization `ℒ ⊗_{𝒪_X} ℒ^{⊗ -1} ≅ 𝒪_X`** of the `(-1)`st tensor power of
[Stacks, Tag 01CU], for the tensor product `Scheme.Modules.tensorObj`. -/
def tensorObjTensorPowerNegOneIso (X : Scheme.{u}) (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Scheme.Modules.tensorObj L
        (Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
          (isSheaf_structureRingPresheaf X) L (-1)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI : Stacks.SheafOfModules.IsInvertible X.presheaf (isSheaf_structureRingPresheaf X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf (isSheaf_structureRingPresheaf X) L
      (Stacks.SheafOfModules.TensorPower.tensorPower X.presheaf
        (isSheaf_structureRingPresheaf X) L (-1))).symm ≪≫
    Stacks.ProjBundleInverseBaseChange.negOneMulIso' X.presheaf
      (isSheaf_structureRingPresheaf X) L ≪≫
    AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (isSheaf_structureRingPresheaf X)

/-! ### Stacks 02SP for a tensor inverse, on Chow classes -/

/-- If `ℒ ⊗_{𝒪_X} ℳ ≅ 𝒪_X` then `c₁(ℳ) ∩ α = -(c₁(ℒ) ∩ α)` in `A_k(X)` for every
`α ∈ A_{k+1}(X)`. -/
theorem firstChernClassCapChow_eq_neg_of_tensorObj_iso_unit (C : ChowSituation.{u})
    {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) (L M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (e : Scheme.Modules.tensorObj L M ≅ SheafOfModules.unit X.ringCatSheaf)
    (α : chowGroup C q (k + 1)) :
    firstChernClassCapChow C k q M α = -firstChernClassCapChow C k q L α :=
  congrFun (congrArg DFunLike.coe (firstChernClassCapOnChow_eq_neg_of_tensorObj_iso_unit C q k L M
    (firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k q L)
    (firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k q M)
    e)) α

/-! ### Transports of degrees -/

/-- Pushforward along an isomorphism over the base commutes with transport along an equality of
degrees. -/
theorem chowPushforwardOfIso_chowGroupCast (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (f : A ⟶ B)
    [IsIso f] (hf : f ≫ sB = sA) {k l : ℤ} (h : k = l) (x : chowGroup C sA k) :
    chowGroupCast C sB h (chowPushforwardOfIso C sA sB f hf k x) =
      chowPushforwardOfIso C sA sB f hf l (chowGroupCast C sA h x) := by
  subst h
  rfl

/-- The first Chern class cap product commutes with transport along an equality of degrees, the
argument being transported as an `Eq.rec`. -/
theorem chowGroupCast_firstChernClassCapChow_eqRec (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    {d n n' : ℤ} (hn : n = n') (hd : d = n + 1) (hd' : d = n' + 1) (x : chowGroup C q d) :
    chowGroupCast C q hn (firstChernClassCapChow C n q M (hd ▸ x)) =
      firstChernClassCapChow C n' q M (chowGroupCast C q hd' x) := by
  subst hn hd
  rfl

/-- The first Chern class cap product commutes with transport along an equality of degrees. -/
theorem chowGroupCast_firstChernClassCapChow (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    {d n n' : ℤ} (hn : n = n') (hd : d = n + 1) (hd' : d = n' + 1) (x : chowGroup C q d) :
    chowGroupCast C q hn (firstChernClassCapChow C n q M (chowGroupCast C q hd x)) =
      firstChernClassCapChow C n' q M (chowGroupCast C q hd' x) := by
  subst hn hd
  rfl

/-! ### Flat pullback of relative dimension zero along an isomorphism -/

/-- **Flat pullback of relative dimension zero along an isomorphism over the base is proper
pushforward along the inverse isomorphism**, up to the transport `A_k = A_{k+0}` of degrees. The
inverse is given as a morphism `g` with `g ≫ f = 𝟙`. -/
theorem flatPullbackChowOfRelativeDimension_of_isIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (f : A ⟶ B)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (hf : f ≫ sB = sA)
    (hdim : AlgebraicGeometry.RelativeDimension f 0) (g : B ⟶ A) [IsIso g]
    (hgf : g ≫ f = 𝟙 B) (hg : g ≫ sA = sB) (k : ℤ) (α : chowGroup C sB k) :
    flatPullbackChowOfRelativeDimension C sA sB f hf 0 hdim k α =
      chowGroupCast C sA (show k = k + ((0 : ℕ) : ℤ) from by simp)
        (chowPushforwardOfIso C sB sA g hg k α) := by
  have key := flatPullbackChow_chowPushforwardOfIso C sB sB sB sA (𝟙 B) (Category.id_comp sB)
    g hg (𝟙 B) (Category.id_comp sB) f hf (by rw [Category.id_comp, hgf]) 0
    (relativeDimension_identity B) hdim k
    (flatPullbackFactorsThroughRationalEquivalence_id C sB k)
    (flatPullbackFactorsThroughRationalEquivalence_general C sA sB f hf 0 hdim k) α
  have hid : chowPushforwardOfIso C sB sB (𝟙 B) (Category.id_comp sB) k α = α :=
    congrFun (congrArg DFunLike.coe (properChowPushforward_id C sB k
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sB sB (𝟙 B)
        (Category.id_comp sB) k))) α
  rw [hid, flatPullbackChow_id] at key
  exact key.trans (chowPushforwardOfIso_chowGroupCast C sB sA g hg
    (show k = k + ((0 : ℕ) : ℤ) from by simp) α).symm

/-! ### Stacks 02SS on Chow classes -/

/-- For `f : X' ⟶ X` flat and locally of finite type of relative dimension `r` over the base,
an invertible module `M` on `X` and a class `α ∈ A_{k+1}(X)`,

  `f^*(c₁(M) ∩ α) = c₁(f^*M) ∩ f^*α`  in  `A_{k+r}(X')`. -/
theorem flatPullbackChowOfRelativeDimension_firstChernClassCapChow (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (α : chowGroup C sX (k + 1)) :
    flatPullbackChowOfRelativeDimension C (f ≫ sX) sX f rfl r hf k
        (firstChernClassCapChow C k sX M α) =
      firstChernClassCapChow C (k + (r : ℤ)) (f ≫ sX) ((Scheme.Modules.pullback f).obj M)
        (chowGroupCast C (f ≫ sX) (show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 from by ring)
          (flatPullbackChowOfRelativeDimension C (f ≫ sX) sX f rfl r hf (k + 1) α)) := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    show flatPullbackChowOfRelativeDimension C (f ≫ sX) sX f rfl r hf k
        (firstChernClassCapChow C k sX M
          (QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1)) c)) =
      firstChernClassCapChow C (k + (r : ℤ)) (f ≫ sX) ((Scheme.Modules.pullback f).obj M)
        (chowGroupCast C (f ≫ sX) (show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 from by ring)
          (flatPullbackChowOfRelativeDimension C (f ≫ sX) sX f rfl r hf (k + 1)
            (QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1)) c)))
    rw [firstChernClassCapChow_mk, flatPullbackChowOfRelativeDimension_mk, chowGroupCast_mk,
      firstChernClassCapChow_mk]
    exact flatPullbackChow_firstChernClassCapOfInvertible_of_invertible C sX f r hf k M
      (flatPullbackFactorsThroughRationalEquivalence_general C (f ≫ sX) sX f rfl r hf k) c

end Stacks.Chow

/-! ### The image of the zero section, and the zero section read through it -/

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The image `o(X)` of the zero section of a line bundle**, as the zero scheme of the
tautological global section of `p^*(ℒ^{⊗ -1})`. -/
abbrev Situation.zeroSectionDivisor : D.totalSpace.IdealSheafData :=
  Stacks.Divisors.zeroScheme D.totalSpace D.basePullbackInverse D.tautologicalSectionBase

/-- **The isomorphism `o(X) ≅ X` carries the inclusion of `o(X)` to the zero section**:
`(o(X) ≅ X) ≫ o = i`. -/
theorem Situation.zeroSectionDivisorIso_hom_comp_zeroSection :
    D.zeroSectionDivisorIso.hom ≫ D.zeroSection = D.zeroSectionDivisor.subschemeι := by
  have hker : D.zeroSectionDivisor.subschemeι.ker = D.zeroSection.ker :=
    (Scheme.IdealSheafData.ker_subschemeι D.zeroSectionDivisor).trans
      D.zeroScheme_tautologicalSectionBase_eq_ker_zeroSection
  obtain ⟨l, hfac⟩ : ∃ l : D.zeroSectionDivisor.subscheme ⟶ D.X,
      l ≫ D.zeroSection = D.zeroSectionDivisor.subschemeι :=
    ⟨IsClosedImmersion.lift D.zeroSection D.zeroSectionDivisor.subschemeι hker.ge,
      IsClosedImmersion.lift_fac _ _ _⟩
  rw [Situation.zeroSectionDivisorIso_hom, ← hfac,
    Category.assoc l D.zeroSection D.totalSpaceToBase, D.zeroSection_comp_totalSpaceToBase,
    Category.comp_id]

/-- **The zero section is the inclusion of its image read through `X ≅ o(X)`**:
`o = (X ≅ o(X)) ≫ i`. -/
theorem Situation.zeroSection_eq_zeroSectionDivisorIso_inv_comp :
    D.zeroSection = D.zeroSectionDivisorIso.inv ≫ D.zeroSectionDivisor.subschemeι := by
  rw [← D.zeroSectionDivisorIso_hom_comp_zeroSection, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

end Stacks.LineBundle

namespace Stacks.Chow

attribute [local instance] Stacks.LineBundle.Situation.flat_totalSpaceToBase

variable (C : ChowSituation.{u}) (D : Stacks.LineBundle.Situation.{u}) (sX : D.X ⟶ C.S)
  [LocallyOfFiniteType sX]

omit [LocallyOfFiniteType sX] in
/-- The isomorphism `X ≅ o(X)` is compatible with the structure morphisms over the base situation
of chapter 42. -/
theorem zeroSectionDivisorIso_inv_comp :
    D.zeroSectionDivisorIso.inv ≫
        D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX = sX := by
  rw [← zeroSectionDivisorIso_hom_comp C D sX, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- **Pushforward along the zero section is pushforward along the inclusion of its image,
precomposed with the transport along `X ≅ o(X)`.** -/
theorem zeroSectionChowPushforward_eq_properChowPushforward (k : ℤ) (α : chowGroup C sX k) :
    zeroSectionChowPushforward C D sX k α =
      properChowPushforward C (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX)
          (D.totalSpaceToBase ≫ sX) D.zeroSectionDivisor.subschemeι rfl k
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            D.zeroSectionDivisor.subschemeι C
            (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX)
            (D.totalSpaceToBase ≫ sX) rfl k)
        (chowPushforwardOfIso C sX
          (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX)
          D.zeroSectionDivisorIso.inv (zeroSectionDivisorIso_inv_comp C D sX) k α) := by
  have hcomp := properChowPushforward_comp C sX
    (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX) (D.totalSpaceToBase ≫ sX)
    D.zeroSectionDivisorIso.inv D.zeroSectionDivisor.subschemeι
    (zeroSectionDivisorIso_inv_comp C D sX) rfl k
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C sX
      (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX) D.zeroSectionDivisorIso.inv
      (zeroSectionDivisorIso_inv_comp C D sX) k)
    (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
      D.zeroSectionDivisor.subschemeι C
      (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX) (D.totalSpaceToBase ≫ sX)
      rfl k)
  have h := congrFun (congrArg DFunLike.coe hcomp) α
  rw [properChowPushforward_congr C sX (D.totalSpaceToBase ≫ sX)
    (D.zeroSectionDivisorIso.inv ≫ D.zeroSectionDivisor.subschemeι) D.zeroSection
    D.zeroSection_eq_zeroSectionDivisorIso_inv_comp.symm _
    (zeroSection_comp_totalSpaceToBase_comp C D sX) k _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX
      (D.totalSpaceToBase ≫ sX) D.zeroSection
      (zeroSection_comp_totalSpaceToBase_comp C D sX) k)] at h
  exact h.symm

/-! ### Stacks 02TR, second equality, with the degrees normalised -/

/-- **The second equality of [Stacks, Tag 02TR] for a relative effective Cartier divisor on a
morphism of relative dimension one**, with the degrees written as `k + 1` rather than as
`k + 1 + (0 : ℕ)` and the transports as `Stacks.Chow.chowGroupCast`. The divisor is the zero
scheme of a global section `t : Γ(L, ⊤)`, which is the evaluation of `s : L.sections`. -/
private theorem firstChernClassCapChow_flatPullbackChow_one (C : ChowSituation.{u})
    {T X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : T ⟶ X)
    [LocallyOfFiniteType p] [AlgebraicGeometry.Flat p]
    (hp : AlgebraicGeometry.RelativeDimension p 1) (k : ℤ) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : L.sections) (t : Γ(L, ⊤)) (hst : s.eval (op ⊤) = t)
    [AlgebraicGeometry.Flat ((Stacks.Divisors.zeroScheme T L t).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p (Stacks.Divisors.zeroScheme T L t))
    (α : chowGroup C sX (k + 1)) :
    firstChernClassCapChow C (k + 1) (p ≫ sX) L
        (chowGroupCast C (p ≫ sX) (show k + 1 + ((1 : ℕ) : ℤ) = k + 1 + 1 from by simp)
          (flatPullbackChowOfRelativeDimension C (p ≫ sX) sX p rfl 1 hp (k + 1) α)) =
      properChowPushforward C ((Stacks.Divisors.zeroScheme T L t).subschemeι ≫ p ≫ sX) (p ≫ sX)
          (Stacks.Divisors.zeroScheme T L t).subschemeι rfl (k + 1)
          (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
            (Stacks.Divisors.zeroScheme T L t).subschemeι C
            ((Stacks.Divisors.zeroScheme T L t).subschemeι ≫ p ≫ sX) (p ≫ sX) rfl (k + 1))
        (chowGroupCast C ((Stacks.Divisors.zeroScheme T L t).subschemeι ≫ p ≫ sX)
            (show k + 1 + ((0 : ℕ) : ℤ) = k + 1 from by simp)
          (flatPullbackChowOfRelativeDimension C
            ((Stacks.Divisors.zeroScheme T L t).subschemeι ≫ p ≫ sX) sX
            ((Stacks.Divisors.zeroScheme T L t).subschemeι ≫ p) (Category.assoc _ _ _) 0
            (AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor p 0 hp
              (Stacks.Divisors.zeroScheme T L t) hD) (k + 1) α)) := by
  subst hst
  have h := firstChernClassCapChow_flatPullbackChow C (p ≫ sX) sX p rfl 0 hp k L s hD
    (show k + 1 + ((0 + 1 : ℕ) : ℤ) = k + 1 + ((0 : ℕ) : ℤ) + 1 from by push_cast; ring) α
  rw [← properChowPushforward_chowGroupCast, ← h]
  exact (chowGroupCast_firstChernClassCapChow_eqRec C (p ≫ sX) L
    (show k + 1 + ((0 : ℕ) : ℤ) = k + 1 from by simp)
    (show k + 1 + ((0 + 1 : ℕ) : ℤ) = k + 1 + ((0 : ℕ) : ℤ) + 1 from by push_cast; ring)
    (show k + 1 + ((0 + 1 : ℕ) : ℤ) = k + 1 + 1 from by push_cast; ring)
    (flatPullbackChowOfRelativeDimension C (p ≫ sX) sX p rfl (0 + 1) hp (k + 1) α)).symm

/-! ### Clause (5) of Stacks 0F96 -/

/-- Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S`,
let `ℒ` be an invertible `𝒪_X`-module and let `p : L ⟶ X` be the associated line bundle with
zero section `o : X ⟶ L`. Then

  `o_* α = - p^*(c₁(ℒ) ∩ α)`  in  `A_{k+1}(L)`  for every  `α ∈ A_{k+1}(X)`.

Here `c₁(ℒ) ∩ -` on `A_{k+1}(X)` is `firstChernClassCapChow C k`, and the flat pullback, which
lands in `A_{k + ((1 : ℕ) : ℤ)}(L)`, is transported to `A_{k+1}(L)` by
`Stacks.Chow.chowGroupCast`. -/
@[stacks 0F96 "part (5)"]
theorem zeroSectionChowPushforward_eq_neg_flatPullbackChow_firstChernClassCapChow (k : ℤ)
    (α : chowGroup C sX (k + 1)) :
    zeroSectionChowPushforward C D sX (k + 1) α =
      -chowGroupCast C (D.totalSpaceToBase ≫ sX)
        (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
        (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
          rfl 1 D.relativeDimension_totalSpaceToBase k (firstChernClassCapChow C k sX D.L α)) := by
  have hiso := D.isIso_zeroScheme_tautologicalSectionBase_subschemeι_comp
  have hinvtp := isInvertible_tensorPowerNegOne D.X D.L
  have hinvpb : AlgebraicGeometry.SheafOfModules.IsInvertible D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property
      ((Scheme.Modules.pullback D.totalSpaceToBase).obj
        (Stacks.SheafOfModules.TensorPower.tensorPower D.X.presheaf
          (isSheaf_structureRingPresheaf D.X) D.L (-1))) :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible D.totalSpace.sheaf.obj
      D.totalSpace.ringCatSheaf.property D.basePullbackInverse)
  have hpush := zeroSectionChowPushforward_eq_properChowPushforward C D sX (k + 1) α
  have hflat := flatPullbackChowOfRelativeDimension_of_isIso C
    (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase ≫ sX) sX
    (D.zeroSectionDivisor.subschemeι ≫ D.totalSpaceToBase) (Category.assoc _ _ _)
    (AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor D.totalSpaceToBase 0
      D.relativeDimension_totalSpaceToBase D.zeroSectionDivisor
      D.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase)
    D.zeroSectionDivisorIso.inv
    (by rw [← Stacks.LineBundle.Situation.zeroSectionDivisorIso_hom]; exact
      D.zeroSectionDivisorIso.inv_hom_id)
    (zeroSectionDivisorIso_inv_comp C D sX) (k + 1) α
  have h02TR := firstChernClassCapChow_flatPullbackChow_one C sX D.totalSpaceToBase
    D.relativeDimension_totalSpaceToBase k D.basePullbackInverse
    D.tautologicalSectionBaseSections D.tautologicalSectionBase rfl
    D.isRelativeEffectiveCartierDivisor_zeroScheme_tautologicalSectionBase α
  have h02SS := flatPullbackChowOfRelativeDimension_firstChernClassCapChow C sX
    D.totalSpaceToBase 1 D.relativeDimension_totalSpaceToBase k
    (Stacks.SheafOfModules.TensorPower.tensorPower D.X.presheaf
      (isSheaf_structureRingPresheaf D.X) D.L (-1)) α
  have h02SP := firstChernClassCapChow_eq_neg_of_tensorObj_iso_unit C sX k D.L
    (Stacks.SheafOfModules.TensorPower.tensorPower D.X.presheaf
      (isSheaf_structureRingPresheaf D.X) D.L (-1))
    (tensorObjTensorPowerNegOneIso D.X D.L) α
  simp only [hflat, chowGroupCast_chowGroupCast, chowGroupCast_rfl] at h02TR
  rw [hpush, ← h02TR, ← map_neg, ← map_neg, ← h02SP, h02SS]
  exact (chowGroupCast_firstChernClassCapChow C (D.totalSpaceToBase ≫ sX)
    ((Scheme.Modules.pullback D.totalSpaceToBase).obj
      (Stacks.SheafOfModules.TensorPower.tensorPower D.X.presheaf
        (isSheaf_structureRingPresheaf D.X) D.L (-1)))
    (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp)
    (show k + 1 + ((1 : ℕ) : ℤ) = k + ((1 : ℕ) : ℤ) + 1 from by push_cast; ring)
    (show k + 1 + ((1 : ℕ) : ℤ) = k + 1 + 1 from by simp)
    (flatPullbackChowOfRelativeDimension C (D.totalSpaceToBase ≫ sX) sX D.totalSpaceToBase
      rfl 1 D.relativeDimension_totalSpaceToBase (k + 1) α)).symm

end Stacks.Chow

end
