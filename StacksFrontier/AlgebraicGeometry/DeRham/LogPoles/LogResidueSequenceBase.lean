module

public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DeRhamComplexLogPoles
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ShiftedBoundarySequence
public import StacksFrontier.AlgebraicGeometry.DeRham.InverseImageLinear
public import StacksFrontier.Algebra.Homology.Embedding.ExtendDesuspend
public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology

/-!
# The residue sequence of log poles in sheaves of `f^{-1}𝒪_S`-modules

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` an effective Cartier divisor, cut out by `I`,
for which the de Rham complex of log poles is defined (Stacks Tag 0FMV). Stacks Tag 0FMW is the
short exact sequence

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`,

and the proof of Tag 0FUQ takes the boundary map `δ : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]` of its translate
in `D(X, f^{-1}𝒪_S)`. `StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidueSequence` has the
sequence in sheaves of abelian groups and
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DeRhamComplexLogPoles` the middle term as a complex
of sheaves of `f^{-1}𝒪_S`-modules (Tag 0FUA). This file supplies the rest in that category: the
de Rham complex of the divisor read on `X`, the restriction of forms, the residue, and the
sequence, unshifted and shifted.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.divisorDeRhamBase` and `AlgebraicGeometry.Scheme.Hom
  .divisorDeRhamInt`: `Ω^•_{Y/S}` read on `X`, i.e. `i_*Ω^•_{Y/S}`, over `ℕ` and over `ℤ`.
* `AlgebraicGeometry.Scheme.Hom.divisorRestrictionBase` and `AlgebraicGeometry.Scheme.Hom
  .divisorRestrictionInt`: the restriction of forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`.
* `AlgebraicGeometry.Scheme.Hom.logResidueBaseMap` and `AlgebraicGeometry.Scheme.Hom
  .logResidueInt`: the residue `Ω^•_{X/S}(log Y) ⟶ Ω^•_{Y/S}[-1]`.
* `AlgebraicGeometry.Scheme.Hom.logPolesShiftedSequence`: **Tag 0FMW, shifted**,
  `0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.logResidueBaseShortComplex_shortExact`: **Tag 0FMW** in sheaves
  of `f^{-1}𝒪_S`-modules, over `ℕ`.
* `AlgebraicGeometry.Scheme.Hom.logResidueInt_shortExact`: the same over `ℤ`.

## Implementation notes

The differential of `i_*Ω^•_{Y/S}` is linear over `f^{-1}𝒪_S` by
`AlgebraicGeometry.Scheme.Hom.pushforwardDeRham_appLE_smul`, and every other map is a morphism of
`𝒪_X`-modules in each degree; all identities between maps are checked after the faithful
forgetful functor to abelian sheaves, where they are those of
`StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.LogResidueSequence` and
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMapDeRham`.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open scoped ZeroObject

universe u

attribute [local implicit_reducible] TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-! ### The de Rham complex of the divisor, read on `X` -/

/-- The de Rham differential of `Y/S`, pushed forward to `X`, as a morphism of sheaves of
`f^{-1}𝒪_S`-modules. -/
def divisorDBase (p : ℕ) :
    (toBaseModules f).obj (divisorForms f I p) ⟶ (toBaseModules f).obj (divisorForms f I (p + 1)) :=
  baseLinearHom f (pushforwardDeRhamDifferentialPresheafHom I.subschemeι f p)
    (pushforwardDeRham_appLE_smul f I.subschemeι p)

/-- The underlying morphism of abelian sheaves of `divisorDBase f I p` is the pushed-forward
de Rham differential `pushforwardDeRhamDifferentialAbHom`. -/
theorem toSheaf_map_divisorDBase (p : ℕ) :
    (SheafOfModules.toSheaf (baseRingSheaf f)).map (divisorDBase f I p) =
      pushforwardDeRhamDifferentialAbHom I.subschemeι f p :=
  rfl

/-- Two consecutive differentials `divisorDBase` compose to zero. -/
theorem divisorDBase_comp (p : ℕ) : divisorDBase f I p ≫ divisorDBase f I (p + 1) = 0 :=
  (SheafOfModules.toSheaf (baseRingSheaf f)).map_injective
    ((Functor.map_comp _ _ _).trans ((pushforwardDeRhamDifferentialAbHom_comp f I p).trans
      (Functor.map_zero _ _ _).symm))

/-- **The de Rham complex `i_*Ω^•_{Y/S}` of the divisor, read on `X`**, as a complex of sheaves
of `f^{-1}𝒪_S`-modules: the de Rham complex of `Y ⟶ S` pushed forward along the closed immersion
`i : Y ⟶ X`. -/
def divisorDeRhamBase : CochainComplex (SheafOfModules.{u} (baseRingSheaf f)) ℕ :=
  CochainComplex.of (fun p => (toBaseModules f).obj (divisorForms f I p)) (divisorDBase f I)
    (divisorDBase_comp f I)

/-- The differential of `divisorDeRhamBase f I` from degree `p` to `p + 1` is
`divisorDBase f I p`. -/
theorem divisorDeRhamBase_d (p : ℕ) : (divisorDeRhamBase f I).d p (p + 1) = divisorDBase f I p := by
  unfold divisorDeRhamBase
  exact CochainComplex.of_d (fun p => (toBaseModules f).obj (divisorForms f I p))
    (divisorDBase f I) p

/-- **The restriction of forms `Ω^•_{X/S} ⟶ i_*Ω^•_{Y/S}`**, the horizontal arrow of the square
of Stacks Tag 0FUQ, as a map of complexes of sheaves of `f^{-1}𝒪_S`-modules. In degree `p` it is
the morphism of `𝒪_X`-modules `AlgebraicGeometry.Scheme.Hom.formRestriction`. -/
def divisorRestrictionBase : deRhamComplex f ⟶ divisorDeRhamBase f I where
  f p := (toBaseModules f).map (formRestriction I.subschemeι f (p : ℤ))
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [divisorDeRhamBase_d]
    exact (SheafOfModules.toSheaf (baseRingSheaf f)).map_injective
      ((Functor.map_comp _ _ _).trans
        ((formRestriction_comm_deRhamDifferentialAbHom I.subschemeι f i).trans
          (Functor.map_comp (SheafOfModules.toSheaf (baseRingSheaf f))
            ((deRhamComplex f).d i (i + 1))
            ((toBaseModules f).map (formRestriction I.subschemeι f ((i + 1 : ℕ) : ℤ)))).symm))

/-- In degree `p`, `divisorRestrictionBase f I` is the restriction of forms `formRestriction`. -/
theorem divisorRestrictionBase_f (p : ℕ) :
    (divisorRestrictionBase f I).f p = (toBaseModules f).map (formRestriction I.subschemeι f p) :=
  rfl

/-! ### The residue -/

variable {I} (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
  (hlog : f.HasLogPolesDeRhamComplex I)

/-- The residue in each degree, in sheaves of `f^{-1}𝒪_S`-modules: `0` in degree `0` and
`AlgebraicGeometry.Scheme.Hom.logResHom` in degree `p + 1`. -/
def logResidueBaseF :
    ∀ n : ℕ, logPolesFormsBase f I n ⟶ CochainComplex.desuspendX (divisorDeRhamBase f I) n
  | 0 => 0
  | p + 1 => (toBaseModules f).map (logResHom f I hI hlog p)

/-- The underlying morphism of abelian sheaves of `logDBaseHom f I hI hlog p` is
`logDAbHom f I hI hlog p`. -/
theorem toSheaf_map_logDBaseHom (p : ℕ) :
    (SheafOfModules.toSheaf (baseRingSheaf f)).map (logDBaseHom f I hI hlog p) =
      logDAbHom f I hI hlog p :=
  rfl

/-- The underlying morphism of abelian sheaves of the residue `logResidueBaseF` in degree
`p + 1` is `logResidueF f I hI hlog (p + 1)`. -/
theorem toSheaf_map_logResidueBaseF_succ (p : ℕ) :
    (SheafOfModules.toSheaf (baseRingSheaf f)).map (logResidueBaseF f hI hlog (p + 1)) =
      logResidueF f I hI hlog (p + 1) :=
  rfl

/-- The residue `logResidueBaseF` commutes with the differentials of
`deRhamComplexLogPoles f I hI hlog` and of the desuspension of `divisorDeRhamBase f I`. -/
theorem logResidueBaseF_comm (n : ℕ) :
    logResidueBaseF f hI hlog n ≫ CochainComplex.desuspendD (divisorDeRhamBase f I) n =
      logDBaseHom f I hI hlog n ≫ logResidueBaseF f hI hlog (n + 1) := by
  have h := logResidueF_comm f I hI hlog n
  have hR : (SheafOfModules.toSheaf (baseRingSheaf f)).map
      (logDBaseHom f I hI hlog n ≫ logResidueBaseF f hI hlog (n + 1)) =
        logDAbHom f I hI hlog n ≫ logResidueF f I hI hlog (n + 1) :=
    (Functor.map_comp _ _ _).trans (by
      rw [toSheaf_map_logDBaseHom, toSheaf_map_logResidueBaseF_succ]; rfl)
  cases n with
  | zero =>
    refine zero_comp.trans ?_
    refine ((SheafOfModules.toSheaf (baseRingSheaf f)).map_injective ?_).symm
    rw [hR, ← h, Functor.map_zero]
    exact zero_comp
  | succ p =>
    refine (SheafOfModules.toSheaf (baseRingSheaf f)).map_injective ?_
    rw [hR, ← h, Functor.map_comp, toSheaf_map_logResidueBaseF_succ]
    have hd : CochainComplex.desuspendD (divisorDeRhamBase f I) (p + 1) = -divisorDBase f I p := by
      show -(divisorDeRhamBase f I).d p (p + 1) = _
      rw [divisorDeRhamBase_d]
      rfl
    rw [hd]
    exact congrArg (logResidueF f I hI hlog (p + 1) ≫ ·)
      ((SheafOfModules.toSheaf (baseRingSheaf f)).map_neg (f := divisorDBase f I p))

/-- **The residue `Ω^•_{X/S}(log Y) ⟶ i_*Ω^•_{Y/S}[-1]`** as a map of complexes of sheaves of
`f^{-1}𝒪_S`-modules, `α + d log t ∧ β ↦ β|_Y`; its underlying map of abelian complexes is
`AlgebraicGeometry.Scheme.Hom.logResidueMap`. -/
def logResidueBaseMap :
    deRhamComplexLogPoles f I hI hlog ⟶ CochainComplex.desuspend (divisorDeRhamBase f I) :=
  CochainComplex.ofHom (logResidueBaseF f hI hlog) fun n => by
    rw [CochainComplex.desuspend_d, deRhamComplexLogPoles_d]
    exact logResidueBaseF_comm f hI hlog n

/-- In degree `p + 1`, the residue `logResidueBaseMap` is the image of `logResHom f I hI hlog p`
in sheaves of `f^{-1}𝒪_S`-modules. -/
theorem logResidueBaseMap_f_succ (p : ℕ) :
    (logResidueBaseMap f hI hlog).f (p + 1) = (toBaseModules f).map (logResHom f I hI hlog p) :=
  rfl

/-- The inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` followed by the residue is zero. -/
theorem deRhamComplexLogPolesInclusion_comp_logResidueBaseMap :
    deRhamComplexLogPolesInclusion f I hI hlog ≫ logResidueBaseMap f hI hlog = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero => exact comp_zero
  | succ p =>
    have h0 : logPolesFormsInclusion f I (p + 1) ≫ logResHom f I hI hlog p = 0 := by
      have : (abelianSheaf X).Faithful :=
        inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
      refine (abelianSheaf X).map_injective ?_
      rw [Functor.map_comp, Functor.map_zero]
      have h := congrArg (fun k => HomologicalComplex.Hom.f k (p + 1))
        (logInclusionMap_comp_logResidueMap f I hI hlog)
      simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
      exact h
    show (toBaseModules f).map (logPolesFormsInclusion f I (p + 1)) ≫
      (toBaseModules f).map (logResHom f I hI hlog p) = 0
    rw [← Functor.map_comp, h0, Functor.map_zero]

/-- **The residue sequence of log poles
`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → i_*Ω^•_{Y/S}[-1] → 0` of complexes of sheaves of
`f^{-1}𝒪_S`-modules**, indexed by `ℕ`. -/
abbrev logResidueBaseShortComplex :
    ShortComplex (CochainComplex (SheafOfModules.{u} (baseRingSheaf f)) ℕ) :=
  ShortComplex.mk (deRhamComplexLogPolesInclusion f I hI hlog) (logResidueBaseMap f hI hlog)
    (deRhamComplexLogPolesInclusion_comp_logResidueBaseMap f hI hlog)

/-- **Stacks Project, Tag 0FMW, in sheaves of `f^{-1}𝒪_S`-modules.** The residue sequence of log
poles is short exact: forgetting the module structure is faithful, and the underlying sequence of
abelian sheaves is `AlgebraicGeometry.Scheme.Hom.logResidueShortComplex_shortExact`. -/
theorem logResidueBaseShortComplex_shortExact :
    (logResidueBaseShortComplex f hI hlog).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  refine CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (SheafOfModules.toSheaf (baseRingSheaf f)) ?_
  cases n with
  | succ p => exact shortExact_eval_succ f I hI hlog p
  | zero =>
    refine ShortComplex.shortExact_of_iso ?_ (shortExact_eval_zero f I hI hlog)
    have hz : IsZero ((SheafOfModules.toSheaf (baseRingSheaf f)).obj
        (CochainComplex.desuspendX (divisorDeRhamBase f I) 0)) :=
      Functor.map_isZero (SheafOfModules.toSheaf (baseRingSheaf f)) (isZero_zero _)
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) ((isZero_zero _).iso hz) ?_ ?_
    · exact (Category.id_comp _).trans
        (Category.comp_id ((logInclusionMap f I hI hlog).f 0)).symm
    · exact hz.eq_of_tgt _ _

/-! ### The sequence indexed by `ℤ`, unshifted and shifted -/

variable (I) in
/-- **`Ω^•_{Y/S}`, the de Rham complex of the divisor read on `X`**, as a complex of sheaves of
`f^{-1}𝒪_S`-modules indexed by `ℤ`: `i_*Ω^•_{Y/S}` extended by zero to negative degrees. This is
the right-hand term of the square of Stacks Tag 0FUQ. -/
abbrev divisorDeRhamInt : CochainComplex (SheafOfModules.{u} (baseRingSheaf f)) ℤ :=
  (divisorDeRhamBase f I).extend ComplexShape.embeddingUpNat

variable (I) in
/-- **The restriction of forms `Ω^•_{X/S} ⟶ Ω^•_{Y/S}`**, indexed by `ℤ`: the horizontal arrows
of the square of Stacks Tag 0FUQ. -/
abbrev divisorRestrictionInt :
    AlgebraicGeometry.SheafOfModules.deRhamComplexInt (deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f)) ⟶
      divisorDeRhamInt f I :=
  HomologicalComplex.extendMap (divisorRestrictionBase f I) ComplexShape.embeddingUpNat

/-- The residue `Ω^•_{X/S}(log Y) ⟶ Ω^•_{Y/S}[-1]`, indexed by `ℤ`, with `[-1]` the translation
of `D(X, f^{-1}𝒪_S)`. -/
def logResidueInt :
    deRhamComplexLogPolesInt f I hI hlog ⟶ (divisorDeRhamInt f I)⟦(-1 : ℤ)⟧ :=
  HomologicalComplex.extendMap (logResidueBaseMap f hI hlog) ComplexShape.embeddingUpNat ≫
    (CochainComplex.desuspendExtendIso (divisorDeRhamBase f I)).hom

/-- The inclusion `Ω^•_{X/S} ⟶ Ω^•_{X/S}(log Y)` followed by the residue `logResidueInt` is zero,
indexed by `ℤ`. -/
theorem deRhamComplexLogPolesIntInclusion_comp_logResidueInt :
    deRhamComplexLogPolesIntInclusion f I hI hlog ≫ logResidueInt f hI hlog = 0 := by
  have h : HomologicalComplex.extendMap (deRhamComplexLogPolesInclusion f I hI hlog)
        ComplexShape.embeddingUpNat ≫
      HomologicalComplex.extendMap (logResidueBaseMap f hI hlog) ComplexShape.embeddingUpNat =
        0 := by
    rw [← HomologicalComplex.extendMap_comp,
      deRhamComplexLogPolesInclusion_comp_logResidueBaseMap, HomologicalComplex.extendMap_zero]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans zero_comp)

/-- **Stacks Project, Tag 0FMW, indexed by `ℤ`, in sheaves of `f^{-1}𝒪_S`-modules**: the sequence

`0 → Ω^•_{X/S} → Ω^•_{X/S}(log Y) → Ω^•_{Y/S}[-1] → 0`

with `Ω^•_{X/S}` the complex `deRhamComplexInt` of Tag 0FU7 and `[-1]` the translation of
`D(X, f^{-1}𝒪_S)`, is short exact. -/
theorem logResidueInt_shortExact :
    (ShortComplex.mk _ _
      (deRhamComplexLogPolesIntInclusion_comp_logResidueInt f hI hlog)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (ComplexShape.Embedding.shortExact_map_extendFunctor
    ComplexShape.embeddingUpNat (logResidueBaseShortComplex_shortExact f hI hlog))
  exact ShortComplex.isoMk (S₁ := (logResidueBaseShortComplex f hI hlog).map
      (ComplexShape.embeddingUpNat.extendFunctor _)) (Iso.refl _) (Iso.refl _)
    (CochainComplex.desuspendExtendIso (divisorDeRhamBase f I))
    ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)

/-- **Stacks Project, Tag 0FMW, in the shifted presentation of the proof of Tag 0FUQ**: the short
exact sequence

`0 → Ω^•_{X/S}[1] → Ω^•_{X/S}(log Y)[1] → Ω^•_{Y/S} → 0`

of complexes of sheaves of `f^{-1}𝒪_S`-modules. Its boundary map
`Stacks.ShiftedBoundary.Sequence.boundary : Ω^•_{Y/S} ⟶ Ω^•_{X/S}[2]` in `D(X, f^{-1}𝒪_S)` is the
`δ` of Tag 0FUQ ("we define `δ` as the boundary map corresponding to the shifted short exact
sequence"). -/
def logPolesShiftedSequence :
    Stacks.ShiftedBoundary.Sequence (C := SheafOfModules.{u} (baseRingSheaf f))
      (AlgebraicGeometry.SheafOfModules.deRhamComplexInt (deRhamAlgebras f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f)))
      (divisorDeRhamInt f I) :=
  Stacks.ShiftedBoundary.Sequence.ofShortExact _ _ _ (logResidueInt_shortExact f hI hlog)

end AlgebraicGeometry.Scheme.Hom
