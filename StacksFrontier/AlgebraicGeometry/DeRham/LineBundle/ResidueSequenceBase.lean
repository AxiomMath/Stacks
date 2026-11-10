module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueSequence
public import StacksFrontier.AlgebraicGeometry.DeRham.InverseImageLinear
public import StacksFrontier.Algebra.Homology.Embedding.ExtendDesuspend
public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.ShiftedBoundarySequence
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.ResidueBoundary

/-!
# The residue sequence of a line bundle in sheaves of `f^{-1}𝒪_S`-modules

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module and `π : L^⋆ ⟶ X` the
complement of the zero section of its line bundle. Stacks Tag 0FUF is the short exact sequence

`0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0`,

whose boundary map in `D(X, f^{-1}𝒪_S)` Tag 0FUG identifies with the map of Remark 0FU7 attached
to `c₁^{dR}(L)`. `StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.ResidueSequence` builds the
sequence in sheaves of abelian groups. This file lifts it to the category in which the source
states it, complexes of sheaves of `f^{-1}𝒪_S`-modules, indexed by `ℤ` and with the translation
of `D(X, f^{-1}𝒪_S)`, on the de Rham complex `deRhamComplexInt` of Tag 0FU7.

## Main definitions

* `Stacks.LineBundle.Situation.weightZeroBaseComplex`: `Ω^•_{L^⋆/S,0}` in sheaves of
  `f^{-1}𝒪_S`-modules.
* `Stacks.LineBundle.Situation.inclusionBaseMap` and
  `Stacks.LineBundle.Situation.residueBaseMap`: the pullback of forms and the residue.
* `Stacks.LineBundle.Situation.residueBaseSequence`: **Tag 0FUF**, as a term of
  `AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence`.
* `Stacks.LineBundle.Situation.residueShiftedSequence`: **Tag 0FUF, shifted**,
  `0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0`, whose boundary map is the one of the
  proofs of Tags 0FUG and 0FUQ.

## Main results

* `Stacks.LineBundle.Situation.weightZeroD_appLE_smul`: the differential of `Ω^•_{L^⋆/S,0}` is
  linear over the base, which is what makes it a morphism of sheaves of `f^{-1}𝒪_S`-modules.
* `Stacks.LineBundle.Situation.residueBaseShortComplex_shortExact`: **Tag 0FUF** in sheaves of
  `f^{-1}𝒪_S`-modules, over `ℕ`.

## Implementation notes

The right-hand term `Ω^•_{X/S}[-1]` is `CochainComplex.desuspend` of the de Rham complex, built
over `ℕ`, and `CochainComplex.desuspendExtendIso` identifies its extension by zero with the
translate `(deRhamComplexInt)⟦-1⟧`.

Every term is an `𝒪_X`-module read over `f^{-1}𝒪_S` by restriction of scalars,
`AlgebraicGeometry.Scheme.Hom.toBaseModules`, and every map has the same underlying map of abelian
sheaves as the corresponding map of `StacksDraft.AlgebraicGeometry.DeRham.LineBundle
.ResidueSequence`, by definition. Identities between maps are therefore checked after the
faithful forgetful functor `SheafOfModules.toSheaf`, and short exactness is reflected by it
(`CategoryTheory.ShortExact.reflects_shortExact_of_faithful`) from the abelian sequence.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF)
* [Stacks Project, Tag 0FUQ](https://stacks.math.columbia.edu/tag/0FUQ)
* [Stacks Project, Tag 011G](https://stacks.math.columbia.edu/tag/011G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom)
open scoped ZeroObject

universe u

attribute [local implicit_reducible] TopCat.Sheaf

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **The de Rham differential of `Ω^•_{L^⋆/S}` pushed forward to `X` is linear over the base.** -/
theorem Situation.gradedDiff_appLE_smul (p : ℕ) (V : D.S.Opens) (W : D.X.Opens)
    (hWV : W ≤ D.f ⁻¹ᵁ V) (s : Γ(D.S, V)) (ω : Γ(D.gradedAmbient p, W)) :
    D.gradedDiff p W ((D.f.appLE V W hWV).hom s • ω) =
      (D.f.appLE V W hWV).hom s • D.gradedDiff p W ω :=
  Scheme.Hom.pushforwardDeRham_appLE_smul D.f D.laurentSpectrumToBase p V W hWV s ω

/-- **The differential of `Ω^•_{L^⋆/S,0}` is linear over the base.** -/
theorem Situation.weightZeroD_appLE_smul (p : ℕ) (V : D.S.Opens) (W : D.X.Opens)
    (hWV : W ≤ D.f ⁻¹ᵁ V) (s : Γ(D.S, V)) (x : Γ(D.weightZero p, W)) :
    (D.weightZeroDPresheafHom p).app (op W) ((D.f.appLE V W hWV).hom s • x) =
      (D.f.appLE V W hWV).hom s • (D.weightZeroDPresheafHom p).app (op W) x :=
  D.weightZeroVal_injective (p + 1) (D.gradedDiff_appLE_smul p V W hWV s (D.weightZeroVal p x))

/-- **The differential of `Ω^•_{L^⋆/S,0}`, as a morphism of sheaves of `f^{-1}𝒪_S`-modules.** -/
def Situation.weightZeroBaseD (p : ℕ) :
    (Scheme.Hom.toBaseModules D.f).obj (D.weightZero p) ⟶
      (Scheme.Hom.toBaseModules D.f).obj (D.weightZero (p + 1)) :=
  Scheme.Hom.baseLinearHom D.f (D.weightZeroDPresheafHom p) (D.weightZeroD_appLE_smul p)

/-- The underlying map of abelian sheaves of `Stacks.LineBundle.Situation.weightZeroBaseD p` is
`Stacks.LineBundle.Situation.weightZeroDAbHom p`. -/
theorem Situation.toSheaf_map_weightZeroBaseD (p : ℕ) :
    (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)).map (D.weightZeroBaseD p) =
      D.weightZeroDAbHom p :=
  rfl

/-- Two consecutive differentials of `Ω^•_{L^⋆/S,0}` in sheaves of `f^{-1}𝒪_S`-modules compose to
zero. -/
theorem Situation.weightZeroBaseD_comp (p : ℕ) :
    D.weightZeroBaseD p ≫ D.weightZeroBaseD (p + 1) = 0 :=
  (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)).map_injective
    ((Functor.map_comp _ _ _).trans (D.weightZeroDAbHom_comp p))

/-- **The weight-zero de Rham complex `Ω^•_{L^⋆/S,0}` as a complex of sheaves of
`f^{-1}𝒪_S`-modules on `X`.** Its underlying complex of abelian sheaves is
`Stacks.LineBundle.Situation.weightZeroComplex`. -/
def Situation.weightZeroBaseComplex :
    CochainComplex (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf D.f)) ℕ :=
  CochainComplex.of (fun p => (Scheme.Hom.toBaseModules D.f).obj (D.weightZero p))
    D.weightZeroBaseD D.weightZeroBaseD_comp

/-- The differential of `Stacks.LineBundle.Situation.weightZeroBaseComplex` from degree `p` to
`p + 1` is `Stacks.LineBundle.Situation.weightZeroBaseD p`. -/
theorem Situation.weightZeroBaseComplex_d (p : ℕ) :
    D.weightZeroBaseComplex.d p (p + 1) = D.weightZeroBaseD p := by
  unfold Situation.weightZeroBaseComplex
  exact CochainComplex.of_d (fun p => (Scheme.Hom.toBaseModules D.f).obj (D.weightZero p))
    D.weightZeroBaseD p

/-- **The inclusion `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}`**, the pullback of forms along `π`, as a map of
complexes of sheaves of `f^{-1}𝒪_S`-modules; its underlying map of abelian complexes is
`Stacks.LineBundle.Situation.inclusionMap`. -/
def Situation.inclusionBaseMap : Scheme.Hom.deRhamComplex D.f ⟶ D.weightZeroBaseComplex where
  f p := (Scheme.Hom.toBaseModules D.f).map (D.pullbackHom p)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [D.weightZeroBaseComplex_d]
    have h := D.inclusionMap.comm i (i + 1)
    rw [D.weightZeroComplex_d, Scheme.Hom.deRhamAbComplex_d] at h
    exact (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)).map_injective
      ((Functor.map_comp _ _ _).trans (h.trans (Functor.map_comp
        (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f))
        ((Scheme.Hom.deRhamComplex D.f).d i (i + 1))
        ((Scheme.Hom.toBaseModules D.f).map (D.pullbackHom (i + 1)))).symm))

/-- The residue in each degree, in sheaves of `f^{-1}𝒪_S`-modules: `0` in degree `0` and
`Stacks.LineBundle.Situation.residueHom` in degree `p + 1`. -/
def Situation.residueBaseF :
    ∀ n : ℕ, (Scheme.Hom.toBaseModules D.f).obj (D.weightZero n) ⟶
      CochainComplex.desuspendX (Scheme.Hom.deRhamComplex D.f) n
  | 0 => 0
  | p + 1 => (Scheme.Hom.toBaseModules D.f).map (D.residueHom p)

/-- The degreewise residues commute with the differentials of `Ω^•_{L^⋆/S,0}` and of
`Ω^•_{X/S}[-1]`. -/
theorem Situation.residueBaseF_comm (n : ℕ) :
    D.residueBaseF n ≫ CochainComplex.desuspendD (Scheme.Hom.deRhamComplex D.f) n =
      D.weightZeroBaseD n ≫ D.residueBaseF (n + 1) := by
  have h := D.residueF_comm n
  cases n with
  | zero =>
    refine zero_comp.trans ?_
    refine ((SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)).map_injective ?_).symm
    refine (Functor.map_comp _ _ _).trans (h.symm.trans ?_)
    exact zero_comp.trans (Functor.map_zero _ _ _).symm
  | succ p =>
    refine (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)).map_injective ?_
    refine (Functor.map_comp _ _ _).trans ?_
    refine Eq.trans ?_ (h.trans (Functor.map_comp
      (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)) (D.weightZeroBaseD (p + 1))
      (D.residueBaseF (p + 1 + 1))).symm)
    exact congrArg (fun k => (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)).map
      (D.residueBaseF (p + 1)) ≫ k) (Functor.map_neg _)

/-- **The residue `Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}[-1]`** as a map of complexes of sheaves of
`f^{-1}𝒪_S`-modules; its underlying map of abelian complexes is
`Stacks.LineBundle.Situation.residueMap`. -/
def Situation.residueBaseMap :
    D.weightZeroBaseComplex ⟶ CochainComplex.desuspend (Scheme.Hom.deRhamComplex D.f) :=
  CochainComplex.ofHom D.residueBaseF fun n => by
    rw [CochainComplex.desuspend_d, D.weightZeroBaseComplex_d]
    exact D.residueBaseF_comm n

/-- The composite of the inclusion `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` and the residue
`Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}[-1]` is zero. -/
theorem Situation.inclusionBaseMap_comp_residueBaseMap :
    D.inclusionBaseMap ≫ D.residueBaseMap = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  cases n with
  | zero => exact comp_zero
  | succ p =>
    have h0 : D.pullbackHom (p + 1) ≫ D.residueHom p = 0 := by
      have : (abelianSheaf D.X).Faithful :=
        inferInstanceAs (SheafOfModules.toSheaf D.X.ringCatSheaf).Faithful
      refine (abelianSheaf D.X).map_injective ?_
      rw [Functor.map_comp, Functor.map_zero]
      have h := congrArg (fun k => HomologicalComplex.Hom.f k (p + 1))
        D.inclusionMap_comp_residueMap
      simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
      exact h
    change (Scheme.Hom.toBaseModules D.f).map (D.pullbackHom (p + 1)) ≫
      (Scheme.Hom.toBaseModules D.f).map (D.residueHom p) = 0
    rw [← Functor.map_comp, h0, Functor.map_zero]

/-- **The residue sequence `0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0` of complexes of
sheaves of `f^{-1}𝒪_S`-modules**, indexed by `ℕ`. -/
abbrev Situation.residueBaseShortComplex :
    ShortComplex (CochainComplex (SheafOfModules.{u} (Scheme.Hom.baseRingSheaf D.f)) ℕ) :=
  ShortComplex.mk D.inclusionBaseMap D.residueBaseMap D.inclusionBaseMap_comp_residueBaseMap

/-- **Stacks Project, Tag 0FUF, in sheaves of `f^{-1}𝒪_S`-modules.** The residue sequence of
complexes of sheaves of `f^{-1}𝒪_S`-modules is short exact: forgetting the module structure is
faithful, and the underlying sequence of abelian sheaves is
`Stacks.LineBundle.Situation.residueShortComplex_shortExact`. -/
theorem Situation.residueBaseShortComplex_shortExact : D.residueBaseShortComplex.ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  refine CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)) ?_
  cases n with
  | succ p => exact D.shortExact_eval_succ p
  | zero =>
    refine ShortComplex.shortExact_of_iso ?_ D.shortExact_eval_zero
    have hz : IsZero ((SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)).obj
        (CochainComplex.desuspendX (Scheme.Hom.deRhamComplex D.f) 0)) :=
      Functor.map_isZero (SheafOfModules.toSheaf (Scheme.Hom.baseRingSheaf D.f)) (isZero_zero _)
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) ((isZero_zero _).iso hz) ?_ ?_
    · exact (Category.id_comp _).trans (Category.comp_id (D.inclusionMap.f 0)).symm
    · exact hz.eq_of_tgt _ _

/-- **Stacks Project, Tag 0FUF, as a short exact sequence of `ℤ`-indexed complexes of sheaves of
`f^{-1}𝒪_S`-modules**:

`0 → Ω^•_{X/S} → Ω^•_{L^⋆/S,0} → Ω^•_{X/S}[-1] → 0`,

with `Ω^•_{X/S}` the complex `deRhamComplexInt` of Tag 0FU7 and `[-1]` the translation of
`D(f^{-1}𝒪_S)`. The first map is the pullback of forms along `π`, the second the residue
`π^*α + d log s ∧ π^*β ↦ β`; the sequence is the extension by zero of
`Stacks.LineBundle.Situation.residueBaseShortComplex`. -/
def Situation.residueBaseSequence :
    AlgebraicGeometry.SheafOfModules.DeRhamResidueSequence (Scheme.Hom.deRhamAlgebras D.f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)) where
  middle := D.weightZeroBaseComplex.extend ComplexShape.embeddingUpNat
  incl := HomologicalComplex.extendMap D.inclusionBaseMap ComplexShape.embeddingUpNat
  res := HomologicalComplex.extendMap D.residueBaseMap ComplexShape.embeddingUpNat ≫
    (CochainComplex.desuspendExtendIso (Scheme.Hom.deRhamComplex D.f)).hom
  incl_comp_res := by
    have h : HomologicalComplex.extendMap D.inclusionBaseMap ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap D.residueBaseMap ComplexShape.embeddingUpNat = 0 := by
      rw [← HomologicalComplex.extendMap_comp, D.inclusionBaseMap_comp_residueBaseMap,
        HomologicalComplex.extendMap_zero]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans zero_comp)
  shortExact := by
    refine ShortComplex.shortExact_of_iso ?_ (ComplexShape.Embedding.shortExact_map_extendFunctor
      ComplexShape.embeddingUpNat D.residueBaseShortComplex_shortExact)
    exact ShortComplex.isoMk (S₁ := D.residueBaseShortComplex.map
        (ComplexShape.embeddingUpNat.extendFunctor _)) (Iso.refl _) (Iso.refl _)
      (CochainComplex.desuspendExtendIso (Scheme.Hom.deRhamComplex D.f))
      ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)

/-- **Stacks Project, Tag 0FUF, in the shifted presentation of the proofs of Tags 0FUG and 0FUQ**:
the short exact sequence

`0 → Ω^•_{X/S}[1] → Ω^•_{L^⋆/S,0}[1] → Ω^•_{X/S} → 0`

of complexes of sheaves of `f^{-1}𝒪_S`-modules, the translate by one of
`Stacks.LineBundle.Situation.residueBaseSequence`. Its boundary map
`Stacks.ShiftedBoundary.Sequence.boundary : Ω^•_{X/S} ⟶ Ω^•_{X/S}[2]` in `D(X, f^{-1}𝒪_S)` is the
map that Tag 0FUG identifies with the map of Remark 0FU7 attached to `c₁^{dR}(L)`. -/
def Situation.residueShiftedSequence :
    Stacks.ShiftedBoundary.Sequence (C := SheafOfModules.{u} (Scheme.Hom.baseRingSheaf D.f))
      (AlgebraicGeometry.SheafOfModules.deRhamComplexInt (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f)))
      (AlgebraicGeometry.SheafOfModules.deRhamComplexInt (Scheme.Hom.deRhamAlgebras D.f)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))) :=
  Stacks.ShiftedBoundary.Sequence.ofShortExact D.residueBaseSequence.incl
    D.residueBaseSequence.res D.residueBaseSequence.incl_comp_res
    D.residueBaseSequence.shortExact

end Stacks.LineBundle
