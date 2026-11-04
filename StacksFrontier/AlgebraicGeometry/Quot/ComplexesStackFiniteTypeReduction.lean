module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackSchemeBaseReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeSubalgebraModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackLargeHoms

/-!
# Stacks 0DLN, the reduction to a base of finite type over `ℤ`

The fifth paragraph of the proof of Stacks 0DLN: "Assume `S = B` is affine, say `S = Spec(Λ)`.
Write `Λ = colim Λ_i` as a filtered colimit with each `Λ_i` of finite type over `ℤ`. For some `i`
we can find a morphism of algebraic spaces `X_i → Spec(Λ_i)` which is proper, flat, of finite
presentation and whose base change to `Λ` is `X` (Stacks 07SK, 08K0, 08K1). If we show that
`Complexes_{X_i/Spec(Λ_i)}` is an algebraic stack, then it follows by base change (Remark 0DLI
and Section 04X4) that `𝒳` is an algebraic stack."

This file carries out that paragraph. The results it uses but does not prove are explicit
hypotheses at their content: Stacks 08K1, Lemmas 0DLF and 0DLG, Remark 0DLI. The change of base
scheme for `Complexes` used by Section 04X4 is not a Stacks tag; it is the named hypothesis
`AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison`.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison`:
  the change-of-base comparison, as a proposition.
* `AlgebraicGeometry.Space.ComplexesSituation.overSmallerBase`: a situation over `S` whose base
  is a scheme `T` of the site, read over `T` by Stacks 04SG, over the final algebraic space of
  `T`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_finiteTypeModel`: if `X ⟶ T`,
  read over `S`, is the base change of a situation over `S` with base `Spec Λ`, `Λ` of finite
  type over `ℤ`, then `Complexes_{X/T}` is algebraic, given the finite type case.
* `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_spec_of_finiteType_case`: the
  fifth paragraph of the proof: `Complexes_{X/Spec A}` is algebraic for every `A` of cardinality
  below the cofinality of the cutoff of the site, given the finite type case.
* `AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_obj_hom_iff` and its
  companions: properness, flatness and finite presentation of an algebraic space over `W` do not
  depend on the base it is read over.

## Implementation notes

The descent is carried out over the final scheme, the only base over which every `Spec Λ_i` and
`Spec A` are algebraic spaces. The situation over `Spec A` is moved there by Stacks 04SG and back
by the change-of-base comparison; the descended situation over the final scheme, whose base is
`Spec Λ_i`, is read over `Spec Λ_i` by
`AlgebraicGeometry.Space.ComplexesSituation.overSmallerBase` and compared by the same
hypothesis. Over the final scheme Remark 0DLI exhibits the 1-morphism between the two
`Complexes` as a base change of `𝒮_{Spec A} ⟶ 𝒮_{Spec Λ_i}`, which is representable, and Stacks
05UM transfers algebraicity:
`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_largeHoms`.

The cardinality bound on `A` comes from Stacks 07SK; see
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FiniteTypeSubalgebraModel.lean`.

## References

* [Stacks Project, Tag 0DLN](https://stacks.math.columbia.edu/tag/0DLN)
* [Stacks Project, Tag 0DLI](https://stacks.math.columbia.edu/tag/0DLI)
* [Stacks Project, Tag 04X4](https://stacks.math.columbia.edu/tag/04X4)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u z

namespace AlgebraicGeometry.Space

section Structural

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) (F : AlgebraicSpaces B W hW)

/-- Properness of the structural morphism of the image of `F` under the forward functor of
Stacks 04SG is properness of `F` over `W`. -/
theorem isProper_spacesOverSmallerBaseFunctor_obj_hom_iff :
    IsProper B S hS ((spacesOverSmallerBaseFunctor B W S hW hS h).obj F).1.hom ↔
      IsProper B W hW (toYonedaId B W hW F.1) := by
  rw [← isProper_isIso_comp_iff B S hS
    ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app F) _,
    relocalizeToYoneda_eq B W S hW hS h F]
  exact isProper_relocalizeToYoneda_iff B W S hW hS h F.1 F.2

/-- An every-étale-chart condition on the structural morphism of the image of `F` under the
forward functor of Stacks 04SG is the same condition on `F` over `W`. -/
theorem holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_obj_hom_iff
    (P : MorphismProperty Scheme.{u}) :
    HoldsOnEveryEtaleChart B S hS P ((spacesOverSmallerBaseFunctor B W S hW hS h).obj F).1.hom ↔
      HoldsOnEveryEtaleChart B W hW P (toYonedaId B W hW F.1) := by
  rw [← holdsOnEveryEtaleChart_iso_comp_iff B S hS P
    ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app F) _,
    relocalizeToYoneda_eq B W S hW hS h F]
  exact holdsOnEveryEtaleChart_relocalizeToYoneda_iff B W S hW hS h P F.1

/-- Finite presentation of the structural morphism of the image of `F` under the forward functor
of Stacks 04SG is finite presentation of `F` over `W`. -/
theorem isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff :
    IsFinitePresentation B S hS ((spacesOverSmallerBaseFunctor B W S hW hS h).obj F).1.hom ↔
      IsFinitePresentation B W hW (toYonedaId B W hW F.1) := by
  refine and_congr
    (holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_obj_hom_iff B hW hS h F _)
    (and_congr ?_ ?_)
  · rw [← isQuasiCompact_isIso_comp_iff B S hS
      ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app F) _,
      relocalizeToYoneda_eq B W S hW hS h F]
    exact isQuasiCompact_relocalizeToYoneda_iff B W S hW hS h F.1
  · rw [← isQuasiSeparated_isIso_comp_iff B S hS
      ((spacesOverSmallerBaseFunctorForgetIso B W S hW hS h).inv.app F) _,
      relocalizeToYoneda_eq B W S hW hS h F]
    exact isQuasiSeparated_relocalizeToYoneda_iff B W S hW hS h F.1

/-- Properness, flatness and finite presentation of the structural morphism of the image of `F`
under the forward functor of Stacks 04SG are the same conditions on `F` over `W`. -/
private theorem isProper_isFlat_isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff :
    (IsProper B S hS ((spacesOverSmallerBaseFunctor B W S hW hS h).obj F).1.hom ∧
      IsFlat B S hS ((spacesOverSmallerBaseFunctor B W S hW hS h).obj F).1.hom ∧
      IsFinitePresentation B S hS ((spacesOverSmallerBaseFunctor B W S hW hS h).obj F).1.hom) ↔
    (IsProper B W hW (toYonedaId B W hW F.1) ∧ IsFlat B W hW (toYonedaId B W hW F.1) ∧
      IsFinitePresentation B W hW (toYonedaId B W hW F.1)) :=
  and_congr (isProper_spacesOverSmallerBaseFunctor_obj_hom_iff B hW hS h F)
    (and_congr (holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_obj_hom_iff B hW hS h F _)
      (isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff B hW hS h F))

end Structural

section Terminal

variable {B : BigFppfSite.{u}} {W : Scheme.{u}} {hW : B.Contains W}

/-- A final algebraic space over `W` is identified with the presheaf represented by `W` itself. -/
def yonedaIsoOfIsTerminal {Y : AlgebraicSpaces B W hW} (hY : IsTerminal Y) :
    Y.obj ≅ yoneda.obj (Over.mk (𝟙 (B.obj hW))) :=
  (ObjectProperty.ι _).mapIso (hY.uniqueUpToIso (terminalSpace_isTerminal B W hW))

/-- A morphism to a final algebraic space over `W`, read through
`AlgebraicGeometry.Space.yonedaIsoOfIsTerminal`, is the structural morphism to `W`. -/
theorem comp_yonedaIsoOfIsTerminal_hom {Y : AlgebraicSpaces B W hW} (hY : IsTerminal Y)
    {F : AlgebraicSpaces B W hW} (f : F ⟶ Y) :
    f.hom ≫ (yonedaIsoOfIsTerminal hY).hom = toYonedaId B W hW F.obj :=
  (baseTerminal_yonedaIsTerminal B W hW).hom_ext _ _

end Terminal

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}}

attribute [local instance] complexesCategory

/-- **The change of base scheme for `Complexes_{X/B}` (not a Stacks tag).**
Let `g : T ⟶ S` be a morphism of the big fppf site. Let `D` be a situation of Stacks 0DLE over
`T` whose base is the final algebraic space over `T`, so that `X = D.X` is an algebraic space
over `T`, proper, flat and of finite presentation over `T`. Let `D₁` be a situation over `S`
whose base is identified with the representable algebraic space of `T ⟶ S` by `eY`, and whose
morphism `X₁ ⟶ T` is identified, over `T`, with the image of `X` under the forward functor of
Stacks 04SG. Then `Complexes_{X/T}` is an algebraic stack over `T` exactly when
`Complexes_{X₁/T}` is one over `S`.

This is what the source's proof of Stacks 0DLN uses when it "replaces `S` by `B`" (Section 04X4)
and again when it changes the base scheme from `Spec Λ` to `Spec Λ_i`: by Lemma 04X5, an
equivalence over `(Sch/T)_fppf` between `Complexes_{X/T}` and Construction A of
`Complexes_{X₁/T}` along `(Sch/T)_fppf ⟶ (Sch/S)_fppf` transfers algebraicity in both directions.
That equivalence is the change-of-base comparison for `Complexes`, which rests on the
relocalization of the derived categories of the small étale sites and its coherence with derived
pullback. It is a hypothesis wherever it is used, under this name. -/
def ChangeOfBaseComparison (B : BigFppfSite.{u}) : Prop :=
  ∀ {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S) (g : B.obj hT ⟶ B.obj hS)
    (D : ComplexesSituation B T hT), Nonempty (IsTerminal D.Y) →
    ∀ (D₁ : ComplexesSituation B S hS) (eY : D₁.Y.obj ≅ yoneda.obj (Over.mk g)),
      Nonempty (((spacesOverSmallerBaseFunctor B T S hT hS g).obj D.X).1 ≅
        Over.mk (D₁.f.hom ≫ eY.hom)) →
      (Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B T hT (complexesBasedCategory D) ↔
        Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D₁))

section OverSmallerBase

variable {T S : Scheme.{u}} {hT : B.Contains T} {hS : B.Contains S} (g : B.obj hT ⟶ B.obj hS)
  (D₁ : ComplexesSituation B S hS) (eY : D₁.Y.obj ≅ yoneda.obj (Over.mk g))

/-- The source of `D₁`, with its morphism to `T`, as an object of the category of Stacks 04SG of
algebraic spaces over `S` with a morphism to `T`. -/
abbrev overSmallerBaseSource : SpacesOverSmallerBase B T S hT hS g :=
  ⟨Over.mk (D₁.f.hom ≫ eY.hom), D₁.X.2⟩

/-- The source of `D₁` read as an algebraic space over `T`, through the quasi-inverse of the
equivalence of Stacks 04SG. -/
abbrev overSmallerBaseSpace : AlgebraicSpaces B T hT :=
  (spacesOverSmallerBaseEquivalence B T S hT hS g).inverse.obj (overSmallerBaseSource g D₁ eY)

/-- The image of the source of `D₁`, read over `T`, under the forward functor of Stacks 04SG is
the source of `D₁` with its morphism to `T` again: the counit of the equivalence. -/
def overSmallerBaseCounitIso :
    ((spacesOverSmallerBaseFunctor B T S hT hS g).obj (overSmallerBaseSpace g D₁ eY)).1 ≅
      Over.mk (D₁.f.hom ≫ eY.hom) :=
  (ObjectProperty.ι _).mapIso
    ((spacesOverSmallerBaseEquivalence B T S hT hS g).counitIso.app
      (overSmallerBaseSource g D₁ eY))

/-- The source of `D₁` read over `T` is proper, flat and of finite presentation over `T`. -/
theorem isProper_isFlat_isFinitePresentation_overSmallerBaseSpace :
    IsProper B T hT (toYonedaId B T hT (overSmallerBaseSpace g D₁ eY).obj) ∧
      IsFlat B T hT (toYonedaId B T hT (overSmallerBaseSpace g D₁ eY).obj) ∧
      IsFinitePresentation B T hT (toYonedaId B T hT (overSmallerBaseSpace g D₁ eY).obj) := by
  let c := overSmallerBaseCounitIso g D₁ eY
  have : IsIso c.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso c).hom)
  have hc : c.hom.left ≫ (D₁.f.hom ≫ eY.hom) =
      ((spacesOverSmallerBaseFunctor B T S hT hS g).obj (overSmallerBaseSpace g D₁ eY)).1.hom :=
    Over.w c.hom
  have h₁ : IsProper B S hS (c.hom.left ≫ (D₁.f.hom ≫ eY.hom)) ∧
      IsFlat B S hS (c.hom.left ≫ (D₁.f.hom ≫ eY.hom)) ∧
      IsFinitePresentation B S hS (c.hom.left ≫ (D₁.f.hom ≫ eY.hom)) :=
    (isProper_isFlat_isFinitePresentation_isIso_comp_iff B S hS _ _).2
      ((isProper_isFlat_isFinitePresentation_comp_isIso_iff B S hS _ _).2
        ⟨D₁.proper, D₁.flat, D₁.finitePresentation⟩)
  rw [hc] at h₁
  exact (isProper_isFlat_isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff
    B hT hS g _).1 h₁

/-- **The situation `D₁` read over the smaller base `T`.** For a situation `D₁` of Stacks 0DLE
over `S` whose base is identified with the representable algebraic space of `g : T ⟶ S`, the
source of `D₁` read over `T` by Stacks 04SG, over the final algebraic space of `T`. It is proper,
flat and of finite presentation over `T` because `D₁.f` is so over `S`, each condition on the
structural morphism of an algebraic space over `T` being independent of the base it is read over
(Stacks 03ZM, 03MJ, 03XP with Stacks 03HE and 03HL). -/
def overSmallerBase : ComplexesSituation B T hT where
  X := overSmallerBaseSpace g D₁ eY
  Y := terminalSpace B T hT
  f := default
  finitePresentation := by
    rw [show (default : overSmallerBaseSpace g D₁ eY ⟶ terminalSpace B T hT).hom =
      toYonedaId B T hT _ from (baseTerminal_yonedaIsTerminal B T hT).hom_ext _ _]
    exact (isProper_isFlat_isFinitePresentation_overSmallerBaseSpace g D₁ eY).2.2
  proper := by
    rw [show (default : overSmallerBaseSpace g D₁ eY ⟶ terminalSpace B T hT).hom =
      toYonedaId B T hT _ from (baseTerminal_yonedaIsTerminal B T hT).hom_ext _ _]
    exact (isProper_isFlat_isFinitePresentation_overSmallerBaseSpace g D₁ eY).1
  flat := by
    rw [show (default : overSmallerBaseSpace g D₁ eY ⟶ terminalSpace B T hT).hom =
      toYonedaId B T hT _ from (baseTerminal_yonedaIsTerminal B T hT).hom_ext _ _]
    exact (isProper_isFlat_isFinitePresentation_overSmallerBaseSpace g D₁ eY).2.1

/-- The base of `AlgebraicGeometry.Space.ComplexesSituation.overSmallerBase` is final. -/
theorem overSmallerBase_isTerminal : Nonempty (IsTerminal (overSmallerBase g D₁ eY).Y) :=
  ⟨terminalSpace_isTerminal B T hT⟩

/-- Under the change-of-base comparison, `Complexes` of `D₁` read over `T` is algebraic over `T`
exactly when `Complexes` of `D₁` is algebraic over `S`. -/
theorem isAlgebraicStack_overSmallerBase_iff (hcomp : ChangeOfBaseComparison.{u, z} B) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B T hT
        (complexesBasedCategory (overSmallerBase g D₁ eY)) ↔
      Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D₁) :=
  hcomp hT hS g (overSmallerBase g D₁ eY) (overSmallerBase_isTerminal g D₁ eY) D₁ eY
    ⟨overSmallerBaseCounitIso g D₁ eY⟩

end OverSmallerBase

/-- **Stacks 0DLN, the base change from a finite type model.** Let `D` be a situation of Stacks
0DLE over a scheme `T` of the site whose base is the final algebraic space over `T`, and let
`g_T : T ⟶ S` be a morphism of the site. Suppose `X = D.X`, read over `S` by Stacks 04SG, is the
base change of a situation `D₁` over `S` along a morphism `φ : T ⟶ Spec Λ` over `S`, with `Λ` of
finite type over `ℤ` and the base of `D₁` the representable algebraic space of `Spec Λ ⟶ S`. Then
`Complexes_{X/T}` is an algebraic stack over `T`.

This is the end of the fifth paragraph of the source's proof: "If we show that
`Complexes_{X_i/Spec(Λ_i)}` is an algebraic stack, then it follows by base change (Remark 0DLI
and Algebraic Stacks, Section 04X4) that `𝒳` is an algebraic stack." The hypotheses are:

* `hcomp`: the change-of-base comparison
  `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison` (Section 04X4 for
  `Complexes`), not a Stacks tag;
* `h0DLF`, `h0DLG`: Stacks 0DLF and 0DLG, over every base scheme;
* `h0DLI`: Remark 0DLI over every base scheme, in the shape of the square of Stacks 08LP, as in
  `AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_isAlgebraicStack_schemeBase`;
* `hcase`: the case `S = B = Spec Λ` with `Λ` of finite type over `ℤ`.

The case `hcase` makes `Complexes` of `D₁`, read over `Spec Λ`, algebraic; `hcomp` moves this to
`S`. By Remark 0DLI the 1-morphism from `Complexes` of the base change of `D₁` along
`T ⟶ Spec Λ` to `Complexes` of `D₁` is a base change of `𝒮_T ⟶ 𝒮_{Spec Λ}`, which is
representable by algebraic spaces (Stacks 045A), so it is representable by algebraic spaces
(Stacks 0302) and its source is algebraic (Stacks 05UM). Finally `hcomp` moves this to `T`. -/
theorem isAlgebraicStack_of_finiteTypeModel
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF hS D)))
    (h0DLI : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
      {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y),
      ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
        (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
        (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
        (e : t ≫ q ≅ q' ≫ baseBasedMap g),
        Nonempty (Bicategory.IsTwoFibreProduct
          (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
            @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
              _ _ _ q (baseBasedMap g))))
    (hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D'))
    {S T : Scheme.{u}} (hS : B.Contains S) (hT : B.Contains T) (gT : B.obj hT ⟶ B.obj hS)
    (D : ComplexesSituation B T hT) (hD : Nonempty (IsTerminal D.Y))
    (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
    (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (gΛ : B.obj hΛ ⟶ B.obj hS)
    (φ : Over.mk gT ⟶ Over.mk gΛ)
    (D₁ : ComplexesSituation B S hS) (eY₁ : D₁.Y.obj ≅ yoneda.obj (Over.mk gΛ))
    (π : ((spacesOverSmallerBaseFunctor B T S hT hS gT).obj D.X).1.left ⟶ D₁.X.obj)
    (hsq : IsPullback π ((spacesOverSmallerBaseFunctor B T S hT hS gT).obj D.X).1.hom
      D₁.f.hom (yoneda.map φ ≫ eY₁.inv)) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B T hT (complexesBasedCategory D) := by
  -- the finite type case, moved to `S`
  have hD₁ : Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS (complexesBasedCategory D₁) :=
    (isAlgebraicStack_overSmallerBase_iff gΛ D₁ eY₁ hcomp).1
      (hcase Λ hΛ _ (overSmallerBase_isTerminal gΛ D₁ eY₁))
  -- the square of Remark 0DLI for the base change along `T ⟶ Spec Λ`
  let g' : (schemeSpaceFunctor B S hS).obj (Over.mk gT) ⟶ D₁.Y :=
    ObjectProperty.homMk (yoneda.map φ ≫ eY₁.inv)
  obtain ⟨q, t, q', e, ⟨hR⟩⟩ := h0DLI hS D₁ g'
  let 𝒳 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (complexesBasedCategory D₁) (h0DLF hS D₁)
  let 𝒳' : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (complexesBasedCategory (D₁.baseChange g'))
      (h0DLF hS (D₁.baseChange g'))
  let qC : 𝒳 ⟶ baseFibredCategory D₁.Y := Bicategory.InducedBicategory.mkHom q
  let P : Bicategory.TwoCommSq qC (baseFibredMap D₁.Y g') :=
    { pt := 𝒳'
      fst := Bicategory.InducedBicategory.mkHom t
      snd := Bicategory.InducedBicategory.mkHom q'
      iso := Bicategory.InducedBicategory.isoMk e }
  -- `𝒮_T ⟶ 𝒮_{Spec Λ}` is representable, hence so is its base change
  have hrep := Stack.isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} B S hS
    (baseFibredCategory _) (baseFibredCategory D₁.Y) 𝒳 (baseFibredMap D₁.Y g') qC P
    (Bicategory.isTwoFibreProduct_of_underlying hR)
    (isRepresentableByAlgebraicSpaces_baseBasedMap_schemeSpace g')
  -- so `Complexes` of the base change is algebraic over `S` (Stacks 05UM)
  have h' : Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B S hS
      (complexesBasedCategory (D₁.baseChange g')) :=
    Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_largeHoms B S hS
      (𝒳 := 𝒳') (𝒴 := 𝒳) P.fst hrep (h0DLG hS (D₁.baseChange g')) hD₁
  -- and `Complexes_{X/T}` is algebraic over `T`
  refine (hcomp hT hS gT D hD (D₁.baseChange g') (Iso.refl _)
    ⟨Over.isoMk hsq.isoPullback ?_⟩).2 h'
  change hsq.isoPullback.hom ≫ (pullback.snd D₁.f.hom (yoneda.map φ ≫ eY₁.inv) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  exact hsq.isoPullback_hom_snd

/-- **Stacks 0DLN, the reduction from `S = B = Spec A` to `Λ` of finite type over `ℤ`** (the
fifth paragraph of the source's proof). Let `A` be a ring with `Spec A` in the site, and let `D`
be a situation of Stacks 0DLE over `S = Spec A` whose base is the final algebraic space, so that
`X = D.X` is proper, flat and of finite presentation over `Spec A`. Then `Complexes_{X/Spec A}` is
an algebraic stack over `Spec A`, provided the cardinality of `A` is below the cofinality of the
cutoff of the site.

The source writes `A` as the filtered colimit of its finite type `ℤ`-subalgebras `Λ_s` and
descends `X ⟶ Spec A` to a proper, flat, finitely presented `X_s ⟶ Spec Λ_s` by Stacks 07SK,
08K0 and 08K1 (`AlgebraicGeometry.Space.exists_adjoinRing_model`, over the final scheme). Then
`Complexes_{X/Spec A}` is a base change of `Complexes_{X_s/Spec Λ_s}` (Remark 0DLI and Section
04X4), which is algebraic by the finite type case
(`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_of_finiteTypeModel`).

The hypotheses, apart from `hcase`, are each a result stated at its content:

* `h08K1`: Stacks 08K1, in the situation of Stacks 084W
  (`AlgebraicGeometry.Space.MorphismDescentSystem`);
* `hcomp`: the change-of-base comparison
  `AlgebraicGeometry.Space.ComplexesSituation.ChangeOfBaseComparison`, not a Stacks tag;
* `h0DLF`, `h0DLG`, `h0DLI`: Stacks 0DLF, 0DLG and Remark 0DLI, over every base scheme;
* `hcase`: the case `S = B = Spec Λ` with `Λ` of finite type over `ℤ`.

The bound `hAsize` is not in the source. It is the bound on the index of the inverse system that
Stacks 07SK (`AlgebraicGeometry.Space.exists_model_of_finitePresentation`, hypothesis `hSize`)
and Stacks 084W (`AlgebraicGeometry.Space.MorphismDescentSystem.indexSize`) require; the
finite subsets of `A` index the system. -/
theorem isAlgebraicStack_spec_of_finiteType_case
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSystem B S hS hZ I),
      IsProper B S hS D.mapLimit → IsLocallyOfFiniteType B S hS D.map₀ →
        ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    (hcomp : ChangeOfBaseComparison.{u, z} B)
    (h0DLF : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      (complexesFunctor D).IsFiberedInGroupoids)
    (h0DLG : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS),
      Stack.HasRepresentableDiagonal B S hS
        (CatFiberedInGroupoids.mk (complexesBasedCategory D) (h0DLF hS D)))
    (h0DLI : ∀ {S : Scheme.{u}} (hS : B.Contains S) (D : ComplexesSituation B S hS)
      {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D.Y),
      ∃ (q : complexesBasedCategory D ⟶ baseBasedCategory D.Y)
        (t : complexesBasedCategory (D.baseChange g) ⟶ complexesBasedCategory D)
        (q' : complexesBasedCategory (D.baseChange g) ⟶ baseBasedCategory Y')
        (e : t ≫ q ≅ q' ≫ baseBasedMap g),
        Nonempty (Bicategory.IsTwoFibreProduct
          (⟨complexesBasedCategory (D.baseChange g), t, q', e⟩ :
            @Bicategory.TwoCommSq (BasedCategory.{u + 1, u + 1} (BigFppfOver B S hS)) _
              _ _ _ q (baseBasedMap g))))
    (hcase : ∀ (Λ : Type u) [CommRing Λ] [Algebra.FiniteType ℤ Λ]
        (hΛ : B.Contains (Spec (CommRingCat.of Λ))) (D' : ComplexesSituation B _ hΛ),
        Nonempty (IsTerminal D'.Y) →
          Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hΛ (complexesBasedCategory D'))
    (A : Type u) [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
    (hAsize : Cardinal.mk A < B.cutoff.ord.cof)
    (D : ComplexesSituation B _ hA) (hD : Nonempty (IsTerminal D.Y)) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hA (complexesBasedCategory D) := by
  have hZ : B.Contains (⊤_ Scheme.{u}) := B.contains_terminal
  let gA := toTerminalSite B hZ hA
  let P := (spacesOverSmallerBaseFunctor B _ _ hA hZ gA).obj D.X
  -- `X ⟶ Spec A`, read over the final scheme, is proper, flat and of finite presentation
  have hDY := hD.some
  have hX : IsProper B _ hA (toYonedaId B _ hA D.X.obj) ∧
      IsFlat B _ hA (toYonedaId B _ hA D.X.obj) ∧
      IsFinitePresentation B _ hA (toYonedaId B _ hA D.X.obj) := by
    rw [← comp_yonedaIsoOfIsTerminal_hom hDY D.f]
    exact (isProper_isFlat_isFinitePresentation_comp_isIso_iff B _ hA D.f.hom
      (yonedaIsoOfIsTerminal hDY).hom).2 ⟨D.proper, D.flat, D.finitePresentation⟩
  have hp : IsProper B _ hZ P.1.hom ∧ IsFlat B _ hZ P.1.hom ∧
      IsFinitePresentation B _ hZ P.1.hom :=
    (isProper_isFlat_isFinitePresentation_spacesOverSmallerBaseFunctor_obj_hom_iff
      B hA hZ gA D.X).2 hX
  -- Stacks 07SK, 08K0, 08K1: a finite type model over some `Spec Λ_s`
  obtain ⟨s, X₁, hX₁, f₁, hf₁, π, hsq⟩ :=
    exists_adjoinRing_model B hZ A hA (fun D => h08K1 _ hZ D) hAsize P.2 P.1.hom hp
  let D₁ : ComplexesSituation B _ hZ :=
    { X := ⟨X₁, hX₁⟩
      Y := schemeSpace ((adjoinSiteDiagram B hZ A hA).obj (Opposite.op s))
      f := ObjectProperty.homMk f₁
      finitePresentation := hf₁.2.2
      proper := hf₁.1
      flat := hf₁.2.1 }
  -- the base change from the model
  exact isAlgebraicStack_of_finiteTypeModel hcomp h0DLF h0DLG h0DLI hcase hZ hA gA D hD
    (adjoinRing A s) (contains_spec_adjoinRing B A hA s)
    (toTerminalSite B hZ (contains_spec_adjoinRing B A hA s))
    ((adjoinSiteCone B hZ A hA).π.app (Opposite.op s)) D₁ (Iso.refl _) π hsq

end AlgebraicGeometry.Space.ComplexesSituation

end
