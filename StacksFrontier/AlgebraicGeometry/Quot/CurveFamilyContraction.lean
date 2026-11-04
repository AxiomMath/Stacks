module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySchemeChart
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContractionEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContractionScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidueFieldObjectMapEtale
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreUniversal

/-!
# Morphisms of families of curves contracting the structure sheaf (Stacks 0E88)

Let `S` be a scheme, `s ∈ S`, and let `f : X → S` and `g : Y → S` be families of curves
(Stacks 0D4Z) with a morphism `c : X → Y` over `S`. Stacks 0E88 says: if
`c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and `R¹c_{s,*}𝒪_{X_s} = 0`, then after replacing `S` by an open
neighbourhood of `s` we have `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this remains true after
base change by any morphism `S' → S`.

This file proves the statement from two inputs not proved here, and records the proof:

* the pointwise form of Stacks 0E6F (two families of curves become schemes over an étale
  neighbourhood of `s`),
  `exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized`,
  whose own input is the smoothness half of Stacks 0DQ0, `CurveFamily.IsSmoothLocallyPolarized`;
* the separated case of Stacks 071N in the spaces formalism, not yet proved here, which compares
  the higher direct images of a represented morphism with those of the morphism of schemes and is
  consumed through `Space.isStructureContraction_schemeSpaceMap_iff`.

The source's proof is followed. Over an étale neighbourhood `(U, u) → (S, s)` on which `X` and
`Y` are schemes, `c` becomes a morphism of schemes `γ : Z_X → Z_Y` over `U`; the hypotheses at `s`
pass to the fibre of `γ` over `u` because `Spec κ(u) → Spec κ(s)` is étale
(`Space.isEtale_schemeSpaceMap_residueFieldObjectMap`) and the condition is étale local
(`Space.isStructureContraction_of_isPullback`); [Stacks, Tag 0E7L] and the properness of
`Z_Y → U` give an open neighbourhood `U₀` of `u` over which every base change of `γ` has the two
properties (`exists_isOpen_forall_isPullback_of_specialFibre`, in the namespace
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`); its image `W` in `S` is open, and a base change of
`c` along `T → S` landing in `W` is checked after the étale surjective base change `T ×_S U₀ → T`,
where it is a base change of `γ`
(`Space.isStructureContraction_of_isPullback_of_isSurjective`).

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_chart`: the statement
  over an étale neighbourhood of `s` on which both total spaces are schemes, with 071N as an
  explicit input.
* `AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_isSmoothLocallyPolarized`:
  the statement of Stacks 0E88, with the inputs of 0E6F (the smoothness half of 0DQ0) and of
  071N (separated case) explicit.

## Implementation notes

The two families share the base scheme through the equation `hb : Y.base = X.base`, and the
structure morphism of `Y` is read over the base of `X` through `eqToHom`. The fibre at `s` is the
base change along the residue-field point `Spec κ(s) → S` of the big fppf site
(`Space.residueFieldMap`), formed by `Space.structureContractionBaseChange`; the conclusion is
stated for every cartesian base change along a scheme `T → S` landing in the open `W`, which
includes the open subscheme `W` itself.

No `@[stacks 0E88]` attribute is placed: the two inputs are binders here. Both are now
dischargeable, and
`StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyContractionPicardCharts` states the same
conclusion with neither: `h071N` is proved there, and `hpol` is replaced by the two
Picard-stack hypotheses it rests on (Stacks 0D04 with Stacks 09DS, Stacks 0DPJ, and
Stacks 0D3D). The registration goes on a declaration from which those too have come off.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- A cartesian square of the big fppf site gives a cartesian square of the algebraic spaces it
represents. -/
theorem isPullback_schemeSpaceMap_of_isPullback {A C D E : BigFppfOver B integerBase hZ}
    {a : A ⟶ C} {b : A ⟶ D} {c : C ⟶ E} {d : D ⟶ E} (H : IsPullback a b c d) :
    IsPullback (schemeSpaceMap a) (schemeSpaceMap b) (schemeSpaceMap c) (schemeSpaceMap d) := by
  refine IsPullback.of_map (ObjectProperty.ι _) ?_ ?_
  · exact ObjectProperty.hom_ext _ (by
      show yoneda.map a ≫ yoneda.map c = yoneda.map b ≫ yoneda.map d
      rw [← Functor.map_comp, ← Functor.map_comp, H.w])
  · exact H.map yoneda

/-- A commutative square of the big fppf site whose square of schemes is cartesian is
cartesian. -/
theorem isPullback_of_isPullback_toScheme_map {A C D E : BigFppfOver B integerBase hZ}
    {a : A ⟶ C} {b : A ⟶ D} {c : C ⟶ E} {d : D ⟶ E} (w : a ≫ c = b ≫ d)
    (H : IsPullback ((𝒯).map a) ((𝒯).map b) ((𝒯).map c) ((𝒯).map d)) :
    IsPullback a b c d :=
  IsPullback.of_map (𝒯) w H

/-- A scheme of the big fppf site, as an object over the spectrum of the integers. -/
def ofScheme (W : Scheme.{u}) (hW : B.Contains W) : BigFppfOver B integerBase hZ :=
  Over.mk (⟨specULiftZIsTerminal.from W⟩ : B.obj hW ⟶ B.obj hZ)

/-- A morphism of schemes between objects of the big fppf site over the spectrum of the
integers, as a morphism of the site. -/
def homOfScheme {A A' : BigFppfOver B integerBase hZ} (g : (𝒯).obj A ⟶ (𝒯).obj A') :
    A ⟶ A' :=
  Over.homMk ⟨g⟩ (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- `homOfScheme` has the given morphism of schemes as its underlying morphism. -/
@[simp]
theorem toScheme_map_homOfScheme {A A' : BigFppfOver B integerBase hZ}
    (g : (𝒯).obj A ⟶ (𝒯).obj A') : (𝒯).map (homOfScheme g) = g := rfl

/-- `ofScheme` has the given scheme as its underlying scheme. -/
theorem toScheme_obj_ofScheme (W : Scheme.{u}) (hW : B.Contains W) :
    (𝒯).obj (ofScheme (hZ := hZ) W hW) = W := rfl

/-- The big fppf site contains the fibre products of its schemes. -/
theorem contains_pullback {W₁ W₂ W₃ : Scheme.{u}} (a : W₁ ⟶ W₃) (b : W₂ ⟶ W₃)
    (h₁ : B.Contains W₁) (h₂ : B.Contains W₂) : B.Contains (pullback a b) :=
  Scheme.size_pullback_lt a b h₁ h₂

/-- **A base change of a morphism over `Z` is a base change of the morphism.** If `X'` and `Y'`
are the base changes of `X ⟶ Z` and `Y ⟶ Z` along `h : Z' ⟶ Z` and `c' : X' ⟶ Y'` lies over `c`
and over `Z'`, then `X'` is the base change of `X` along `Y' ⟶ Y`. -/
theorem isPullback_of_isPullback_of_isPullback {X Y Z Z' X' Y' : AlgebraicSpaces B integerBase hZ}
    {fX : X ⟶ Z} {g : Y ⟶ Z} {c : X ⟶ Y} (hc : c ≫ g = fX) {h : Z' ⟶ Z} {pX' : X' ⟶ X}
    {fX' : X' ⟶ Z'} {pY' : Y' ⟶ Y} {fY' : Y' ⟶ Z'} {c' : X' ⟶ Y'}
    (sqX' : IsPullback pX' fX' fX h) (sqY' : IsPullback pY' fY' g h)
    (hc₁ : c' ≫ pY' = pX' ≫ c) (hc₂ : c' ≫ fY' = fX') : IsPullback pX' c' c pY' :=
  IsPullback.of_bot (by rwa [hc₂, hc]) hc₁.symm sqY'

/-- **The base change of a chart of a contraction along a scheme over the base.** Let `c : X ⟶ Y`
be a morphism of algebraic spaces over `schemeSpace S₀` and suppose that over an object `U` of the
site, through `φ : U ⟶ S₀`, the base change of `c` is the morphism of schemes `γ : Z_X ⟶ Z_Y`
(`cX`, `sqY`). Let `Y'` be a base change of `Y` along `h : T ⟶ S₀`, `X'` the base change of `X`
along `Y' ⟶ Y`, with `c' : X' ⟶ Y'`, and let `T₁` map to `T` and to `U` compatibly. Then the base
change of `γ` along the fibre product `Y₁ = Z_Y ×_U T₁` is a base change of `c'` along a morphism
`Y₁ ⟶ Y'`, and that morphism is the base change of `T₁ ⟶ T`. -/
theorem exists_isPullback_baseChange_chart {X Y S₀ : AlgebraicSpaces B integerBase hZ}
    {g : Y ⟶ S₀} {c : X ⟶ Y} {U ZX ZY T T₁ : BigFppfOver B integerBase hZ}
    {φ : schemeSpace U ⟶ S₀} {pX : schemeSpace ZX ⟶ X} {pY : schemeSpace ZY ⟶ Y} {qY : ZY ⟶ U}
    {γ : ZX ⟶ ZY} (cX : IsPullback pX (schemeSpaceMap γ) c pY)
    (sqY : IsPullback pY (schemeSpaceMap qY) g φ) {h : schemeSpace T ⟶ S₀} (t₁ : T₁ ⟶ T)
    (h₁ : T₁ ⟶ U) (hcomm : schemeSpaceMap h₁ ≫ φ = schemeSpaceMap t₁ ≫ h)
    {X' Y' : AlgebraicSpaces B integerBase hZ} {pX' : X' ⟶ X} {c' : X' ⟶ Y'} {pY' : Y' ⟶ Y}
    {fY' : Y' ⟶ schemeSpace T} (cX' : IsPullback pX' c' c pY') (sqY' : IsPullback pY' fY' g h) :
    let hY₁ : B.Contains (pullback ((𝒯).map qY) ((𝒯).map h₁)) :=
      contains_pullback _ _ ZY.left.property T₁.left.property
    let hX₁ : B.Contains (pullback ((𝒯).map γ) (pullback.fst ((𝒯).map qY) ((𝒯).map h₁))) :=
      contains_pullback _ _ ZX.left.property hY₁
    ∃ (a₁ : schemeSpace (ofScheme (hZ := hZ) _ hX₁) ⟶ X')
      (b₁ : schemeSpace (ofScheme (hZ := hZ) _ hY₁) ⟶ Y'),
      IsPullback a₁ (schemeSpaceMap (homOfScheme (pullback.snd ((𝒯).map γ)
          (pullback.fst ((𝒯).map qY) ((𝒯).map h₁))) :
          ofScheme (hZ := hZ) _ hX₁ ⟶ ofScheme (hZ := hZ) _ hY₁)) c' b₁ ∧
      IsPullback b₁ (schemeSpaceMap (homOfScheme (pullback.snd ((𝒯).map qY) ((𝒯).map h₁)) :
          ofScheme (hZ := hZ) _ hY₁ ⟶ T₁)) fY' (schemeSpaceMap t₁) := by
  intro hY₁ hX₁
  let Y₁ : BigFppfOver B integerBase hZ := ofScheme _ hY₁
  let X₁ : BigFppfOver B integerBase hZ := ofScheme _ hX₁
  let jY : Y₁ ⟶ ZY := homOfScheme (pullback.fst ((𝒯).map qY) ((𝒯).map h₁))
  let rY : Y₁ ⟶ T₁ := homOfScheme (pullback.snd ((𝒯).map qY) ((𝒯).map h₁))
  let kX : X₁ ⟶ ZX := homOfScheme (pullback.fst ((𝒯).map γ)
    (pullback.fst ((𝒯).map qY) ((𝒯).map h₁)))
  let F₁ : X₁ ⟶ Y₁ := homOfScheme (pullback.snd ((𝒯).map γ)
    (pullback.fst ((𝒯).map qY) ((𝒯).map h₁)))
  have H1 : IsPullback jY rY qY h₁ :=
    isPullback_of_isPullback_toScheme_map ((𝒯).map_injective pullback.condition)
      (IsPullback.of_hasPullback _ _)
  have H2 : IsPullback kX F₁ γ jY :=
    isPullback_of_isPullback_toScheme_map ((𝒯).map_injective pullback.condition)
      (IsPullback.of_hasPullback _ _)
  have S1 := isPullback_schemeSpaceMap_of_isPullback H1
  have S2 := isPullback_schemeSpaceMap_of_isPullback H2
  have outerY : IsPullback (schemeSpaceMap jY ≫ pY) (schemeSpaceMap rY) g
      (schemeSpaceMap t₁ ≫ h) := by
    rw [← hcomm]
    exact S1.paste_horiz sqY
  let b₁ : schemeSpace Y₁ ⟶ Y' := sqY'.lift (schemeSpaceMap jY ≫ pY)
    (schemeSpaceMap rY ≫ schemeSpaceMap t₁) (by simpa only [Category.assoc] using outerY.w)
  have Ysq : IsPullback b₁ (schemeSpaceMap rY) fY' (schemeSpaceMap t₁) :=
    IsPullback.of_right (by rwa [sqY'.lift_fst]) (sqY'.lift_snd _ _ _) sqY'
  have outerX : IsPullback (schemeSpaceMap kX ≫ pX) (schemeSpaceMap F₁) c (b₁ ≫ pY') := by
    rw [sqY'.lift_fst]
    exact S2.paste_horiz cX
  let a₁ : schemeSpace X₁ ⟶ X' := cX'.lift (schemeSpaceMap kX ≫ pX)
    (schemeSpaceMap F₁ ≫ b₁) (by simpa only [Category.assoc] using outerX.w)
  exact ⟨a₁, b₁, .of_right (by rwa [cX'.lift_fst]) (cX'.lift_snd _ _ _) cX', Ysq⟩

/-- `schemeSpaceMap` takes a composite with an `eqToHom` to the composite with an `eqToHom`. -/
theorem schemeSpaceMap_comp_eqToHom {A A' A'' : BigFppfOver B integerBase hZ} (φ : A ⟶ A')
    (e : A' = A'') :
    schemeSpaceMap (φ ≫ eqToHom e) = schemeSpaceMap φ ≫ eqToHom (congrArg schemeSpace e) := by
  subst e
  simp

/-- Moving an `eqToHom` across the corner of a cartesian square. -/
theorem isPullback_comp_eqToHom_of_isPullback {C : Type*} [Category C] {P X' Y' Z Z' : C}
    {fst : P ⟶ X'} {snd : P ⟶ Y'} {f : X' ⟶ Z'} {k : Y' ⟶ Z} (e : Z = Z')
    (H : IsPullback fst snd f (k ≫ eqToHom e)) : IsPullback fst snd (f ≫ eqToHom e.symm) k := by
  subst e
  simpa using H

open Stacks.AlgebraicGeometry.TopDegreeBaseChange Space in
/-- `Space.isStructureContraction_schemeSpaceMap_iff` for a morphism of schemes read as a
morphism of the site by `homOfScheme`. -/
theorem isStructureContraction_homOfScheme_iff {W W' : Scheme.{u}} {hW : B.Contains W}
    {hW' : B.Contains W'} (g : W ⟶ W') [QuasiCompact g] [IsSeparated g]
    (h071N : ∀ {T' T : BigFppfOver B integerBase hZ} (g : T' ⟶ T)
      (_hqc : QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map g))
      (_hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map g))
      (F : ((BigFppfOver.toScheme B integerBase hZ).obj T').Modules) (_hF : F.IsQuasicoherent)
      (k : ℕ),
      have := hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T')
        (isAlgebraicSpace_yoneda B integerBase hZ T')
      have := modulePushforward_additive B integerBase hZ (representedSpaceMap B integerBase hZ g)
      Nonempty (((modulePushforward B integerBase hZ
          (representedSpaceMap B integerBase hZ g)).rightDerived k).obj
          ((representedAssociatedModule B integerBase hZ T'
            (isAlgebraicSpace_yoneda B integerBase hZ T')).obj F) ≅
        (representedAssociatedModule B integerBase hZ T
          (isAlgebraicSpace_yoneda B integerBase hZ T)).obj
          (((Scheme.Modules.pushforward
            ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived k).obj F))) :
    IsStructureContraction B integerBase hZ
        (schemeSpaceMap (homOfScheme (A := ofScheme W hW) (A' := ofScheme W' hW') g)) ↔
      IsIso (Scheme.Modules.unitToPushforwardUnit g) ∧
        IsZero (firstDirectImageStructureSheaf g) := by
  have : QuasiCompact ((𝒯).map (homOfScheme (A := ofScheme W hW) (A' := ofScheme W' hW') g)) :=
    ‹QuasiCompact g›
  have : IsSeparated ((𝒯).map (homOfScheme (A := ofScheme W hW) (A' := ofScheme W' hW') g)) :=
    ‹IsSeparated g›
  exact Space.isStructureContraction_schemeSpaceMap_iff _ h071N

open Stacks.AlgebraicGeometry.TopDegreeBaseChange Space in
/-- **Stacks 0E88 over an étale chart on which both families are schemes.** Let `c : X ⟶ Y` be a
morphism of families of curves over `S`, and `φ : U ⟶ S` étale with `X ×_S U` and `Y ×_S U`
represented by schemes `Z_X`, `Z_Y` (`sqX`, `sqY`). If `c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and
`R¹c_{s,*}𝒪_{X_s} = 0` at `s = φ(u)`, there is an open neighbourhood `W` of `s` such that every
base change of `c` along a scheme `T ⟶ S` landing in `W` has `𝒪 = c'_*𝒪` and `R¹c'_*𝒪 = 0`.
The input `h071N` is the separated case of Stacks 071N. -/
theorem exists_isOpen_isStructureContraction_of_chart (X Y : CurveFamily B hZ)
    (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    {U : BigFppfOver B integerBase hZ} (φ : U ⟶ X.base) (hφ : Etale ((𝒯).map φ))
    (u : U.left.1)
    (hs : Space.IsStructureContraction B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ c hc
        (schemeSpaceMap (Space.residueFieldMap B integerBase hZ X.base (φ.left.1 u)
          (B.residueField_spec_contains X.base.left.property (φ.left.1 u))))))
    {ZX ZY : BigFppfOver B integerBase hZ} (pX : schemeSpace ZX ⟶ X.total) (qX : ZX ⟶ U)
    (sqX : IsPullback pX (schemeSpaceMap qX) X.toBase (schemeSpaceMap φ))
    (pY : schemeSpace ZY ⟶ Y.total) (qY : ZY ⟶ U)
    (sqY : IsPullback pY (schemeSpaceMap qY) Y.toBase (schemeSpaceMap (φ ≫ eqToHom hb.symm)))
    (h071N : ∀ {T' T : BigFppfOver B integerBase hZ} (g : T' ⟶ T)
      (_hqc : QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map g))
      (_hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map g))
      (F : ((BigFppfOver.toScheme B integerBase hZ).obj T').Modules) (_hF : F.IsQuasicoherent)
      (k : ℕ),
      have := hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T')
        (isAlgebraicSpace_yoneda B integerBase hZ T')
      have := modulePushforward_additive B integerBase hZ (representedSpaceMap B integerBase hZ g)
      Nonempty (((modulePushforward B integerBase hZ
          (representedSpaceMap B integerBase hZ g)).rightDerived k).obj
          ((representedAssociatedModule B integerBase hZ T'
            (isAlgebraicSpace_yoneda B integerBase hZ T')).obj F) ≅
        (representedAssociatedModule B integerBase hZ T
          (isAlgebraicSpace_yoneda B integerBase hZ T)).obj
          (((Scheme.Modules.pushforward
            ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived k).obj F))) :
    ∃ W : X.base.left.1.Opens, φ.left.1 u ∈ W ∧
      ∀ (T : BigFppfOver B integerBase hZ) (h : T ⟶ X.base),
        (∀ t, ((𝒯).map h).base t ∈ W) →
        ∀ (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total)
          (fX' : X' ⟶ schemeSpace T) (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T)
          (c' : X' ⟶ Y'),
          IsPullback pX' fX' X.toBase (schemeSpaceMap h) →
          IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap h) →
          c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
          Space.IsStructureContraction B integerBase hZ c' := by
  set g : Y.total ⟶ schemeSpace X.base := Y.toBase ≫ eqToHom (congrArg schemeSpace hb) with hgdef
  have sqYg : IsPullback pY (schemeSpaceMap qY) g (schemeSpaceMap φ) := by
    rw [schemeSpaceMap_comp_eqToHom] at sqY
    exact isPullback_comp_eqToHom_of_isPullback _ sqY
  -- the chart morphism of schemes
  let cU : schemeSpace ZX ⟶ schemeSpace ZY := sqYg.lift (pX ≫ c) (schemeSpaceMap qX)
    (by rw [Category.assoc, hc]; exact sqX.w)
  let γ : ZX ⟶ ZY := yoneda.preimage cU.hom
  have hγ : schemeSpaceMap γ = cU :=
    ObjectProperty.hom_ext _ (yoneda.map_preimage cU.hom)
  have hγq : γ ≫ qY = qX := by
    apply yoneda.map_injective
    rw [Functor.map_comp]
    show (schemeSpaceMap γ ≫ schemeSpaceMap qY).hom = (schemeSpaceMap qX).hom
    rw [hγ, sqYg.lift_snd]
  have cX : IsPullback pX (schemeSpaceMap γ) c pY :=
    .of_bot (by rwa [hγ, sqYg.lift_snd, hc]) (by rw [hγ, sqYg.lift_fst]) sqYg
  -- the scheme data of Stacks 0E7L
  have hfq : ((𝒯).map γ) ≫ ((𝒯).map qY) = (𝒯).map qX := by rw [← Functor.map_comp, hγq]
  have : LocallyOfFinitePresentation (((𝒯).map γ) ≫ ((𝒯).map qY)) := by
    rw [hfq]; exact X.locallyOfFinitePresentation_toScheme_map_of_isPullback sqX
  have : LocallyOfFinitePresentation ((𝒯).map qY) :=
    Y.locallyOfFinitePresentation_toScheme_map_of_isPullback sqY
  have : IsProper ((𝒯).map qY) :=
    Y.isProper_toScheme_map_of_isPullback_schemeSpaceMap sqY
  have : IsProper (((𝒯).map γ) ≫ ((𝒯).map qY)) := by
    rw [hfq]; exact X.isProper_toScheme_map_of_isPullback_schemeSpaceMap sqX
  have : IsProper ((𝒯).map γ) := IsProper.of_comp ((𝒯).map γ) ((𝒯).map qY)
  have : Flat (((𝒯).map γ) ≫ ((𝒯).map qY)) := by
    rw [hfq]; exact X.flat_toScheme_map_of_isPullback sqX
  have hflat : ∀ x, (((𝒯).map γ) ≫ ((𝒯).map qY)) x = u →
      IsFlatAt (((𝒯).map γ) ≫ ((𝒯).map qY)).toLRSHom.toShHom x :=
    fun x _ ↦ Flat.stalkMap (((𝒯).map γ) ≫ ((𝒯).map qY)) x
  have hdim : ∀ y : ((𝒯).map qY).fiber u,
      topologicalKrullDim ((Stacks.Flatness.fiberHom ((𝒯).map γ) ((𝒯).map qY) u).fiber y) ≤
        ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_fiberHom_le ((𝒯).map γ) ((𝒯).map qY) u (by
      rw [hfq]; exact X.topologicalKrullDim_fiber_toScheme_map_le_of_isPullback sqX hφ u)
  -- the special fibre
  have hfib : IsIso (Scheme.Modules.unitToPushforwardUnit
        (pullback.snd ((𝒯).map γ) (((𝒯).map qY).fiberι u))) ∧
      IsZero (firstDirectImageStructureSheaf
        (pullback.snd ((𝒯).map γ) (((𝒯).map qY).fiberι u))) := by
    let h := Space.residueFieldMap B integerBase hZ X.base (φ.left.1 u)
      (B.residueField_spec_contains X.base.left.property (φ.left.1 u))
    let t₁ := Space.residueFieldObjectMap B integerBase hZ U X.base φ u
    let h₁ := Space.residueFieldMap B integerBase hZ U u
      (B.residueField_spec_contains U.left.property u)
    have hcomm : schemeSpaceMap h₁ ≫ schemeSpaceMap φ = schemeSpaceMap t₁ ≫ schemeSpaceMap h := by
      rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, Space.residueFieldObjectMap_comp]
    have sqXs := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase
      (schemeSpaceMap h)
    have sqYs := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ g (schemeSpaceMap h)
    have cXs := isPullback_of_isPullback_of_isPullback hc sqXs sqYs
      (Space.structureContractionBaseChange_fst B integerBase hZ c hc (schemeSpaceMap h))
      (Space.structureContractionBaseChange_snd B integerBase hZ c hc (schemeSpaceMap h))
    obtain ⟨a₁, b₁, H₁, H₂⟩ := exists_isPullback_baseChange_chart cX sqYg t₁ h₁ hcomm cXs sqYs
    have hb₁ : Space.IsEtale B integerBase hZ b₁.hom :=
      Space.isEtale_of_isPullback B integerBase hZ _ _ _ _ H₂.flip
        (Space.isEtale_schemeSpaceMap_residueFieldObjectMap B integerBase hZ U X.base φ hφ u)
    have hC := Space.isStructureContraction_of_isPullback H₁ hb₁ hs
    exact (isStructureContraction_homOfScheme_iff _ h071N).1 hC
  -- the neighbourhood
  obtain ⟨U₀, huU₀, hU₀⟩ :=
    exists_isOpen_forall_isPullback_of_specialFibre ((𝒯).map γ) ((𝒯).map qY) u hflat hdim
      hfib.2 hfib.1
  refine ⟨⟨((𝒯).map φ).base '' U₀, ((𝒯).map φ).isOpenMap _ U₀.isOpen⟩, ⟨u, huU₀, rfl⟩, ?_⟩
  intro T h hh X' Y' pX' fX' pY' fY' c' sqX' sqY' hc₁ hc₂
  have hT₁ : B.Contains (pullback ((𝒯).map h) (U₀.ι ≫ (𝒯).map φ)) :=
    contains_pullback _ _ T.left.property (Scheme.size_lt_of_isOpenImmersion U₀.ι U.left.property)
  let T₁ : BigFppfOver B integerBase hZ := ofScheme _ hT₁
  let t₁ : T₁ ⟶ T := homOfScheme (pullback.fst ((𝒯).map h) (U₀.ι ≫ (𝒯).map φ))
  let h₁ : T₁ ⟶ U := homOfScheme (pullback.snd ((𝒯).map h) (U₀.ι ≫ (𝒯).map φ) ≫ U₀.ι)
  have hcomm : schemeSpaceMap h₁ ≫ schemeSpaceMap φ = schemeSpaceMap t₁ ≫ schemeSpaceMap h := by
    rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp]
    congr 1
    apply (𝒯).map_injective
    show (pullback.snd ((𝒯).map h) (U₀.ι ≫ (𝒯).map φ) ≫ U₀.ι) ≫ (𝒯).map φ =
      pullback.fst ((𝒯).map h) (U₀.ι ≫ (𝒯).map φ) ≫ (𝒯).map h
    exact (Category.assoc _ _ _).trans pullback.condition.symm
  have cX' := isPullback_of_isPullback_of_isPullback hc sqX' sqY' hc₁ hc₂
  obtain ⟨a₁, b₁, H₁, H₂⟩ := exists_isPullback_baseChange_chart cX sqYg t₁ h₁ hcomm cX' sqY'
  have hK := hU₀ ((𝒯).map h₁) (pullback.fst ((𝒯).map qY) ((𝒯).map h₁)) (pullback.snd _ _)
    (pullback.fst ((𝒯).map γ) (pullback.fst ((𝒯).map qY) ((𝒯).map h₁))) (pullback.snd ((𝒯).map γ) _)
    (fun t ↦ (pullback.snd ((𝒯).map h) (U₀.ι ≫ (𝒯).map φ) t).2)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)
  have het : Space.IsEtale B integerBase hZ (schemeSpaceMap t₁).hom :=
    Space.isEtale_schemeSpaceMap B integerBase hZ T₁ t₁
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance)
  have hsu : Space.IsSurjective B integerBase hZ (schemeSpaceMap t₁).hom := by
    refine Space.isSurjective_yoneda_map B integerBase hZ t₁ ⟨fun t ↦ ?_⟩
    obtain ⟨v, hv, hvt⟩ := hh t
    obtain ⟨w, rfl⟩ : v ∈ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hv
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (𝒯).map h)
      (g := U₀.ι ≫ (𝒯).map φ) t w (by rw [Scheme.Hom.comp_apply]; exact hvt.symm)
    exact ⟨z, hz⟩
  exact Space.isStructureContraction_of_isPullback_of_isSurjective H₁
    (Space.isEtale_of_isPullback B integerBase hZ _ _ _ _ H₂.flip het)
    (Space.isSurjective_of_isPullback B integerBase hZ H₂.flip hsu)
    ((isStructureContraction_homOfScheme_iff _ h071N).2 hK)

open Stacks.AlgebraicGeometry.TopDegreeBaseChange Space in
/-- **Stacks 0E88, from its two inputs.** Let `S` be a scheme, `s ∈ S`, and `c : X ⟶ Y` a
morphism over `S` of families of curves. If `c_{s,*}𝒪_{X_s} = 𝒪_{Y_s}` and
`R¹c_{s,*}𝒪_{X_s} = 0`, there is an open neighbourhood `W` of `s` such that for every scheme
`T ⟶ S` landing in `W` and every base change `c' : X_T ⟶ Y_T` of `c`, `𝒪_{Y_T} = c'_*𝒪_{X_T}`
and `R¹c'_*𝒪_{X_T} = 0`.

The inputs are the smoothness half of Stacks 0DQ0 (`hpol`, consumed by the pointwise form of
Stacks 0E6F) and the separated case of Stacks 071N (`h071N`). -/
theorem exists_isOpen_isStructureContraction_of_isSmoothLocallyPolarized
    (hpol : ∀ X : CurveFamily B hZ, X.IsSmoothLocallyPolarized)
    (h071N : ∀ {T' T : BigFppfOver B integerBase hZ} (g : T' ⟶ T)
      (_hqc : QuasiCompact ((BigFppfOver.toScheme B integerBase hZ).map g))
      (_hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B integerBase hZ).map g))
      (F : ((BigFppfOver.toScheme B integerBase hZ).obj T').Modules) (_hF : F.IsQuasicoherent)
      (k : ℕ),
      have := hasInjectiveResolutions_modules B integerBase hZ (yoneda.obj T')
        (isAlgebraicSpace_yoneda B integerBase hZ T')
      have := modulePushforward_additive B integerBase hZ (representedSpaceMap B integerBase hZ g)
      Nonempty (((modulePushforward B integerBase hZ
          (representedSpaceMap B integerBase hZ g)).rightDerived k).obj
          ((representedAssociatedModule B integerBase hZ T'
            (isAlgebraicSpace_yoneda B integerBase hZ T')).obj F) ≅
        (representedAssociatedModule B integerBase hZ T
          (isAlgebraicSpace_yoneda B integerBase hZ T)).obj
          (((Scheme.Modules.pushforward
            ((BigFppfOver.toScheme B integerBase hZ).map g)).rightDerived k).obj F)))
    (X Y : CurveFamily B hZ) (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase) (s : X.base.left.1)
    (hs : Space.IsStructureContraction B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ c hc
        (schemeSpaceMap (Space.residueFieldMap B integerBase hZ X.base s
          (B.residueField_spec_contains X.base.left.property s))))) :
    ∃ W : X.base.left.1.Opens, s ∈ W ∧
      ∀ (T : BigFppfOver B integerBase hZ) (h : T ⟶ X.base),
        (∀ t, ((𝒯).map h).base t ∈ W) →
        ∀ (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total)
          (fX' : X' ⟶ schemeSpace T) (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T)
          (c' : X' ⟶ Y'),
          IsPullback pX' fX' X.toBase (schemeSpaceMap h) →
          IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap h) →
          c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
          Space.IsStructureContraction B integerBase hZ c' := by
  have hX : ∀ i, (![X, Y] i).base = X.base := by
    intro i
    fin_cases i
    · rfl
    · exact hb
  obtain ⟨U, φ, u, hφ, rfl, hsq⟩ :=
    exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized ![X, Y] hX
      (fun _ ↦ hpol _) s
  obtain ⟨ZX, pX, qX, sqX, -⟩ := hsq 0
  obtain ⟨ZY, pY, qY, sqY, -⟩ := hsq 1
  have sqX₀ : IsPullback pX (schemeSpaceMap qX) X.toBase
      (schemeSpaceMap (φ ≫ eqToHom (rfl : X.base = X.base))) := sqX
  have sqX' : IsPullback pX (schemeSpaceMap qX) X.toBase (schemeSpaceMap φ) := by
    simpa using sqX₀
  exact exists_isOpen_isStructureContraction_of_chart X Y hb c hc φ hφ u hs pX qX sqX' pY qY sqY
    h071N

end CurveFamily

end AlgebraicGeometry

end
