module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.SectionExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowGerbeCompactificationSection
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SectionMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance

/-!
# Extending an isomorphism of two sections of a separated stack by an admissible blowup

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space, let
`p : Y' ⟶ Y` be a morphism from a quasi-compact quasi-separated algebraic space, let `V ⊆ U ⊆ Y'`
be quasi-compact open subspaces and let `x_a, x_b : U ⟶ 𝒳` be two 1-morphisms over `Y` (that is,
`x_a ≫ f` and `x_b ≫ f` are 2-isomorphic to `U ⟶ Y' ⟶ Y`) whose restrictions to `V` are
2-isomorphic. Then after a `V`-admissible blowup `b : Y'' ⟶ Y'` the restrictions of `x_a` and
`x_b` to `b⁻¹(U)` are 2-isomorphic. This is the step "`φᵢⱼ` defines a section `V ⟶ Iᵢⱼ` of the
proper morphism `Iᵢⱼ ⟶ Wᵢ ∩ Wⱼ`, which extends after a `V`-admissible blowup by
[Stacks, Tag 0CPI]" of the proof of [Stacks, Tag 0CQ7].

The isomorphism space is realized as follows. The base change `f_U : 𝒳_U ⟶ U` of `f` is
separated, and `x_a`, `x_b` give sections `s_a`, `s_b` of it; a section of a separated
1-morphism is proper (Stacks 050J). The 2-fibre product `I = U ×_{s_a, 𝒳_U, s_b} U` has an
algebraic space as apex, and its first projection `I ⟶ U` is proper, as a base change of `s_b`.
A section of `I ⟶ U` over an open `O ⊆ U` is the same as a 2-isomorphism between the
restrictions of `x_a` and `x_b` to `O`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.baseChangeSection`: the section of the base change
  defined by a 1-morphism over the base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_baseChangeSection`: it is proper when `f` is
  separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_isAdmissibleBlowup_iso_of_iso`: the extension
  of the isomorphism.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CPI](https://stacks.math.columbia.edu/tag/0CPI)
* [Stacks Project, Tag 050J](https://stacks.math.columbia.edu/tag/050J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section BaseChangeSection

variable {Y U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (hU : IsAlgebraicSpace B S hS U) (φ : U ⟶ Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- The base change `𝒳 ×_Y U ⟶ U` of `f` along `φ : U ⟶ Y`. -/
abbrev baseChangeSquare : TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hU hY φ) f :=
  twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hU hY φ) f

/-- The 2-commutative square with apex `U` given by a 1-morphism `x : U ⟶ 𝒳` over `φ`. -/
def sectionCone (x : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ) :
    TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hU hY φ) f where
  pt := algebraicSpaceStack.{u, w} B S hS U hU
  fst := 𝟙 _
  snd := x
  iso := λ_ _ ≪≫ e.symm

/-- **The section of the base change `𝒳 ×_Y U ⟶ U` defined by a 1-morphism `x : U ⟶ 𝒳` over
`φ`.** -/
def baseChangeSectionPreHom (x : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ) :
    TwoCommSq.PreHom (sectionCone hY hU φ f x e) (baseChangeSquare hY hU φ f) :=
  twoFibreProductPreHom (isTwoFibreProduct_twoFibreProductSquare B S hS _ f) _

/-- The section of the base change defined by a 1-morphism over `φ`. -/
abbrev baseChangeSection (x : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ) :
    algebraicSpaceStack.{u, w} B S hS U hU ⟶ (baseChangeSquare hY hU φ f).pt :=
  (baseChangeSectionPreHom hY hU φ f x e).hom

/-- The section is a section. -/
def baseChangeSectionFst (x : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ) :
    baseChangeSection hY hU φ f x e ≫ (baseChangeSquare hY hU φ f).fst ≅ 𝟙 _ :=
  (baseChangeSectionPreHom hY hU φ f x e).isoFst.symm

/-- The section followed by the projection to `𝒳` is `x`. -/
def baseChangeSectionSnd (x : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ) :
    baseChangeSection hY hU φ f x e ≫ (baseChangeSquare hY hU φ f).snd ≅ x :=
  (baseChangeSectionPreHom hY hU φ f x e).isoSnd.symm

/-- The base change of a separated 1-morphism is separated. -/
theorem isSeparated_baseChangeSquare_fst (hf : IsSeparated B S hS f) :
    IsSeparated B S hS (baseChangeSquare hY hU φ f).fst :=
  isSeparated_baseChange_of_isTwoFibreProduct B S hS f _ (baseChangeSquare hY hU φ f).swap
    (isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare B S hS _ f)) hf

/-- **The section of the base change is proper** when `f` is separated (Stacks 050J). -/
theorem isProper_baseChangeSection (hf : IsSeparated B S hS f)
    (x : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ) :
    IsProper B S hS (baseChangeSection hY hU φ f x e) :=
  (isProper_iff_isProper_hom B S hS _
    (isRepresentableByAlgebraicSpaces_section B S hS _ _ ⟨baseChangeSectionFst hY hU φ f x e⟩)).mpr
    (isRelativelyProper_section B S hS _ _ ⟨baseChangeSectionFst hY hU φ f x e⟩
      (isSeparated_baseChangeSquare_fst hY hU φ f hf))

/-- The section is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_baseChangeSection
    (x : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (e : x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ) :
    IsRepresentableByAlgebraicSpaces B S hS (baseChangeSection hY hU φ f x e).hom.hom :=
  isRepresentableByAlgebraicSpaces_section B S hS _ _ ⟨baseChangeSectionFst hY hU φ f x e⟩

end BaseChangeSection

section SectionIso

variable {Y U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (hU : IsAlgebraicSpace B S hS U) (φ : U ⟶ Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- Precomposing `e : s ≫ q ≅ x` with `g` and reassociating. -/
private def whiskerCompIso {C : Type*} [Bicategory C] {a b c d : C} {s : b ⟶ c} {q : c ⟶ d}
    {x : b ⟶ d} (g : a ⟶ b) (e : s ≫ q ≅ x) : g ≫ x ≅ (g ≫ s) ≫ q :=
  whiskerLeftIso g e.symm ≪≫ (α_ _ _ _).symm

/-- Two 2-cells between 1-morphisms into the stack of an algebraic space are equal. -/
theorem hom₂_eq_of_algebraicSpaceStack {𝒯 : AlgebraicStacks.{u, w} B S hS}
    {g g' : 𝒯 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} (a b : g ⟶ g') : a = b :=
  (subsingleton_hom₂_algebraicSpaceStackFunctor_obj (Y := ⟨Y, hY⟩) g g').elim a b

/-- **Two 1-morphisms over `φ` which are 2-isomorphic after restriction along `ι` give sections
of the base change which are 2-isomorphic after restriction along `ι`.** Both restricted
sections are mediating 1-morphisms into the 2-fibre product from one and the same cone, the
compatibility conditions holding because 2-cells into the stack of `Y` are unique. -/
theorem nonempty_iso_baseChangeSection_of_iso {O : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hO : IsAlgebraicSpace B S hS O) (k : O ⟶ U)
    (xa xb : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (ea : xa ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ)
    (eb : xb ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ)
    (ψ : algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ xa ≅
      algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ xb) :
    Nonempty (algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ baseChangeSection hY hU φ f xa ea ≅
      algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ baseChangeSection hY hU φ f xb eb) := by
  let ι := algebraicSpaceStackMap.{u, w} B S hS hO hU k
  let P := baseChangeSquare hY hU φ f
  let Q : TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hU hY φ) f :=
    { pt := algebraicSpaceStack.{u, w} B S hS O hO
      fst := ι
      snd := ι ≫ xa
      iso := whiskerLeftIso ι ea.symm ≪≫ (α_ _ _ _).symm }
  let L : TwoCommSq.PreHom Q P :=
    { hom := ι ≫ baseChangeSection hY hU φ f xa ea
      isoFst := (ρ_ ι).symm ≪≫ whiskerCompIso ι (baseChangeSectionFst hY hU φ f xa ea)
      isoSnd := whiskerCompIso ι (baseChangeSectionSnd hY hU φ f xa ea)
      compat := hom₂_eq_of_algebraicSpaceStack hY _ _ }
  let M : TwoCommSq.PreHom Q P :=
    { hom := ι ≫ baseChangeSection hY hU φ f xb eb
      isoFst := (ρ_ ι).symm ≪≫ whiskerCompIso ι (baseChangeSectionFst hY hU φ f xb eb)
      isoSnd := ψ ≪≫ whiskerCompIso ι (baseChangeSectionSnd hY hU φ f xb eb)
      compat := hom₂_eq_of_algebraicSpaceStack hY _ _ }
  obtain ⟨θ, -, -⟩ :=
    twoFibreProductPreHom_rel (isTwoFibreProduct_twoFibreProductSquare B S hS _ f) L M
  exact ⟨θ⟩

/-- **Restricted sections which are 2-isomorphic give restricted 1-morphisms which are
2-isomorphic**: whisker with the projection to `𝒳`. -/
theorem nonempty_iso_of_iso_baseChangeSection {O : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hO : IsAlgebraicSpace B S hS O) (k : O ⟶ U)
    (xa xb : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (ea : xa ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ)
    (eb : xb ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU hY φ)
    (θ : algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ baseChangeSection hY hU φ f xa ea ≅
      algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ baseChangeSection hY hU φ f xb eb) :
    Nonempty (algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ xa ≅
      algebraicSpaceStackMap.{u, w} B S hS hO hU k ≫ xb) :=
  ⟨whiskerCompIso _ (baseChangeSectionSnd hY hU φ f xa ea) ≪≫ whiskerRightIso θ _ ≪≫
    (whiskerCompIso _ (baseChangeSectionSnd hY hU φ f xb eb)).symm⟩

end SectionIso

section Extension

/-- The representing morphism of a 1-morphism between the stacks of two algebraic spaces
induces that 1-morphism. -/
theorem algebraicSpaceStackMap_representingMap {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (φ : algebraicSpaceStack.{u, w} B S hS X hX ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) :
    algebraicSpaceStackMap.{u, w} B S hS hX hY
      (representingMap B S hS _ _ X Y (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) φ.hom) = φ :=
  algebraicSpaceStackFunctor_map_homMk_representingMap (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) φ

/-- The 1-morphism of stacks attached to a morphism of algebraic spaces determines it. -/
theorem eq_of_algebraicSpaceStackMap_eq {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {g g' : X ⟶ Y}
    (h : algebraicSpaceStackMap.{u, w} B S hS hX hY g =
      algebraicSpaceStackMap.{u, w} B S hS hX hY g') : g = g' :=
  congrArg (fun m => m.hom) (algebraicSpaceStackFunctor_map_injective.{u, w}
    (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (f := ObjectProperty.homMk g) (g := ObjectProperty.homMk g') h)

/-- Two 2-isomorphic 1-morphisms into the stack of an algebraic space are equal. -/
theorem eq_of_iso_algebraicSpaceStack {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒯 : AlgebraicStacks.{u, w} B S hS}
    {g g' : 𝒯 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY} (e : g ≅ g') : g = g' :=
  eq_of_hom₂_algebraicSpaceStackFunctor_obj (Y := ⟨Y, hY⟩) e.hom

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)

/-- **Extending an isomorphism of two sections of a separated stack by an admissible blowup.**
Let `f : 𝒳 ⟶ Y` be separated, let `Y'` be a quasi-compact quasi-separated algebraic space with a
morphism `p : Y' ⟶ Y`, let `V ⊆ U ⊆ Y'` be quasi-compact open subspaces and let
`x_a, x_b : U ⟶ 𝒳` be 1-morphisms with `x_a ≫ f` and `x_b ≫ f` 2-isomorphic to `U ⟶ Y' ⟶ Y`. If
the restrictions of `x_a` and `x_b` to `V` are 2-isomorphic, then there is a `V`-admissible
blowup `b : Y'' ⟶ Y'` such that the restrictions of `x_a` and `x_b` to `b⁻¹(U)` are
2-isomorphic.

The 2-isomorphism over `V` is a section over `V` of the isomorphism space `I ⟶ U`, which is
proper (`AlgebraicGeometry.Stack.AlgebraicStacks.isProper_baseChangeSection`); by
[Stacks, Tag 0CPI] it extends over `b⁻¹(U)` after a `V`-admissible blowup, and a section of
`I ⟶ U` over `b⁻¹(U)` is a 2-isomorphism of the restrictions there. -/
theorem exists_isAdmissibleBlowup_iso_of_iso (hf : IsSeparated B S hS f)
    {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (hY'qc : Space.IsQuasiCompactSpace B S hS Y')
    (hY'qs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y') (p : Y' ⟶ Y)
    (U V : Subfunctor Y') (hU : Space.IsOpenSubspace B S hS U)
    (hV : Space.IsOpenSubspace B S hS V) (hUqc : Space.IsQuasiCompactSpace B S hS U.toFunctor)
    (hVqc : Space.IsQuasiCompactSpace B S hS V.toFunctor) (hVU : V ≤ U)
    (xa xb : algebraicSpaceStack.{u, w} B S hS U.toFunctor hU.1 ⟶ 𝒳)
    (ea : xa ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p))
    (eb : xb ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hU.1 hY (U.ι ≫ p))
    (ψ : algebraicSpaceStackMap.{u, w} B S hS hV.1 hU.1 (Subfunctor.homOfLe hVU) ≫ xa ≅
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hU.1 (Subfunctor.homOfLe hVU) ≫ xb) :
    ∃ (Y'' : AlgebraicSpaces B S hS) (b : Y'' ⟶ ⟨Y', hY'⟩),
      Space.IsAdmissibleBlowup B S hS ⟨V, hV⟩ b ∧
        Nonempty (algebraicSpaceStackMap.{u, w} B S hS
            (Space.isOpenSubspace_preimage B S hS b.hom U hY' Y''.2 hU).1 hU.1
            (U.fromPreimage b.hom) ≫ xa ≅
          algebraicSpaceStackMap.{u, w} B S hS
            (Space.isOpenSubspace_preimage B S hS b.hom U hY' Y''.2 hU).1 hU.1
            (U.fromPreimage b.hom) ≫ xb) := by
  have hUa := hU.1
  let sa : algebraicSpaceStack.{u, w} B S hS U.toFunctor hUa ⟶
      (baseChangeSquare hY hUa (U.ι ≫ p) f).pt := baseChangeSection hY hUa (U.ι ≫ p) f xa ea
  let sb : algebraicSpaceStack.{u, w} B S hS U.toFunctor hUa ⟶
      (baseChangeSquare hY hUa (U.ι ≫ p) f).pt := baseChangeSection hY hUa (U.ι ≫ p) f xb eb
  obtain ⟨I, a, b, γ, ⟨hI⟩⟩ := exists_isTwoFibreProduct_algebraicSpaceStackFunctor_obj sa sb <|
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS _ _ _ sb.hom sa.hom _
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        sa.hom sb.hom)
      (isRepresentableByAlgebraicSpaces_baseChangeSection hY hUa (U.ι ≫ p) f xb eb)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS U.toFunctor hUa)
  let r : I.obj ⟶ U.toFunctor := representingMap B S hS _ _ I.obj U.toFunctor
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom
  have hra : algebraicSpaceStackMap.{u, w} B S hS I.2 hUa r = a :=
    algebraicSpaceStackMap_representingMap I.2 hUa a
  have hab : a = b := eq_of_iso_algebraicSpaceStack hUa <|
    (ρ_ a).symm ≪≫ whiskerCompIso a (baseChangeSectionFst hY hUa (U.ι ≫ p) f xa ea) ≪≫
      whiskerRightIso γ _ ≪≫
      (whiskerCompIso b (baseChangeSectionFst hY hUa (U.ι ≫ p) f xb eb)).symm ≪≫ ρ_ b
  -- the projection `I ⟶ U` is proper
  have hrp : Space.IsProper B S hS r := by
    have ha : IsProper B S hS a :=
      isProper_baseChange B S hS sb sa (⟨_, a, b, γ⟩ : TwoCommSq sa sb) hI
        (isProper_baseChangeSection hY hUa (U.ι ≫ p) f hf xb eb)
    rw [← hra] at ha
    exact (isProper_algebraicSpaceStackMap_iff.{u, w} B S hS I.2 hUa r).1 ha
  -- the section of `I ⟶ U` over `V`
  obtain ⟨θ⟩ := nonempty_iso_baseChangeSection_of_iso hY hUa (U.ι ≫ p) f hV.1
    (Subfunctor.homOfLe hVU) xa xb ea eb ψ
  let ιV := algebraicSpaceStackMap.{u, w} B S hS hV.1 hUa (Subfunctor.homOfLe hVU)
  let C : TwoCommSq sa sb := ⟨algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1, ιV, ιV, θ⟩
  let σ := (twoFibreProductPreHom hI C).hom
  let t : V.toFunctor ⟶ I.obj := representingMap B S hS _ _ V.toFunctor I.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) σ.hom
  have htσ : algebraicSpaceStackMap.{u, w} B S hS hV.1 I.2 t = σ :=
    algebraicSpaceStackMap_representingMap hV.1 I.2 σ
  have htr : t ≫ r = Subfunctor.homOfLe hVU := eq_of_algebraicSpaceStackMap_eq hV.1 hUa <| by
    rw [← algebraicSpaceStackMap_comp B S hS hV.1 I.2 hUa t r, htσ, hra]
    exact eq_of_iso_algebraicSpaceStack hUa (twoFibreProductPreHom hI C).isoFst.symm
  -- Stacks 0CPI
  obtain ⟨Y'', bl, hbl, s', hs', -⟩ :=
    Space.exists_isAdmissibleBlowup_extending_section_of_isProper (X := I)
      (Y := ⟨Y', hY'⟩) hY'qc hY'qs ⟨V, hV⟩ ⟨U, hU⟩ hVU hVqc hUqc (ObjectProperty.homMk r) hrp t htr
  refine ⟨Y'', bl, hbl, ?_⟩
  -- the extended section is an isomorphism over `b⁻¹(U)`
  have hU'a := (Space.isOpenSubspace_preimage B S hS bl.hom U hY' Y''.2 hU).1
  let ι' := algebraicSpaceStackMap.{u, w} B S hS hU'a hUa (U.fromPreimage bl.hom)
  let σ' := algebraicSpaceStackMap.{u, w} B S hS hU'a I.2 s'
  have hσ'a : σ' ≫ a = ι' := by
    rw [← hra, algebraicSpaceStackMap_comp B S hS hU'a I.2 hUa s' r]
    exact congrArg _ hs'
  have hσ'b : σ' ≫ b = ι' := by rwa [← hab]
  exact nonempty_iso_of_iso_baseChangeSection hY hUa (U.ι ≫ p) f hU'a (U.fromPreimage bl.hom)
    xa xb ea eb <| eqToIso (congrArg (· ≫ sa) hσ'a.symm) ≪≫ α_ _ _ _ ≪≫ whiskerLeftIso σ' γ ≪≫
      (α_ _ _ _).symm ≪≫ eqToIso (congrArg (· ≫ sb) hσ'b)

end Extension

end AlgebraicGeometry.Stack.AlgebraicStacks

end
