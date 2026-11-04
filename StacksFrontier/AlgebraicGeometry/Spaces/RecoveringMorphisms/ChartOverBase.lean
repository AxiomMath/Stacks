module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.AffineLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.BaseFunctionTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomRigidity
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.LeftAdjointLocalLift

/-!
# The chart morphisms of a 2-compatible morphism of small étale ringed topoi lie over the base

Let `ψ` be a morphism of the small étale ringed topoi of two algebraic spaces `P` and `Q` over a
scheme `S`, and suppose `ψ` is 2-compatible with a pair of morphisms `p_P : P ⟶ A`, `p_Q : Q ⟶ A`
to a third algebraic space: the composite `(p_Q)_{small} ∘ ψ` is 2-isomorphic to
`(p_P)_{small}`.  For an affine étale chart `V` of `Q`, an étale chart `U` of `P` and a section
`s` over `U` of `ψ⁻¹h_V`, the proof of [Stacks Project, Tag 04KL] produces a morphism of schemes
`f_s : U ⟶ V` (`AlgebraicGeometry.Space.chartSchemeHom`).  This file proves that `f_s` commutes
with the structure morphisms of the two charts to `S`, for an **arbitrary** base scheme `S`:
`AlgebraicGeometry.Space.isChartOverBase_of_twoCompatible`.

The proof has three steps.

* *Morphisms of algebraic spaces.*  For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the
  chart morphisms of `f_{small}` are morphisms over `S`
  (`AlgebraicGeometry.Space.isChartOverBase_smallEtaleRingedToposHom`).  The chart maps over `f`
  into `V` give sections of `f⁻¹h_V` (`AlgebraicGeometry.Space.chartFiberSection`) whose chart
  morphisms are the chart maps themselves, which are morphisms of the big fppf site of `S`; and
  these sections detect maps out of `f⁻¹h_V`, by the description of the sections of the direct
  image of Stacks 03G8, so they generate `f⁻¹h_V` locally.  The condition on a section is local,
  since a morphism of schemes into `S` is determined on an étale covering
  (`AlgebraicGeometry.Space.SmallEtale.eq_of_mem_topology`, the fpqc topology being
  subcanonical).
* *Composites and 2-isomorphisms.*  The chart ring map of a composite at an iterated section is
  the composite of the chart ring maps (`AlgebraicGeometry.Space.chartRingHom_comp`), and a
  2-isomorphism carries sections to sections with the same chart ring map
  (`AlgebraicGeometry.Space.chartRingHom_eq_of_twoIso`).  So for `W` an affine chart of `A` and
  a section `σ` of `p_Q⁻¹h_W` over `V`, the morphism `f_s` followed by `f_σ` is a chart morphism
  of `(p_P)_{small}`, and both `f_σ` and that one are morphisms over `S`; hence so is `f_s`.
* *Localisation.*  Such a `σ` exists only locally on `V`, and the affine charts of `A` cover
  `A`; a section of `ψ⁻¹h_V` lifts, locally on `U`, along any covering of `V`
  (`CategoryTheory.Sheaf.exists_covering_lift_of_adjunction`), and the equation descends along
  the resulting covering of `U`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.eq_of_mem_topology`: morphisms of schemes out of an étale
  chart are determined on a covering sieve.
* `AlgebraicGeometry.Space.isChartOverBase_smallEtaleRingedToposHom`: the chart morphisms of the
  morphism of small étale ringed topoi of a morphism of algebraic spaces lie over the base.
* `AlgebraicGeometry.Space.isChartOverBase_of_twoCompatible`: the chart morphisms of a
  2-compatible morphism of small étale ringed topoi lie over the base.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] smallEtaleTopology_subcanonical

/-! ### Morphisms of schemes out of a chart are determined on a covering -/

/-- **Morphisms of schemes out of an étale chart are determined on a covering sieve** of the
small étale site. -/
theorem SmallEtale.eq_of_mem_topology {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : SmallEtale B S hS F} {Z : Scheme.{u}} {a b : chartSch U ⟶ Z} {R : Sieve U}
    (hR : R ∈ SmallEtale.topology B S hS F U)
    (h : ∀ ⦃V : SmallEtale B S hS F⦄ (i : V ⟶ U), R i →
      (BigFppfOver.toScheme B S hS).map i.hom.left ≫ a =
        (BigFppfOver.toScheme B S hS).map i.hom.left ≫ b) :
    a = b := by
  have := SmallEtale.isContinuous_toScheme B S hS F
  have hsh :=
    (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).op_comp_isSheaf_of_isSheaf_type
    (SmallEtale.topology B S hS F)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.fpqcTopology)
      (yoneda.obj Z))
  exact (hsh R hR).isSeparatedFor.ext fun V i hi ↦ h i hi

/-- A morphism of the big fppf site of `S` commutes with the structure morphisms to `S`. -/
theorem toScheme_map_comp_inclusion_map {T T' : BigFppfOver B S hS} (m : T ⟶ T') :
    (BigFppfOver.toScheme B S hS).map m ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom := by
  change B.inclusion.map m.left ≫ _ = _
  rw [← Functor.map_comp]
  exact congrArg B.inclusion.map (Over.w m)

/-! ### Chart ring maps of composites and under 2-isomorphisms -/

section ChartRingHom

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **A 2-isomorphism carries sections to sections with the same chart ring map**: the chart ring
map of `g` at `s` is that of `g'` at the image of `s` under the isomorphism of inverse images
attached to the 2-isomorphism. -/
theorem chartRingHom_eq_of_twoIso
    {g g' : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    (t : RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS X)
      (B := smallEtaleRingedTopos B S hS Y) g g')
    (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    chartRingHom g V U s =
      chartRingHom g' V U ((t.symm.inverseImageIso.hom.app _).hom.app (op U) s) := by
  ext b
  refine (chartRingHom_apply g V U s b).trans (Eq.trans ?_ (chartRingHom_apply g' V U _ b).symm)
  have hkey : ∀ b' : (setO Y).obj.obj (op V),
      invCoord g V b' = t.symm.inverseImageIso.hom.app _ ≫ invCoord g' V b' := fun b' ↦ by
    unfold invCoord
    rw [t.fSharpSet_eq, ← Category.assoc, NatTrans.naturality, Category.assoc]
  exact congrArg (fun m ↦ m.hom.app (op U) s) (hkey b)

section Comp

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **The chart ring map of a composite at an iterated section is the composite of the chart
ring maps.**  For a section `σ` over `V` of `χ⁻¹h_W` and a section `s` over `U` of `ψ⁻¹h_V`, the
image of `s` under `ψ⁻¹` of the map `h_V ⟶ χ⁻¹h_W` classifying `σ` is a section over `U` of
`(χ ∘ ψ)⁻¹h_W`, and its chart ring map is the chart ring map of `σ` followed by that of `s`. -/
theorem chartRingHom_comp
    (χ : RingedToposHom (smallEtaleRingedTopos B S hS Y) (smallEtaleRingedTopos B S hS Z))
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (W : SmallEtale B S hS Z.1) (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (σ : (invRep χ W).obj.obj (op V)) (s : (invRep ψ V).obj.obj (op U)) :
    chartRingHom (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z) χ ψ) W U
        ((ψ.toToposHom.inverseImage.map
          ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm σ)).hom.app (op U) s) =
      chartRingHom χ W V σ ≫ chartRingHom ψ V U s := by
  ext b
  change _ = (chartRingHom ψ V U s).hom ((chartRingHom χ W V σ).hom b)
  refine (chartRingHom_apply _ W U _ b).trans (Eq.trans ?_
    ((congrArg (chartRingHom ψ V U s).hom (chartRingHom_apply χ W V σ b)).trans
      (chartRingHom_apply ψ V U s _)).symm)
  have key : ∀ b' : (setO Z).obj.obj (op W),
      ψ.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm σ) ≫
        invCoord (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X)
          (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z) χ ψ) W b' =
      invCoord ψ V ((invCoord χ W b').hom.app (op V) σ) := fun b' ↦ by
    have h2 : (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm σ ≫ invCoord χ W b' =
        (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm ((invCoord χ W b').hom.app (op V) σ) :=
      GrothendieckTopology.yonedaEquiv_symm_naturality_right _ V _ σ
    have h3 : invCoord ψ V ((invCoord χ W b').hom.app (op V) σ) =
        ψ.toToposHom.inverseImage.map
          ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm σ ≫ invCoord χ W b') ≫
          ψ.fSharpSet := by
      rw [h2]
      rfl
    rw [h3]
    unfold invCoord
    rw [RingedToposHom.fSharpSet_comp χ ψ]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  exact congrArg (fun m ↦ m.hom.app (op U) s) (key b)

end Comp

end ChartRingHom

/-! ### The chart morphisms of a morphism of algebraic spaces -/

section OfHom

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The section of the direct image of `f⁻¹h_V` over `V` given by the unit of the adjunction. -/
abbrev unitSection (V : SmallEtale B S hS Y.1) :
    ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj
      (invRep (smallEtaleRingedToposHom B S hS f) V)).obj.obj (op V) :=
  (SmallEtale.topology B S hS Y.1).yonedaEquiv
    ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app _)

/-- **The sections of `f⁻¹h_V` named by the chart maps over `f` into `V`**: the map out of
`AlgebraicGeometry.Space.chartFiber` corresponding, by the description of the sections of the
direct image of Stacks 03G8, to the unit of the adjunction. -/
def chartFiberSection (V : SmallEtale B S hS Y.1) :
    (chartFiber B S hS f V).toFunctor ⟶ (invRep (smallEtaleRingedToposHom B S hS f) V).obj :=
  sectionEquivChartFiberHom B S hS f V _ (unitSection f V)

/-- Composing `AlgebraicGeometry.Space.chartFiberSection` with a map out of `f⁻¹h_V` is the map
out of the chart fibre corresponding to its adjoint. -/
theorem chartFiberSection_comp (V : SmallEtale B S hS Y.1)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (a : invRep (smallEtaleRingedToposHom B S hS f) V ⟶ E) :
    chartFiberSection f V ≫ a.hom = sectionEquivChartFiberHom B S hS f V E
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv
        ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _ a)) := by
  rw [chartFiberSection, ← sectionEquivChartFiberHom_naturality, Adjunction.homEquiv_unit,
    GrothendieckTopology.yonedaEquiv_comp]
  rfl

/-- **The sections named by the chart maps detect maps out of `f⁻¹h_V`.** -/
theorem hom_ext_chartFiberSection (V : SmallEtale B S hS Y.1)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (a a' : invRep (smallEtaleRingedToposHom B S hS f) V ⟶ E)
    (h : chartFiberSection f V ≫ a.hom = chartFiberSection f V ≫ a'.hom) : a = a' := by
  rw [chartFiberSection_comp, chartFiberSection_comp] at h
  exact ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _).injective
    ((SmallEtale.topology B S hS Y.1).yonedaEquiv.injective
      ((sectionEquivChartFiberHom B S hS f V E).injective h))

/-- **The chart ring map at the section named by a chart map is pullback of functions along the
chart map.** -/
theorem chartRingHom_chartFiberSection (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (c : (chartFiber B S hS f V).toFunctor.obj (op U)) :
    chartRingHom (smallEtaleRingedToposHom B S hS f) V U
        ((chartFiberSection f V).app (op U) c) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map c.1).op := by
  ext b
  refine (chartRingHom_apply _ V U _ b).trans ?_
  have key : ∀ b' : (setO Y).obj.obj (op V),
      chartFiberSection f V ≫ (invCoord (smallEtaleRingedToposHom B S hS f) V b').hom =
        chartFiberCoordinate B S hS f V b' := fun b' ↦ by
    have h1 : (smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _
        (invCoord (smallEtaleRingedToposHom B S hS f) V b') =
        (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm
          ((RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V)
            b') := by
      rw [← homEquiv_symm_forgetFSharp, Equiv.apply_symm_apply]
    rw [chartFiberSection_comp, h1, Equiv.apply_symm_apply]
    exact sectionEquivChartFiberHom_fSharp B S hS f V b'
  exact congrArg (fun m ↦ m.app (op U) c) (key b)

end OfHom

/-! ### The chart morphisms of a 2-compatible morphism -/

section TwoCompatible

variable {A P Q : AlgebraicSpaces B S hS} (pP : P ⟶ A) (pQ : Q ⟶ A)
  (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q))

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **Over an affine chart carrying a section of `p_Q⁻¹h_W`, the chart morphisms of `ψ` lie over
the base.** -/
theorem chartSchemeHom_comp_inclusion_map_of_section
    (t : RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS P)
      (B := smallEtaleRingedTopos B S hS A)
      (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS P)
        (Y := smallEtaleRingedTopos B S hS Q) (Z := smallEtaleRingedTopos B S hS A)
        (smallEtaleRingedToposHom B S hS pQ) ψ)
      (smallEtaleRingedToposHom B S hS pP))
    (V : SmallEtale B S hS Q.1) [IsAffine (chartSch V)] (W : SmallEtale B S hS A.1)
    [IsAffine (chartSch W)] (σ : (invRep (smallEtaleRingedToposHom B S hS pQ) W).obj.obj (op V))
    (U : SmallEtale B S hS P.1) (s : (invRep ψ V).obj.obj (op U)) :
    chartSchemeHom ψ V U s ≫ B.inclusion.map V.obj.left.hom = B.inclusion.map U.obj.left.hom := by
  let τ := (ψ.toToposHom.inverseImage.map
    ((SmallEtale.topology B S hS Q.1).yonedaEquiv.symm σ)).hom.app (op U) s
  have hcomp : chartSchemeHom ψ V U s ≫ chartSchemeHom (smallEtaleRingedToposHom B S hS pQ) W V σ =
      chartSchemeHom (smallEtaleRingedToposHom B S hS pP) W U
        ((t.symm.inverseImageIso.hom.app _).hom.app (op U) τ) := by
    apply ext_of_isAffine
    rw [Scheme.Hom.comp_appTop, chartSchemeHom_appTop, chartSchemeHom_appTop,
      chartSchemeHom_appTop, ← chartRingHom_eq_of_twoIso t, chartRingHom_comp]
  rw [← isChartOverBase_smallEtaleRingedToposHom pQ W V σ, ← Category.assoc, hcomp]
  exact isChartOverBase_smallEtaleRingedToposHom pP W U _

/-- **The chart morphisms of a 2-compatible morphism of small étale ringed topoi lie over the
base**, for an arbitrary base scheme. -/
theorem isChartOverBase_of_twoCompatible
    (t : RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS P)
      (B := smallEtaleRingedTopos B S hS A)
      (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS P)
        (Y := smallEtaleRingedTopos B S hS Q) (Z := smallEtaleRingedTopos B S hS A)
        (smallEtaleRingedToposHom B S hS pQ) ψ)
      (smallEtaleRingedToposHom B S hS pP)) :
    IsChartOverBase ψ := by
  intro V _ U s
  let pQs := smallEtaleRingedToposHom B S hS pQ
  let good : SmallEtale B S hS Q.1 → Prop := fun V₀ ↦ IsAffine (chartSch V₀) ∧
    ∃ (W : SmallEtale B S hS A.1) (_ : IsAffine (chartSch W)),
      Nonempty ((invRep pQs W).obj.obj (op V₀))
  let R : Sieve V :=
    { arrows := fun V'' j ↦ ∃ (V₀ : SmallEtale B S hS Q.1) (k : V'' ⟶ V₀) (j₀ : V₀ ⟶ V),
        good V₀ ∧ k ≫ j₀ = j
      downward_closed := by
        rintro V'' V''' j ⟨V₀, k, j₀, hV₀, rfl⟩ m
        exact ⟨V₀, m ≫ k, j₀, hV₀, Category.assoc _ _ _⟩ }
  have hsub : ∀ W : SmallEtale B S hS A.1,
      Subsingleton ((⊤_ Sheaf (SmallEtale.topology B S hS A.1) (Type u)).obj.obj (op W)) :=
    fun W ↦ @Unique.instSubsingleton _
      (Functor.uniqueTerminalObj (P := Sheaf.sectionsFunctor.{u} (SmallEtale.topology B S hS A.1)
        (op W)))
  have hRmem : R ∈ SmallEtale.topology B S hS Q.1 V := by
    obtain ⟨T, hT, hTs⟩ := Sheaf.exists_locally_lift_of_adjunction pQs.toToposHom.adj
      (Z := ⊤_ Sheaf (SmallEtale.topology B S hS A.1) (Type u))
      (ι := {W : SmallEtale B S hS A.1 // IsAffine (chartSch W)}) (fun W ↦ W.1)
      (fun W ↦ (Functor.uniqueTerminalObj (P := Sheaf.sectionsFunctor.{u}
          (SmallEtale.topology B S hS A.1) (op W.1))).default)
      (fun W' z ↦ by
        refine ⟨_, generate_ofArrows_affineOpens_mem_topology W', fun W'' i hi ↦ ?_⟩
        obtain ⟨_, φ, _, ⟨O⟩, rfl⟩ := hi
        exact ⟨⟨chartOpenRestriction B S hS A.1 W' O.1, O.2⟩, φ, (hsub W'').elim _ _⟩)
      (Functor.uniqueTerminalObj (P := pQs.toToposHom.inverseImage ⋙
        Sheaf.sectionsFunctor (SmallEtale.topology B S hS Q.1) (op V))).default
    refine GrothendieckTopology.transitive _ hT R fun V' i hi ↦ ?_
    obtain ⟨⟨W, hW⟩, σ, -⟩ := hTs i hi
    refine GrothendieckTopology.superset_covering _ ?_
      (generate_ofArrows_affineOpens_mem_topology V')
    rintro V''' _ ⟨_, g', _, ⟨O⟩, rfl⟩
    exact ⟨chartOpenRestriction B S hS Q.1 V' O.1, g',
      chartOpenRestrictionHom B S hS Q.1 V' O.1 ≫ i,
      ⟨O.2, W, hW, ⟨(invRep pQs W).obj.map (chartOpenRestrictionHom B S hS Q.1 V' O.1).op σ⟩⟩,
      (Category.assoc _ _ _).symm⟩
  obtain ⟨T, hT, hTs⟩ := Sheaf.exists_covering_lift_of_adjunction ψ.toToposHom.adj hRmem s
  refine SmallEtale.eq_of_mem_topology hT fun U' i hi ↦ ?_
  obtain ⟨V'', _, ⟨V₀, k, j₀, ⟨hV₀, W, hW, ⟨σ⟩⟩, rfl⟩, s', hs'⟩ := hTs i hi
  let s'' := (ψ.toToposHom.inverseImage.map
    ((SmallEtale.topology B S hS Q.1).yoneda.map k)).hom.app (op U') s'
  have hs'' : (ψ.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Q.1).yoneda.map j₀)).hom.app (op U') s'' =
      (invRep ψ V).obj.map i.op s := by
    rw [← hs', Functor.map_comp, Functor.map_comp]
    rfl
  rw [← Category.assoc, ← chartSchemeHom_restrict, ← hs'', chartSchemeHom_map, Category.assoc,
    toScheme_map_comp_inclusion_map, toScheme_map_comp_inclusion_map]
  exact chartSchemeHom_comp_inclusion_map_of_section pP pQ ψ t V₀ W σ U' s''

end TwoCompatible

end AlgebraicGeometry.Space
