module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramCommonRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroScheme
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsDerivation
public import StacksFrontier.RingTheory.Unramified.ThickeningDerivationExtension

/-!
# Extending derivations across a universal first-order thickening of algebraic spaces

Let `h' : Z' ⟶ X` be a morphism of algebraic spaces over `S`, let `Z ⊆ Z'` be a closed subspace
and let `G` be an `𝒪_{Z'}`-module killed by the ideal of `Z`.  Suppose that on every commutative
square `d` of affine étale scheme charts over `h'` — a chart `U` of `Z'`, a chart `V` of `X` and a
morphism of schemes `U ⟶ V` over `h'` — the ring map `Γ(V) → Γ(U)` exhibits `Γ(U)` as the
universal first-order thickening of `Γ(U)/I(U)` over `Γ(V)`, where `I(U)` is the ideal of `Z` on
`U`.  Then restriction along the structure map `(h')^♯ : 𝒪_X ⟶ h'_*𝒪_{Z'}` is a bijection from
the derivations of `𝒪_{Z'}` with values in `G` onto the derivations of `𝒪_X` with values in
`h'_*G`, and the same holds for derivations relative to a base `p : X ⟶ Y`.

This is the derivation form of Stacks 060E.  Injectivity is the uniqueness half of the
ring-level universal property, `RingHom.IsUniversalFirstOrderThickening.leibniz_ext`, applied on
the squares of charts, which cover `Z'`.  For surjectivity a derivation `D` of `𝒪_X` is projected
to each affine square (`AlgebraicGeometry.Space.chartDiagramProjectedDerivation`), extended there
along `Γ(V) → Γ(U)` by `RingHom.IsUniversalFirstOrderThickening.existsUnique_leibniz`, and the
extensions are glued: uniqueness makes the extensions over two squares agree on a common
refinement, and the affine squares cover every chart of `Z'`.

## Main definitions

* `AlgebraicGeometry.Space.chartDiagramProjectedDerivation`: a derivation of `𝒪_X` with values
  in `h'_*G`, read on a square of charts.
* `AlgebraicGeometry.Space.thickeningChartExtension`: its extension over an affine square.
* `AlgebraicGeometry.Space.thickeningLiftDerivation` and
  `AlgebraicGeometry.Space.thickeningLiftDerivationRelative`: the glued extension, as an absolute
  derivation and as a `Y`-derivation of `𝒪_{Z'}` with values in `G`.

## Main results

* `AlgebraicGeometry.Space.thickeningLiftValue_chartDiagramFunctionMap`: the glued extension
  restricts to `D` on every square of charts.
* `AlgebraicGeometry.Space.injective_pushforwardUniversalDerivation_postcomp` and
  `AlgebraicGeometry.Space.surjective_pushforwardUniversalDerivation_postcomp`: restriction of
  `Y`-derivations along `(h')^♯` is bijective.

## Implementation notes

The chartwise universal property is a hypothesis of this file.  For a universal first-order
thickening of algebraic spaces it is proved in
`AlgebraicGeometry.Space.isUniversalFirstOrderThickening_chartDiagramFunctionMap`, through the
étale localization of Stacks 060D.

## References

* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 04EF](https://stacks.math.columbia.edu/tag/04EF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Z' : AlgebraicSpaces B S hS} (h' : Z' ⟶ X) (G : Modules.{u, u} B S hS Z'.1 Z'.2)

/-- The ring of regular functions of an étale chart, as a commutative ring. -/
noncomputable abbrev chartFunctionRing {F : AlgebraicSpaces B S hS} (U : SmallEtale B S hS F.1) :
    CommRingCat.{u} :=
  (smallEtaleRingedSite B S hS F.1 F.2).O.obj.obj (op U)

/-- The pullback of regular functions along the vertical morphism of a square of charts. -/
noncomputable abbrev chartDiagramFunctionMap (d : ChartDiagram B S hS Z'.1 X.1 h'.hom) :
    chartFunctionRing B S hS d.V →+* chartFunctionRing B S hS d.U :=
  (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op).hom

section PointwiseCover

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A family of arrows into an étale chart which hits every point of it generates a covering
sieve. -/
theorem generate_mem_topology_of_pointwise (T : SmallEtale B S hS F)
    (P : Presieve T)
    (hP : ∀ z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T),
      ∃ (T' : SmallEtale B S hS F) (a : T' ⟶ T), P a ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T'),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map a) z' = z) :
    Sieve.generate P ∈ SmallEtale.topology B S hS F T := by
  refine smallEtale_sieve_of_pointwise_covering B S hS F T _ fun z => ?_
  obtain ⟨T', a, ha, z', hz'⟩ := hP z
  exact ⟨T', a, Sieve.le_generate P T' a ha, z', hz'⟩

/-- **Sections of a sheaf of sets agreeing along a pointwise covering family are equal.** -/
theorem sheaf_ext_of_pointwise (E : Sheaf (SmallEtale.topology B S hS F) (Type u))
    (T : SmallEtale B S hS F) (P : Presieve T)
    (hP : ∀ z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T),
      ∃ (T' : SmallEtale B S hS F) (a : T' ⟶ T), P a ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T'),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map a) z' = z)
    {s t : E.obj.obj (op T)}
    (h : ∀ ⦃T' : SmallEtale B S hS F⦄ (a : T' ⟶ T), P a → E.obj.map a.op s = E.obj.map a.op t) :
    s = t := by
  have hS' := (isSheaf_iff_isSheaf_of_type _ _).1 E.property _
    (generate_mem_topology_of_pointwise B S hS T P hP)
  rw [← Presieve.isSheafFor_iff_generate] at hS'
  exact hS'.isSeparatedFor.ext fun T' a ha => h a ha

/-- **A compatible family of sections along a pointwise covering family glues.** -/
theorem sheaf_exists_of_pointwise (E : Sheaf (SmallEtale.topology B S hS F) (Type u))
    (T : SmallEtale B S hS F) (P : Presieve T)
    (hP : ∀ z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T),
      ∃ (T' : SmallEtale B S hS F) (a : T' ⟶ T), P a ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj T'),
          (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map a) z' = z)
    (x : Presieve.FamilyOfElements E.obj P) (hx : x.Compatible) :
    ∃ s : E.obj.obj (op T), ∀ ⦃T' : SmallEtale B S hS F⦄ (a : T' ⟶ T) (ha : P a),
      E.obj.map a.op s = x a ha := by
  have hS' := (isSheaf_iff_isSheaf_of_type _ _).1 E.property _
    (generate_mem_topology_of_pointwise B S hS T P hP)
  rw [← Presieve.isSheafFor_iff_generate] at hS'
  exact ⟨hS'.amalgamate x hx, fun T' a ha => hS'.valid_glue hx a ha⟩

end PointwiseCover

/-- **Affine squares dominating two squares exist locally.**  Let `d₁`, `d₂` be squares of
charts over `h'` whose charts of `Z'` receive a chart `T`.  Above every point of `T` there is an
affine chart `T₃ ⟶ T` carrying a square with affine chart `V₃` of `X` mapping to the charts of
`X` of `d₁` and `d₂`, compatibly with the vertical morphisms. -/
theorem exists_affine_dominating_chartDiagram (d₁ d₂ : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    {T : SmallEtale B S hS Z'.1} (k₁ : T ⟶ d₁.U) (k₂ : T ⟶ d₂.U)
    (z : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Z'.1).obj T)) :
    ∃ (T₃ : SmallEtale B S hS Z'.1) (a : T₃ ⟶ T) (V₃ : SmallEtale B S hS X.1)
      (g₃ : (SmallEtale.toOver B S hS Z'.1).obj T₃ ⟶ (SmallEtale.toOver B S hS X.1).obj V₃)
      (_ : T₃.1.hom ≫ h'.hom = yoneda.map g₃ ≫ V₃.1.hom) (m₁ : V₃ ⟶ d₁.V) (m₂ : V₃ ⟶ d₂.V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₃.1.left) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₃.1.left) ∧
      (SmallEtale.toOver B S hS Z'.1).map (a ≫ k₁) ≫ d₁.g =
        g₃ ≫ (SmallEtale.toOver B S hS X.1).map m₁ ∧
      (SmallEtale.toOver B S hS Z'.1).map (a ≫ k₂) ≫ d₂.g =
        g₃ ≫ (SmallEtale.toOver B S hS X.1).map m₂ ∧
      ∃ z' : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Z'.1).obj T₃),
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z'.1).map a) z' = z := by
  obtain ⟨W, g, hc, p, q, hp, hq⟩ := exists_dominating_chart B S hS h' d₁ d₂ k₁ k₂
  obtain ⟨W₀, ι, hW₀, w₀, hw₀⟩ := exists_affine_chart_at B S hS X.1 W
    ((BigFppfOver.toScheme B S hS).map g z)
  obtain ⟨T', π, p', hp', hcomm, w', hw'1, -⟩ :=
    exists_chart_pullback B S hS h' T g hc.symm ι z w₀ hw₀.symm
  obtain ⟨T₃, ι₃, hT₃, z₃, hz₃⟩ := exists_affine_chart_at B S hS Z'.1 T' w'
  have hT₃w : yoneda.map ((SmallEtale.toOver B S hS Z'.1).map ι₃) ≫ T'.1.hom = T₃.1.hom :=
    CostructuredArrow.w ι₃.hom
  refine ⟨T₃, ι₃ ≫ π, W₀, (SmallEtale.toOver B S hS Z'.1).map ι₃ ≫ p', ?_, ι ≫ p, ι ≫ q,
    hT₃, hW₀, ?_, ?_, z₃, ?_⟩
  · rw [← hT₃w, Category.assoc, ← hp', Functor.map_comp, Category.assoc]
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hp,
      ← Category.assoc ((SmallEtale.toOver B S hS Z'.1).map π), ← hcomm, Functor.map_comp]
    simp only [Category.assoc]
  · rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hq,
      ← Category.assoc ((SmallEtale.toOver B S hS Z'.1).map π), ← hcomm, Functor.map_comp]
    simp only [Category.assoc]
  · rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hz₃, hw'1]

/-- Sections of `G` over the chart of a square, agreeing on every affine chart dominating two
squares, are equal. -/
private theorem section_ext_of_dominating (d₁ d₂ : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (i : d₂.U ⟶ d₁.U) {s t : G.val.obj (op d₂.U)}
    (h : ∀ (T₃ : SmallEtale B S hS Z'.1) (a : T₃ ⟶ d₂.U) (V₃ : SmallEtale B S hS X.1)
      (g₃ : (SmallEtale.toOver B S hS Z'.1).obj T₃ ⟶ (SmallEtale.toOver B S hS X.1).obj V₃)
      (_ : T₃.1.hom ≫ h'.hom = yoneda.map g₃ ≫ V₃.1.hom) (m₁ : V₃ ⟶ d₁.V) (m₂ : V₃ ⟶ d₂.V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₃.1.left) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₃.1.left) →
      (SmallEtale.toOver B S hS Z'.1).map (a ≫ i) ≫ d₁.g =
        g₃ ≫ (SmallEtale.toOver B S hS X.1).map m₁ →
      (SmallEtale.toOver B S hS Z'.1).map a ≫ d₂.g =
        g₃ ≫ (SmallEtale.toOver B S hS X.1).map m₂ →
      G.val.map a.op s = G.val.map a.op t) : s = t := by
  refine sheaf_ext_of_pointwise B S hS
    (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Z') G) d₂.U
    (fun T₃ a => ∃ (V₃ : SmallEtale B S hS X.1)
      (g₃ : (SmallEtale.toOver B S hS Z'.1).obj T₃ ⟶ (SmallEtale.toOver B S hS X.1).obj V₃)
      (_ : T₃.1.hom ≫ h'.hom = yoneda.map g₃ ≫ V₃.1.hom) (m₁ : V₃ ⟶ d₁.V) (m₂ : V₃ ⟶ d₂.V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T₃.1.left) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₃.1.left) ∧
      (SmallEtale.toOver B S hS Z'.1).map (a ≫ i) ≫ d₁.g =
        g₃ ≫ (SmallEtale.toOver B S hS X.1).map m₁ ∧
      (SmallEtale.toOver B S hS Z'.1).map a ≫ d₂.g =
        g₃ ≫ (SmallEtale.toOver B S hS X.1).map m₂)
    (fun z => ?_) fun T₃ a ⟨V₃, g₃, hc, m₁, m₂, hT, hV, h₁, h₂⟩ =>
      h T₃ a V₃ g₃ hc m₁ m₂ hT hV h₁ h₂
  obtain ⟨T₃, a, V₃, g₃, hc, m₁, m₂, hT, hV, h₁, h₂, z', hz⟩ :=
    exists_affine_dominating_chartDiagram B S hS h' d₁ d₂ i (𝟙 _) z
  rw [Category.comp_id] at h₂
  exact ⟨T₃, a, ⟨V₃, g₃, hc, m₁, m₂, hT, hV, h₁, h₂⟩, z', hz⟩

section Projection

variable {R : (SmallEtale B S hS X.1)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (smallEtaleRingedSite B S hS X.1 X.2).O.obj}
  (D : ((modulePushforward B S hS h').obj G).val.Derivation' ψ)

/-- A derivation of `𝒪_X` with values in `h'_*G`, projected to a square `d` of charts: an additive
map from the regular functions on the chart of `X` to the sections of `G` over the chart of `Z'`,
satisfying the Leibniz rule through the pullback along the square. -/
noncomputable def chartDiagramProjectedDerivation (d : ChartDiagram B S hS Z'.1 X.1 h'.hom) :
    chartFunctionRing B S hS d.V →+ G.val.obj (op d.U) :=
  (chartDiagramProjection B S hS h' G d).comp D.d

/-- The projected derivation satisfies the Leibniz rule for the action of a regular function on
`V` through its pullback to `U`. -/
theorem chartDiagramProjectedDerivation_mul (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (a b : chartFunctionRing B S hS d.V) :
    chartDiagramProjectedDerivation B S hS h' G D d (a * b) =
      chartDiagramFunctionMap B S hS h' d a • chartDiagramProjectedDerivation B S hS h' G D d b +
        chartDiagramFunctionMap B S hS h' d b • chartDiagramProjectedDerivation B S hS h' G D d a
            := by
  show chartDiagramProjection B S hS h' G d (D.d (a * b)) = _
  rw [D.d_mul, map_add]
  exact congrArg₂ (· + ·) (chartDiagramProjection_smul B S hS h' G d a (D.d b))
    (chartDiagramProjection_smul B S hS h' G d b (D.d a))

end Projection

/-- Restriction of regular functions along a morphism of étale charts. -/
noncomputable abbrev chartFunctionRestrict {F : AlgebraicSpaces B S hS} {U U' : SmallEtale B S hS
    F.1}
    (i : U' ⟶ U) : chartFunctionRing B S hS U →+* chartFunctionRing B S hS U' :=
  ((smallEtaleRingedSite B S hS F.1 F.2).O.obj.map i.op).hom

/-- The pullbacks of regular functions along a morphism of squares of charts commute with
restriction. -/
theorem chartDiagramFunctionMap_comp_chartFunctionRestrict (d d' : ChartDiagram B S hS Z'.1 X.1
    h'.hom)
    (i : d'.U ⟶ d.U) (m : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS Z'.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS X.1).map m) (a : chartFunctionRing B S hS d.V) :
    chartFunctionRestrict B S hS i (chartDiagramFunctionMap B S hS h' d a) =
      chartDiagramFunctionMap B S hS h' d' (chartFunctionRestrict B S hS m a) := by
  have hc := congrArg (fun k => (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom a) h
  simp only [Functor.map_comp, op_comp, CommRingCat.hom_comp] at hc
  exact hc

section Restriction

variable {Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)

/-- **The restriction of a derivation along `h'`, projected to a square.**  For a morphism
`x : Ω_{Z'/Y} ⟶ G`, the `Y`-derivation `h'_*x ∘ (h'_*d_{Z'/Y} ∘ h'^♯)` of `𝒪_X`, projected to a
square `d` of charts, is `x ∘ d_{Z'/Y}` applied to the pullback along `d`. -/
theorem chartDiagramProjectedDerivation_pushforwardUniversalDerivation_postcomp
    (x : sheafOfDifferentials B S hS (h' ≫ p) ⟶ G)
    (d : ChartDiagram B S hS Z'.1 X.1 h'.hom) (a : chartFunctionRing B S hS d.V) :
    chartDiagramProjectedDerivation B S hS h' G ((pushforwardUniversalDerivation B S hS h' p (h' ≫
        p) (𝟙 Y)
        (Category.comp_id (h' ≫ p)).symm).postcomp ((modulePushforward B S hS h').map x).val) d a =
      (x.val.app (op d.U)).hom ((universalDerivation B S hS (h' ≫ p)).d
        (chartDiagramFunctionMap B S hS h' d a)) := by
  have e1 : ((pushforwardUniversalDerivation B S hS h' p (h' ≫ p) (𝟙 Y)
        (Category.comp_id (h' ≫ p)).symm).postcomp ((modulePushforward B S hS h').map x).val).d a =
      (smallEtaleDirectImageSections B S hS h' (op d.V)).map
        ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z')).map x)
        ((smallEtaleDirectImageSections B S hS h' (op d.V)).map
          (universalDerivationHom B S hS (h' ≫ p))
          ((structureSharpSet B S hS h').hom.app (op d.V) a)) := rfl
  have e2 := chartDiagramProjectionNat_map B S hS h' d
    ((CategoryTheory.Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Z')).map x)
    ((smallEtaleDirectImageSections B S hS h' (op d.V)).map
      (universalDerivationHom B S hS (h' ≫ p))
      ((structureSharpSet B S hS h').hom.app (op d.V) a))
  have e3 := chartDiagramProjectionNat_map B S hS h' d (universalDerivationHom B S hS (h' ≫ p))
    ((structureSharpSet B S hS h').hom.app (op d.V) a)
  have e4 := chartDiagramProjectionNat_structureSharpSet B S hS h' d a
  have e5 := (congrArg (chartDiagramProjection B S hS h' G d) e1).trans
    (e2.trans (congrArg _ (e3.trans (congrArg _ e4))))
  exact e5

end Restriction

/-- Restriction of regular functions along a composite of chart morphisms. -/
theorem chartFunctionRestrict_comp {F : AlgebraicSpaces B S hS} {U₁ U₂ U₃ : SmallEtale B S hS F.1}
    (a : U₃ ⟶ U₂) (i : U₂ ⟶ U₁) (x : chartFunctionRing B S hS U₁) :
    chartFunctionRestrict B S hS (a ≫ i) x = chartFunctionRestrict B S hS a (chartFunctionRestrict
        B S hS i x) :=
  congrArg (fun f => f.hom x) ((smallEtaleRingedSite B S hS F.1 F.2).O.obj.map_comp i.op a.op)

/-- The square of charts carried by a chart of `Z'` with an affine chart diagram over `h'`. -/
noncomputable def HasAffineChartDiagram.chartDiagram {W : SmallEtale B S hS Z'.1}
    (hW : HasAffineChartDiagram B S hS h' W) : ChartDiagram B S hS Z'.1 X.1 h'.hom :=
  ⟨W, hW.2.choose, hW.2.choose_spec.choose, hW.2.choose_spec.choose_spec.1.symm⟩

/-- The target chart of the square chosen by `AlgebraicGeometry.Space.HasAffineChartDiagram` is
affine. -/
theorem HasAffineChartDiagram.isAffine_V {W : SmallEtale B S hS Z'.1}
    (hW : HasAffineChartDiagram B S hS h' W) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (hW.chartDiagram B S hS h').V.1.left) :=
  hW.2.choose_spec.choose_spec.2

/-- A chart of `Z'` which carries an affine square has an affine chart diagram. -/
theorem ChartDiagram.hasAffineChartDiagram (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left)) :
    HasAffineChartDiagram B S hS h' d.U :=
  ⟨hU, d.V, d.g, d.comm.symm, hV⟩

section Extension

variable (Zcl : ClosedSubspaces B S hS Z'.1)
  (hG : ∀ (U : SmallEtale B S hS Z'.1) (x : chartFunctionRing B S hS U),
    x ∈ definingIdealAt B S hS Z' Zcl (op U) → ∀ m : G.val.obj (op U), x • m = 0)
  (hKL : ∀ d : ChartDiagram B S hS Z'.1 X.1 h'.hom,
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) →
    (chartDiagramFunctionMap B S hS h' d).IsUniversalFirstOrderThickening
      (definingIdealAt B S hS Z' Zcl (op d.U)))
  {R : (SmallEtale B S hS X.1)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (smallEtaleRingedSite B S hS X.1 X.2).O.obj}
  (D : ((modulePushforward B S hS h').obj G).val.Derivation' ψ)

include hG hKL in
/-- **The chartwise extension.**  Over an affine square of charts the projected derivation extends
uniquely along the universal first-order thickening of rings `Γ(V) → Γ(U)` to a Leibniz map out
of `Γ(U)`. -/
theorem existsUnique_chartDiagramExtension (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left)) :
    ∃! E : chartFunctionRing B S hS d.U →+ G.val.obj (op d.U), (∀ x y, E (x * y) = x • E y + y • E
        x) ∧
      ∀ a, E (chartDiagramFunctionMap B S hS h' d a) = chartDiagramProjectedDerivation B S hS h' G
          D d a :=
  (hKL d hU hV).existsUnique_leibniz (hG d.U) _
    (chartDiagramProjectedDerivation_mul B S hS h' G D d)

/-- **The extension of a projected derivation across the universal first-order thickening over
an affine square of charts**: the unique derivation of the regular functions on the chart of
`Z'` with values in `G` restricting, along the square, to the projection of `D`. -/
noncomputable def thickeningChartExtension (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left)) :
    chartFunctionRing B S hS d.U →+ G.val.obj (op d.U) :=
  (existsUnique_chartDiagramExtension B S hS h' G Zcl hG hKL D d hU hV).exists.choose

/-- The chartwise extension satisfies the Leibniz rule. -/
theorem thickeningChartExtension_mul (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left))
    (x y : chartFunctionRing B S hS d.U) :
    thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV (x * y) =
      x • thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV y +
        y • thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV x :=
  (existsUnique_chartDiagramExtension B S hS h' G Zcl hG hKL D d hU hV).exists.choose_spec.1 x y

/-- The chartwise extension restricts to the projected derivation along `Γ(V) → Γ(U)`. -/
theorem thickeningChartExtension_chartDiagramFunctionMap (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left))
    (a : chartFunctionRing B S hS d.V) :
    thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV (chartDiagramFunctionMap B S hS h' d
        a) =
      chartDiagramProjectedDerivation B S hS h' G D d a :=
  (existsUnique_chartDiagramExtension B S hS h' G Zcl hG hKL D d hU hV).exists.choose_spec.2 a

/-- The projected derivation is compatible with a morphism of squares of charts. -/
theorem chartDiagramProjectedDerivation_naturality (d d' : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (i : d'.U ⟶ d.U) (m : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS Z'.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS X.1).map m) (a : chartFunctionRing B S hS d.V) :
    G.val.map i.op (chartDiagramProjectedDerivation B S hS h' G D d a) =
      chartDiagramProjectedDerivation B S hS h' G D d' (chartFunctionRestrict B S hS m a) := by
  show G.val.map i.op (chartDiagramProjection B S hS h' G d (D.d a)) =
    chartDiagramProjection B S hS h' G d' (D.d (chartFunctionRestrict B S hS m a))
  rw [← chartDiagramProjection_naturality B S hS h' G d d' i m h]
  exact congrArg (chartDiagramProjection B S hS h' G d') (D.d_map m.op a).symm

/-- **The extensions over two affine squares are compatible with a morphism of squares.** -/
theorem thickeningChartExtension_naturality (d d' : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left))
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj d'.U.1.left))
    (hV' : IsAffine ((BigFppfOver.toScheme B S hS).obj d'.V.1.left))
    (i : d'.U ⟶ d.U) (m : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS Z'.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS X.1).map m) (x : chartFunctionRing B S hS d.U) :
    G.val.map i.op (thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV x) =
      thickeningChartExtension B S hS h' G Zcl hG hKL D d' hU' hV' (chartFunctionRestrict B S hS i
          x) := by
  let : Module (chartFunctionRing B S hS d.U) (G.val.obj (op d'.U)) :=
    Module.compHom _ (chartFunctionRestrict B S hS i)
  let d₁ : chartFunctionRing B S hS d.U →+ G.val.obj (op d'.U) :=
    (G.val.map i.op).hom.toAddMonoidHom.comp (thickeningChartExtension B S hS h' G Zcl hG hKL D d
        hU hV)
  let d₂ : chartFunctionRing B S hS d.U →+ G.val.obj (op d'.U) :=
    (thickeningChartExtension B S hS h' G Zcl hG hKL D d' hU' hV').comp
      (chartFunctionRestrict B S hS i).toAddMonoidHom
  have key : d₁ = d₂ := by
    refine (hKL d hU hV).leibniz_ext d₁ d₂ ?_ ?_ ?_
    · intro x y
      show G.val.map i.op (thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV (x * y)) = _
      rw [thickeningChartExtension_mul]
      exact ((G.val.map i.op).hom.map_add _ _).trans (congrArg₂ (· + ·)
        (G.val.map_smul i.op x _) (G.val.map_smul i.op y _))
    · intro x y
      show thickeningChartExtension B S hS h' G Zcl hG hKL D d' hU' hV'
        (chartFunctionRestrict B S hS i (x * y)) = _
      rw [map_mul, thickeningChartExtension_mul]
      rfl
    · intro a
      show G.val.map i.op (thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV
          (chartDiagramFunctionMap B S hS h' d a)) =
        thickeningChartExtension B S hS h' G Zcl hG hKL D d' hU' hV'
          (chartFunctionRestrict B S hS i (chartDiagramFunctionMap B S hS h' d a))
      rw [thickeningChartExtension_chartDiagramFunctionMap,
        chartDiagramProjectedDerivation_naturality B S hS h' G D d d' i m h,
        chartDiagramFunctionMap_comp_chartFunctionRestrict B S hS h' d d' i m h,
        thickeningChartExtension_chartDiagramFunctionMap]
  exact congrArg (fun f => f x) key

/-- **The extensions over two affine squares agree after restriction**, with no compatibility
asked of the charts of `X`: over every affine chart `T₃` dominating both squares the two
restrictions are the extension over the dominating square. -/
theorem thickeningChartExtension_restrict (d₁ d₂ : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj d₁.U.1.left))
    (hV₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj d₁.V.1.left))
    (hU₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj d₂.U.1.left))
    (hV₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj d₂.V.1.left))
    (i : d₂.U ⟶ d₁.U) (x : chartFunctionRing B S hS d₁.U) :
    G.val.map i.op (thickeningChartExtension B S hS h' G Zcl hG hKL D d₁ hU₁ hV₁ x) =
      thickeningChartExtension B S hS h' G Zcl hG hKL D d₂ hU₂ hV₂ (chartFunctionRestrict B S hS i
          x) := by
  refine section_ext_of_dominating B S hS h' G d₁ d₂ i ?_
  intro T₃ a V₃ g₃ hc m₁ m₂ hT hV h₁ h₂
  let d₃ : ChartDiagram B S hS Z'.1 X.1 h'.hom := ⟨T₃, V₃, g₃, hc⟩
  have e₁ := thickeningChartExtension_naturality B S hS h' G Zcl hG hKL D d₁ d₃ hU₁ hV₁ hT hV
    (a ≫ i) m₁ h₁ x
  have e₂ := thickeningChartExtension_naturality B S hS h' G Zcl hG hKL D d₂ d₃ hU₂ hV₂ hT hV
    a m₂ h₂ (chartFunctionRestrict B S hS i x)
  exact (G.val.map_comp_apply i.op a.op _).symm.trans
    (e₁.trans ((congrArg _ (chartFunctionRestrict_comp B S hS a i x)).trans e₂.symm))

/-- The family of extensions over the charts of a chart `T` of `Z'` which carry affine chart
diagrams. -/
noncomputable def thickeningLiftFamily (T : SmallEtale B S hS Z'.1) (s : chartFunctionRing B S hS
    T) :
    Presieve.FamilyOfElements
      (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Z') G).obj
      (fun T' (_ : T' ⟶ T) => HasAffineChartDiagram B S hS h' T') :=
  fun _ a ha => thickeningChartExtension B S hS h' G Zcl hG hKL D (ha.chartDiagram B S hS h') ha.1
    (ha.isAffine_V B S hS h') (chartFunctionRestrict B S hS a s)

/-- The chartwise extensions of a regular function on `T` are compatible on overlaps. -/
theorem thickeningLiftFamily_compatible (T : SmallEtale B S hS Z'.1) (s : chartFunctionRing B S hS
    T) :
    (thickeningLiftFamily B S hS h' G Zcl hG hKL D T s).Compatible := by
  intro Y₁ Y₂ W g₁ g₂ f₁ f₂ h₁ h₂ hw
  refine sheaf_ext_of_pointwise B S hS
    (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Z') G) W
    (fun T₃ _ => HasAffineChartDiagram B S hS h' T₃) (fun z => ?_) (fun T₃ c hc => ?_)
  · exact exists_hasAffineChartDiagram B S hS h' W z
  · have e₁ := thickeningChartExtension_restrict B S hS h' G Zcl hG hKL D
      (h₁.chartDiagram B S hS h') (hc.chartDiagram B S hS h') h₁.1 (h₁.isAffine_V B S hS h')
      hc.1 (hc.isAffine_V B S hS h') (c ≫ g₁) (chartFunctionRestrict B S hS f₁ s)
    have e₂ := thickeningChartExtension_restrict B S hS h' G Zcl hG hKL D
      (h₂.chartDiagram B S hS h') (hc.chartDiagram B S hS h') h₂.1 (h₂.isAffine_V B S hS h')
      hc.1 (hc.isAffine_V B S hS h') (c ≫ g₂) (chartFunctionRestrict B S hS f₂ s)
    have r₁ : chartFunctionRestrict B S hS (c ≫ g₁) (chartFunctionRestrict B S hS f₁ s) =
        chartFunctionRestrict B S hS (c ≫ g₂) (chartFunctionRestrict B S hS f₂ s) := by
      rw [← chartFunctionRestrict_comp, ← chartFunctionRestrict_comp, Category.assoc,
          Category.assoc, hw]
    show G.val.map c.op (G.val.map g₁.op (thickeningLiftFamily B S hS h' G Zcl hG hKL D T s f₁
        h₁)) =
      G.val.map c.op (G.val.map g₂.op (thickeningLiftFamily B S hS h' G Zcl hG hKL D T s f₂ h₂))
    exact (G.val.map_comp_apply g₁.op c.op _).symm.trans
      (e₁.trans ((congrArg _ r₁).trans (e₂.symm.trans (G.val.map_comp_apply g₂.op c.op _))))

/-- The compatible family of chartwise extensions glues to a section of `G` over `T`. -/
theorem exists_thickeningLiftValue (T : SmallEtale B S hS Z'.1) (s : chartFunctionRing B S hS T) :
    ∃ v : G.val.obj (op T), ∀ ⦃T' : SmallEtale B S hS Z'.1⦄ (a : T' ⟶ T)
      (ha : HasAffineChartDiagram B S hS h' T'),
      G.val.map a.op v = thickeningLiftFamily B S hS h' G Zcl hG hKL D T s a ha :=
  sheaf_exists_of_pointwise B S hS
    (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Z') G) T _
    (fun z => exists_hasAffineChartDiagram B S hS h' T z) _
    (thickeningLiftFamily_compatible B S hS h' G Zcl hG hKL D T s)

/-- **The extended derivation**, on the sections over a chart of `Z'`: glued from the extensions
over the charts carrying affine squares. -/
noncomputable def thickeningLiftValue (T : SmallEtale B S hS Z'.1) (s : chartFunctionRing B S hS T)
    :
    G.val.obj (op T) :=
  (exists_thickeningLiftValue B S hS h' G Zcl hG hKL D T s).choose

/-- **The characterizing property of the extended derivation**: restricted to the chart of any
affine square over `h'`, it is the extension over that square. -/
theorem thickeningLiftValue_restrict (T : SmallEtale B S hS Z'.1) (s : chartFunctionRing B S hS T)
    (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left)) (a : d.U ⟶ T) :
    G.val.map a.op (thickeningLiftValue B S hS h' G Zcl hG hKL D T s) =
      thickeningChartExtension B S hS h' G Zcl hG hKL D d hU hV (chartFunctionRestrict B S hS a s)
          := by
  have ha := d.hasAffineChartDiagram B S hS h' hU hV
  refine ((exists_thickeningLiftValue B S hS h' G Zcl hG hKL D T s).choose_spec a ha).trans ?_
  have e := thickeningChartExtension_restrict B S hS h' G Zcl hG hKL D (ha.chartDiagram B S hS h') d
    ha.1 (ha.isAffine_V B S hS h') hU hV (𝟙 _) (chartFunctionRestrict B S hS a s)
  have h1 : ∀ m : G.val.obj (op d.U), G.val.map (𝟙 d.U).op m = m := fun m =>
    congrArg (fun f => f.hom m) (G.val.presheaf.map_id (op d.U))
  have h2 : chartFunctionRestrict B S hS (𝟙 d.U) (chartFunctionRestrict B S hS a s) =
      chartFunctionRestrict B S hS a s :=
    congrArg (fun f => f.hom (chartFunctionRestrict B S hS a s))
      ((smallEtaleRingedSite B S hS Z'.1 Z'.2).O.obj.map_id _)
  exact (h1 _).symm.trans (e.trans (congrArg _ h2))

/-- Sections of `G` over a chart of `Z'` agreeing on the charts carrying affine chart diagrams
are equal. -/
theorem sections_eq_of_hasAffineChartDiagram {T : SmallEtale B S hS Z'.1} {v w : G.val.obj (op T)}
    (h : ∀ ⦃T' : SmallEtale B S hS Z'.1⦄ (a : T' ⟶ T), HasAffineChartDiagram B S hS h' T' →
      G.val.map a.op v = G.val.map a.op w) : v = w :=
  sheaf_ext_of_pointwise B S hS
    (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Z') G) T _
    (fun z => exists_hasAffineChartDiagram B S hS h' T z) h

/-- The glued value restricts, over a chart carrying an affine square, to the chartwise extension
along the square chosen there. -/
theorem thickeningLiftValue_restrict' (T : SmallEtale B S hS Z'.1) (s : chartFunctionRing B S hS T)
    {T' : SmallEtale B S hS Z'.1} (a : T' ⟶ T) (ha : HasAffineChartDiagram B S hS h' T') :
    G.val.map a.op (thickeningLiftValue B S hS h' G Zcl hG hKL D T s) =
      thickeningChartExtension B S hS h' G Zcl hG hKL D (ha.chartDiagram B S hS h') ha.1
        (ha.isAffine_V B S hS h') (chartFunctionRestrict B S hS a s) :=
  thickeningLiftValue_restrict B S hS h' G Zcl hG hKL D T s (ha.chartDiagram B S hS h') ha.1
    (ha.isAffine_V B S hS h') a

/-- The glued value is additive in the regular function. -/
theorem thickeningLiftValue_add (T : SmallEtale B S hS Z'.1) (s t : chartFunctionRing B S hS T) :
    thickeningLiftValue B S hS h' G Zcl hG hKL D T (s + t) =
      thickeningLiftValue B S hS h' G Zcl hG hKL D T s + thickeningLiftValue B S hS h' G Zcl hG hKL
          D T t := by
  refine sections_eq_of_hasAffineChartDiagram B S hS h' G fun T' a ha => ?_
  have e₀ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T (s + t) a ha
  have e₁ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T s a ha
  have e₂ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T t a ha
  have h₁ := (chartFunctionRestrict B S hS a).map_add s t
  have h₂ := (thickeningChartExtension B S hS h' G Zcl hG hKL D (ha.chartDiagram B S hS h') ha.1
    (ha.isAffine_V B S hS h')).map_add (chartFunctionRestrict B S hS a s) (chartFunctionRestrict B
        S hS a t)
  have h₃ := (G.val.map a.op).hom.map_add (thickeningLiftValue B S hS h' G Zcl hG hKL D T s)
    (thickeningLiftValue B S hS h' G Zcl hG hKL D T t)
  exact e₀.trans ((congrArg _ h₁).trans (h₂.trans ((congrArg₂ (· + ·) e₁ e₂).symm.trans h₃.symm)))

/-- The glued value satisfies the Leibniz rule. -/
theorem thickeningLiftValue_mul (T : SmallEtale B S hS Z'.1) (s t : chartFunctionRing B S hS T) :
    thickeningLiftValue B S hS h' G Zcl hG hKL D T (s * t) =
      s • thickeningLiftValue B S hS h' G Zcl hG hKL D T t + t • thickeningLiftValue B S hS h' G
          Zcl hG hKL D T s := by
  refine sections_eq_of_hasAffineChartDiagram B S hS h' G fun T' a ha => ?_
  have e₀ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T (s * t) a ha
  have e₁ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T s a ha
  have e₂ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T t a ha
  have h₁ := (chartFunctionRestrict B S hS a).map_mul s t
  have h₂ := thickeningChartExtension_mul B S hS h' G Zcl hG hKL D (ha.chartDiagram B S hS h') ha.1
    (ha.isAffine_V B S hS h') (chartFunctionRestrict B S hS a s) (chartFunctionRestrict B S hS a t)
  have h₃ := (G.val.map a.op).hom.map_add (s • thickeningLiftValue B S hS h' G Zcl hG hKL D T t)
    (t • thickeningLiftValue B S hS h' G Zcl hG hKL D T s)
  have h₄ := G.val.map_smul a.op s (thickeningLiftValue B S hS h' G Zcl hG hKL D T t)
  have h₅ := G.val.map_smul a.op t (thickeningLiftValue B S hS h' G Zcl hG hKL D T s)
  refine e₀.trans ((congrArg _ h₁).trans (h₂.trans (Eq.trans ?_ h₃.symm)))
  refine Eq.trans ?_ (congrArg₂ (· + ·) h₄.symm h₅.symm)
  exact congrArg₂ (· + ·)
    (congrArg (fun m : G.val.obj (op T') => chartFunctionRestrict B S hS a s • m) e₂.symm)
    (congrArg (fun m : G.val.obj (op T') => chartFunctionRestrict B S hS a t • m) e₁.symm)

/-- The glued value is natural in the étale chart of `Z'`. -/
theorem thickeningLiftValue_map {T₁ T₂ : SmallEtale B S hS Z'.1} (f : T₂ ⟶ T₁) (s :
    chartFunctionRing B S hS T₁) :
    G.val.map f.op (thickeningLiftValue B S hS h' G Zcl hG hKL D T₁ s) =
      thickeningLiftValue B S hS h' G Zcl hG hKL D T₂ (chartFunctionRestrict B S hS f s) := by
  refine sections_eq_of_hasAffineChartDiagram B S hS h' G (T := T₂) fun T' a ha => ?_
  have e₁ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T₁ s (a ≫ f) ha
  have e₂ := thickeningLiftValue_restrict' B S hS h' G Zcl hG hKL D T₂ (chartFunctionRestrict B S
      hS f s) a ha
  have c := G.val.map_comp_apply f.op a.op (thickeningLiftValue B S hS h' G Zcl hG hKL D T₁ s)
  have r := chartFunctionRestrict_comp B S hS a f s
  exact c.symm.trans (e₁.trans ((congrArg _ r).trans e₂.symm))

/-- **The extended derivation restricts to `D`**, read on every square of charts: on the
pullback of a regular function on the chart of `X` it is the projection of `D`. -/
theorem thickeningLiftValue_chartDiagramFunctionMap (d : ChartDiagram B S hS Z'.1 X.1 h'.hom)
    (a : chartFunctionRing B S hS d.V) :
    thickeningLiftValue B S hS h' G Zcl hG hKL D d.U (chartDiagramFunctionMap B S hS h' d a) =
      chartDiagramProjectedDerivation B S hS h' G D d a := by
  refine section_ext_of_dominating B S hS h' G d d (𝟙 _) ?_
  intro T₃ c V₃ g₃ hc m₁ _ hT hV h₁ _
  rw [Category.comp_id] at h₁
  let d₃ : ChartDiagram B S hS Z'.1 X.1 h'.hom := ⟨T₃, V₃, g₃, hc⟩
  have e₁ := thickeningLiftValue_restrict B S hS h' G Zcl hG hKL D d.U (chartDiagramFunctionMap B
      S hS h' d a)
    d₃ hT hV c
  have r := chartDiagramFunctionMap_comp_chartFunctionRestrict B S hS h' d d₃ c m₁ h₁ a
  have e₂ := thickeningChartExtension_chartDiagramFunctionMap B S hS h' G Zcl hG hKL D d₃ hT hV
    (chartFunctionRestrict B S hS m₁ a)
  have e₃ := chartDiagramProjectedDerivation_naturality B S hS h' G D d d₃ c m₁ h₁ a
  exact e₁.trans ((congrArg _ r).trans (e₂.trans e₃.symm))

/-- **The extended derivation**, as an absolute derivation of `𝒪_{Z'}` with values in `G`. -/
noncomputable def thickeningLiftDerivation :
    G.val.Derivation' (Stacks.Sites.constIntMap (smallEtaleRingedSite B S hS Z'.1 Z'.2).O.obj) where
  d {T} := AddMonoidHom.mk' (thickeningLiftValue B S hS h' G Zcl hG hKL D T.unop)
    (thickeningLiftValue_add B S hS h' G Zcl hG hKL D T.unop)
  d_mul {T} s t := thickeningLiftValue_mul B S hS h' G Zcl hG hKL D T.unop s t
  d_map {T₁ T₂} f s := (thickeningLiftValue_map B S hS h' G Zcl hG hKL D f.unop s).symm
  d_app {T} a := by
    refine Stacks.Sites.constIntMap_app_eq_zero (AddMonoidHom.mk'
      (thickeningLiftValue B S hS h' G Zcl hG hKL D T.unop) (thickeningLiftValue_add B S hS h' G
          Zcl hG hKL D T.unop))
      ?_ a
    have h1 := thickeningLiftValue_mul B S hS h' G Zcl hG hKL D T.unop 1 1
    rw [mul_one, one_smul] at h1
    exact left_eq_add.mp h1

/-- The extended derivation is the glued value, on sections. -/
theorem thickeningLiftDerivation_d (T : SmallEtale B S hS Z'.1) (s : chartFunctionRing B S hS T) :
    (thickeningLiftDerivation B S hS h' G Zcl hG hKL D).d (X := op T) s =
      thickeningLiftValue B S hS h' G Zcl hG hKL D T s := rfl

end Extension

section Relative

variable {Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
  (Zcl : ClosedSubspaces B S hS Z'.1)
  (hG : ∀ (U : SmallEtale B S hS Z'.1) (x : chartFunctionRing B S hS U),
    x ∈ definingIdealAt B S hS Z' Zcl (op U) → ∀ m : G.val.obj (op U), x • m = 0)
  (hKL : ∀ d : ChartDiagram B S hS Z'.1 X.1 h'.hom,
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) →
    (chartDiagramFunctionMap B S hS h' d).IsUniversalFirstOrderThickening
      (definingIdealAt B S hS Z' Zcl (op d.U)))
  (D : ((modulePushforward B S hS h').obj G).val.Derivation' (structureSharpInverseImage B S hS
      p).hom)

/-- The structure map of `h'` followed by the direct image of the extended derivation is `D`. -/
theorem structureSharpSet_comp_map_thickeningLiftDerivation :
    structureSharpSet B S hS h' ≫ (smallEtaleDirectImage B S hS h').map
        (derivationSetHom B S hS (thickeningLiftDerivation B S hS h' G Zcl hG hKL D)) =
      derivationSetHom B S hS D := by
  refine CategoryTheory.Sheaf.hom_ext_sections fun V a => ?_
  refine chartDiagramProjection_ext B S hS h' G V.unop fun U g hc => ?_
  let d : ChartDiagram B S hS Z'.1 X.1 h'.hom := ⟨U, V.unop, g, hc⟩
  have e₁ := chartDiagramProjectionNat_map B S hS h' d
    (derivationSetHom B S hS (thickeningLiftDerivation B S hS h' G Zcl hG hKL D))
    ((structureSharpSet B S hS h').hom.app (op d.V) a)
  have e₂ := chartDiagramProjectionNat_structureSharpSet B S hS h' d a
  have e₃ := thickeningLiftValue_chartDiagramFunctionMap B S hS h' G Zcl hG hKL D d a
  exact e₁.trans ((congrArg _ e₂).trans e₃)

/-- The structure map of `h'` followed by the direct image of the zero derivation is zero. -/
theorem structureSharpSet_comp_map_zeroSetHom :
    structureSharpSet B S hS h' ≫ (smallEtaleDirectImage B S hS h').map (zeroSetHom B S hS G) =
      zeroSetHom B S hS ((modulePushforward B S hS h').obj G) := by
  refine CategoryTheory.Sheaf.hom_ext_sections fun V a => ?_
  refine chartDiagramProjection_ext B S hS h' G V.unop fun U g hc => ?_
  let d : ChartDiagram B S hS Z'.1 X.1 h'.hom := ⟨U, V.unop, g, hc⟩
  have e₁ := chartDiagramProjectionNat_map B S hS h' d (zeroSetHom B S hS G)
    ((structureSharpSet B S hS h').hom.app (op d.V) a)
  exact e₁.trans (chartDiagramProjection B S hS h' G d).map_zero.symm

/-- **The extended derivation is a `Y`-derivation.** -/
theorem structureSharpInverseImageSet_comp_thickeningLiftDerivation :
    structureSharpInverseImageSet B S hS (h' ≫ p) ≫
        derivationSetHom B S hS (thickeningLiftDerivation B S hS h' G Zcl hG hKL D) =
      structureSharpInverseImageSet B S hS (h' ≫ p) ≫ zeroSetHom B S hS G := by
  refine structureSharpInverseImage_of_structureSharpSetComp B S hS (h' ≫ p) _ _ ?_
  have hY : structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (derivationSetHom B S hS D) =
      structureSharpSet B S hS p ≫ (smallEtaleDirectImage B S hS p).map
        (zeroSetHom B S hS ((modulePushforward B S hS h').obj G)) :=
    structureSharpSetComp_of_structureSharpInverseImage B S hS p _ _
      (comp_eq_of_sections (structureSharpInverseImageSet B S hS p) _ _ (fun _ s ↦ D.d_app s))
  have c₁ := structureSharpSet_comp_map B S hS h' p
    (derivationSetHom B S hS (thickeningLiftDerivation B S hS h' G Zcl hG hKL D))
  have c₂ := structureSharpSet_comp_map B S hS h' p (zeroSetHom B S hS G)
  rw [structureSharpSet_comp_map_thickeningLiftDerivation] at c₁
  rw [structureSharpSet_comp_map_zeroSetHom] at c₂
  exact (cancel_mono ((smallToposMorphismTypeU_comp B S hS h' p).inv.app _)).1
    ((Category.assoc _ _ _).trans ((c₁.symm.trans (hY.trans c₂)).trans (Category.assoc _ _ _).symm))

/-- **The extended derivation**, as a `Y`-derivation of `𝒪_{Z'}` with values in `G`. -/
noncomputable def thickeningLiftDerivationRelative :
    G.val.Derivation' (structureSharpInverseImage B S hS (h' ≫ p)).hom where
  d := (thickeningLiftDerivation B S hS h' G Zcl hG hKL D).d
  d_mul := (thickeningLiftDerivation B S hS h' G Zcl hG hKL D).d_mul
  d_map := (thickeningLiftDerivation B S hS h' G Zcl hG hKL D).d_map
  d_app {T} s :=
    congr_sections_comp (structureSharpInverseImageSet B S hS (h' ≫ p))
      (structureSharpInverseImageSet_comp_thickeningLiftDerivation B S hS h' G p Zcl hG hKL D) T s

end Relative

section Main

variable {Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
  (Zcl : ClosedSubspaces B S hS Z'.1)
  (hG : ∀ (U : SmallEtale B S hS Z'.1) (x : chartFunctionRing B S hS U),
    x ∈ definingIdealAt B S hS Z' Zcl (op U) → ∀ m : G.val.obj (op U), x • m = 0)
  (hKL : ∀ d : ChartDiagram B S hS Z'.1 X.1 h'.hom,
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.U.1.left) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj d.V.1.left) →
    (chartDiagramFunctionMap B S hS h' d).IsUniversalFirstOrderThickening
      (definingIdealAt B S hS Z' Zcl (op d.U)))

include hKL in
/-- **Restriction of derivations along `h'` is injective**: a `Y`-derivation of `𝒪_{Z'}` with
values in `G` is determined by its composite with `h'^♯`. -/
theorem injective_pushforwardUniversalDerivation_postcomp :
    Function.Injective fun x : sheafOfDifferentials B S hS (h' ≫ p) ⟶ G =>
      (pushforwardUniversalDerivation B S hS h' p (h' ≫ p) (𝟙 Y)
        (Category.comp_id (h' ≫ p)).symm).postcomp ((modulePushforward B S hS h').map x).val := by
  intro x₁ x₂ hx
  refine (differentialsHomEquiv B S hS (h' ≫ p) G).injective ?_
  refine PresheafOfModules.Derivation.ext (funext fun T => AddMonoidHom.ext fun s => ?_)
  refine sections_eq_of_hasAffineChartDiagram B S hS h' G (T := T.unop) fun T' a ha => ?_
  let d := ha.chartDiagram B S hS h'
  have key : ∀ x : sheafOfDifferentials B S hS (h' ≫ p) ⟶ G, ∀ y : chartFunctionRing B S hS d.V,
      (x.val.app (op d.U)).hom ((universalDerivation B S hS (h' ≫ p)).d
        (chartDiagramFunctionMap B S hS h' d y)) =
      chartDiagramProjectedDerivation B S hS h' G ((pushforwardUniversalDerivation B S hS h' p (h'
          ≫ p)
        (𝟙 Y) (Category.comp_id (h' ≫ p)).symm).postcomp
          ((modulePushforward B S hS h').map x).val) d y := fun x y =>
    (chartDiagramProjectedDerivation_pushforwardUniversalDerivation_postcomp B S hS h' G p x d
        y).symm
  let D₁ := (differentialsHomEquiv B S hS (h' ≫ p) G x₁)
  let D₂ := (differentialsHomEquiv B S hS (h' ≫ p) G x₂)
  have hd : D₁.d (X := op d.U) = D₂.d (X := op d.U) := by
    refine (hKL d ha.1 (ha.isAffine_V B S hS h')).leibniz_ext _ _
      (fun x y => D₁.d_mul x y) (fun x y => D₂.d_mul x y) fun y => ?_
    exact (key x₁ y).trans ((congrArg (fun D => chartDiagramProjectedDerivation B S hS h' G D d y)
        hx).trans
      (key x₂ y).symm)
  have m₁ := D₁.d_map a.op s
  have m₂ := D₂.d_map a.op s
  have hd' := congrArg (fun f : chartFunctionRing B S hS d.U →+ G.val.obj (op d.U) =>
    f ((smallEtaleRingedSite B S hS Z'.1 Z'.2).O.obj.map a.op s)) hd
  exact m₁.symm.trans (hd'.trans m₂)

include hG hKL in
/-- **Restriction of derivations along `h'` is surjective**: every `Y`-derivation of `𝒪_X` with
values in `h'_*G` is the composite with `h'^♯` of a `Y`-derivation of `𝒪_{Z'}` with values in
`G`. -/
theorem surjective_pushforwardUniversalDerivation_postcomp :
    Function.Surjective fun x : sheafOfDifferentials B S hS (h' ≫ p) ⟶ G =>
      (pushforwardUniversalDerivation B S hS h' p (h' ≫ p) (𝟙 Y)
        (Category.comp_id (h' ≫ p)).symm).postcomp ((modulePushforward B S hS h').map x).val := by
  intro D
  refine ⟨(differentialsHomEquiv B S hS (h' ≫ p) G).symm
    (thickeningLiftDerivationRelative B S hS h' G p Zcl hG hKL D), ?_⟩
  set x := (differentialsHomEquiv B S hS (h' ≫ p) G).symm
    (thickeningLiftDerivationRelative B S hS h' G p Zcl hG hKL D)
  have hx : (universalDerivation B S hS (h' ≫ p)).postcomp x.val =
      thickeningLiftDerivationRelative B S hS h' G p Zcl hG hKL D :=
    (differentialsHomEquiv B S hS (h' ≫ p) G).apply_symm_apply _
  refine PresheafOfModules.Derivation.ext (funext fun V => AddMonoidHom.ext fun a => ?_)
  refine chartDiagramProjection_ext B S hS h' G V.unop fun U g hc => ?_
  let d : ChartDiagram B S hS Z'.1 X.1 h'.hom := ⟨U, V.unop, g, hc⟩
  have e₁ := chartDiagramProjectedDerivation_pushforwardUniversalDerivation_postcomp B S hS h' G p
      x d a
  have e₂ := PresheafOfModules.Derivation.congr_d hx (X := op d.U)
    (chartDiagramFunctionMap B S hS h' d a)
  have e₃ := thickeningLiftValue_chartDiagramFunctionMap B S hS h' G Zcl hG hKL D d a
  exact e₁.trans (e₂.trans e₃)

end Main

end AlgebraicGeometry.Space

end
