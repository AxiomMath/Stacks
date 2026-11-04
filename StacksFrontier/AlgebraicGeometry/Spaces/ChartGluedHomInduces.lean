module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartInducesOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartFamilyInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart

/-!
# Step 5 of Stacks 04KL: the chartwise morphisms glue

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B`, and let
`ψ` be a morphism of their small étale ringed topoi. Given, for every étale chart of `X` carrying a
section of one of the sheaves `ψ⁻¹h_{W i}`, a morphism to `Y` inducing `ψ` after that chart, these
morphisms glue to a single morphism `l` of the underlying sheaves of `X` and `Y` which induces `ψ`
over every selected chart factoring through a given surjective étale atlas of `X`.

## Main results

* `AlgebraicGeometry.Space.exists_hom_induces_chartwise_of_chartHoms`: from a family of chartwise
  morphisms inducing `ψ`, a morphism `l` inducing `ψ` over every selected chart factoring through
  the atlas.
* `AlgebraicGeometry.Space.exists_hom_induces_chartwise`: the same for a locally ringed `ψ`
  compatible with the structure morphisms to the base, with no chartwise family given.
* `AlgebraicGeometry.Space.exists_hom_induces_chartwise_affineCharts`: the same for the covering
  family of affine étale charts of `Y`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory

universe w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : AlgebraicSpaces B S hS)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

/-- **Step 5 of the proof of [Stacks Project, Tag 04KL].**  Let `W` be a family of étale charts
of `Y` covering the final object of its small étale site, let `m` attach to every étale chart of
`X` carrying a section of one of the sheaves `ψ⁻¹h_{W i}` a morphism of algebraic spaces to `Y`
inducing `ψ` after that chart, and let `b : h_A ⟶ X` be a surjective étale scheme chart of `X`.
Then there is a morphism `l` of the underlying sheaves of `X` and `Y` which induces `ψ` over
every selected chart of `X` factoring through `b`. -/
theorem exists_hom_induces_chartwise_of_chartHoms {I : Type w'}
    (W : I → SmallEtale B S hS Y.1)
    (hWcov : (SmallEtale.topology B S hS Y.1).CoversTop W)
    (m : ∀ (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ X.1),
      HasSomeChartSection B S hS X.1
        (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (W i))) R c →
      (schemeSpace R ⟶ Y))
    (hm : ∀ (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ X.1)
      (hP : HasSomeChartSection B S hS X.1
        (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (W i))) R c),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (m R c hP))
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
          (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS c)))))
    (A : BigFppfOver B S hS) (b : yoneda.obj A ⟶ X.1) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : X.1 ⟶ Y.1, ∀ (T : BigFppfOver B S hS) (_ : IsAffineOver B S hS T) (r : T ⟶ A)
      (_ : IsEtale B S hS (yoneda.map r ≫ b))
      (_ : HasSomeChartSection B S hS X.1
        (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (W i))) T
        (yoneda.map r ≫ b)),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (ObjectProperty.homMk (yoneda.map r ≫ b ≫ l) :
          schemeSpace T ⟶ Y))
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
          (smallEtaleRingedToposHom B S hS
            (etaleChartToSpace B S hS (yoneda.map r ≫ b))))) := by
  obtain ⟨l, hl⟩ := exists_hom_of_chartHoms_twoIso_of_coversTop B S hS ψ W hWcov
    (fun R _ c _ hP => (m R c hP).hom)
    (fun T R _ _ r c _ _ hPc hPrc =>
      nonempty_twoIso_chartHoms_of_induces B S hS X Y ψ m hm T R r c hPc hPrc)
    A b hb hsurj
  refine ⟨l, fun T hT r hrb hPrb => ?_⟩
  have e : (ObjectProperty.homMk (yoneda.map r ≫ b ≫ l) : schemeSpace T ⟶ Y) =
      m T (yoneda.map r ≫ b) hPrb :=
    ObjectProperty.hom_ext _ (hl T hT r hrb hPrb)
  rw [e]
  exact hm T (yoneda.map r ≫ b) hPrb

/-- **Step 5 of the proof of [Stacks Project, Tag 04KL].** Let `ψ` be locally ringed and
2-compatible with the structure morphisms of `X` and `Y` to the base, let `W` be a family of affine
étale charts of `Y` covering the final object of its small étale site, and let `b : h_A ⟶ X` be a
surjective étale scheme chart of `X`. Then there is a morphism `l` of the underlying sheaves of `X`
and `Y` which induces `ψ` over every selected chart of `X` factoring through `b`. -/
theorem exists_hom_induces_chartwise {I : Type w'} (hψ : ψ.IsLocallyRinged)
    (hbase : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X)))
    (W : I → SmallEtale B S hS Y.1)
    (hWcov : (SmallEtale.topology B S hS Y.1).CoversTop W)
    (hWaff : ∀ i, IsAffineOver B S hS (chartFppfObject B S hS Y (W i)))
    (A : BigFppfOver B S hS) (b : yoneda.obj A ⟶ X.1) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : X.1 ⟶ Y.1, ∀ (T : BigFppfOver B S hS) (_ : IsAffineOver B S hS T) (r : T ⟶ A)
      (_ : IsEtale B S hS (yoneda.map r ≫ b))
      (_ : HasSomeChartSection B S hS X.1
        (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (W i))) T
        (yoneda.map r ≫ b)),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (ObjectProperty.homMk (yoneda.map r ≫ b ≫ l) :
          schemeSpace T ⟶ Y))
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
          (smallEtaleRingedToposHom B S hS
            (etaleChartToSpace B S hS (yoneda.map r ≫ b))))) :=
  exists_hom_induces_chartwise_of_chartHoms B S hS X Y ψ W hWcov
    (fun R c hP => (exists_chartHom_induces_of_hasSomeChartSection B S hS X Y ψ hψ hbase W
      hWaff R c hP).choose)
    (fun R c hP => (exists_chartHom_induces_of_hasSomeChartSection B S hS X Y ψ hψ hbase W
      hWaff R c hP).choose_spec)
    A b hb hsurj

/-- **Step 5 of the proof of [Stacks Project, Tag 04KL], for all affine charts of `Y`.** Let `ψ`
be locally ringed and 2-compatible with the structure morphisms of `X` and `Y` to the base, and
let `b : h_A ⟶ X` be a surjective étale scheme chart of `X`. Then there is a morphism `l` of the
underlying sheaves of `X` and `Y` which induces `ψ` over every chart of `X` factoring through `b`
and carrying a section of `ψ⁻¹h_W` for some affine étale chart `W` of `Y`. -/
theorem exists_hom_induces_chartwise_affineCharts (hψ : ψ.IsLocallyRinged)
    (hbase : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X)))
    (A : BigFppfOver B S hS) (b : yoneda.obj A ⟶ X.1) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : X.1 ⟶ Y.1, ∀ (T : BigFppfOver B S hS) (_ : IsAffineOver B S hS T) (r : T ⟶ A)
      (_ : IsEtale B S hS (yoneda.map r ≫ b))
      (_ : HasSomeChartSection B S hS X.1
        (fun W : {W : SmallEtale B S hS Y.1 //
            IsAffine ((BigFppfOver.toScheme B S hS).obj
              ((SmallEtale.toOver B S hS Y.1).obj W))} =>
          ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y W.1)) T
        (yoneda.map r ≫ b)),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (ObjectProperty.homMk (yoneda.map r ≫ b ≫ l) :
          yonedaSpace B S hS T ⟶ Y))
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
          (smallEtaleRingedToposHom B S hS
            (etaleChartToSpace B S hS (yoneda.map r ≫ b))))) :=
  exists_hom_induces_chartwise B S hS X Y ψ hψ hbase _
    (SmallEtale.coversTop_affineCharts B S hS Y.1) (fun W => W.2) A b hb hsurj

end AlgebraicGeometry.Space

end
