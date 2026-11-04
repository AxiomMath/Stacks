module

public import StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystem
public import StacksFrontier.AlgebraicGeometry.Limits.GoodDiagramClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemComparison

/-!
# The proper model, from a closed immersion into a descended one

Let `S = lim S_i` be the limit of a directed inverse system of Noetherian schemes with affine
transition morphisms, let `X ⟶ S` and `Y ⟶ S` be quasi-separated and of finite type, and let
`f : X ⟶ Y` be a morphism over `S`. Suppose that `f` factors as a closed immersion `X ⟶ X'`
followed by a morphism `X' ⟶ Y` which is the base change, along the morphism from `Y` to the model
`H.W` of a good diagram `H` for `Y`, of a proper morphism of finite presentation `Z ⟶ H.W`. Then
there are good diagrams for `X` and for `Y` over a common stage whose models are related by a
proper morphism compatible with `f`, and consequently the morphism of image systems attached to `f`
is eventually proper, which is the conclusion of Tag 0CNV.

## Main results

In namespace `AlgebraicGeometry.LimitNoetherianSituation`:

* `exists_properModel_of_isClosedImmersion`: given such a factorisation of `f`, there are good
  diagrams for `X` and for `Y` over a common stage whose models are related by a proper morphism
  compatible with `f`.
* `eventually_isProper_morphismAt_of_exists_properModel`: given such a factorisation of `f`, the
  morphism of image systems attached to `f` is proper over every sufficiently large stage.

## Implementation notes

The good diagram for `X` is `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofModel` for
`X'`, transported along the closed immersion by
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.ofIsClosedImmersion`. It has the same stage
as `H`, so the two good diagrams have equal indices by `rfl`.

## References

* [Stacks Project, Tag 0CNV](https://stacks.math.columbia.edu/tag/0CNV)
* [Stacks Project, Tag 09ZR](https://stacks.math.columbia.edu/tag/09ZR)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe v u

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **A proper model from a closed immersion into a base change of a proper model.** Suppose `X`
closed-immerses into a scheme `X'` over `Y`, and that `X' ⟶ Y` is the base change along `H.toModel`
of a morphism `Z.hom` that is proper and of finite presentation, for some good diagram `H` for `Y`.
Then there are good diagrams for `X` and for `Y` over a common stage whose models are related by a
proper morphism compatible with `f`. -/
theorem exists_properModel_of_isClosedImmersion
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y X' : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (g : X' ⟶ Y) (ι : X ⟶ X') [IsClosedImmersion ι] (hιg : ι ≫ g = f)
    (H : GoodDiagram D pY) (Z : Over H.W) (hZ : FinitePresentation Z.hom) [IsProper Z.hom]
    (e : Over.mk g ≅ (Over.pullback H.toModel).obj Z) :
    ∃ (GX' : GoodDiagram D pX) (GY' : GoodDiagram D pY)
      (hi : GX'.index = GY'.index) (m : GX'.W ⟶ GY'.W) (_ : IsProper m),
      m ≫ GY'.modelMap = GX'.modelMap ≫ D.system.map (eqToHom (congrArg op hi)) ∧
        GX'.toModel ≫ m = f ≫ GY'.toModel := by
  have hu : ι ≫ (g ≫ pY) = pX := by rw [← Category.assoc, hιg, hf]
  have he : e.hom.left ≫ pullback.snd Z.hom H.toModel = g := e.hom.w
  have key : e.hom.left ≫ pullback.fst Z.hom H.toModel ≫ Z.hom = g ≫ H.toModel := by
    rw [pullback.condition, ← Category.assoc, he]
  refine ⟨(GoodDiagram.ofModel g rfl H Z hZ e).ofIsClosedImmersion hu, H, rfl, Z.hom,
    ‹IsProper Z.hom›, ?_, ?_⟩
  · show Z.hom ≫ H.modelMap = (Z.hom ≫ H.modelMap) ≫ D.system.map (eqToHom (congrArg op rfl))
    simp
  · show (ι ≫ e.hom.left ≫ pullback.fst Z.hom H.toModel) ≫ Z.hom = f ≫ H.toModel
    rw [← hιg]
    simp only [Category.assoc]
    rw [key]

/-- **Eventual properness from a closed immersion into a base change of a proper model.** Let `F`
be a morphism of image systems attached to `f`, and suppose that `f` factors as a closed immersion
`ι : X ⟶ X'` followed by a morphism `g : X' ⟶ Y` which is the base change, along the horizontal
morphism of some good diagram `H` for `Y`, of a proper morphism of finite presentation. Then
`F.maps.app j` is proper for every `j` over a sufficiently large stage. -/
theorem eventually_isProper_morphismAt_of_exists_properModel [FinallySmall.{u} I]
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY)
    (hfactor : ∃ (X' : Scheme.{u}) (g : X' ⟶ Y) (ι : X ⟶ X') (_ : IsClosedImmersion ι),
      ι ≫ g = f ∧ ∃ (H : GoodDiagram D pY) (Z : Over H.W) (_ : FinitePresentation Z.hom)
        (_ : IsProper Z.hom), Nonempty (Over.mk g ≅ (Over.pullback H.toModel).obj Z)) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → IsProper (F.maps.app j) := by
  obtain ⟨X', g, ι, hι, hιg, H, Z, hZ, hprop, ⟨e⟩⟩ := hfactor
  have := hι
  have := hprop
  exact eventually_isProper_morphismAt_of_exists_model D f hf GX GY i₀ hX hY F
    (exists_properModel_of_isClosedImmersion D f hf g ι hιg H Z hZ e)

end LimitNoetherianSituation

end AlgebraicGeometry

end
