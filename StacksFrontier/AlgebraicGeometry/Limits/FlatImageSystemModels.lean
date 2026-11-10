module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing

/-!
# Stacks Tag 0CNT

Let `S = lim Sᵢ` be a directed inverse limit of Noetherian schemes with affine transition
morphisms and let `f : X ⟶ Y` be a flat morphism of finite presentation between schemes of finite
type over `S`.  Then the morphisms of the associated systems of scheme-theoretic images are flat
on a late tail, the transition squares of that morphism of systems are cartesian on a late tail,
and each late stage morphism is a base change of `f`.

The three statements are proved in
`StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystem` with Stacks Tag 01ZM part (1) carried
as the explicit hypothesis
`AlgebraicGeometry.LimitDescent.HasFinitePresentationModels`.  That tag is now proved, as
`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation`, so this file records the
three statements without it and attaches the tag.

## Main results

* `AlgebraicGeometry.LimitNoetherianSituation.eventually_flat_morphismAt`
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_isPullback_morphismAt`
* `AlgebraicGeometry.LimitNoetherianSituation.eventually_isPullback_limit_morphismAt`

## Implementation notes

Each proof is the corresponding statement of
`StacksFrontier.AlgebraicGeometry.Limits.FlatImageSystem`, which no longer carries `hmod`, so the
hypotheses and conclusions are those statements'.

## References

* [Stacks Project, Tag 0CNT](https://stacks.math.columbia.edu/tag/0CNT)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

namespace LimitNoetherianSituation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **Stacks Project, Tag 0CNT, eventual flatness.**

The morphisms of the image systems of a flat morphism of finite presentation are flat at every
sufficiently late stage. -/
@[stacks 0CNT "eventual flatness"]
public theorem eventually_flat_morphismAt
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → Flat (F.maps.app j) :=
  eventually_flat_morphismAt_of_hasFinitePresentationModels
    D f hf hfp GX GY i₀ hX hY F

/-- **Stacks Project, Tag 0CNT, cartesian transition squares.**

On a sufficiently late tail every transition square of the morphism of image systems of a flat
morphism of finite presentation is cartesian. -/
@[stacks 0CNT "cartesian transition squares"]
public theorem eventually_isPullback_morphismAt
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ {j k : Over (op i₀)} (a : j ⟶ k),
        i₃ ≤ unop j.left → i₃ ≤ unop k.left →
          IsPullback (F.maps.app j)
            ((Over.map ((homOfLE hX).op) ⋙ GoodDiagram.imageSystem GX).map a)
            ((Over.map ((homOfLE hY).op) ⋙ GoodDiagram.imageSystem GY).map a)
            (F.maps.app k) :=
  eventually_isPullback_morphismAt_of_hasFinitePresentationModels
    D f hf hfp GX GY i₀ hX hY F

/-- **Stacks Project, Tag 0CNT, cartesian limit square.**

The square relating a flat morphism of finite presentation to each sufficiently late morphism of
the image systems is cartesian. -/
@[stacks 0CNT "cartesian limit square"]
public theorem eventually_isPullback_limit_morphismAt
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left →
        IsPullback f
          ((GoodDiagram.imageCone GX).π.app ((Over.map ((homOfLE hX).op)).obj j))
          ((GoodDiagram.imageCone GY).π.app ((Over.map ((homOfLE hY).op)).obj j))
          (F.maps.app j) :=
  eventually_isPullback_limit_morphismAt_of_hasFinitePresentationModels
    D f hf hfp GX GY i₀ hX hY F

end LimitNoetherianSituation

namespace LimitNoetherianSituation

/-! The statements of Tag 0CNT for an index carrying no smallness hypothesis, under the primed
names. The registered statements above carry no smallness hypothesis either. -/

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- **Stacks Project, Tag 0CNT, eventual flatness, with no smallness hypothesis on the index.**

The morphisms of the image systems of a flat morphism of finite presentation are flat at every
sufficiently late stage. -/
public theorem eventually_flat_morphismAt'
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left → Flat (F.maps.app j) :=
  eventually_flat_morphismAt_of_hasFinitePresentationModels'
    D f hf hfp GX GY i₀ hX hY F

/-- **Stacks Project, Tag 0CNT, cartesian transition squares, with no smallness hypothesis on the
index.**

On a sufficiently late tail every transition square of the morphism of image systems of a flat
morphism of finite presentation is cartesian. -/
public theorem eventually_isPullback_morphismAt'
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ {j k : Over (op i₀)} (a : j ⟶ k),
        i₃ ≤ unop j.left → i₃ ≤ unop k.left →
          IsPullback (F.maps.app j)
            ((Over.map ((homOfLE hX).op) ⋙ GoodDiagram.imageSystem GX).map a)
            ((Over.map ((homOfLE hY).op) ⋙ GoodDiagram.imageSystem GY).map a)
            (F.maps.app k) :=
  eventually_isPullback_morphismAt_of_hasFinitePresentationModels'
    D f hf hfp GX GY i₀ hX hY F

/-- **Stacks Project, Tag 0CNT, cartesian limit square, with no smallness hypothesis on the
index.**

The square relating a flat morphism of finite presentation to each sufficiently late morphism of
the image systems is cartesian. -/
public theorem eventually_isPullback_limit_morphismAt'
    (D : LimitNoetherianSituation.{v, u} I)
    {X Y : Scheme.{u}} {pX : X ⟶ D.limitScheme} {pY : Y ⟶ D.limitScheme}
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    [QuasiSeparated pX] [LocallyOfFiniteType pX] [QuasiCompact pX]
    [QuasiSeparated pY] [LocallyOfFiniteType pY] [QuasiCompact pY]
    [Flat f] (hfp : FinitePresentation f)
    (GX : GoodDiagram D pX) (GY : GoodDiagram D pY)
    (i₀ : I) (hX : GX.index ≤ i₀) (hY : GY.index ≤ i₀)
    (F : MorphismAt D f GX GY i₀ hX hY) :
    ∃ (i₃ : I) (_ : i₀ ≤ i₃),
      ∀ (j : Over (op i₀)), i₃ ≤ unop j.left →
        IsPullback f
          ((GoodDiagram.imageCone GX).π.app ((Over.map ((homOfLE hX).op)).obj j))
          ((GoodDiagram.imageCone GY).π.app ((Over.map ((homOfLE hY).op)).obj j))
          (F.maps.app j) :=
  eventually_isPullback_limit_morphismAt_of_hasFinitePresentationModels'
    D f hf hfp GX GY i₀ hX hY F

end LimitNoetherianSituation

end AlgebraicGeometry
