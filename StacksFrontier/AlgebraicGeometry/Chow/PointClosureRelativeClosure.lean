module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureIntermediatePoints

/-!
# The closure of a point taken inside a closed subscheme, and taken inside the ambient scheme

Let `f : W ⟶ X` be a closed immersion and let `z` be a point of `W`. There are two reduced closed
subschemes attached to `z`: the closure of `z` taken inside `W`, and the closure of the image
`f z` taken inside `X`. This file makes the restriction of `f` between them,
`Stacks.Chow.integralComponentMap`, into a *named* isomorphism of schemes over `X`, and
transports the local rings, the function field and the order of vanishing of Stacks 02MD across
it.

The identification is needed because the two halves of the proof of Stacks 0GU9 take the closure
in two different places. The index correspondence
`Stacks.Chow.heightOnePrimeEquivIntermediatePoint` lives on `W = closure {x}`, so the divisor cut
out by a height-one prime of `𝒪_{W, x''}` is a divisor on the closure of a point of `W` *taken
inside `W`*, which is what `Stacks.Chow.quotStalkEquivIntermediatePointStalk` produces. The
divisor differential of Stacks 0GU3, on the other hand, pushes principal divisors forward from
`Stacks.Chow.integralComponentAt x'` for a point `x'` of `X`, so `Stacks.Chow.pointClosureOrd`
reads the same divisor on the closure *taken inside `X`*.

## What the development already had, and what was missing

The ideal-sheaf computation is `Stacks.Chow.map_integralComponentAt`, and the restriction of `f`
between the two closed subschemes is `Stacks.Chow.integralComponentMap`; both are general, for an
arbitrary morphism of schemes. That the restriction is invertible for a closed immersion was
available only as an existence statement, twice:
`Stacks.Chow.exists_iso_integralComponentAt_comp` and
`Stacks.Chow.exists_iso_integralComponentAt`, each producing *some* isomorphism over `X` from
`Stacks.Chow.exists_iso_of_ker_eq`. An existence statement cannot carry a transport: there is no
way to name the image of a rational function, or of a germ, under an isomorphism which is only
known to exist, so no equation between two orders of vanishing can be stated. What is added here
is the instance `Stacks.Chow.isIso_integralComponentMap`, which says that the canonical
restriction *itself* is invertible, and the identifications of local rings, function fields and
orders of vanishing that follow from it.

## The argument

Both `(integralComponentAt z).subschemeι ≫ f` and `(integralComponentAt (f z)).subschemeι` are
closed immersions into `X`, and their kernel ideal sheaves agree by
`Stacks.Chow.map_integralComponentAt`, so
`AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq` applies to the canonical restriction, which
commutes with the two closed immersions by `Stacks.Chow.integralComponentMap_subschemeι`. Being
an isomorphism over `X` is what makes every transport below the identity on the ambient points:
the two closed immersions are injective, so the identification is forced on points.

The transports are then the general ones of
`StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.FunctionField` and
`StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order`, read at this isomorphism.

## What is carried

No further input is assumed. Everything needs only that the morphism is a closed immersion, and
the order-of-vanishing statements need local Noetherianness of the two closed subschemes, which
is what makes the order defined at all. On the schemes of Stacks 0GUA that holds, since a scheme
locally of finite type over a locally Noetherian base is locally Noetherian.

Nothing here asserts Stacks 0GU9 or Stacks 0GUA. No chain group, no differential and no complex
appears, and the identification of the individual summands of the displayed sum of Stacks 0GU9 is
not proved here either.

## Main definitions

* `Stacks.Chow.integralComponentIso` — **the identification**, for `f` a closed immersion: the
  canonical restriction of `f`, read as an isomorphism.
* `Stacks.Chow.integralComponentStalkEquiv`,
  `Stacks.Chow.integralComponentFunctionFieldEquiv` — the induced identifications of the local
  rings and of the function fields.
* `Stacks.Chow.pointClosureInnerIso` — the identification in the shape the proof of Stacks 0GU9
  uses it: `W` is the integral closed subscheme spanned by a point `x` of `X`.

## Main results

* `Stacks.Chow.mem_closure_image_singleton` — the image of a point of the closure of `z` lies in
  the closure of the image of `z`.
* `Stacks.Chow.isIso_integralComponentMap` — the canonical restriction of a closed immersion to
  the reduced closures is invertible.
* `Stacks.Chow.subschemeι_integralComponentIso` — the identification is one over `X`.
* `Stacks.Chow.integralComponentIso_pointClosurePoint` — it carries the point of the inner
  closure above a point `t` of `W` to the point of the outer closure above `f t`.
* `Stacks.Chow.integralComponentFunctionFieldEquiv_algebraMap` — the square relating the local
  rings, the function fields and the two induced identifications commutes.
* `Stacks.Chow.ord_integralComponentIso`, `Stacks.Chow.ord_pointClosureInnerIso` — **the order
  transport**: the order of vanishing of Stacks 02MD of a rational function on the inner closure,
  at a point of it, is the order of vanishing of the transported function on the outer closure,
  at the transported point.
* `Stacks.Chow.ord_pointClosureIntermediatePoint` — the order transport with the image point
  written as `Stacks.Chow.intermediatePointValue`.

## References

* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02RL](https://stacks.math.columbia.edu/tag/02RL)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable {W X : Scheme.{u}}

/-! ### The image of the closure of a point -/

/-- The image of a point of the closure of `z` lies in the closure of the image of `z`: a
morphism of schemes is continuous, so it preserves specialization. -/
theorem mem_closure_image_singleton (f : W ⟶ X) {z t : W}
    (ht : t ∈ closure ({z} : Set W)) :
    f.base t ∈ closure ({f.base z} : Set X) :=
  specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr ht).map f.continuous)

/-! ### The identification of the two closures -/

/-- **The canonical restriction of a closed immersion to the reduced closure of a point is
invertible.** For `f : W ⟶ X` a closed immersion and `z` a point of `W`, both
`(integralComponentAt z).subschemeι ≫ f` and `(integralComponentAt (f z)).subschemeι` are closed
immersions into `X` whose kernel ideal sheaves agree by `Stacks.Chow.map_integralComponentAt`, and
`Stacks.Chow.integralComponentMap` is a morphism over `X` between them; a morphism over `X`
between two closed immersions with the same kernel is an isomorphism.

The development already knew that *some* isomorphism over `X` exists, twice, as
`Stacks.Chow.exists_iso_integralComponentAt_comp` and
`Stacks.Chow.exists_iso_integralComponentAt`. What this adds is that the canonical restriction is
the isomorphism, which is what lets germs and rational functions be transported by name. -/
instance isIso_integralComponentMap (f : W ⟶ X) [IsClosedImmersion f] (z : W) :
    IsIso (integralComponentMap f z) := by
  refine IsClosedImmersion.isIso_of_ker_eq ((integralComponentAt z).subschemeι ≫ f)
    (integralComponentAt (f.base z)).subschemeι _ (integralComponentMap_subschemeι f z) ?_
  rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map]
  exact map_integralComponentAt f z

/-- **The closure of a point inside a closed subscheme is the closure of its image.** Let
`f : W ⟶ X` be a closed immersion and let `z` be a point of `W`. Then the reduced closure of `z`
taken inside `W` and the reduced closure of `f z` taken inside `X` are isomorphic as schemes over
`X`, by the restriction of `f`.

This is the identification the proof of Stacks 0GU9 needs in order to read a divisor on the
closure of a point of `W` as a divisor on the closure of its image in `X`, which is where the
divisor differential of Stacks 0GU3 reads it. -/
def integralComponentIso (f : W ⟶ X) [IsClosedImmersion f] (z : W) :
    (integralComponentAt z).subscheme ≅ (integralComponentAt (f.base z)).subscheme :=
  asIso (integralComponentMap f z)

/-- The identification is one over `X`, read on points: a point of the inner closure and its
image under the identification have the same image in `X`. -/
theorem subschemeι_integralComponentIso (f : W ⟶ X) [IsClosedImmersion f] (z : W)
    (t : (integralComponentAt z).subscheme) :
    (integralComponentAt (f.base z)).subschemeι ((integralComponentIso f z).hom.base t) =
      f.base ((integralComponentAt z).subschemeι t) := by
  change (integralComponentMap f z ≫ (integralComponentAt (f.base z)).subschemeι).base t = _
  rw [integralComponentMap_subschemeι]
  rfl

/-- The identification carries the point of the inner closure sitting above a point `t` of `W` to
the point of the outer closure sitting above `f t`. Both closed immersions are injective on
points, so this follows from the compatibility over `X`. -/
theorem integralComponentIso_pointClosurePoint (f : W ⟶ X) [IsClosedImmersion f] (z : W)
    {t : W} (ht : t ∈ closure ({z} : Set W))
    (ht' : f.base t ∈ closure ({f.base z} : Set X)) :
    (integralComponentIso f z).hom.base (pointClosurePoint z ht) =
      pointClosurePoint (f.base z) ht' := by
  refine (integralComponentAt (f.base z)).subschemeι.isClosedEmbedding.injective ?_
  rw [subschemeι_integralComponentIso, subschemeι_pointClosurePoint,
    subschemeι_pointClosurePoint]

/-! ### The induced identifications of local rings and of function fields -/

/-- The identification of local rings induced by `Stacks.Chow.integralComponentIso`: the local
ring at a point of the closure of `z` inside `W` is the local ring at the corresponding point of
the closure of `f z` inside `X`. -/
def integralComponentStalkEquiv (f : W ⟶ X) [IsClosedImmersion f] (z : W)
    (t : (integralComponentAt z).subscheme) :
    ↥((integralComponentAt z).subscheme.presheaf.stalk t) ≃+*
      ↥((integralComponentAt (f.base z)).subscheme.presheaf.stalk
        ((integralComponentIso f z).hom.base t)) :=
  stalkRingEquivOfIso (integralComponentIso f z) t

/-- The identification of function fields induced by `Stacks.Chow.integralComponentIso`: a
rational function on the closure of `z` inside `W` is a rational function on the closure of `f z`
inside `X`. -/
def integralComponentFunctionFieldEquiv (f : W ⟶ X) [IsClosedImmersion f] (z : W) :
    ↥((integralComponentAt z).subscheme.functionField) ≃+*
      ↥((integralComponentAt (f.base z)).subscheme.functionField) :=
  functionFieldRingEquivOfIso (integralComponentIso f z)

/-- **The compatibility of the two induced identifications.** Sending a germ at `t` into the
function field of the inner closure and then transporting it is the same as transporting the germ
and then sending it into the function field of the outer closure. This is the compatible pair of
ring isomorphisms that a transport of the order of vanishing consumes. -/
theorem integralComponentFunctionFieldEquiv_algebraMap (f : W ⟶ X) [IsClosedImmersion f]
    (z : W) (t : (integralComponentAt z).subscheme)
    (a : ↥((integralComponentAt z).subscheme.presheaf.stalk t)) :
    integralComponentFunctionFieldEquiv f z
        (algebraMap ↥((integralComponentAt z).subscheme.presheaf.stalk t)
          ↥((integralComponentAt z).subscheme.functionField) a) =
      algebraMap ↥((integralComponentAt (f.base z)).subscheme.presheaf.stalk
            ((integralComponentIso f z).hom.base t))
          ↥((integralComponentAt (f.base z)).subscheme.functionField)
        (integralComponentStalkEquiv f z t a) :=
  functionFieldRingEquivOfIso_algebraMap (integralComponentIso f z) t a

/-! ### The order of vanishing across the identification -/

/-- **The order of vanishing is the same on the two closures.** For `f : W ⟶ X` a closed immersion
and `z` a point of `W`, the order of vanishing of Stacks 02MD of a rational function on the
closure of `z` inside `W`, at a point `t` of that closure, is the order of vanishing of the
transported rational function on the closure of `f z` inside `X`, at the transported point.

This is `Stacks.Chow.ord_functionFieldRingEquivOfIso` read at
`Stacks.Chow.integralComponentIso`. -/
theorem ord_integralComponentIso (f : W ⟶ X) [IsClosedImmersion f] (z : W)
    [IsLocallyNoetherian (integralComponentAt z).subscheme]
    [IsLocallyNoetherian (integralComponentAt (f.base z)).subscheme]
    (g : ↥((integralComponentAt z).subscheme.functionField))
    (t : (integralComponentAt z).subscheme) :
    (integralComponentAt (f.base z)).subscheme.ord
        (integralComponentFunctionFieldEquiv f z g)
        ((integralComponentIso f z).hom.base t) =
      (integralComponentAt z).subscheme.ord g t :=
  ord_functionFieldRingEquivOfIso (integralComponentIso f z) g t

/-! ### The identification at the integral closed subscheme spanned by a point -/

/-- **The identification in the shape the proof of Stacks 0GU9 uses it.** Let `x` be a point of a
scheme `X`, let `W = closure {x}` be the integral closed subscheme it spans, and let `z` be a
point of `W` with image `x'` in `X`. Then the reduced closure of `z` taken inside `W` and the
reduced closure of `x'` taken inside `X` are isomorphic as schemes over `X`.

The left-hand side is where `Stacks.Chow.quotStalkEquivIntermediatePointStalk` puts the divisor
cut out by a height-one prime of `𝒪_{W, x''}`; the right-hand side is where the divisor
differential of Stacks 0GU3 reads it, since `Stacks.Chow.pointClosureOrd` pushes forward from
`Stacks.Chow.integralComponentAt x'`. -/
def pointClosureInnerIso (x : X) (z : (integralComponentAt x).subscheme) :
    (integralComponentAt z).subscheme ≅
      (integralComponentAt ((integralComponentAt x).subschemeι z)).subscheme :=
  integralComponentIso (integralComponentAt x).subschemeι z

/-- The identification of the two closures of a point of `closure {x}` is one over `X`. -/
theorem subschemeι_pointClosureInnerIso (x : X) (z : (integralComponentAt x).subscheme)
    (t : (integralComponentAt z).subscheme) :
    (integralComponentAt ((integralComponentAt x).subschemeι z)).subschemeι
        ((pointClosureInnerIso x z).hom.base t) =
      (integralComponentAt x).subschemeι ((integralComponentAt z).subschemeι t) :=
  subschemeι_integralComponentIso (integralComponentAt x).subschemeι z t

/-- The identification carries the point of the closure of `z` inside `W` above a point `t` of
`W` to the point of the closure of `x'` inside `X` above the image of `t`. -/
theorem pointClosureInnerIso_pointClosurePoint (x : X)
    (z : (integralComponentAt x).subscheme) {t : (integralComponentAt x).subscheme}
    (ht : t ∈ closure ({z} : Set (integralComponentAt x).subscheme))
    (ht' : (integralComponentAt x).subschemeι t ∈
      closure ({(integralComponentAt x).subschemeι z} : Set X)) :
    (pointClosureInnerIso x z).hom.base (pointClosurePoint z ht) =
      pointClosurePoint ((integralComponentAt x).subschemeι z) ht' :=
  integralComponentIso_pointClosurePoint (integralComponentAt x).subschemeι z ht ht'

/-- **The order transport in the shape the proof of Stacks 0GU9 uses it.** The order of vanishing
of a rational function on the closure of `z` taken inside `closure {x}` is the order of vanishing
of the transported rational function on the closure of the image of `z` taken inside `X`. -/
theorem ord_pointClosureInnerIso (x : X) (z : (integralComponentAt x).subscheme)
    [IsLocallyNoetherian (integralComponentAt z).subscheme]
    [IsLocallyNoetherian
      (integralComponentAt ((integralComponentAt x).subschemeι z)).subscheme]
    (g : ↥((integralComponentAt z).subscheme.functionField))
    (t : (integralComponentAt z).subscheme) :
    (integralComponentAt ((integralComponentAt x).subschemeι z)).subscheme.ord
        (integralComponentFunctionFieldEquiv (integralComponentAt x).subschemeι z g)
        ((pointClosureInnerIso x z).hom.base t) =
      (integralComponentAt z).subscheme.ord g t :=
  ord_integralComponentIso (integralComponentAt x).subschemeι z g t

/-- **The order transport at an intermediate point of `closure {x}`.** The same statement as
`Stacks.Chow.ord_pointClosureInnerIso`, with the image point written as
`Stacks.Chow.intermediatePointValue`, which is the spelling in which the index translation of
`StacksFrontier.AlgebraicGeometry.Chow.PointClosureIntermediatePoints` hands a point of
`closure {x}` to the divisor differential of Stacks 0GU3.

The two spellings are equal by definition, but instance resolution does not see through the
definition, so the local Noetherianness needed to make the order defined has to be supplied at
this spelling; that is the only content of the restatement. -/
theorem ord_pointClosureIntermediatePoint {x y : X} (hy : y ∈ closure ({x} : Set X))
    (z : PointClosureIntermediatePoint x hy)
    [IsLocallyNoetherian (integralComponentAt z.1).subscheme]
    [IsLocallyNoetherian (integralComponentAt (intermediatePointValue hy z)).subscheme]
    (g : ↥((integralComponentAt z.1).subscheme.functionField))
    (t : (integralComponentAt z.1).subscheme) :
    (integralComponentAt (intermediatePointValue hy z)).subscheme.ord
        (integralComponentFunctionFieldEquiv (integralComponentAt x).subschemeι z.1 g)
        ((pointClosureInnerIso x z.1).hom.base t) =
      (integralComponentAt z.1).subscheme.ord g t := by
  let _ : IsLocallyNoetherian
      (integralComponentAt ((integralComponentAt x).subschemeι z.1)).subscheme :=
    inferInstanceAs (IsLocallyNoetherian
      (integralComponentAt (intermediatePointValue hy z)).subscheme)
  exact ord_pointClosureInnerIso x z.1 g t

end Stacks.Chow

end
