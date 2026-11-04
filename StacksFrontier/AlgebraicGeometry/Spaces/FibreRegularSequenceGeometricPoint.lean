module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingAlongDominationGerms
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreChartRegularityDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointNeighborhoodLift

/-!
# The fibre hypothesis of Stacks 06LW at a dominating geometric point

Let `ξ : F ⟶ X` be a morphism of algebraic spaces over a scheme `S` in a big fppf site — in the
application the projection of a fibre `F = X ×_Y Spec k` — and let `f₁, …, f_r ∈ Γ(X, 𝒪_X)`.  The
hypothesis of Stacks 06LW is that the images of the `f_i` in the étale local ring `𝒪_{F, z̄}`
form a regular sequence, the image of `f_i` being its germ along a small étale neighbourhood of
`ξ(z̄)` pushed into `𝒪_{F, z̄}` by the comparison homomorphism of Stacks 04NG.

This file shows that the hypothesis is unchanged by replacing `z` with a geometric point
dominating it, that is by enlarging the field over which the point of the fibre is taken.  That
enlargement is the first step of the source's proof of the flatness half of Stacks 06LW, and the
hypothesis has to travel across it.

## Main results

* `AlgebraicGeometry.Space.forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates`: the fibre
  hypothesis of Stacks 06LW holds at a geometric point if and only if it holds at any geometric
  point dominating it.

## Implementation notes

The transport itself is `AlgebraicGeometry.Space.isRegular_etaleLocalRingGerm_along_iff`, which
compares regularity of a sequence of germs of regular functions *on one chart of `F`* at the two
points.  Two rewritings separate that from the hypothesis as Stacks 06LW states it, and both are
performed here.

The first identifies the image of a germ under the comparison homomorphism of Stacks 04NG with
a germ on a chart of `F`.  That is `AlgebraicGeometry.Space.etaleLocalRingMap_isEtaleLocalRingMap`
at a commuting diagram of pointed charts over `ξ`, which
`AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_lift` produces at a prescribed geometric
point and a prescribed pointed chart of `X`.  It is used in both directions: downwards at the
dominated point, upwards at the dominating one, where the chart of `X` the diagram goes to is
`AlgebraicGeometry.Space.targetNeighborhood` of the restricted chart of `F`, whose point is the
image of the point of that chart on the nose.

The second is that the hypothesis does not depend on the chosen small étale neighbourhood of
`ξ(z̄)`, which is `AlgebraicGeometry.Space.etaleLocalRingGerm_chartValue_eq` for the germ of a
global function.  It is needed because the chart of `X` that the transport lands on is the one
the chart diagram at the dominated point happened to use, while the conclusion quantifies over
all of them — the form in which Stacks 06MD states the hypothesis,
`AlgebraicGeometry.Stack.FibreIsRegularSequenceAt`.

## References

* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Xs Fs : AlgebraicSpaces B S hS} (ξ : Fs ⟶ Xs) {r : ℕ}
  (fs : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Xs)).sections)

/-- The images in `𝒪_{F, z̄}` of the germs of global functions on `X` along a small étale
neighbourhood of `ξ(z̄)` are the germs at `z` of their restrictions to a chart of `F` over that
neighbourhood: the comparison homomorphism of Stacks 04NG pulls germs back along the vertical
morphism of a commuting diagram of pointed charts. -/
private theorem germs_eq_map_chart {w : GeometricPoint B S hS Fs.1}
    (U : SmallEtaleNeighborhood w) (N : SmallEtaleNeighborhood (geometricPointMap ξ.hom w))
    (g : U.chart.obj.left ⟶ N.chart.obj.left)
    (hcomm : U.chart.obj.hom ≫ ξ.hom = yoneda.map g ≫ N.chart.obj.hom)
    (hpt : U.point ≫ g = N.point) :
    (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom w
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom w) (op N)
          ((fs i).eval (op N.chart)))) =
      (List.ofFn fun i : Fin r =>
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom
            ((fs i).eval (op N.chart))).map
        (etaleLocalRingGerm B S hS Fs.1 w (op U)) :=
  Eq.trans
    (congrArg List.ofFn (funext fun i : Fin r =>
      RingHom.congr_fun
        (etaleLocalRingMap_isEtaleLocalRingMap Fs.2 ξ.hom w U N g hcomm hpt).symm
        ((fs i).eval (op N.chart))))
    (List.map_ofFn (f := fun i : Fin r =>
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom ((fs i).eval (op N.chart)))
      (g := ⇑(etaleLocalRingGerm B S hS Fs.1 w (op U)))).symm

/-- The images in `𝒪_{F, z̄}` of the germs of global functions on `X` do not depend on the chosen
small étale neighbourhood of `ξ(z̄)`. -/
private theorem germs_eq_of_neighborhood (w : GeometricPoint B S hS Fs.1)
    (N₁ N₂ : SmallEtaleNeighborhood (geometricPointMap ξ.hom w)) :
    (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom w
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom w) (op N₁)
          ((fs i).eval (op N₁.chart)))) =
      (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom w
        (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom w) (op N₂)
          ((fs i).eval (op N₂.chart)))) :=
  congrArg List.ofFn (funext fun i => congrArg (etaleLocalRingMap Fs.2 ξ.hom w)
    (etaleLocalRingGerm_chartValue_eq B S hS Xs.1 Xs.2 (fs i) N₁ N₂))

/-- **The fibre hypothesis of Stacks 06LW is unchanged by a domination of geometric points.**
Let `ξ : F ⟶ X` be a morphism of algebraic spaces over `S`, let `f₁, …, f_r` be global regular
functions on `X` and let `y` be a geometric point of `F` dominating a geometric point `x`, that
is with the section defining `y` the restriction of the section defining `x` along a morphism
`d` of the underlying field spectra.  Then the images of the `f_i` form a regular sequence in
`𝒪_{F, x̄}` if and only if they do in `𝒪_{F, ȳ}`. -/
theorem forall_isRegular_etaleLocalRingMap_germ_iff_of_dominates
    {x y : GeometricPoint B S hS Fs.1} (d : y.val.siteObject ⟶ x.val.siteObject)
    (hd : Fs.1.map d.op x.val.value = y.val.value) :
    (∀ N : SmallEtaleNeighborhood (geometricPointMap ξ.hom x),
        RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 x)
          (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom x
            (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom x) (op N)
              ((fs i).eval (op N.chart))))) ↔
      ∀ N : SmallEtaleNeighborhood (geometricPointMap ξ.hom y),
        RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 y)
          (List.ofFn fun i : Fin r => etaleLocalRingMap Fs.2 ξ.hom y
            (etaleLocalRingGerm B S hS Xs.1 (geometricPointMap ξ.hom y) (op N)
              ((fs i).eval (op N.chart)))) := by
  constructor
  · intro hx Ny
    obtain ⟨Nx⟩ := nonempty_smallEtaleNeighborhood Xs.2 (geometricPointMap ξ.hom x)
    obtain ⟨U, -, g, hcomm, hpt⟩ := exists_smallEtaleNeighborhood_lift ξ.hom
      (nonempty_smallEtaleNeighborhood Fs.2 x).some Nx
    rw [← germs_eq_of_neighborhood B S hS ξ fs y
        (targetNeighborhood B S hS ((neighborhoodAlong d hd).obj U) Nx.chart g hcomm) Ny,
      germs_eq_map_chart B S hS ξ fs ((neighborhoodAlong d hd).obj U)
        (targetNeighborhood B S hS ((neighborhoodAlong d hd).obj U) Nx.chart g hcomm) g hcomm rfl]
    refine (isRegular_etaleLocalRingGerm_along_iff Fs.2 d hd U _).1 ?_
    exact (iff_of_eq (congrArg (RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 x))
      (germs_eq_map_chart B S hS ξ fs U Nx g hcomm hpt))).1 (hx Nx)
  · intro hy Nx
    obtain ⟨U, -, g, hcomm, hpt⟩ := exists_smallEtaleNeighborhood_lift ξ.hom
      (nonempty_smallEtaleNeighborhood Fs.2 x).some Nx
    rw [germs_eq_map_chart B S hS ξ fs U Nx g hcomm hpt]
    refine (isRegular_etaleLocalRingGerm_along_iff Fs.2 d hd U _).2 ?_
    exact (iff_of_eq (congrArg (RingTheory.Sequence.IsRegular (etaleLocalRing B S hS Fs.1 y))
      (germs_eq_map_chart B S hS ξ fs ((neighborhoodAlong d hd).obj U)
        (targetNeighborhood B S hS ((neighborhoodAlong d hd).obj U) Nx.chart g hcomm) g hcomm
        rfl))).1 (hy _)

end AlgebraicGeometry.Space

end
