module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineRefinementOfNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartIndependence

/-!
# The embedding of Stacks 0ENK does not depend on the chart

Let `X` be a decent, locally Noetherian, integral algebraic space over a scheme `S`, let
`Z ⊂ X` be a prime divisor with generic point `ξ`, and let `(U, u)` be an elementary étale
neighbourhood of `ξ` whose scheme is affine. Pulling a rational function of `X` back to
`Q(Γ(U, 𝒪_U))` and pushing it along `Γ(U, 𝒪_U) → 𝒪^h_{X, ξ}` gives the canonical map
`R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK, whatever affine `U` is used — in particular, the chosen
chart `AlgebraicGeometry.Space.PrimeDivisor.genericChart` may be replaced by any other affine
elementary étale neighbourhood of `ξ`.

For a morphism `V → U` of elementary étale neighbourhoods with both schemes affine this is
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_comp_eq`, whose compatibility
hypothesis is the naturality of the canonical map of Stacks 0EMY in the neighbourhood,
`AlgebraicGeometry.Space.stalkToHenselianLocalRing_naturality`. Two affine neighbourhoods are
refined by a common affine one by Stacks 0BGV, which reduces the general case to that one.

## Main results

* `AlgebraicGeometry.Space.neighborhoodStalkMap_germ_top`: the germ at the marked point of a
  global section moves along a morphism of elementary étale neighbourhoods.
* `PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing_naturality`: the map from global
  sections into the henselian local ring is compatible with every morphism of elementary étale
  neighbourhoods.
* `AlgebraicGeometry.Space.PrimeDivisor.neighborhoodTotalFractionRingToGeneric_pullback_eq`: the
  canonical map of Stacks 0ENK is computed on any affine elementary étale neighbourhood of the
  generic point of the prime divisor.

## References

* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The pullback of rational functions to an affine chart depends on the chart morphism only
through the morphism itself. -/
theorem rationalFunctionsToTotalFractionRing_congr (W : BigFppfOver B S hS)
    [IsAffine W.left.1] [IsReduced W.left.1] [IsLocallyNoetherian W.left.1]
    {c c' : yoneda.obj W ⟶ X} (h : c = c') (hc : IsEtale B S hS c) (hc' : IsEtale B S hS c')
    (f : rationalFunctions B S hS hX) :
    rationalFunctionsToTotalFractionRing B S hS hX W c hc f =
      rationalFunctionsToTotalFractionRing B S hS hX W c' hc' f := by
  subst h; rfl

variable (x : points B S hS X)

/-- The germ at the marked point of a global section of an elementary étale neighbourhood moves
along a morphism of neighbourhoods by restriction of global sections. -/
theorem neighborhoodStalkMap_germ_top
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
    (s : Γ(U.scheme.left.1, ⊤)) :
    neighborhoodStalkMap B S hS X hX x f
        (U.scheme.left.1.presheaf.germ ⊤ U.point trivial s) =
      V.scheme.left.1.presheaf.germ ⊤ V.point trivial (f.hom.left.1.appTop s) := by
  have hpoint : f.hom.left.1 V.point ⤳ U.point := by
    simpa only [f.map_point] using specializes_refl U.point
  calc neighborhoodStalkMap B S hS X hX x f
        (U.scheme.left.1.presheaf.germ ⊤ U.point trivial s)
      = f.hom.left.1.stalkMap V.point
          (U.scheme.left.1.presheaf.germ ⊤ (f.hom.left.1 V.point) trivial s) := by
        dsimp [neighborhoodStalkMap]
        rw [TopCat.Presheaf.stalkCongr_hom]
        congr 1
        simpa only [ConcreteCategory.comp_apply] using
          ConcreteCategory.congr_hom
            (U.scheme.left.1.presheaf.germ_stalkSpecializes
              (U := (⊤ : U.scheme.left.1.Opens)) trivial hpoint) s
    _ = V.scheme.left.1.presheaf.germ ⊤ V.point trivial (f.hom.left.1.appTop s) :=
        Scheme.Hom.germ_stalkMap_apply (f := f.hom.left.1) ⊤ V.point trivial s

variable (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

/-- **Stacks 0EMY.** The map from the global sections of an elementary étale neighbourhood of
the generic point of a prime divisor into the henselian local ring there is compatible with
every morphism of neighbourhoods. -/
@[stacks 0EMY "naturality in the neighbourhood of the map from global sections into the \
  henselian local ring"]
theorem PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing_naturality
    {V U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)} (f : V ⟶ U)
    (a : Γ(U.scheme.left.1, ⊤)) :
    Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec V (f.hom.left.1.appTop a) =
      Z.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX hdec U a := by
  have hnat := RingHom.congr_fun
    (stalkToHenselianLocalRing_naturality B S hS X hX (Z.genericPoint B S hS X) hdec f)
    (U.scheme.left.1.presheaf.germ ⊤ U.point trivial a)
  rw [PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing,
    PrimeDivisor.neighborhoodSectionsToGenericHenselianLocalRing, RingHom.comp_apply,
    RingHom.comp_apply, ← neighborhoodStalkMap_germ_top B S hS hX (Z.genericPoint B S hS X) f a]
  rwa [RingHom.comp_apply] at hnat

/-- The pullback of a rational function to an affine elementary étale neighbourhood of the
generic point of a prime divisor, pushed into the total ring of fractions of the henselian local
ring, is unchanged by refining the neighbourhood. -/
theorem PrimeDivisor.neighborhoodTotalFractionRingToGeneric_comp_eq
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    {V U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)} (f : V ⟶ U)
    [IsAffine U.scheme.left.1] [IsReduced U.scheme.left.1]
    [IsLocallyNoetherian U.scheme.left.1] [IsAffine V.scheme.left.1]
    [IsReduced V.scheme.left.1] [IsLocallyNoetherian V.scheme.left.1]
    (r : rationalFunctions B S hS hX) :
    Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec V
        (rationalFunctionsToTotalFractionRing B S hS hX V.scheme V.toSpace V.etale_toSpace r) =
      Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U
        (rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace
          U.etale_toSpace r) := by
  have hetale : IsEtale B S hS (yoneda.map f.hom ≫ U.toSpace) := by
    rw [f.over]; exact V.etale_toSpace
  rw [← rationalFunctionsToTotalFractionRing_congr B S hS hX V.scheme f.over hetale
    V.etale_toSpace r]
  refine rationalFunctionsToTotalFractionRing_comp_eq B S hS hX f.hom U.etale_toSpace hetale
    (Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U)
    (Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec V) (fun a => ?_) r
  rw [PrimeDivisor.neighborhoodTotalFractionRingToGeneric,
    PrimeDivisor.neighborhoodTotalFractionRingToGeneric,
    IsLocalization.map_eq, IsLocalization.map_eq]
  exact congrArg _
    (Z.neighborhoodSectionsToGenericHenselianLocalRing_naturality B S hS hX hdec f a).symm

/-- **Stacks 0ENK, computed on an arbitrary affine chart.** The canonical map from the function
field of a decent, locally Noetherian, integral algebraic space into the total ring of fractions
of the henselian local ring at the generic point of a prime divisor is computed on *any* affine
elementary étale neighbourhood of that generic point, not only on the chart of Stacks 0BBP which
defines it. -/
@[stacks 0ENK "independence of the canonical map R(X) → Q(𝒪^h_{X, ξ}) of the affine elementary \
  étale neighbourhood used to compute it -- a verification the source omits"]
theorem PrimeDivisor.neighborhoodTotalFractionRingToGeneric_pullback_eq
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    [IsAffine U.scheme.left.1] [IsReduced U.scheme.left.1]
    [IsLocallyNoetherian U.scheme.left.1]
    (r : rationalFunctions B S hS hX) :
    Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec U
        (rationalFunctionsToTotalFractionRing B S hS hX U.scheme U.toSpace U.etale_toSpace r) =
      Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN r := by
  have := Z.isLocallyNoetherian_chart B S hS hX hN (Z.genericChart B S hS hX hdec)
  have := Z.isReduced_chart B S hS hX hInt (Z.genericChart B S hS hX hdec)
  obtain ⟨T, a, b, _⟩ := ElementaryEtaleNeighborhood.exists_affine_cone_objs B S hS X hX
    (Z.genericPoint B S hS X) U (Z.genericChart B S hS hX hdec)
  have := Z.isLocallyNoetherian_chart B S hS hX hN T
  have := Z.isReduced_chart B S hS hX hInt T
  have hgen : Z.neighborhoodTotalFractionRingToGeneric B S hS hX hdec
      (Z.genericChart B S hS hX hdec)
      (rationalFunctionsToTotalFractionRing B S hS hX (Z.genericChart B S hS hX hdec).scheme
        (Z.genericChart B S hS hX hdec).toSpace
        (Z.genericChart B S hS hX hdec).etale_toSpace r) =
      Z.rationalFunctionsToGenericTotalFractionRing B S hS hX hdec hInt hN r := rfl
  rw [← hgen, ← Z.neighborhoodTotalFractionRingToGeneric_comp_eq B S hS hX hdec a r,
    ← Z.neighborhoodTotalFractionRingToGeneric_comp_eq B S hS hX hdec b r]

end AlgebraicGeometry.Space

end
