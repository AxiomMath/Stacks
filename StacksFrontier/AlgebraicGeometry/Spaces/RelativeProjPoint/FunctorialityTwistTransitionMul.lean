module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationDatum
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistMul

/-!
# The transitions of the twists of a relative Proj are multiplicative

In Situation 0849 the comparison `y^*𝒪_{U ×_X P}(n) ≅ 𝒪_{V ×_X P}(n)` of the twists of Stacks 01NR
along a morphism `y` of base changes lying over `k : V ⟶ U`
(`AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison`) is the degree-`n` piece of
one isomorphism of sheaves of graded algebras `y^*(⨁_n 𝒪(n)) ≅ ⨁_n 𝒪(n)` on the scheme of
`V ×_X P`.  Hence the comparisons, and the scheme transitions
`AlgebraicGeometry.Space.RelativeProjSituation.twistTransition` of the twists along a presentation
`P = P_U/P_R`, preserve products of homogeneous local sections.  This is the scheme-level input for
the multiplicativity of the map `θ` of Stacks 085F.

The declarations live in the namespace `AlgebraicGeometry.Space.C1359Bridge`: they are the minimal
scheme-level helpers that the descent of the multiplication of the twists needs here.

## Main definitions

* `AlgebraicGeometry.Space.C1359Bridge.twistComparisonAlgebraIso`: the comparison of the twists
  along a morphism of base changes, as an isomorphism of sheaves of graded algebras, the comparison
  `AlgebraicGeometry.Space.pullbackGradedAlgebraIsoOfSquare` along the square of
  `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`.
* `AlgebraicGeometry.Space.C1359Bridge.twistTransitionAlgebraIso`: the transition of the twists
  along a presentation, as an isomorphism of sheaves of graded algebras.

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.map_mul_of_eq_app`: degreewise morphisms equal to the
  components of a homomorphism of sheaves of graded algebras are multiplicative.
* `AlgebraicGeometry.Space.C1359Bridge.twistTransition_eq_comp`: the transition of the twists is
  the comparison along the target projection followed by the inverse of the one along the source.
* `AlgebraicGeometry.Space.C1359Bridge.twistPieceComparison_hom_hom_eq_app`: the comparison of the
  twists `𝒪(n)` is the degree-`n` piece of `…twistComparisonAlgebraIso`.
* `AlgebraicGeometry.Space.C1359Bridge.twistPieceComparison_map_mul`: the comparisons of the twists
  preserve products of homogeneous local sections.
* `AlgebraicGeometry.Space.C1359Bridge.twistTransition_hom_eq_app` and
  `AlgebraicGeometry.Space.C1359Bridge.twistTransition_map_mul`: the transitions of the twists are
  the pieces of an isomorphism of sheaves of graded algebras, hence multiplicative.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp
open Stacks.AlgebraicGeometry.RelativeProjTwists (SchemeGradedAlgebra)
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra)

universe u m t a v₁ u₁

namespace AlgebraicGeometry.Space.C1359Bridge

section Generic

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : SheafOfModules.GradedAlgebra.{t, a} R}

/-- Degreewise morphisms which are the components of a homomorphism of sheaves of graded algebras
preserve products of homogeneous local sections. -/
theorem map_mul_of_eq_app (φ : A ⟶ B) (f : ∀ n, A.piece n ⟶ B.piece n)
    (hf : ∀ n, f n = φ.app n) (i j : ℤ) (U : Cᵒᵖ) (x : (A.piece i).val.obj U)
    (y : (A.piece j).val.obj U) :
    (f (i + j)).val.app U ((A.mul i j).app U x y) =
      (B.mul i j).app U ((f i).val.app U x) ((f j).val.app U y) := by
  rw [hf, hf, hf]
  exact φ.map_mul i j U x y

/-- A composite of components of two isomorphisms of sheaves of graded algebras is the component
of the composite with the inverse. -/
theorem comp_eq_app_trans_symm {D : SheafOfModules.GradedAlgebra.{t, a} R} (φ : A ≅ B)
    (ψ : D ≅ B) {n : ℤ} (f : A.piece n ⟶ B.piece n) (g : B.piece n ⟶ D.piece n)
    (hf : f = φ.hom.app n) (hg : g = ψ.inv.app n) : f ≫ g = (φ ≪≫ ψ.symm).hom.app n := by
  subst hf hg
  rfl

/-- The underlying morphism of a morphism of a full subcategory which is a composite. -/
theorem hom_eq_comp_hom_of_eq {𝒞 : Type*} [Category 𝒞] {P : ObjectProperty 𝒞}
    {x y z : P.FullSubcategory} (f : x ⟶ y) (g : y ⟶ z) (h : x ⟶ z) (hh : h = f ≫ g) :
    h.hom = f.hom ≫ g.hom := by
  subst hh
  rfl

end Generic

section Square

variable {X' X Y' Y : Scheme.{u}} (ιX : X' ⟶ X) (ιY : Y' ⟶ Y) (y : Y' ⟶ X') (pc : Y ⟶ X)
  (e : y ≫ ιX = ιY ≫ pc) {G : SchemeGradedAlgebra X} {N : SchemeGradedAlgebra Y}
  (T : pbAlgS pc G ≅ N)

/-- The inverse of the comparison `AlgebraicGeometry.Space.pullbackGradedAlgebraIsoOfSquare` along
a square of sheaves of graded algebras is, in degree `n`, the inverse of the comparison along the
square of the degree-`n` pieces. -/
theorem _root_.AlgebraicGeometry.Space.pullbackGradedAlgebraIsoOfSquare_inv_app (n : ℤ) :
    (pullbackGradedAlgebraIsoOfSquare ιX ιY y pc e T).inv.app n =
      (pullbackSheafIsoOfSquare ιX ιY y pc e (gradedPieceIso pc T n)).inv :=
  rfl

end Square

section Twist

variable (s : RelativeProjSituation.{u, m}) {U V : BigFppfOver s.site s.base s.containsBase}
  {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} (k : V ⟶ U)
  (hv : yoneda.map k ≫ u = v)
  (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
  (hy : s.relativeProjPoints.LiesOver y k)

/-- **The comparison of the twists along a morphism of base changes, as an isomorphism of sheaves
of graded algebras**: `y^*(⨁_n 𝒪_{U ×_X P}(n)) ≅ ⨁_n 𝒪_{V ×_X P}(n)` for `y` lying over `k`. -/
def twistComparisonAlgebraIso :
    pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (pbAlgS (s.toRelativeProj U u) (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u))) ≅
      pbAlgS (s.toRelativeProj V v) (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v)) :=
  pullbackGradedAlgebraIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y) (s.map_comp_toRelativeProj y)
    (s.pointTwistComparison k u v hv ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_eq_of_liesOver hv hy))

private theorem twistComparisonAlgebraIso_hom_app (n : ℤ) :
    (twistComparisonAlgebraIso s k hv y hy).hom.app n =
      (pullbackSheafIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.map_comp_toRelativeProj y)
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
          (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.pointTwistComparison k u v hv
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.toScheme_map_eq_of_liesOver hv hy)) n)).hom :=
  (pullbackGradedAlgebraIsoOfSquare_hom_app _ _ _ _ _ _ n).trans
    (pullbackSheafIsoOfSquare_hom _ _ _ _ _ _).symm

private theorem twistComparisonAlgebraIso_inv_app (n : ℤ) :
    (twistComparisonAlgebraIso s k hv y hy).inv.app n =
      (pullbackSheafIsoOfSquare (s.toRelativeProj U u) (s.toRelativeProj V v)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.map_comp_toRelativeProj y)
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
          (Y := (relativeProj (s.shrink.pointAlgebra V v)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.pointTwistComparison k u v hv
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.toScheme_map_eq_of_liesOver hv hy)) n)).inv :=
  pullbackGradedAlgebraIsoOfSquare_inv_app _ _ _ _ _ _ n

/-- **The comparison of the twists `𝒪(n)` is the degree-`n` piece of the comparison of sheaves of
graded algebras.** -/
theorem twistPieceComparison_hom_hom_eq_app (n : ℤ) :
    (s.twistPieceComparison k hv y hy n).hom.hom =
      (twistComparisonAlgebraIso s k hv y hy).hom.app n :=
  (s.twistPieceComparison_hom_hom k hv y hy n).trans
    (twistComparisonAlgebraIso_hom_app s k hv y hy n).symm

/-- The inverse of the comparison of the twists `𝒪(n)` is the degree-`n` piece of the inverse of
the comparison of sheaves of graded algebras. -/
theorem twistPieceComparison_inv_hom_eq_app (n : ℤ) :
    (s.twistPieceComparison k hv y hy n).inv.hom =
      (twistComparisonAlgebraIso s k hv y hy).inv.app n :=
  (rfl : _ = (s.twistPieceSheafIso k hv y hy n).inv).trans
    (twistComparisonAlgebraIso_inv_app s k hv y hy n).symm

/-- **The comparisons of the twists are multiplicative**: they preserve products of homogeneous
local sections of `y^*(⨁_n 𝒪(n))`. -/
theorem twistPieceComparison_map_mul (i j : ℤ)
    (W : (TopologicalSpace.Opens ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      (s.relativeProjPoints.fibre V v)).carrier)ᵒᵖ)
    (a : ((pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (pbAlgS (s.toRelativeProj U u)
        (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)))).piece i).val.obj W)
    (b : ((pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (pbAlgS (s.toRelativeProj U u)
        (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)))).piece j).val.obj W) :
    (s.twistPieceComparison k hv y hy (i + j)).hom.hom.val.app W
        (((pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (pbAlgS (s.toRelativeProj U u)
            (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra U u)))).mul i j).app W a b) =
      ((pbAlgS (s.toRelativeProj V v)
          (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra V v))).mul i j).app W
        ((s.twistPieceComparison k hv y hy i).hom.hom.val.app W a)
        ((s.twistPieceComparison k hv y hy j).hom.hom.val.app W b) :=
  map_mul_of_eq_app (twistComparisonAlgebraIso s k hv y hy).hom
    (fun n => (s.twistPieceComparison k hv y hy n).hom.hom)
    (twistPieceComparison_hom_hom_eq_app s k hv y hy) i j W a b

end Twist

section Transition

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

/-- **The transition of the twists along a presentation `P = P_U/P_R`, as an isomorphism of sheaves
of graded algebras** on the scheme of `P_R`: the comparison along the target projection followed by
the inverse of the comparison along the source projection. -/
def twistTransitionAlgebraIso :
    pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
        (pbAlgS (s.toRelativeProj Px.U Px.toSpace)
          (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra Px.U Px.toSpace))) ≅
      pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
        (pbAlgS (s.toRelativeProj Px.U Px.toSpace)
          (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra Px.U Px.toSpace))) :=
  twistComparisonAlgebraIso s (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.target rfl (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor) ≪≫
    (twistComparisonAlgebraIso s (u := Px.toSpace) (v := RelativeProjPoints.relationPoint Px)
      Px.source (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)).symm

/-- **The transition of the twists `𝒪(n)` is, by definition, the comparison along the target
projection followed by the inverse of the comparison along the source projection.** -/
theorem twistTransition_eq_comp (n : ℤ) :
    s.twistTransition Px n =
      (s.twistPieceComparison (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.target rfl
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceTarget Px
          s.isAlgebraicSpace_relativeProjFunctor) n).hom ≫
      (s.twistPieceComparison (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceSource Px
          s.isAlgebraicSpace_relativeProjFunctor) n).inv :=
  rfl

private theorem twistTransition_hom_eq_comp (n : ℤ) :
    (s.twistTransition Px n).hom =
      (s.twistPieceComparison (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.target rfl
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceTarget Px
          s.isAlgebraicSpace_relativeProjFunctor) n).hom.hom ≫
      (s.twistPieceComparison (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceSource Px
          s.isAlgebraicSpace_relativeProjFunctor) n).inv.hom :=
  hom_eq_comp_hom_of_eq
    (s.twistPieceComparison (u := Px.toSpace)
      (v := RelativeProjPoints.relationPoint Px) Px.target rfl
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor) n).hom
    (s.twistPieceComparison (u := Px.toSpace)
      (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor) n).inv
    (s.twistTransition Px n) (twistTransition_eq_comp s Px n)

private theorem twistTransition_comp_eq_app (n : ℤ) :
    (s.twistPieceComparison (u := Px.toSpace)
      (v := RelativeProjPoints.relationPoint Px) Px.target rfl
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px
        s.isAlgebraicSpace_relativeProjFunctor) n).hom.hom ≫
      (s.twistPieceComparison (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceSource Px
          s.isAlgebraicSpace_relativeProjFunctor) n).inv.hom =
      ((twistComparisonAlgebraIso s (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.target rfl
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)) ≪≫
      (twistComparisonAlgebraIso s (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceSource Px
          s.isAlgebraicSpace_relativeProjFunctor)).symm).hom.app n :=
  comp_eq_app_trans_symm
    (twistComparisonAlgebraIso s (u := Px.toSpace)
      (v := RelativeProjPoints.relationPoint Px) Px.target rfl
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
    (twistComparisonAlgebraIso s (u := Px.toSpace)
      (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)) _ _
    (twistPieceComparison_hom_hom_eq_app s (u := Px.toSpace)
      (v := RelativeProjPoints.relationPoint Px) Px.target rfl
      (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor) n)
    (twistPieceComparison_inv_hom_eq_app s (u := Px.toSpace)
      (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
      (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
      (s.relativeProjPoints.liesOver_spaceSource Px s.isAlgebraicSpace_relativeProjFunctor) n)

private theorem twistTransitionAlgebraIso_eq :
    twistTransitionAlgebraIso s Px =
      (twistComparisonAlgebraIso s (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.target rfl
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)) ≪≫
      (twistComparisonAlgebraIso s (u := Px.toSpace)
        (v := RelativeProjPoints.relationPoint Px) Px.source (s.map_source_comp_toSpace Px)
        (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.relativeProjPoints.liesOver_spaceSource Px
          s.isAlgebraicSpace_relativeProjFunctor)).symm :=
  rfl

/-- **The transition of the twists `𝒪(n)` is the degree-`n` piece of the transition of sheaves of
graded algebras.** -/
theorem twistTransition_hom_eq_app (n : ℤ) :
    (s.twistTransition Px n).hom = (twistTransitionAlgebraIso s Px).hom.app n :=
  (twistTransition_hom_eq_comp s Px n).trans ((twistTransition_comp_eq_app s Px n).trans
    (congrArg (fun φ => φ.hom.app n) (twistTransitionAlgebraIso_eq s Px).symm))

/-- **The transitions of the twists are multiplicative** (the scheme-level input of Stacks 084D for
the multiplication of `⨁_n 𝒪_P(n)`): on the scheme of `P_R` they preserve products of homogeneous
local sections of `t^*(⨁_n 𝒪(n))`. -/
theorem twistTransition_map_mul (i j : ℤ)
    (W : (TopologicalSpace.Opens ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      (s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))).carrier)ᵒᵖ)
    (a : ((pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
        (pbAlgS (s.toRelativeProj Px.U Px.toSpace)
          (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra Px.U Px.toSpace)))).piece i).val.obj W)
    (b : ((pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map
        (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
        (pbAlgS (s.toRelativeProj Px.U Px.toSpace) (Tag07ZGTwist.twistAlgebra
          (s.shrink.pointAlgebra Px.U Px.toSpace)))).piece j).val.obj W) :
    (s.twistTransition Px (i + j)).hom.val.app W
        (((pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor))
          (pbAlgS (s.toRelativeProj Px.U Px.toSpace)
            (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra Px.U Px.toSpace)))).mul i j).app W
          a b) =
      ((pbAlgS ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor))
          (pbAlgS (s.toRelativeProj Px.U Px.toSpace)
            (Tag07ZGTwist.twistAlgebra (s.shrink.pointAlgebra Px.U Px.toSpace)))).mul i j).app W
        ((s.twistTransition Px i).hom.val.app W a) ((s.twistTransition Px j).hom.val.app W b) :=
  map_mul_of_eq_app (twistTransitionAlgebraIso s Px).hom (fun n => (s.twistTransition Px n).hom)
    (twistTransition_hom_eq_app s Px) i j W a b

end Transition

end AlgebraicGeometry.Space.C1359Bridge

end
