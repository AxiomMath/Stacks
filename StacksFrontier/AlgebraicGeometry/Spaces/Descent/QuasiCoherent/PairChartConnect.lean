module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSitePresheaf

/-!
# A chart of a pairwise fibre product as the test space of an arrow of the member site

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`.  A chart `Z` of the pairwise fibre product `Y i ×_X Y j`
induces two charts of `X`: push `Z` to a chart of `Y i` along the first projection and then to
`X` along `f i`, or push it to a chart of `Y j` along the second projection and then to `X`
along `f j`.  The two have the same underlying object of the big fppf site of `S`, and their
structure morphisms to `X` agree because the two projections of the fibre product do, so the
identity of that object is a morphism of charts of `X` from the second to the first.

That morphism is `AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect`, and the test
space attached to it by `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartPair` is the
chart space of `Z` with its own structure morphism to `Y i ×_X Y j`.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect` is the morphism of charts of
  `X` relating the two charts a chart of the pairwise fibre product induces, carrying the
  identity of the underlying object of the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.eq_id_comp`: a morphism equal to an identity is a
  left unit for composition.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.chartToSpace_smallEtalePostcomp`: the structure
  morphism of a chart pushed forward along an étale morphism is the structure morphism of the
  chart followed by that morphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pairChartConnect_hom_left` and
  `.chartMap_pairChartConnect`: the morphism of the big fppf site of `S` underlying the
  connecting morphism of charts is the identity, and so is the morphism of represented
  algebraic spaces it induces.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.chartToSpace_comp_pairFst` and
  `.chartToSpace_comp_pairSnd`: the two projections of the structure morphism of a chart of the
  pairwise fibre product, read as the two legs of the test space of the connecting morphism.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberChartPair_pairChartConnect`: the test space
  of the connecting morphism is the chart space of the chart of the pairwise fibre product, with
  its own structure morphism.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

/-! ### Two pieces of elementary algebra -/

/-- A morphism of a category equal to an identity is a left unit for composition. -/
theorem eq_id_comp {C₀ : Type*} [Category C₀] {A T : C₀} {m : A ⟶ A} (hm : m = 𝟙 A)
    (c : A ⟶ T) : m ≫ c = c :=
  (congrArg (fun q => q ≫ c) hm).trans (Category.id_comp c)

/-- The structure morphism of a chart pushed forward along an étale morphism is the structure
morphism of the chart followed by that morphism. -/
theorem chartToSpace_smallEtalePostcomp {Z' Y : AlgebraicSpaces B S hS} (g : Z' ⟶ Y)
    (hg : IsEtale B S hS g.hom) (V : SmallEtale B S hS Z'.1) :
    chartToSpace B S hS Y ((smallEtalePostcomp B S hS g hg).obj V) =
      chartToSpace B S hS Z' V ≫ g :=
  ObjectProperty.hom_ext _ rfl

/-! ### The connecting morphism of charts of a chart of a pairwise fibre product -/

/-- The morphism of charts of `X` relating the two charts that a chart of the pairwise fibre
product `Y i ×_X Y j` induces. Both have the underlying object of the big fppf site of `S`
of the given chart, and their structure morphisms to `X` agree because the two projections of
the fibre product do; the morphism carries the identity of that object. -/
def pairChartConnect {i j : I} (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    (smallEtalePostcomp B S hS (f j) (hf j)).obj
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z) ⟶
      (smallEtalePostcomp B S hS (f i) (hf i)).obj
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z) :=
  ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 _)
    ((SmallEtale.map_id_comp_eq yoneda _).trans
      ((Category.assoc Z.1.hom _ _).trans
        ((congrArg (fun q => Z.1.hom ≫ q)
            (congrArg (fun m => m.hom) (pair_condition B S hS Yi f i j))).trans
          (Category.assoc Z.1.hom _ _).symm))))

/-- The morphism of the big fppf site of `S` underlying the connecting morphism is the
identity. -/
theorem pairChartConnect_hom_left {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    (pairChartConnect B S hS Yi f hf Z).hom.left = 𝟙 _ :=
  rfl

/-- The morphism of represented algebraic spaces induced by the connecting morphism is the
identity of the chart space of the chart of the pairwise fibre product. -/
theorem chartMap_pairChartConnect {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    chartMap B S hS X (pairChartConnect B S hS Yi f hf Z) =
      𝟙 (chartSpace B S hS (pair B S hS Yi f i j) Z) :=
  ObjectProperty.hom_ext _
    ((congrArg (fun m => yoneda.map m) (pairChartConnect_hom_left B S hS Yi f hf Z)).trans
      (yoneda.map_id _))

/-! ### The test space of the connecting morphism -/

/-- The structure morphism of a chart of the pairwise fibre product followed by the first
projection is the morphism to the target member of the test space of the connecting morphism. -/
theorem chartToSpace_comp_pairFst {i j : I} (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    chartToSpace B S hS (pair B S hS Yi f i j) Z ≫ pairFst B S hS Yi f i j =
      memberChartMap B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (pairChartConnect B S hS Yi f hf Z) :=
  (chartToSpace_smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
        (isEtale_pairFst B S hS Yi f hf i j) Z).symm.trans
    (eq_id_comp (chartMap_pairChartConnect B S hS Yi f hf Z) _).symm

/-- The structure morphism of a chart of the pairwise fibre product followed by the second
projection is the morphism to the target member of the test space of an identity morphism of the
site of the charts of the members. -/
theorem chartToSpace_comp_pairSnd {i j : I} (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    chartToSpace B S hS (pair B S hS Yi f i j) Z ≫ pairSnd B S hS Yi f i j =
      memberChartMap B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (𝟙 ((smallEtalePostcomp B S hS (f j) (hf j)).obj
          ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
            (isEtale_pairSnd B S hS Yi f hf i j)).obj Z))) :=
  (chartToSpace_smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j) Z).symm.trans
    (chartToSpace_eq_memberChartMap B S hS Yi f hf
      ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j)).obj Z) _ rfl)

/-- The test space of the connecting morphism of a chart of the pairwise fibre product is that
chart's own chart space, with its own structure morphism to `Y i ×_X Y j`. -/
theorem memberChartPair_pairChartConnect {i j : I}
    (Z : SmallEtale B S hS (pair B S hS Yi f i j).1) :
    memberChartPair B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (pairChartConnect B S hS Yi f hf Z) =
      chartToSpace B S hS (pair B S hS Yi f i j) Z :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)).hom_ext
    ((memberChartPair_fst B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (pairChartConnect B S hS Yi f hf Z)).trans
      (chartToSpace_comp_pairFst B S hS Yi f hf Z).symm)
    ((memberChartPair_snd B S hS Yi f hf
        ((smallEtalePostcomp B S hS (pairFst B S hS Yi f i j)
          (isEtale_pairFst B S hS Yi f hf i j)).obj Z)
        ((smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
          (isEtale_pairSnd B S hS Yi f hf i j)).obj Z)
        (pairChartConnect B S hS Yi f hf Z)).trans
      (chartToSpace_smallEtalePostcomp B S hS (pairSnd B S hS Yi f i j)
        (isEtale_pairSnd B S hS Yi f hf i j) Z))

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
