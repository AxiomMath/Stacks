module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# The defining ideal of a reduced closed subspace, on an étale chart

Let `X` be an algebraic space over a scheme `S` and let `T` be a closed subset of the points of
`X`. The reduced closed subspace `AlgebraicGeometry.Space.reducedClosedSubspace` supported on `T`
is built, in `StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean`, by descending the
reduced induced closed subscheme of one surjective étale chart; nothing there computes its
*defining ideal sheaf* of Stacks 03MB on the charts of `X`. That computation is what this file
supplies: over an étale chart `A` of `X` lying over the chart used in the construction, the
defining ideal of the reduced closed subspace is the vanishing ideal, in the sense of
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, of the part of `A` lying over `T`.

Two consequences are drawn, both of them statements about the *ideal sheaves* of the reduced
closed subspaces of two closed sets `T₀, T₁`:

* the defining ideal sheaves intersect in the defining ideal sheaf of the union `T₀ ∪ T₁`;
* when `T₀` and `T₁` are **disjoint** the two defining ideals are comaximal on every affine
  chart, so `1` splits as a sum of a section of each.

## Main results

* `AlgebraicGeometry.Space.comap_atlasVanishingIdeal`: the vanishing ideal of the part of a chart
  lying over `T` pulls back, along a morphism of étale charts, to the vanishing ideal of the part
  of the smaller chart lying over `T`. This is
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_of_etale` together with the
  identification of the two preimages, and it is where étaleness of a morphism of charts is used.
* `AlgebraicGeometry.Space.definingIdealAt_reducedClosedSubspaceOfChart` and
  `AlgebraicGeometry.Space.definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal`: **the defining
  ideal of a reduced closed subspace at an étale chart over the chart of its construction.** The
  first states it as the kernel of pullback of regular functions to the reduced induced closed
  subscheme of the chart, the second — for an *affine* chart — as the ideal of the vanishing
  ideal sheaf at the affine open `⊤`.
* `AlgebraicGeometry.Space.definingIdealSheaf_reducedClosedSubspaceOfChart_inf` and
  `AlgebraicGeometry.Space.definingIdealSheaf_reducedClosedSubspace_inf`: **the defining ideal
  sheaves of the reduced closed subspaces of two closed sets meet in the defining ideal sheaf of
  the reduced closed subspace of their union.**
* `AlgebraicGeometry.Space.sup_definingIdealAt_reducedClosedSubspaceOfChart_of_disjoint` and
  `AlgebraicGeometry.Space.sup_definingIdealAt_reducedClosedSubspace_of_disjoint`: **the defining
  ideals of the reduced closed subspaces of two disjoint closed sets are comaximal on every
  affine étale chart.**

## Implementation notes

The chart formula is obtained from
`AlgebraicGeometry.Space.definingIdealAt_invariantSubspace_subschemeι`, which computes the
defining ideal of the closed subspace cut out by an invariant ideal sheaf `J` on a chart as the
kernel attached to the pullback of `J`. For the reduced closed subspace `J` is
`AlgebraicGeometry.Space.atlasVanishingIdeal`, a vanishing ideal, and the pullback of a vanishing
ideal along an étale morphism is again a vanishing ideal; so the formula becomes a formula about
vanishing ideals, where the lattice identities of
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` apply. That is the only reason the two
consequences come out cheaply: both `⊓` against a union and comaximality against a disjoint set
are Galois-connection identities for `vanishingIdeal` and `support`, and neither is available for
a defining ideal sheaf presented as a kernel.

Both the formula and the consequences are stated for charts admitting a morphism to the chart of
the construction. That is not a restriction on the *consequences*: a sheaf submodule of `𝒪_X` is
determined by its sections over the affine charts lying over a fixed surjective chart, by
`AlgebraicGeometry.Space.structureSubmodule_ext_of_forall_isAffine_hom`, which is how the
intersection formula is proved for the ideal sheaves themselves. It is a restriction on the
formula, which is why the formula is not stated for `AlgebraicGeometry.Space.reducedClosedSubspace`
at an arbitrary chart: the chart of the construction there is chosen from the atlas clause of the
algebraic-space hypothesis, and an arbitrary chart of `X` need not lie over it.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X.obj}

/-! ### The vanishing ideal of the part of a chart lying over a closed set -/

/-- **The vanishing ideal of the part of a chart lying over `T` pulls back to the vanishing ideal
of the part of a smaller chart lying over `T`.**

A morphism of étale charts of `X` is étale on underlying schemes, so the pullback of a vanishing
ideal along it is the vanishing ideal of the preimage,
`AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_of_etale`; and the preimage of the
part of the bigger chart lying over `T` is the part of the smaller chart lying over `T`, because
the morphism of charts commutes with the structure morphisms to `X`. -/
theorem comap_atlasVanishingIdeal
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (T : Set (points B S hS X.obj)) (hT : IsClosed T)
    (A : SmallEtale B S hS X.obj)
    (m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.obj)) :
    (atlasVanishingIdeal B S hS φ T hT).comap
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.obj).map m)) =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨atlasPointSet B S hS A.1.hom T,
          isClosed_atlasPointSet B S hS A.1.hom T hT⟩ : Closeds _) := by
  have _he := etale_toScheme_toOver_map B S hS X.obj m
  refine Scheme.IdealSheafData.comap_vanishingIdeal_of_etale _ _ _ ?_
  ext x
  show x ∈ atlasPointSet B S hS A.1.hom T ↔
    ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.obj).map m)).base x ∈ atlasPointSet B S hS φ T
  rw [mem_atlasPointSet_map_iff B S hS ((SmallEtale.toOver B S hS X.obj).map m) φ T x,
    mem_atlasPointSet_iff]
  exact Iff.of_eq (congrArg (fun ψ => pointsMap B S hS _ ψ _ ∈ T) (CostructuredArrow.w m.1).symm)

/-- The part of a chart lying over a union of two sets of points is the union of the two parts. -/
theorem atlasPointSet_union (ψ : yoneda.obj U ⟶ X.obj) (T₀ T₁ : Set (points B S hS X.obj)) :
    atlasPointSet B S hS ψ (T₀ ∪ T₁) =
      atlasPointSet B S hS ψ T₀ ∪ atlasPointSet B S hS ψ T₁ :=
  rfl

/-- The parts of a chart lying over two disjoint sets of points are disjoint. -/
theorem disjoint_atlasPointSet (ψ : yoneda.obj U ⟶ X.obj) {T₀ T₁ : Set (points B S hS X.obj)}
    (hdisj : Disjoint T₀ T₁) :
    Disjoint (atlasPointSet B S hS ψ T₀) (atlasPointSet B S hS ψ T₁) :=
  Set.disjoint_left.2 fun _ h₀ h₁ => (Set.disjoint_left.1 hdisj) h₀ h₁

/-! ### The defining ideal of a reduced closed subspace on a chart -/

section Chart

variable
    (hs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (he : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)

include hs he in
/-- **The defining ideal of a reduced closed subspace, on a chart lying over the chart of its
construction.**

The reduced closed subspace supported on `T` is cut out by the reduced induced closed subscheme
of the chart `φ` on the part of `φ` lying over `T`, that is, by the vanishing ideal
`AlgebraicGeometry.Space.atlasVanishingIdeal`. So the formula
`AlgebraicGeometry.Space.definingIdealAt_invariantSubspace_subschemeι` applies, and the pullback
of that vanishing ideal to the chart `A` is again a vanishing ideal, by
`AlgebraicGeometry.Space.comap_atlasVanishingIdeal`. -/
theorem definingIdealAt_reducedClosedSubspaceOfChart
    (T : Set (points B S hS X.obj)) (hT : IsClosed T)
    (hZ : IsClosedSubspace B S hS (reducedClosedSubspaceOfChart B S hS φ T hT))
    (A : SmallEtale B S hS X.obj)
    (m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.obj)) :
    definingIdealAt B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T hT, hZ⟩ (op A) =
      RingHom.ker ((Scheme.IdealSheafData.vanishingIdeal
        (⟨atlasPointSet B S hS A.1.hom T,
          isClosed_atlasPointSet B S hS A.1.hom T hT⟩ : Closeds _)).subschemeι.appTop).hom := by
  rw [← comap_atlasVanishingIdeal B S hS X he T hT A m]
  exact definingIdealAt_invariantSubspace_subschemeι B S hS X hs he
    (atlasVanishingIdeal B S hS φ T hT)
    (isInvariantSubscheme_atlasReducedSubscheme B S hS hs he T hT) hZ A m

include hs he in
/-- **The defining ideal of a reduced closed subspace at an affine chart is a vanishing ideal.**
On an affine étale chart `A` lying over the chart of the construction, the defining ideal of the
reduced closed subspace supported on `T` is the ideal which
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` of the part of `A` lying over `T`
attaches to the affine open `⊤`.

This is `AlgebraicGeometry.Space.definingIdealAt_reducedClosedSubspaceOfChart` with the kernel
evaluated by `AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι_app`, which needs the open
to be affine. -/
theorem definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal
    (T : Set (points B S hS X.obj)) (hT : IsClosed T)
    (hZ : IsClosedSubspace B S hS (reducedClosedSubspaceOfChart B S hS φ T hT))
    (A : SmallEtale B S hS X.obj)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.obj).obj A)))
    (m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.obj)) :
    definingIdealAt B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T hT, hZ⟩ (op A) =
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨atlasPointSet B S hS A.1.hom T,
          isClosed_atlasPointSet B S hS A.1.hom T hT⟩ : Closeds _)).ideal
            ⟨⊤, @isAffineOpen_top _ hA⟩ := by
  rw [definingIdealAt_reducedClosedSubspaceOfChart B S hS X hs he T hT hZ A m]
  exact Scheme.IdealSheafData.ker_subschemeι_app _ ⟨⊤, @isAffineOpen_top _ hA⟩

include hs he in
/-- **The defining ideal sheaves of the reduced closed subspaces of two closed sets meet in the
defining ideal sheaf of the reduced closed subspace of their union.**

A sheaf submodule of `𝒪_X` is determined by its sections over the affine charts lying over a
fixed surjective chart, so it is enough to check this at such a chart `A`; there both sides are
ideals of vanishing ideal sheaves on the scheme `A`, by
`AlgebraicGeometry.Space.definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal`, and the identity
is the Galois-connection identity
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_sup`. -/
theorem definingIdealSheaf_reducedClosedSubspaceOfChart_inf
    (T₀ T₁ : Set (points B S hS X.obj)) (hT₀ : IsClosed T₀) (hT₁ : IsClosed T₁)
    (hZ₀ : IsClosedSubspace B S hS (reducedClosedSubspaceOfChart B S hS φ T₀ hT₀))
    (hZ₁ : IsClosedSubspace B S hS (reducedClosedSubspaceOfChart B S hS φ T₁ hT₁))
    (hZ : IsClosedSubspace B S hS
      (reducedClosedSubspaceOfChart B S hS φ (T₀ ∪ T₁) (hT₀.union hT₁))) :
    definingIdealSheaf B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T₀ hT₀, hZ₀⟩ ⊓
        definingIdealSheaf B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T₁ hT₁, hZ₁⟩ =
      definingIdealSheaf B S hS X
        ⟨reducedClosedSubspaceOfChart B S hS φ (T₀ ∪ T₁) (hT₀.union hT₁), hZ⟩ := by
  refine structureSubmodule_ext_of_forall_isAffine_hom B S hS X
    (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U φ).1 hs) _ _
    fun A hA m => ?_
  show definingIdealAt B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T₀ hT₀, hZ₀⟩ (op A) ⊓
      definingIdealAt B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T₁ hT₁, hZ₁⟩ (op A) =
    definingIdealAt B S hS X
      ⟨reducedClosedSubspaceOfChart B S hS φ (T₀ ∪ T₁) (hT₀.union hT₁), hZ⟩ (op A)
  rw [definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal B S hS X hs he T₀ hT₀ hZ₀ A hA m,
    definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal B S hS X hs he T₁ hT₁ hZ₁ A hA m,
    definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal B S hS X hs he (T₀ ∪ T₁)
      (hT₀.union hT₁) hZ A hA m,
    show (⟨atlasPointSet B S hS A.1.hom (T₀ ∪ T₁),
          isClosed_atlasPointSet B S hS A.1.hom (T₀ ∪ T₁) (hT₀.union hT₁)⟩ : Closeds _) =
        (⟨atlasPointSet B S hS A.1.hom T₀,
            isClosed_atlasPointSet B S hS A.1.hom T₀ hT₀⟩ : Closeds _) ⊔
          ⟨atlasPointSet B S hS A.1.hom T₁,
            isClosed_atlasPointSet B S hS A.1.hom T₁ hT₁⟩ from
      Closeds.ext (atlasPointSet_union B S hS X A.1.hom T₀ T₁),
    Scheme.IdealSheafData.vanishingIdeal_sup, Scheme.IdealSheafData.ideal_inf]
  rfl

include hs he in
/-- **The defining ideals of the reduced closed subspaces of two disjoint closed sets are
comaximal on an affine chart.**

The two ideals are the ideals at the affine open `⊤` of the vanishing ideal sheaves of the two
parts of the chart lying over the two sets. Those parts are disjoint, so the support of the join
of the two ideal sheaves — which is the intersection of the supports — is empty, and an ideal
sheaf with empty support is the unit ideal sheaf. Evaluating at `⊤` turns that into the
comaximality asserted. -/
theorem sup_definingIdealAt_reducedClosedSubspaceOfChart_of_disjoint
    (T₀ T₁ : Set (points B S hS X.obj)) (hT₀ : IsClosed T₀) (hT₁ : IsClosed T₁)
    (hdisj : Disjoint T₀ T₁)
    (hZ₀ : IsClosedSubspace B S hS (reducedClosedSubspaceOfChart B S hS φ T₀ hT₀))
    (hZ₁ : IsClosedSubspace B S hS (reducedClosedSubspaceOfChart B S hS φ T₁ hT₁))
    (A : SmallEtale B S hS X.obj)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.obj).obj A)))
    (m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.obj)) :
    definingIdealAt B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T₀ hT₀, hZ₀⟩ (op A) ⊔
        definingIdealAt B S hS X ⟨reducedClosedSubspaceOfChart B S hS φ T₁ hT₁, hZ₁⟩ (op A) =
      ⊤ := by
  rw [definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal B S hS X hs he T₀ hT₀ hZ₀ A hA m,
    definingIdealAt_reducedClosedSubspaceOfChart_eq_ideal B S hS X hs he T₁ hT₁ hZ₁ A hA m]
  have hsup : Scheme.IdealSheafData.vanishingIdeal
        (⟨atlasPointSet B S hS A.1.hom T₀,
          isClosed_atlasPointSet B S hS A.1.hom T₀ hT₀⟩ : Closeds _) ⊔
      Scheme.IdealSheafData.vanishingIdeal
        (⟨atlasPointSet B S hS A.1.hom T₁,
          isClosed_atlasPointSet B S hS A.1.hom T₁ hT₁⟩ : Closeds _) = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_sup]
    refine SetLike.coe_injective ?_
    rw [Closeds.coe_inf, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (disjoint_atlasPointSet B S hS X A.1.hom hdisj).inter_eq
  exact congrArg (fun K : Scheme.IdealSheafData _ => K.ideal ⟨⊤, @isAffineOpen_top _ hA⟩) hsup

end Chart

/-! ### The reduced closed subspace of an algebraic space -/

section Atlas

variable (T₀ T₁ : Set (points B S hS X.obj)) (hT₀ : IsClosed T₀) (hT₁ : IsClosed T₁)

/-- **The defining ideal sheaves of the reduced closed subspaces of two closed sets meet in the
defining ideal sheaf of the reduced closed subspace of their union**, for
`AlgebraicGeometry.Space.reducedClosedSubspace`.

This is `AlgebraicGeometry.Space.definingIdealSheaf_reducedClosedSubspaceOfChart_inf` at the chart
the atlas clause of the algebraic-space hypothesis supplies, which is the chart
`AlgebraicGeometry.Space.reducedClosedSubspace` is built from; the three subspaces are built from
the *same* chart, which is what makes the chart-level statement applicable. -/
theorem definingIdealSheaf_reducedClosedSubspace_inf :
    definingIdealSheaf B S hS X ⟨reducedClosedSubspace B S hS X.obj X.2 T₀ hT₀,
          isClosedSubspace_reducedClosedSubspace B S hS X.obj X.2 T₀ hT₀⟩ ⊓
        definingIdealSheaf B S hS X ⟨reducedClosedSubspace B S hS X.obj X.2 T₁ hT₁,
          isClosedSubspace_reducedClosedSubspace B S hS X.obj X.2 T₁ hT₁⟩ =
      definingIdealSheaf B S hS X
        ⟨reducedClosedSubspace B S hS X.obj X.2 (T₀ ∪ T₁) (hT₀.union hT₁),
          isClosedSubspace_reducedClosedSubspace B S hS X.obj X.2 (T₀ ∪ T₁) (hT₀.union hT₁)⟩ :=
  definingIdealSheaf_reducedClosedSubspaceOfChart_inf B S hS X
    (Classical.choose_spec (Classical.choose_spec X.2.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec X.2.exists_atlas)).2 T₀ T₁ hT₀ hT₁ _ _ _

/-- **The defining ideals of the reduced closed subspaces of two disjoint closed sets are
comaximal on an affine chart lying over the chart of the atlas**, for
`AlgebraicGeometry.Space.reducedClosedSubspace`.

This is `AlgebraicGeometry.Space.sup_definingIdealAt_reducedClosedSubspaceOfChart_of_disjoint` at
the chart the atlas clause of the algebraic-space hypothesis supplies. -/
theorem sup_definingIdealAt_reducedClosedSubspace_of_disjoint (hdisj : Disjoint T₀ T₁)
    (A : SmallEtale B S hS X.obj)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.obj).obj A)))
    (m : A ⟶ (⟨CostructuredArrow.mk (Classical.choose
      (Classical.choose_spec X.2.exists_atlas)),
      (Classical.choose_spec (Classical.choose_spec X.2.exists_atlas)).2⟩ :
        SmallEtale B S hS X.obj)) :
    definingIdealAt B S hS X ⟨reducedClosedSubspace B S hS X.obj X.2 T₀ hT₀,
          isClosedSubspace_reducedClosedSubspace B S hS X.obj X.2 T₀ hT₀⟩ (op A) ⊔
        definingIdealAt B S hS X ⟨reducedClosedSubspace B S hS X.obj X.2 T₁ hT₁,
          isClosedSubspace_reducedClosedSubspace B S hS X.obj X.2 T₁ hT₁⟩ (op A) =
      ⊤ :=
  sup_definingIdealAt_reducedClosedSubspaceOfChart_of_disjoint B S hS X
    (Classical.choose_spec (Classical.choose_spec X.2.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec X.2.exists_atlas)).2 T₀ T₁ hT₀ hT₁ hdisj _ _
    A hA m

end Atlas

end AlgebraicGeometry.Space

end
