module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria

/-!
# A closed subspace as the inverse limit of a directed family of closed subspaces

Let `Y` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`X ⊆ Y` be a closed subspace.  Stacks 0A0U writes `X` as a directed inverse limit of closed
subspaces of `Y` which are of finite presentation over `Y`.  This file proves the geometric
assertion that statement rests on — **a directed family of closed subspaces of `Y` whose
chartwise ideal sheaves have supremum the chartwise ideal sheaf of `X` has `X` as its inverse
limit**, with closed immersions for the transition morphisms of the system and for the
projections out of `X` — and then produces the family itself from a monotone family of invariant
sheaves of ideals on one surjective étale scheme chart of `Y`, which is Stacks 0829 for the
ideal sheaf of `X` read on that chart.

The *chartwise ideal sheaf* `AlgebraicGeometry.Space.etaleChartKer` of a closed subspace `Z ⊆ Y`
at an étale scheme chart `U` of `Y` is the ideal sheaf on the scheme `U` of the closed
immersion of schemes `Z ×_Y U ⟶ U`.  A sheaf of ideals on a chart is *invariant* when its two
inverse images along the two legs of the relation `R = U ×_Y U` agree; that is the condition
under which it cuts out a closed subspace of `Y` rather than merely of the chart.

## Main definitions

* `AlgebraicGeometry.Space.etaleChartKer` is the ideal sheaf cut out on an étale scheme chart of
  `Y` by a closed subspace of `Y`.
* `AlgebraicGeometry.Space.closedSubspaceDiagram` is the inverse system of an antitone family
  of subfunctors, and `AlgebraicGeometry.Space.closedSubspaceCone` the cone over it whose
  vertex is a subfunctor contained in every member.
* `AlgebraicGeometry.Space.ClosedSubspaceApproximation` is the conclusion of Stacks 0A0U as
  data — a directed family of closed subspaces of `Y`, each of finite presentation over `Y`,
  with `X` as its inverse limit — and
  `AlgebraicGeometry.Space.HasClosedSubspaceApproximation` the corresponding proposition.
* `AlgebraicGeometry.Space.chartOfSurjectiveEtale` is a surjective étale morphism out of a
  representable object, read as an object of the small étale site of `Y`.
* `AlgebraicGeometry.Space.invariantStage` is the closed subspace of `Y` cut out by one member
  of a family of invariant sheaves of ideals on such a chart, and
  `AlgebraicGeometry.Space.closedSubspaceApproximationOfInvariantIdeals` the approximation of
  `X` those subspaces form.

## Main results

* `AlgebraicGeometry.Space.subfunctor_eq_iInf_of_etaleChartKer_eq_iSup`: a closed subspace whose
  chartwise ideal sheaves are the supremum of those of a family of closed subspaces is the
  intersection of that family.
* `AlgebraicGeometry.Space.isLimitClosedSubspaceCone`: the cone over an antitone family of
  subfunctors with vertex their intersection is a limiting cone, for a directed index with a
  chosen element.
* `AlgebraicGeometry.Space.isLimitClosedSubspaceConeOfEtaleChartKer`: the two combined — **the
  geometric assertion of Stacks 0A0U.**  A directed family of closed subspaces of `Y` whose
  chartwise ideal sheaves have supremum those of `X` has `X` as its inverse limit.
* `AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceDiagram_map` and
  `AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceCone_π`: the transition morphisms of
  the system and the projections out of its limit are closed immersions, because the inclusion
  of a closed subspace of `Y` into a larger subfunctor of `Y` is one.
* `AlgebraicGeometry.Space.ClosedSubspaceApproximation.ofEtaleChartKer` assembles the above into
  the conclusion of Stacks 0A0U, given the family and the finite presentation of its stages.
* `AlgebraicGeometry.Space.le_of_etaleChartKer_le_of_chart`,
  `AlgebraicGeometry.Space.iInf_le_of_etaleChartKer_le_iSup_of_chart` and
  `AlgebraicGeometry.Space.subfunctor_eq_iInf_of_etaleChartKer_eq_iSup_of_chart`: the same
  comparisons of closed subspaces, tested at a single *surjective* étale chart instead of at
  every chart.
* `AlgebraicGeometry.Space.etaleChartKer_invariantSubspace_subschemeι`: the chart ideal of the
  closed subspace cut out by an invariant sheaf of ideals `J` on a surjective étale chart is,
  at any chart lying over it, the pullback of `J`.
* `AlgebraicGeometry.Space.invariantStage_antitone`: a monotone family of invariant sheaves of
  ideals cuts out an antitone family of closed subspaces.
* `AlgebraicGeometry.Space.hasClosedSubspaceApproximation_of_invariantIdeals` is
  **Stacks 0A0U**: a closed subspace `X ⊆ Y` is the directed inverse limit of closed subspaces
  of `Y` of finite presentation, given a monotone family of invariant sheaves of ideals on a
  surjective étale scheme chart of `Y` whose supremum is the ideal sheaf cut out by `X` and
  each of which cuts out a closed subspace of finite presentation.

## Implementation notes

The index is an arbitrary directed preorder together with a *chosen element*, exactly as in
Situation 084R, `AlgebraicGeometry.Space.LimitSituation`.  The chosen element is what the
limiting cone is built from — the mediating morphism out of an arbitrary cone is the morphism
to `Y` that its leg at that index induces — and taking it as an argument rather than as a
`Nonempty` instance keeps the construction choice-free.  Directedness is used only to know
that all the legs of a cone induce the *same* morphism to `Y`; the identification of `X` with
the intersection of the family needs neither directedness nor a chosen index.

`AlgebraicGeometry.Space.closedSubspaceDiagram` and
`AlgebraicGeometry.Space.closedSubspaceCone` are reducible, so that the structure projections
of the diagram and of the cone agree syntactically with `CategoryTheory.Subfunctor.homOfLe`;
the rewriting in the proofs of the limit properties is by `CategoryTheory.Subfunctor.homOfLe_ι`
and goes through only at that transparency.

The approximating family is the hypothesis of
`AlgebraicGeometry.Space.hasClosedSubspaceApproximation_of_invariantIdeals`, and it is the one
step of the source's proof that this tree cannot yet take.  The source produces it from the
ideal sheaf `𝓘 ⊆ 𝒪_Y` cutting out `X`: Stacks 0829 writes `𝓘` as the filtered colimit of its
finite type quasi-coherent submodules `𝓘_i`, Stacks 03MB turns each `𝓘_i` into a closed subspace
`V(𝓘_i)`, and Stacks 084Q makes each `V(𝓘_i) ⟶ Y` of finite presentation.  Of those three the
second is available — `AlgebraicGeometry.Space.isClosedSubspace_invariantSubspace_subschemeι`
cuts out a closed subspace from an invariant sheaf of ideals on a chart, and
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts` does it for
a sheaf of ideals on the small étale site which is cartesian on affine charts — and it is what
the hypothesis is phrased through.  The other two are not: Stacks 0829, in
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeQuasicoherentSubobjects.lean`, carries the
forward implication of Descent, Proposition 03DX(2) at the small étale site, the cokernel clause
of Stacks 03M1 and Stacks 07V9 as named hypotheses, and Stacks 084Q, in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/ClosedImmersionFinitePresentation.lean`, reads
finite presentation of a closed immersion off one surjective étale chart.

Phrasing the hypothesis in sheaves of ideals on a *scheme* chart, rather than as a filtered
colimit of modules on the small étale site of `Y`, is also what keeps the derivation
unconditional.  The two statements of Stacks 03MB it consumes,
`AlgebraicGeometry.Space.mem_obj_iff_ker_le` and
`AlgebraicGeometry.Space.etaleChartKer_invariantSubspace_subschemeι`, are both about ideal sheaves
of schemes, so no comparison of quasi-coherence on the small étale site with quasi-coherence on
a chart enters; identifying a supremum of ideal sheaves on charts with a colimit of modules on
the small étale site is exactly that comparison, and is where the forward implication of
Descent, Proposition 03DX(2) would be needed again.

## References

* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Chartwise ideal sheaves -/

/-- The ideal sheaf cut out on an étale scheme chart `U` of `Y` by a closed subspace `Z` of
`Y`: the ideal sheaf of the closed immersion of schemes `Z ×_Y U ⟶ U`.  This is
`AlgebraicGeometry.Space.chartKer` at the structure morphism of the chart. -/
noncomputable abbrev etaleChartKer (Y : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS Y.1) (U : SmallEtale B S hS Y.1) :
    Scheme.IdealSheafData ((BigFppfOver.toScheme B S hS).obj U.1.left) :=
  chartKer B S hS Y Z U.1.hom

/-- **Membership in a closed subspace is detected on a single surjective étale chart.** A point
`x` of `Y` lies in `X` as soon as, after every pullback to the chart `U`, the chart ideal of `X`
is contained in the ideal of the resulting point. -/
private theorem mem_obj_of_chartKer_le (Y : AlgebraicSpaces B S hS)
    (X : ClosedSubspaces B S hS Y.1) (U : SmallEtale B S hS Y.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) U.1.hom)
    {T : (BigFppfOver B S hS)ᵒᵖ} (x : Y.1.obj T)
    (h : ∀ {T' : BigFppfOver B S hS} (q : T' ⟶ T.unop) (k : T' ⟶ U.1.left),
      Y.1.map q.op x = U.1.hom.app (op T') k →
        ((BigFppfOver.toScheme B S hS).map (X.2.2.rep.snd U.1.hom)).ker ≤
          ((BigFppfOver.toScheme B S hS).map k).ker) :
    x ∈ X.1.obj T := by
  set τ : yoneda.obj T.unop ⟶ Y.1 := yonedaEquiv.symm x with hτ
  refine mem_obj_of_surjective_etale B S hS Y.2.isSheaf X.1 X.2.1.isSheaf
    (U.2.rep.snd τ) (hsurj.property_snd τ) (U.2.property_snd τ) _ ?_
  have hw : yoneda.map (U.2.rep.fst' τ) ≫ U.1.hom = yoneda.map (U.2.rep.snd τ) ≫ τ := by
    rw [U.2.rep.map_fst' τ]
    exact U.2.rep.w τ
  have hval : Y.1.map (U.2.rep.snd τ).op x =
      U.1.hom.app (op (U.2.rep.pullback τ)) (U.2.rep.fst' τ) := by
    rw [← yonedaEquiv_yoneda_map_comp B S hS U.1.hom (U.2.rep.fst' τ), hw,
      ← yonedaEquiv_naturality, hτ, Equiv.apply_symm_apply]
  rw [hval, mem_obj_iff_ker_le]
  exact h _ _ hval

/-- **The intersection of a family of closed subspaces is contained in any closed subspace
whose chartwise ideal sheaves are dominated by the supremum of theirs.** This is the family
version of `AlgebraicGeometry.Space.le_of_forall_ker_le`, proved the same way: a point of the
intersection is pushed to an étale scheme chart of `Y`, where membership in each member of the
family becomes an inclusion of ideal sheaves by Stacks 03MB. -/
theorem iInf_le_of_etaleChartKer_le_iSup {ι : Type v} (Y : AlgebraicSpaces B S hS)
    (Z : ι → ClosedSubspaces B S hS Y.1) (X : ClosedSubspaces B S hS Y.1)
    (h : ∀ U, etaleChartKer B S hS Y X U ≤ ⨆ i, etaleChartKer B S hS Y (Z i) U) :
    (⨅ i, (Z i).1) ≤ X.1 := by
  intro T x hx
  rw [Subfunctor.iInf_obj, Set.mem_iInter] at hx
  obtain ⟨UY, f, hfS, hfE⟩ := Y.2.exists_atlas
  exact mem_obj_of_chartKer_le B S hS Y X ⟨CostructuredArrow.mk f, hfE⟩ hfS x fun q k hk =>
    (h _).trans (iSup_le fun i => (mem_obj_iff_ker_le B S hS Y (Z i) _ k).1
      (hk ▸ (Z i).1.map q.op (hx i)))

/-- **A closed subspace whose chartwise ideal sheaves are the supremum of those of a family of
closed subspaces is the intersection of that family.** -/
theorem subfunctor_eq_iInf_of_etaleChartKer_eq_iSup {ι : Type v} (Y : AlgebraicSpaces B S hS)
    (Z : ι → ClosedSubspaces B S hS Y.1) (X : ClosedSubspaces B S hS Y.1)
    (h : ∀ U, etaleChartKer B S hS Y X U = ⨆ i, etaleChartKer B S hS Y (Z i) U) :
    X.1 = ⨅ i, (Z i).1 :=
  le_antisymm
    (le_iInf fun i => le_of_forall_ker_le B S hS Y X (Z i) fun U =>
      (h U).ge.trans' (le_iSup (fun j => etaleChartKer B S hS Y (Z j) U) i))
    (iInf_le_of_etaleChartKer_le_iSup B S hS Y Z X fun U => (h U).le)

/-! ### The inverse system of an antitone family of subfunctors -/

variable {ι : Type v} [Preorder ι] {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The inverse system of an antitone family of subfunctors of `Y`, indexed by the opposite of
the index preorder, with the inclusions as its transition morphisms. -/
abbrev closedSubspaceDiagram (Z : ι → Subfunctor Y) (hZ : ∀ ⦃i j : ι⦄, i ≤ j → Z j ≤ Z i) :
    ιᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  obj i := (Z i.unop).toFunctor
  map f := Subfunctor.homOfLe (hZ (leOfHom f.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cone over the inverse system of an antitone family of subfunctors whose vertex is a
subfunctor contained in every member, with the inclusions as its projections. -/
abbrev closedSubspaceCone (Z : ι → Subfunctor Y) (hZ : ∀ ⦃i j : ι⦄, i ≤ j → Z j ≤ Z i)
    (X : Subfunctor Y) (hle : ∀ i, X ≤ Z i) :
    Cone (closedSubspaceDiagram B S hS Z hZ) where
  pt := X.toFunctor
  π :=
    { app := fun i => Subfunctor.homOfLe (hle i.unop)
      naturality := fun _ _ _ => (cancel_mono (Z _).ι).1 (by simp) }

/-- The transition morphisms of the inverse system of an antitone family of closed subspaces of
`Y` are closed immersions. -/
theorem isClosedImmersion_closedSubspaceDiagram_map (Z : ι → ClosedSubspaces B S hS Y)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → (Z j).1 ≤ (Z i).1) {i j : ιᵒᵖ} (f : i ⟶ j) :
    IsClosedImmersion B S hS
      ((closedSubspaceDiagram B S hS (fun i => (Z i).1) hZ).map f) :=
  isClosedImmersion_homOfLe B S hS (Z i.unop) (hZ (leOfHom f.unop))

/-- The projections out of the vertex of the cone over an antitone family of closed subspaces
of `Y` are closed immersions, as soon as the vertex is itself a closed subspace of `Y`. -/
theorem isClosedImmersion_closedSubspaceCone_π (Z : ι → ClosedSubspaces B S hS Y)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → (Z j).1 ≤ (Z i).1) (X : ClosedSubspaces B S hS Y)
    (hle : ∀ i, X.1 ≤ (Z i).1) (i : ιᵒᵖ) :
    IsClosedImmersion B S hS
      ((closedSubspaceCone B S hS (fun i => (Z i).1) hZ X.1 hle).π.app i) :=
  isClosedImmersion_homOfLe B S hS X (hle i.unop)

/-- **All legs of a cone over an antitone family of subfunctors induce the same morphism to the
ambient presheaf**, because the index is directed and the transition morphisms are inclusions. -/
theorem cone_π_comp_ι_eq [IsDirected ι (· ≤ ·)] (Z : ι → Subfunctor Y)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → Z j ≤ Z i) (c : Cone (closedSubspaceDiagram B S hS Z hZ))
    (i j : ι) :
    c.π.app (op i) ≫ (Z i).ι = c.π.app (op j) ≫ (Z j).ι := by
  have key : ∀ a b : ι, a ≤ b →
      c.π.app (op a) ≫ (Z a).ι = c.π.app (op b) ≫ (Z b).ι := fun a b hab => by
    rw [← c.w (homOfLE hab).op, Category.assoc, Subfunctor.homOfLe_ι]
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  rw [key i k hik, key j k hjk]

/-- **The intersection of an antitone family of subfunctors is its inverse limit.** For a
directed index with a chosen element `i₀`, the cone of inclusions with vertex a subfunctor `X`
which is contained in every member and contains their intersection is a limiting cone. -/
def isLimitClosedSubspaceCone [IsDirected ι (· ≤ ·)] (i₀ : ι) (Z : ι → Subfunctor Y)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → Z j ≤ Z i) (X : Subfunctor Y) (hle : ∀ i, X ≤ Z i)
    (hge : (⨅ i, Z i) ≤ X) :
    IsLimit (closedSubspaceCone B S hS Z hZ X hle) where
  lift c := Subfunctor.lift (c.π.app (op i₀) ≫ (Z i₀).ι) (by
    intro T _ hx
    obtain ⟨p, rfl⟩ := hx
    refine hge T ?_
    rw [Subfunctor.iInf_obj, Set.mem_iInter]
    intro i
    rw [cone_π_comp_ι_eq B S hS Z hZ c i₀ i]
    exact ((c.π.app (op i)).app T p).2)
  fac c i := by
    refine (cancel_mono (Z i.unop).ι).1 ?_
    rw [Category.assoc, Subfunctor.homOfLe_ι]
    exact cone_π_comp_ι_eq B S hS Z hZ c i₀ i.unop
  uniq c m hm := by
    refine (cancel_mono X.ι).1 ?_
    change m ≫ X.ι = c.π.app (op i₀) ≫ (Z i₀).ι
    rw [← hm (op i₀), Category.assoc, Subfunctor.homOfLe_ι]

/-- **The geometric assertion of Stacks 0A0U.** A directed family of closed subspaces of an
algebraic space `Y`, indexed by a preorder with a chosen element, whose chartwise ideal sheaves
have supremum the chartwise ideal sheaves of a closed subspace `X`, has `X` as its inverse
limit: the inclusions of `X` into the members form a limiting cone. -/
def isLimitClosedSubspaceConeOfEtaleChartKer [IsDirected ι (· ≤ ·)] (i₀ : ι)
    (Y : AlgebraicSpaces B S hS) (Z : ι → ClosedSubspaces B S hS Y.1)
    (hZ : ∀ ⦃i j : ι⦄, i ≤ j → (Z j).1 ≤ (Z i).1) (X : ClosedSubspaces B S hS Y.1)
    (h : ∀ U, etaleChartKer B S hS Y X U = ⨆ i, etaleChartKer B S hS Y (Z i) U) :
    IsLimit (closedSubspaceCone B S hS (fun i => (Z i).1) hZ X.1
      (fun i => (subfunctor_eq_iInf_of_etaleChartKer_eq_iSup B S hS Y Z X h).trans_le
        (iInf_le _ i))) :=
  isLimitClosedSubspaceCone B S hS i₀ _ hZ X.1 _
    (iInf_le_of_etaleChartKer_le_iSup B S hS Y Z X fun U => (h U).le)

/-! ### The conclusion of Stacks 0A0U as an interface -/

/-- **The conclusion of Stacks 0A0U as data.** A directed index with a chosen element, an
antitone family of closed subspaces of `Y` each of finite presentation over `Y`, and a limiting
cone exhibiting the given closed subspace `X` as their inverse limit. -/
structure ClosedSubspaceApproximation (Y : AlgebraicSpaces B S hS)
    (X : ClosedSubspaces B S hS Y.1) where
  /-- The index of the inverse system. -/
  index : Type u
  [indexPreorder : Preorder index]
  /-- A chosen index, as in Situation 084R. -/
  point : index
  [indexDirected : IsDirected index (· ≤ ·)]
  /-- The stages of the system: closed subspaces of `Y`. -/
  stage : index → ClosedSubspaces B S hS Y.1
  /-- The stages shrink as the index grows, so they form an inverse system. -/
  stage_antitone : ∀ ⦃i j : index⦄, i ≤ j → (stage j).1 ≤ (stage i).1
  /-- Every stage contains `X`. -/
  le_stage : ∀ i, X.1 ≤ (stage i).1
  /-- Every stage is a closed immersion of finite presentation into `Y`. -/
  stage_isFinitePresentation : ∀ i, IsFinitePresentation B S hS (stage i).1.ι
  /-- `X` is the inverse limit of the stages, along the inclusions. -/
  isLimit : IsLimit (closedSubspaceCone B S hS (fun i => (stage i).1) stage_antitone X.1 le_stage)

/-- **The conclusion of Stacks 0A0U as a proposition.** A closed subspace of an algebraic space
is the directed inverse limit of closed subspaces of finite presentation.  This is the
hypothesis a consumer of the unproved tag should carry. -/
abbrev HasClosedSubspaceApproximation (Y : AlgebraicSpaces B S hS)
    (X : ClosedSubspaces B S hS Y.1) : Prop :=
  Nonempty (ClosedSubspaceApproximation B S hS Y X)

/-- A directed family of closed subspaces of `Y` which are of finite presentation over `Y` and
whose chartwise ideal sheaves have supremum those of `X` is an approximation of `X` in the sense
of Stacks 0A0U. -/
noncomputable def ClosedSubspaceApproximation.ofEtaleChartKer {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] (i₀ : I) (Y : AlgebraicSpaces B S hS)
    (Z : I → ClosedSubspaces B S hS Y.1)
    (hZ : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1) (X : ClosedSubspaces B S hS Y.1)
    (hfp : ∀ i, IsFinitePresentation B S hS (Z i).1.ι)
    (h : ∀ U, etaleChartKer B S hS Y X U = ⨆ i, etaleChartKer B S hS Y (Z i) U) :
    ClosedSubspaceApproximation B S hS Y X where
  index := I
  point := i₀
  stage := Z
  stage_antitone := hZ
  le_stage i := (subfunctor_eq_iInf_of_etaleChartKer_eq_iSup B S hS Y Z X h).trans_le (iInf_le _ i)
  stage_isFinitePresentation := hfp
  isLimit := isLimitClosedSubspaceConeOfEtaleChartKer B S hS i₀ Y Z hZ X h

/-! ### The same, tested on a single surjective étale chart -/

/-- **Two monomorphisms of schemes defining the same subobject have the same ideal sheaf.** Each
factors through the other, so `AlgebraicGeometry.Scheme.Hom.le_ker_comp` applies both ways. -/
private theorem ker_eq_of_subobject_mk_eq {A A' W : Scheme.{u}} (p : A ⟶ W) (q : A' ⟶ W)
    [Mono p] [Mono q] (h : Subobject.mk p = Subobject.mk q) :
    p.ker = q.ker := by
  refine le_antisymm ?_ ?_
  · rw [← Subobject.ofMkLEMk_comp (f := q) (g := p) h.ge]
    exact Scheme.Hom.le_ker_comp _ _
  · rw [← Subobject.ofMkLEMk_comp (f := p) (g := q) h.le]
    exact Scheme.Hom.le_ker_comp _ _

/-- **A closed subspace is recovered from the chartwise ideal sheaf of its base change along a
single surjective étale chart.** If the chart ideal of `W` at one surjective étale scheme chart
`U` of `Y` is contained in that of `Z`, then `Z ⊆ W`.

This is `AlgebraicGeometry.Space.le_of_forall_ker_le` with the chart given rather than taken
from `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`: membership in `W` is checked after the
surjective étale base change along `U`, where Stacks 03MB turns it into the stated inclusion. -/
theorem le_of_etaleChartKer_le_of_chart (Y : AlgebraicSpaces B S hS)
    (Z W : ClosedSubspaces B S hS Y.1) (U : SmallEtale B S hS Y.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) U.1.hom)
    (h : etaleChartKer B S hS Y W U ≤ etaleChartKer B S hS Y Z U) :
    Z.1 ≤ W.1 := by
  intro T x hx
  exact mem_obj_of_chartKer_le B S hS Y W U hsurj x fun q k hk =>
    h.trans ((mem_obj_iff_ker_le B S hS Y Z U k).1 (hk ▸ Z.1.map q.op hx))

omit [Preorder ι] in
/-- **The intersection of a family of closed subspaces is contained in any closed subspace whose
chart ideal at a single surjective étale chart is dominated by the supremum of theirs.** This is
`AlgebraicGeometry.Space.iInf_le_of_etaleChartKer_le_iSup` with the chart given rather than taken
from `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`. -/
theorem iInf_le_of_etaleChartKer_le_iSup_of_chart (Y : AlgebraicSpaces B S hS)
    (Z : ι → ClosedSubspaces B S hS Y.1) (X : ClosedSubspaces B S hS Y.1)
    (U : SmallEtale B S hS Y.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) U.1.hom)
    (h : etaleChartKer B S hS Y X U ≤ ⨆ i, etaleChartKer B S hS Y (Z i) U) :
    (⨅ i, (Z i).1) ≤ X.1 := by
  intro T x hx
  rw [Subfunctor.iInf_obj, Set.mem_iInter] at hx
  exact mem_obj_of_chartKer_le B S hS Y X U hsurj x fun q k hk =>
    h.trans (iSup_le fun i => (mem_obj_iff_ker_le B S hS Y (Z i) U k).1
      (hk ▸ (Z i).1.map q.op (hx i)))

omit [Preorder ι] in
/-- **A closed subspace whose chart ideal at a single surjective étale chart is the supremum of
those of a family of closed subspaces is the intersection of that family.** -/
theorem subfunctor_eq_iInf_of_etaleChartKer_eq_iSup_of_chart (Y : AlgebraicSpaces B S hS)
    (Z : ι → ClosedSubspaces B S hS Y.1) (X : ClosedSubspaces B S hS Y.1)
    (U : SmallEtale B S hS Y.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) U.1.hom)
    (h : etaleChartKer B S hS Y X U = ⨆ i, etaleChartKer B S hS Y (Z i) U) :
    X.1 = ⨅ i, (Z i).1 :=
  le_antisymm
    (le_iInf fun i => le_of_etaleChartKer_le_of_chart B S hS Y X (Z i) U hsurj
      ((le_iSup (fun j => etaleChartKer B S hS Y (Z j) U) i).trans h.ge))
    (iInf_le_of_etaleChartKer_le_iSup_of_chart B S hS Y Z X U hsurj h.le)

/-! ### The closed subspace cut out by an invariant ideal sheaf on a chart -/

section Invariant

variable (Y : AlgebraicSpaces B S hS) {V : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ Y.1}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))) φ)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

/-- The surjective étale chart of `Y` given by a surjective étale morphism out of a
representable object of the big fppf category over `S`. -/
abbrev chartOfSurjectiveEtale : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk φ, he⟩

variable (J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)

include hs he in
/-- **The chart ideal of the closed subspace cut out by an invariant ideal sheaf.** For an étale
chart `A` of `Y` with a morphism `m : A ⟶ V` to the chart carrying the invariant ideal sheaf
`J`, the ideal sheaf cut out on `A` by the closed subspace `V(J) ⊆ Y` is the pullback `m^{-1}J`.

This is `AlgebraicGeometry.Space.definingIdealAt_invariantSubspace_subschemeι` read on ideal
sheaves instead of on ideals of global functions: the base change of `V(J)` along `A` is the
pullback subscheme as a subobject, and two monomorphisms with the same subobject have the same
ideal sheaf. -/
theorem etaleChartKer_invariantSubspace_subschemeι
    (hinv : IsInvariantSubscheme B S hS hs (Subobject.mk J.subschemeι))
    (hZ : IsClosedSubspace B S hS
      (invariantSubspace B S hS φ (Subobject.mk J.subschemeι)))
    (A : SmallEtale B S hS Y.1)
    (m : A ⟶ chartOfSurjectiveEtale B S hS Y he) :
    etaleChartKer B S hS Y
        ⟨invariantSubspace B S hS φ (Subobject.mk J.subschemeι), hZ⟩ A =
      J.comap ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS Y.1).map m)) := by
  have hw : yoneda.map ((SmallEtale.toOver B S hS Y.1).map m) ≫ φ = A.1.hom :=
    CostructuredArrow.w m.1
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom)) :=
    hZ.2.property A.1.hom _ _ (hZ.2.rep.isPullback A.1.hom)
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom)) :=
    inferInstance
  have hpres : (Subobject.underlyingIso ((BigFppfOver.toScheme B S hS).map
        (hZ.2.rep.snd A.1.hom))).symm.hom ≫
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))).arrow =
      (BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom) :=
    Subobject.underlyingIso_arrow _
  have himmp : _root_.AlgebraicGeometry.IsImmersion
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk
      ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))]
    infer_instance
  have hsp : subschemePoints B S hS
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom))) =
      subschemePoints B S hS ((Subobject.pullback ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS Y.1).map m))).obj (Subobject.mk J.subschemeι)) := by
    rw [subschemePoints_eq_range B S hS _ _ hpres,
      range_yoneda_snd_eq_preimage B S hS A.1.hom hZ.2.rep, ← hw,
      Subfunctor.preimage_comp, preimage_invariantSubspace B S hS hs _ hinv,
      subschemePoints_pullback]
  have hqci : _root_.AlgebraicGeometry.IsClosedImmersion
      (Subobject.mk (J.comap ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS Y.1).map m))).subschemeι).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    infer_instance
  have hobj : Subobject.mk ((BigFppfOver.toScheme B S hS).map (hZ.2.rep.snd A.1.hom)) =
      Subobject.mk (J.comap ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS Y.1).map m))).subschemeι := by
    rw [← Scheme.IdealSheafData.pullback_subobject_mk_subschemeι]
    refine subschemePoints_injective B S hS himmp ?_ hsp
    rw [Scheme.IdealSheafData.pullback_subobject_mk_subschemeι]
    exact inferInstance
  exact (ker_eq_of_subobject_mk_eq _ _ hobj).trans
    (Scheme.IdealSheafData.ker_subschemeι _)

/-! ### Stacks 0A0U from an approximating family of invariant ideal sheaves -/

variable {I : Type u} (K : I → ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
  (hKinv : ∀ i, IsInvariantSubscheme B S hS hs (Subobject.mk (K i).subschemeι))

include he in
/-- The closed subspace of `Y` cut out by one member of a family of invariant ideal sheaves on a
surjective étale chart of `Y`. -/
noncomputable def invariantStage (i : I) : ClosedSubspaces B S hS Y.1 :=
  ⟨invariantSubspace B S hS φ (Subobject.mk (K i).subschemeι),
    isClosedSubspace_invariantSubspace_subschemeι B S hS Y hs he (K i) (hKinv i)⟩

include he in
/-- The chart ideal of `AlgebraicGeometry.Space.invariantStage` at the chart carrying the family
is the given ideal sheaf. -/
theorem etaleChartKer_invariantStage (i : I) :
    etaleChartKer B S hS Y (invariantStage B S hS Y hs he K hKinv i)
        (chartOfSurjectiveEtale B S hS Y he) = K i := by
  have h := etaleChartKer_invariantSubspace_subschemeι B S hS Y hs he (K i) (hKinv i)
    (isClosedSubspace_invariantSubspace_subschemeι B S hS Y hs he (K i) (hKinv i))
    (chartOfSurjectiveEtale B S hS Y he) (𝟙 (chartOfSurjectiveEtale B S hS Y he))
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Scheme.IdealSheafData.comap_id] at h
  exact h

include he in
/-- **A monotone family of invariant ideal sheaves cuts out an antitone family of closed
subspaces.** -/
theorem invariantStage_antitone [Preorder I] (hK : Monotone K) {i j : I} (hij : i ≤ j) :
    (invariantStage B S hS Y hs he K hKinv j).1 ≤
      (invariantStage B S hS Y hs he K hKinv i).1 :=
  le_of_etaleChartKer_le_of_chart B S hS Y _ _ (chartOfSurjectiveEtale B S hS Y he) hs
    (by rw [etaleChartKer_invariantStage, etaleChartKer_invariantStage]; exact hK hij)

include he in
/-- **Stacks 0A0U from an approximating family of invariant ideal sheaves, as data.** Let
`X ⊆ Y` be a closed subspace of an algebraic space `Y` over `S`, let `φ : V ⟶ Y` be a surjective
étale scheme chart of `Y`, and let `K` be a monotone family of ideal sheaves of `𝒪_V`, indexed by
a directed preorder with a chosen element, each invariant under the relation `R = V ×_Y V` and
each cutting out a closed subspace of finite presentation over `Y`.  If the supremum of the
family is the ideal sheaf cut out on `V` by `X`, then the closed subspaces `V(K i)` form an
inverse system of closed immersions with `X` as its limit. -/
noncomputable def closedSubspaceApproximationOfInvariantIdeals [Preorder I]
    [IsDirected I (· ≤ ·)] (i₀ : I) (X : ClosedSubspaces B S hS Y.1) (hK : Monotone K)
    (hsup : (⨆ i, K i) = etaleChartKer B S hS Y X (chartOfSurjectiveEtale B S hS Y he))
    (hfp : ∀ i, IsFinitePresentation B S hS
      (invariantSubspace B S hS φ (Subobject.mk (K i).subschemeι)).ι) :
    ClosedSubspaceApproximation B S hS Y X :=
  let Z : I → ClosedSubspaces B S hS Y.1 := invariantStage B S hS Y hs he K hKinv
  have hchart : ∀ i, etaleChartKer B S hS Y (Z i) (chartOfSurjectiveEtale B S hS Y he) = K i :=
    etaleChartKer_invariantStage B S hS Y hs he K hKinv
  have hanti : ∀ ⦃i j : I⦄, i ≤ j → (Z j).1 ≤ (Z i).1 := fun _ _ hij =>
    invariantStage_antitone B S hS Y hs he K hKinv hK hij
  have hle : ∀ i, X.1 ≤ (Z i).1 := fun i =>
    le_of_etaleChartKer_le_of_chart B S hS Y X (Z i) (chartOfSurjectiveEtale B S hS Y he) hs
      ((hchart i).trans_le ((le_iSup K i).trans hsup.le))
  have hsup' : etaleChartKer B S hS Y X (chartOfSurjectiveEtale B S hS Y he) =
      ⨆ i, etaleChartKer B S hS Y (Z i) (chartOfSurjectiveEtale B S hS Y he) :=
    hsup.symm.trans (iSup_congr fun i => (hchart i).symm)
  { index := I
    point := i₀
    stage := Z
    stage_antitone := hanti
    le_stage := hle
    stage_isFinitePresentation := hfp
    isLimit := isLimitClosedSubspaceCone B S hS i₀ (fun i => (Z i).1) hanti X.1 hle
      (iInf_le_of_etaleChartKer_le_iSup_of_chart B S hS Y Z X
        (chartOfSurjectiveEtale B S hS Y he) hs hsup'.le) }

include hs he hKinv in
/-- **Stacks 0A0U.** Let `S` be a scheme and let `X ⊆ Y` be a closed subspace of an algebraic
space `Y` over `S`.  Then `X` is a directed inverse limit `X = lim X_i` of closed subspaces of
`Y` whose transition morphisms are closed immersions and whose structure morphisms `X_i ⟶ Y` are
closed immersions of finite presentation, as soon as the ideal sheaf cut out by `X` on a
surjective étale scheme chart `V ⟶ Y` is the supremum of a monotone family of invariant ideal
sheaves of `𝒪_V` each of which cuts out a closed subspace of finite presentation over `Y`.

The approximating family is the hypothesis: it is what Stacks 0829 supplies for the ideal sheaf
of `X`, read on the chart `V`, together with Stacks 084Q for the finite presentation of the
stages.  Everything else is proved here and unconditionally: each member of the family cuts out
a closed subspace of `Y` by étale descent, its chart ideal on `V` is the given ideal sheaf, the
family of subspaces is antitone with `X` contained in every member, and the inclusions exhibit
`X` as the inverse limit. -/
@[stacks 0A0U "given the approximating family of invariant ideal sheaves on a chart, which is \
Stacks 0829 for the ideal sheaf of `X` read on that chart"]
theorem hasClosedSubspaceApproximation_of_invariantIdeals [Preorder I] [IsDirected I (· ≤ ·)]
    (i₀ : I) (X : ClosedSubspaces B S hS Y.1) (hK : Monotone K)
    (hsup : (⨆ i, K i) = etaleChartKer B S hS Y X (chartOfSurjectiveEtale B S hS Y he))
    (hfp : ∀ i, IsFinitePresentation B S hS
      (invariantSubspace B S hS φ (Subobject.mk (K i).subschemeι)).ι) :
    HasClosedSubspaceApproximation B S hS Y X :=
  ⟨closedSubspaceApproximationOfInvariantIdeals B S hS Y hs he K hKinv i₀ X hK hsup hfp⟩

end Invariant

end Space

end AlgebraicGeometry

end
