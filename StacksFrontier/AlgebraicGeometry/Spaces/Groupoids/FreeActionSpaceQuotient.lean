module

public import StacksFrontier.AlgebraicGeometry.Limits.CoproductUniversal
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeQuotientTorsor
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize

/-!
# The quotient of an algebraic space by a free action of an abstract group

Let `S` be a scheme, `X` an algebraic space over `S` and `G` an abstract group acting on `X`
by a natural pointwise action. Tag 071S says that the quotient sheaf `X/G` is again an
algebraic space when the action is free. This file proves it, at a surjective étale chart
`φ : U ⟶ X` of `X`.

For each `g ∈ G` the *twisted relation* is the fibre product `R g = U ×_{φ, X, g • φ} U`,
whose `T`-points are the pairs `(a, b)` of `T`-points of `U` with `φ a = g • φ b`. It is an
object of the site because the diagonal of an algebraic space is representable. The relation
presenting `X/G` is the disjoint union `∐_{g ∈ G} R g` of these over `U`: the twisted
relations are exactly the parts into which `U ×_{X/G} U` decomposes.

Rather than the source's reduction to a `G`-equivariant chart `V = ∐_{g ∈ G} U` — which needs
a bound on `G` before the construction can even start — the twisted relations are formed
directly at `U`, and the bound on `G` is then a *consequence* of freeness
(`AlgebraicGeometry.Space.mk_le_of_isFreeOnNonemptyPoints`) rather than a hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.spaceActionHom` and `AlgebraicGeometry.Space.spaceActionIso`: the
  automorphism of `X` given by a group element of a natural action.
* `AlgebraicGeometry.Space.twistedChart`: the chart `φ` composed with that automorphism.
* `AlgebraicGeometry.Space.twistObj`, with `AlgebraicGeometry.Space.twistTarget` and
  `AlgebraicGeometry.Space.twistSource`: the twisted relation `R g` and its two projections,
  and `AlgebraicGeometry.Space.twistPre` the pre-relation `R g ⟶ U ×_S U` they form.
* `AlgebraicGeometry.Space.twistRelation`, with
  `AlgebraicGeometry.Space.twistRelationTarget` and
  `AlgebraicGeometry.Space.twistRelationSource`: the relation `R = ∐_{g ∈ G} R g` as an object
  of the site, and its two projections, glued from those of the summands. Its index set is
  `AlgebraicGeometry.Space.twistSupport`, the group elements whose twisted relation is
  nonempty.
* `AlgebraicGeometry.Space.twistQuotientChart`: the chart followed by the projection of `X`
  onto `X/G`.

## Main results

* `AlgebraicGeometry.Space.etale_twistSource` and `AlgebraicGeometry.Space.etale_twistTarget`:
  both projections of a twisted relation are étale, being base changes of the chart;
  `AlgebraicGeometry.Space.etale_twistRelationSource` and
  `AlgebraicGeometry.Space.etale_twistRelationTarget` carry that to `R`, where the twisted
  relations are an open cover.
* `AlgebraicGeometry.Space.mono_twistPre`: each twisted relation is a monomorphism into
  `U ×_S U`.
* `AlgebraicGeometry.Space.eq_of_common_twistPoint` and
  `AlgebraicGeometry.Space.disjoint_range_twistPre`: **freeness is disjointness.** Two twisted
  relations that meet — over a test object with nonempty underlying scheme, respectively in a
  point of `U ×_S U` — have the same index. Together with the previous item this is the
  chart-level form of the monomorphism `∐_{g ∈ G} R g ⟶ U ×_S U`, which is the only way
  freeness enters the source's proof.
* `AlgebraicGeometry.Space.mk_le_of_isFreeOnNonemptyPoints` and
  `AlgebraicGeometry.Space.mk_twistSupport_le`: a free action of an abstract group on an
  algebraic space with a nonempty chart has `#G ≤ #(U ×_S U)`, and without any hypothesis on
  the chart the same bound holds for the group elements with a nonempty twisted relation.
  This is what puts `R` inside the site.
* `AlgebraicGeometry.Space.twistRelation_point_ext`: a point of `R` is determined by its
  source and its target, the site-level form of the monomorphism `R ⟶ U ×_S U`.
* `AlgebraicGeometry.Space.isPullback_twistRelation`: **`R` is the kernel pair of
  `U ⟶ X/G`**, and `AlgebraicGeometry.Space.isEtaleEquivalenceRelation_twistRelation`: it is
  therefore an étale equivalence relation.
* `AlgebraicGeometry.Space.isAlgebraicSpace_orbitQuotientSheaf_of_isFreeOnNonemptyPoints`:
  **Tag 071S**, the quotient of an algebraic space by a free action of an abstract group is an
  algebraic space.

## Implementation notes

**Which notion of freeness.** The hypothesis is
`AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`: the action is cancellative on the points
over each test object whose underlying scheme is nonempty. Asking it over *every* test object
is unsatisfiable for a nontrivial group — over a test object with empty underlying scheme a
sheaf is terminal, so
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton` turns that demand into
`Subsingleton G`; `AlgebraicGeometry.Space.isAlgebraicSpace_orbitQuotientSheaf` of
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotient` is the resulting
vacuous statement, and carries no tag for that reason. Read on the test objects with nonempty
underlying scheme, the condition says precisely that for `g ≠ 1` the fixed subsheaf of `g` is
initial, equivalently that `∐_{g ∈ G} X ⟶ X ×_S X`, `(g, x) ↦ (g • x, x)`, is a
monomorphism of sheaves; `disjoint_range_twistPre` is that monomorphism pulled back to the
chart, which is the form the geometry consumes.

**How the tag is proved.** In three steps, at a surjective étale chart `φ : U ⟶ X` of the
algebraic space, which is relatively representable because the diagonal of `X` is.

1. `R = ∐_{g ∈ G} R g` is assembled by
   `AlgebraicGeometry.BigFppfOver.exists_coproduct_of_size_le`, whose size hypothesis is met
   because freeness bounds the index set by the points of `U ×_S U`
   (`mk_twistSupport_le`) while `AlgebraicGeometry.Scheme.size_le_of_mono` bounds each summand
   through `mono_twistPre`, both by the same cardinal. Only the group elements with a nonempty
   twisted relation are taken as indices: the remaining summands are empty, and leaving them
   out is what makes the bound available with no hypothesis on the chart.
2. `R` is the kernel pair of `q : h_U ⟶ X/G`. Injectivity is `twistRelation_point_ext`:
   a test object splits into the parts over which two given points of `R` lie in given
   twisted relations, freeness empties the parts with different indices, and a point of a
   twisted relation is determined by its projections. Surjectivity is where the sheaf
   condition enters: two points of `U` with the same image in `X/G` differ, locally on a
   covering sieve, by a group element — this is
   `AlgebraicGeometry.Space.orbitSieve_mem`, which is local injectivity of the sheafification
   map — and the resulting local points of `R` glue, being compatible by injectivity and the
   big fppf site being subcanonical.
3. `AlgebraicGeometry.Space.isEquivalenceRelation_of_isPullback` then makes `(t, s)` an étale
   equivalence relation, `AlgebraicGeometry.Space.isAlgebraicSpace_quotient_unconditional`
   (Tag 02WW, unconditional here) makes `U/R` an algebraic space, and `X/G ≅ U/R` because
   both are the coequalizer of `h_R ⇉ h_U` in fppf sheaves: each of the two maps out of `h_U`
   is locally surjective with that kernel pair, so
   `CategoryTheory.Sheaf.isColimitCoforkOfKernelPair` applies to both.

The scheme case of the tag — an action on an object of the site rather than on an arbitrary
algebraic space — is proved separately, in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotient` and
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionOrbitQuotient`, where the relation
is the graph of the action rather than the kernel pair of a chart.

## References

* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {G : Type u} [Group G]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [∀ T, MulAction G (X.obj T)]

section Action

variable (hnat : IsNaturalAction B S hS G X)

/-- The endomorphism of `X` given by the action of a group element. -/
def spaceActionHom (hnat : IsNaturalAction B S hS G X) (g : G) : X ⟶ X where
  app T := ↾(fun x : X.obj T => g • x)
  naturality _ _ f := ConcreteCategory.hom_ext _ _ fun x => (hnat f.unop.op g x).symm

/-- The endomorphism given by `g` sends a point `x` to `g • x`. -/
@[simp]
theorem spaceActionHom_app (g : G) (T : (BigFppfOver B S hS)ᵒᵖ) (x : X.obj T) :
    (spaceActionHom hnat g).app T x = g • x := rfl

include hnat in
/-- The identity element acts as the identity of `X`. -/
theorem spaceActionHom_one : spaceActionHom hnat (1 : G) = 𝟙 X :=
  NatTrans.ext (funext fun _ => ConcreteCategory.hom_ext _ _ fun x => one_smul _ x)

include hnat in
/-- The endomorphism given by `g * h` is that given by `h` followed by that given by `g`. -/
theorem spaceActionHom_mul (g h : G) :
    spaceActionHom hnat (g * h) = spaceActionHom hnat h ≫ spaceActionHom hnat g :=
  NatTrans.ext (funext fun _ => ConcreteCategory.hom_ext _ _ fun x => mul_smul g h x)

/-- The automorphism of `X` given by the action of a group element. -/
@[simps]
def spaceActionIso (hnat : IsNaturalAction B S hS G X) (g : G) : X ≅ X where
  hom := spaceActionHom hnat g
  inv := spaceActionHom hnat g⁻¹
  hom_inv_id := by rw [← spaceActionHom_mul hnat, inv_mul_cancel, spaceActionHom_one]
  inv_hom_id := by rw [← spaceActionHom_mul hnat, mul_inv_cancel, spaceActionHom_one]

/-- The endomorphism of `X` given by a group element is an isomorphism. -/
instance (g : G) : IsIso (spaceActionHom hnat g) := (spaceActionIso hnat g).isIso_hom

end Action

/-- Being surjective after every representable base change, for a morphism of presheaves on the
big fppf site of `S`. -/
abbrev IsChartSurjective : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf

/-- Being étale after every representable base change, for a morphism of presheaves on the big
fppf site of `S`. -/
abbrev IsChartEtale : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf

section Twist

variable (hnat : IsNaturalAction B S hS G X) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X)

/-- The chart `φ : U ⟶ X` twisted by a group element: `u ↦ g • φ u`. -/
def twistedChart (g : G) : yoneda.obj U ⟶ X := φ ≫ spaceActionHom hnat g

/-- A twisted chart is surjective after every representable base change when the chart is. -/
theorem isChartSurjective_twistedChart (hsurj : IsChartSurjective φ) (g : G) :
    IsChartSurjective (twistedChart hnat φ g) :=
  MorphismProperty.RespectsIso.postcomp _ (spaceActionIso hnat g).hom φ hsurj

/-- A twisted chart is étale after every representable base change when the chart is. -/
theorem isChartEtale_twistedChart (hetale : IsChartEtale φ) (g : G) :
    IsChartEtale (twistedChart hnat φ g) :=
  MorphismProperty.RespectsIso.postcomp _ (spaceActionIso hnat g).hom φ hetale

variable (hrep : yoneda.relativelyRepresentable φ)

/-- The `g`-twisted relation object `R g = U ×_{φ, X, g • φ} U`: an object of the site whose
`T`-points are the pairs `(a, b)` of `T`-points of `U` with `φ a = g • φ b`. -/
noncomputable def twistObj (g : G) : BigFppfOver B S hS := hrep.pullback (twistedChart hnat φ g)

/-- The first projection `R g ⟶ U`. -/
noncomputable def twistTarget (g : G) : twistObj hnat φ hrep g ⟶ U :=
  hrep.fst' (twistedChart hnat φ g)

/-- The second projection `R g ⟶ U`. -/
noncomputable def twistSource (g : G) : twistObj hnat φ hrep g ⟶ U :=
  hrep.snd (twistedChart hnat φ g)

/-- The twisted relation `R g` with its two projections is the fibre product of `φ` and the
chart twisted by `g`. -/
theorem isPullback_twistObj (g : G) :
    IsPullback (yoneda.map (twistTarget hnat φ hrep g)) (yoneda.map (twistSource hnat φ hrep g))
      φ (twistedChart hnat φ g) :=
  hrep.isPullback' (twistedChart hnat φ g)

/-- The defining relation among the `T`-points of `R g`: the first projection is `g` times the
second, measured in `X`. -/
theorem twistObj_w (g : G) (T : BigFppfOver B S hS) (r : T ⟶ twistObj hnat φ hrep g) :
    φ.app (Opposite.op T) (r ≫ twistTarget hnat φ hrep g) =
      g • φ.app (Opposite.op T) (r ≫ twistSource hnat φ hrep g) := by
  have h := congrArg (fun η : yoneda.obj (twistObj hnat φ hrep g) ⟶ X => η.app (Opposite.op T) r)
    (isPullback_twistObj hnat φ hrep g).w
  simpa [twistedChart] using h

/-- The second projection of a twisted relation is étale when the chart is. -/
theorem etale_twistSource (hetale : IsChartEtale φ) (g : G) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (twistSource hnat φ hrep g) :=
  hetale.property (twistedChart hnat φ g) _ _ (isPullback_twistObj hnat φ hrep g)

/-- The first projection of a twisted relation is étale when the chart is. -/
theorem etale_twistTarget (hetale : IsChartEtale φ) (g : G) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (twistTarget hnat φ hrep g) :=
  (isChartEtale_twistedChart hnat φ hetale g).property φ _ _
    (isPullback_twistObj hnat φ hrep g).flip

/-- The second projection of a twisted relation is surjective when the chart is. -/
theorem surjective_twistSource (hsurj : IsChartSurjective φ) (g : G) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (twistSource hnat φ hrep g) :=
  hsurj.property (twistedChart hnat φ g) _ _ (isPullback_twistObj hnat φ hrep g)

/-! ### The twisted relation is a monomorphism into `U ×_S U` -/

/-- The twisted relation `R g ⟶ U ×_S U` as a pre-relation on `U` over `S`. -/
noncomputable abbrev twistPre (g : G) :
    Stacks.Groupoids.PreRelation ((Over.post B.inclusion).obj (twistObj hnat φ hrep g))
      ((Over.post B.inclusion).obj U) :=
  prod.lift ((Over.post B.inclusion).map (twistTarget hnat φ hrep g))
    ((Over.post B.inclusion).map (twistSource hnat φ hrep g))

private theorem mono_twistPre_aux (g : G) :
    Mono (prod.lift (twistTarget hnat φ hrep g) (twistSource hnat φ hrep g)) := by
  constructor
  intro Y a b hab
  apply yoneda.map_injective
  refine (isPullback_twistObj hnat φ hrep g).hom_ext ?_ ?_
  · simpa only [← Functor.map_comp] using congrArg yoneda.map
      (by simpa using congrArg (fun k => k ≫ prod.fst) hab)
  · simpa only [← Functor.map_comp] using congrArg yoneda.map
      (by simpa using congrArg (fun k => k ≫ prod.snd) hab)

/-- **Each twisted relation is a monomorphism into `U ×_S U`.** This is one summand of the
monomorphism `∐_{g ∈ G} R g ⟶ U ×_S U` through which the Stacks Project reads freeness. On a
single summand it holds with no hypothesis on the action, the summand being a base change of
the diagonal of `X`; what freeness adds is that distinct summands do not meet, which is
`AlgebraicGeometry.Space.disjoint_range_twistPre`. -/
instance mono_twistPre (g : G) : Mono (twistPre hnat φ hrep g) := by
  let : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesLimitsOfShape WalkingCospan B.inclusion := by infer_instance
  let : PreservesLimitsOfShape (Discrete PEmpty) B.inclusion := by infer_instance
  let : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let : PreservesFiniteLimits F :=
    PreservesFiniteLimits.overPost (F := B.inclusion) (X := B.obj hS)
  let : PreservesLimitsOfShape WalkingCospan F := by infer_instance
  let : PreservesLimitsOfShape (Discrete WalkingPair) F := by infer_instance
  let p : twistObj hnat φ hrep g ⟶ U ⨯ U :=
    prod.lift (twistTarget hnat φ hrep g) (twistSource hnat φ hrep g)
  let : Mono p := mono_twistPre_aux hnat φ hrep g
  let : Mono (F.map p) := preserves_mono_of_preservesLimit F p
  let eprod : F.obj (U ⨯ U) ≅ F.obj U ⨯ F.obj U := PreservesLimitPair.iso F U U
  have hfst : eprod.hom ≫ (prod.fst : F.obj U ⨯ F.obj U ⟶ _) = F.map prod.fst := by
    simp [eprod, PreservesLimitPair.iso_hom]
  have hsnd : eprod.hom ≫ (prod.snd : F.obj U ⨯ F.obj U ⟶ _) = F.map prod.snd := by
    simp [eprod, PreservesLimitPair.iso_hom]
  have hfac : twistPre hnat φ hrep g = F.map p ≫ eprod.hom := by
    apply prod.hom_ext
    · rw [prod.lift_fst, Category.assoc, hfst, ← F.map_comp, show p ≫ prod.fst =
        twistTarget hnat φ hrep g from prod.lift_fst _ _]
    · rw [prod.lift_snd, Category.assoc, hsnd, ← F.map_comp, show p ≫ prod.snd =
        twistSource hnat φ hrep g from prod.lift_snd _ _]
  rw [hfac]
  infer_instance

/-! ### Freeness separates the twisted relations -/

/-- **Freeness is disjointness of the twisted relations.** A test object of the site carrying a
point of `R g` and a point of `R g'` with the same image in `U ×_S U` — that is, a point of the
intersection of the two relations — forces `g = g'`, as soon as its underlying scheme is
nonempty.

This is the step at which the Stacks Project uses freeness, and the reason the map
`∐_{g ∈ G} R g ⟶ U ×_S U` is a monomorphism: the summands do not meet. -/
theorem eq_of_common_twistPoint (hfree : IsFreeOnNonemptyPoints B S hS G X) {g g' : G}
    (W : BigFppfOver B S hS) (hW : Nonempty ((BigFppfOver.toScheme B S hS).obj W))
    (a : W ⟶ twistObj hnat φ hrep g) (b : W ⟶ twistObj hnat φ hrep g')
    (htgt : a ≫ twistTarget hnat φ hrep g = b ≫ twistTarget hnat φ hrep g')
    (hsrc : a ≫ twistSource hnat φ hrep g = b ≫ twistSource hnat φ hrep g') :
    g = g' := by
  have h1 := twistObj_w hnat φ hrep g W a
  have h2 := twistObj_w hnat φ hrep g' W b
  rw [← htgt, ← hsrc] at h2
  have := hfree (Opposite.op W) hW
  exact IsCancelSMul.right_cancel g g' _ (h1.symm.trans h2)

/-- The underlying scheme of an object of the site, in the `Over S` idiom used by the
pre-relations. -/
abbrev postScheme (V : BigFppfOver B S hS) : Scheme.{u} :=
  ((Over.post B.inclusion).obj V).left

/-- A morphism of schemes out of a scheme presented as an object of the site, compatible with
the structure morphisms, as a morphism of site objects. -/
private def siteHom {Y : Scheme.{u}} (hY : B.Contains Y) (σ : Y ⟶ S)
    {V : BigFppfOver B S hS} (h : Y ⟶ postScheme V)
    (w : h ≫ ((Over.post B.inclusion).obj V).hom = σ) : BigFppfOver.mk B S hS hY σ ⟶ V :=
  Over.homMk (ObjectProperty.homMk h) (by apply ObjectProperty.hom_ext; exact w)

private theorem left_map_siteHom {Y : Scheme.{u}} (hY : B.Contains Y) (σ : Y ⟶ S)
    {V : BigFppfOver B S hS} (h : Y ⟶ postScheme V)
    (w : h ≫ ((Over.post B.inclusion).obj V).hom = σ) :
    ((Over.post B.inclusion).map (siteHom hY σ h w)).left = h := rfl

/-- Two points of the twisted relations with a common monomorphic source over `U ×_S U` have
the same index, when the source is nonempty. -/
private theorem eq_of_mono_cospan (hfree : IsFreeOnNonemptyPoints B S hS G X) {g g' : G}
    {A : Scheme.{u}} (hA : Nonempty A)
    (p : A ⟶ postScheme (twistObj hnat φ hrep g)) (q : A ⟶ postScheme (twistObj hnat φ hrep g'))
    (hp : Mono p)
    (hpq : p ≫ (twistPre hnat φ hrep g).left = q ≫ (twistPre hnat φ hrep g').left) :
    g = g' := by
  have hA' : B.Contains A := B.contains_of_mono p (twistObj hnat φ hrep g).left.2
  have hstr (i : G) (r : A ⟶ postScheme (twistObj hnat φ hrep i)) :
      r ≫ (twistPre hnat φ hrep i).left ≫
          ((Over.post B.inclusion).obj U ⨯ (Over.post B.inclusion).obj U : Over S).hom =
        r ≫ ((Over.post B.inclusion).obj (twistObj hnat φ hrep i)).hom :=
    congrArg (fun m => r ≫ m) (Over.w (twistPre hnat φ hrep i))
  have hqw : q ≫ ((Over.post B.inclusion).obj (twistObj hnat φ hrep g')).hom =
      p ≫ ((Over.post B.inclusion).obj (twistObj hnat φ hrep g)).hom := by
    rw [← hstr g' q, ← hstr g p, ← Category.assoc, ← Category.assoc, hpq]
  have key (pr : (Over.post B.inclusion).obj U ⨯ (Over.post B.inclusion).obj U ⟶
      (Over.post B.inclusion).obj U) (f : ∀ i, twistObj hnat φ hrep i ⟶ U)
      (hf : ∀ i, twistPre hnat φ hrep i ≫ pr = (Over.post B.inclusion).map (f i)) :
      p ≫ ((Over.post B.inclusion).map (f g)).left =
        q ≫ ((Over.post B.inclusion).map (f g')).left := by
    rw [← hf, ← hf, Over.comp_left, Over.comp_left, ← Category.assoc, ← Category.assoc, hpq]
  refine eq_of_common_twistPoint hnat φ hrep hfree
    (BigFppfOver.mk B S hS hA' (p ≫ ((Over.post B.inclusion).obj
      (twistObj hnat φ hrep g)).hom)) hA
    (siteHom hA' _ p rfl) (siteHom hA' _ q hqw) ?_ ?_
  · exact (Over.post B.inclusion (X := B.obj hS)).map_injective (Over.OverMorphism.ext
      (key _ _ fun _ => prod.lift_fst _ _))
  · exact (Over.post B.inclusion (X := B.obj hS)).map_injective (Over.OverMorphism.ext
      (key _ _ fun _ => prod.lift_snd _ _))

/-- **Freeness separates the twisted relations, at the level of schemes.** For `g ≠ g'` the
images of `R g` and `R g'` in `U ×_S U` are disjoint. This is the content of the Stacks
Project's monomorphism `∐_{g ∈ G} R ⟶ U ×_S U`, and the only place freeness is used. -/
theorem disjoint_range_twistPre (hfree : IsFreeOnNonemptyPoints B S hS G X) {g g' : G}
    (hne : g ≠ g') :
    Disjoint (Set.range (twistPre hnat φ hrep g).left.base)
      (Set.range (twistPre hnat φ hrep g').left.base) := by
  rw [← Scheme.isEmpty_pullback_iff]
  refine ⟨fun w => hne ?_⟩
  have hm' : Mono ((twistPre hnat φ hrep g').left) :=
    Over.mono_left_of_mono (twistPre hnat φ hrep g')
  exact eq_of_mono_cospan hnat φ hrep hfree ⟨w⟩
    (pullback.fst (twistPre hnat φ hrep g).left (twistPre hnat φ hrep g').left)
    (pullback.snd (twistPre hnat φ hrep g).left (twistPre hnat φ hrep g').left)
    pullback.fst_of_mono pullback.condition

/-! ### The group is bounded by the site's cutoff -/

/-- A twisted relation is nonempty as soon as the chart is: its source map is surjective, being
a base change of the chart. -/
theorem nonempty_twistObj (hsurj : IsChartSurjective φ) (hU : Nonempty (postScheme U)) (g : G) :
    Nonempty (postScheme (twistObj hnat φ hrep g)) := by
  obtain ⟨x⟩ := hU
  have : Surjective ((BigFppfOver.toScheme B S hS).map (twistSource hnat φ hrep g)) :=
    surjective_twistSource hnat φ hrep hsurj g
  obtain ⟨y, -⟩ := Scheme.Hom.surjective
    ((BigFppfOver.toScheme B S hS).map (twistSource hnat φ hrep g)) x
  exact ⟨y⟩

/-- Freeness bounds any family of nonempty twisted relations, indexed injectively by group
elements, by the points of `U ×_S U`. -/
private theorem mk_le_of_injective_nonempty (hfree : IsFreeOnNonemptyPoints B S hS G X)
    {ι : Type u} (g : ι → G) (hg : Function.Injective g)
    (hne : ∀ i, Nonempty (postScheme (twistObj hnat φ hrep (g i)))) :
    Cardinal.mk ι ≤ Cardinal.mk
      (((Over.post B.inclusion).obj U ⨯ (Over.post B.inclusion).obj U : Over S).left) := by
  refine Cardinal.mk_le_of_injective (f := fun i =>
    (twistPre hnat φ hrep (g i)).left.base (Classical.choice (hne i))) fun i i' h => ?_
  by_contra hii
  exact Set.disjoint_left.mp (disjoint_range_twistPre hnat φ hrep hfree fun h' => hii (hg h'))
    ⟨Classical.choice (hne i), rfl⟩ ⟨Classical.choice (hne i'), h.symm⟩

include hnat hrep in
/-- **A free action of an abstract group on an algebraic space is bounded by its chart.** The
group injects into the points of `U ×_S U`: each `g` contributes a nonempty piece `R g` of
`U ×_S U`, and freeness keeps those pieces disjoint.

This is what makes the relation of Tag 071S live inside the big fppf site at all: no bound on
the group is assumed, it is a consequence of freeness. -/
theorem mk_le_of_isFreeOnNonemptyPoints (hfree : IsFreeOnNonemptyPoints B S hS G X)
    (hsurj : IsChartSurjective φ) (hU : Nonempty (postScheme U)) :
    Cardinal.mk G ≤ Cardinal.mk
      (((Over.post B.inclusion).obj U ⨯ (Over.post B.inclusion).obj U : Over S).left) :=
  mk_le_of_injective_nonempty hnat φ hrep hfree id Function.injective_id
    (nonempty_twistObj hnat φ hrep hsurj hU)

/-! ### The relation `R = ∐_{g ∈ G} R g` inside the site -/

/-- The ambient product `V ×_S V` of the twisted relations on `V`, as a scheme. -/
noncomputable abbrev twistProd (V : BigFppfOver B S hS) : Scheme.{u} :=
  ((Over.post B.inclusion).obj V ⨯ (Over.post B.inclusion).obj V : Over S).left

/-- The index set of the relation of Tag 071S: the group elements whose twisted relation is
nonempty.

The summands indexed by the remaining group elements are empty, so nothing is lost by leaving
them out, and freeness bounds this index set by the points of `U ×_S U` with no hypothesis on
the chart — which is what puts the disjoint union inside the site. -/
abbrev twistSupport : Type u :=
  {g : G // Nonempty ((BigFppfOver.toScheme B S hS).obj (twistObj hnat φ hrep g))}

include hnat hrep in
/-- **Freeness bounds the index set of the relation.** The group elements with a nonempty
twisted relation inject into the points of `U ×_S U`, each one through a chosen point of its
own relation, because freeness keeps the relations disjoint. -/
theorem mk_twistSupport_le (hfree : IsFreeOnNonemptyPoints B S hS G X) :
    Cardinal.mk (twistSupport hnat φ hrep) ≤ Cardinal.mk (twistProd U) :=
  mk_le_of_injective_nonempty hnat φ hrep hfree Subtype.val Subtype.val_injective
    fun k => k.2

include hnat hrep in
/-- The twisted relations with a nonempty summand have a disjoint union inside the site: the
index set is bounded by `mk_twistSupport_le` and each summand by
`AlgebraicGeometry.Scheme.size_le_of_mono`, both by the same cardinal attached to
`U ×_S U`. -/
theorem exists_twistRelation (hfree : IsFreeOnNonemptyPoints B S hS G X) :
    ∃ (R : BigFppfOver B S hS)
      (c : ∀ k : twistSupport hnat φ hrep, twistObj hnat φ hrep k.1 ⟶ R),
      (∀ k, AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (c k))) ∧
      (∀ k k', k ≠ k' →
        Disjoint (Set.range ((BigFppfOver.toScheme B S hS).map (c k)))
          (Set.range ((BigFppfOver.toScheme B S hS).map (c k')))) ∧
      (∀ z : postScheme R, ∃ k,
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (c k))) := by
  have hP : (twistProd U).size < B.cutoff := B.contains_prod_left _ _ U.left.2 U.left.2
  obtain ⟨R, c, hoi, hne, hcov⟩ := BigFppfOver.exists_coproduct_of_size_le B S hS
    (fun k : twistSupport hnat φ hrep => twistObj hnat φ hrep k.1)
    (μ := max (2 ^ Cardinal.mk (twistProd U)) (twistProd U).size)
    (le_max_of_le_right (Scheme.aleph0_le_size _))
    (Scheme.max_two_pow_mk_size_lt_of_isStrongPrelimit B.cutoff_isStrongPrelimit hP)
    ((mk_twistSupport_le hnat φ hrep hfree).trans (le_max_of_le_left (Cardinal.cantor _).le))
    (fun k => @Scheme.size_le_of_mono _ _ ((twistPre hnat φ hrep k.1).left)
      (Over.mono_left_of_mono (twistPre hnat φ hrep k.1)))
  refine ⟨R, c, hoi, fun k k' hkk' => Set.disjoint_left.2 ?_, hcov⟩
  rintro z ⟨y, rfl⟩ ⟨y', hy'⟩
  exact hne k k' hkk' y y' hy'.symm

variable (hfree : IsFreeOnNonemptyPoints B S hS G X)

/-- **The relation of Tag 071S**, the disjoint union `∐_{g ∈ G} R g` of the twisted relations,
as an object of the big fppf site of `S`. -/
noncomputable def twistRelation : BigFppfOver B S hS :=
  (exists_twistRelation hnat φ hrep hfree).choose

/-- The inclusion of a twisted relation into the relation of Tag 071S. -/
noncomputable def twistRelationIncl (k : twistSupport hnat φ hrep) :
    twistObj hnat φ hrep k.1 ⟶ twistRelation hnat φ hrep hfree :=
  (exists_twistRelation hnat φ hrep hfree).choose_spec.choose k

/-- Each twisted relation is an open subobject of the relation of Tag 071S. -/
theorem isOpenImmersion_twistRelationIncl (k : twistSupport hnat φ hrep) :
    AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (twistRelationIncl hnat φ hrep hfree k)) :=
  (exists_twistRelation hnat φ hrep hfree).choose_spec.choose_spec.1 k

/-- Distinct twisted relations have disjoint images in the relation of Tag 071S. -/
theorem disjoint_range_twistRelationIncl {k k' : twistSupport hnat φ hrep} (hkk' : k ≠ k') :
    Disjoint
      (Set.range ((BigFppfOver.toScheme B S hS).map
        (twistRelationIncl hnat φ hrep hfree k)))
      (Set.range ((BigFppfOver.toScheme B S hS).map
        (twistRelationIncl hnat φ hrep hfree k'))) :=
  (exists_twistRelation hnat φ hrep hfree).choose_spec.choose_spec.2.1 k k' hkk'

/-- A point of a twisted relation and a point of another one have distinct images in the
relation of Tag 071S. -/
theorem twistRelationIncl_ne {k k' : twistSupport hnat φ hrep} (hkk' : k ≠ k')
    (y : (BigFppfOver.toScheme B S hS).obj (twistObj hnat φ hrep k.1))
    (y' : (BigFppfOver.toScheme B S hS).obj (twistObj hnat φ hrep k'.1)) :
    (BigFppfOver.toScheme B S hS).map (twistRelationIncl hnat φ hrep hfree k) y ≠
      (BigFppfOver.toScheme B S hS).map (twistRelationIncl hnat φ hrep hfree k') y' :=
  fun h => Set.disjoint_left.1 (disjoint_range_twistRelationIncl hnat φ hrep hfree hkk')
    ⟨y, rfl⟩ ⟨y', h.symm⟩

/-- The twisted relations cover the relation of Tag 071S. -/
theorem exists_mem_range_twistRelationIncl
    (z : (BigFppfOver.toScheme B S hS).obj (twistRelation hnat φ hrep hfree)) :
    ∃ k, z ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (twistRelationIncl hnat φ hrep hfree k)) :=
  (exists_twistRelation hnat φ hrep hfree).choose_spec.choose_spec.2.2 z

/-- The twisted relations cover the relation of Tag 071S, so a morphism out of it is
determined by its restrictions to them. -/
theorem twistRelation_hom_ext {Y : BigFppfOver B S hS}
    {h₁ h₂ : twistRelation hnat φ hrep hfree ⟶ Y}
    (h : ∀ k, twistRelationIncl hnat φ hrep hfree k ≫ h₁ =
      twistRelationIncl hnat φ hrep hfree k ≫ h₂) : h₁ = h₂ :=
  BigFppfOver.hom_ext_of_openCover (twistRelationIncl hnat φ hrep hfree)
    (isOpenImmersion_twistRelationIncl hnat φ hrep hfree)
    (exists_mem_range_twistRelationIncl hnat φ hrep hfree) h

/-- The inclusions of the twisted relations generate a covering sieve of the relation of
Tag 071S. -/
theorem ofArrows_twistRelationIncl_mem :
    Sieve.ofArrows _ (twistRelationIncl hnat φ hrep hfree) ∈
      BigFppfOver.topology B S hS (twistRelation hnat φ hrep hfree) :=
  BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS
    (twistRelationIncl hnat φ hrep hfree)
    (isOpenImmersion_twistRelationIncl hnat φ hrep hfree)
    (exists_mem_range_twistRelationIncl hnat φ hrep hfree)

/-- A family of morphisms out of the twisted relations glues to a morphism out of their
disjoint union: the inclusions cover it and a representable presheaf is a sheaf. -/
theorem exists_twistRelationHom {Y : BigFppfOver B S hS}
    (σ : ∀ k : twistSupport hnat φ hrep, twistObj hnat φ hrep k.1 ⟶ Y) :
    ∃ τ : twistRelation hnat φ hrep hfree ⟶ Y,
      ∀ k, twistRelationIncl hnat φ hrep hfree k ≫ τ = σ k :=
  BigFppfOver.exists_section_of_disjoint_openCover
    ((isSheaf_iff_isSheaf_of_type _ _).1 (BigFppfOver.isSheaf_yoneda_obj B S hS Y))
    (twistRelationIncl hnat φ hrep hfree)
    (isOpenImmersion_twistRelationIncl hnat φ hrep hfree)
    (fun _ _ hkk' => twistRelationIncl_ne hnat φ hrep hfree hkk')
    (exists_mem_range_twistRelationIncl hnat φ hrep hfree) σ

/-- The target map of the relation of Tag 071S, glued from the first projections of the
twisted relations. -/
noncomputable def twistRelationTarget : twistRelation hnat φ hrep hfree ⟶ U :=
  (exists_twistRelationHom hnat φ hrep hfree
    (fun k => twistTarget hnat φ hrep k.1)).choose

/-- The target map of the relation restricts on each twisted relation to its first
projection. -/
@[simp]
theorem twistRelationIncl_target (k : twistSupport hnat φ hrep) :
    twistRelationIncl hnat φ hrep hfree k ≫ twistRelationTarget hnat φ hrep hfree =
      twistTarget hnat φ hrep k.1 :=
  (exists_twistRelationHom hnat φ hrep hfree
    (fun k => twistTarget hnat φ hrep k.1)).choose_spec k

/-- The source map of the relation of Tag 071S, glued from the second projections of the
twisted relations. -/
noncomputable def twistRelationSource : twistRelation hnat φ hrep hfree ⟶ U :=
  (exists_twistRelationHom hnat φ hrep hfree
    (fun k => twistSource hnat φ hrep k.1)).choose

/-- The source map of the relation restricts on each twisted relation to its second
projection. -/
@[simp]
theorem twistRelationIncl_source (k : twistSupport hnat φ hrep) :
    twistRelationIncl hnat φ hrep hfree k ≫ twistRelationSource hnat φ hrep hfree =
      twistSource hnat φ hrep k.1 :=
  (exists_twistRelationHom hnat φ hrep hfree
    (fun k => twistSource hnat φ hrep k.1)).choose_spec k

/-- The twisted relations as an open cover of the relation of Tag 071S. -/
noncomputable def twistRelationCover :
    Scheme.OpenCover ((BigFppfOver.toScheme B S hS).obj (twistRelation hnat φ hrep hfree)) :=
  Scheme.Cover.mkOfCovers (twistSupport hnat φ hrep)
    (fun k => (BigFppfOver.toScheme B S hS).obj (twistObj hnat φ hrep k.1))
    (fun k => (BigFppfOver.toScheme B S hS).map (twistRelationIncl hnat φ hrep hfree k))
    (fun z => by
      obtain ⟨k, y, hy⟩ := exists_mem_range_twistRelationIncl hnat φ hrep hfree z
      exact ⟨k, y, hy⟩)
    (isOpenImmersion_twistRelationIncl hnat φ hrep hfree)

/-- A morphism out of the relation of Tag 071S is étale when it is étale on each twisted
relation. -/
private theorem etale_twistRelation_of_incl (f : twistRelation hnat φ hrep hfree ⟶ U)
    (h : ∀ k : twistSupport hnat φ hrep, Etale ((BigFppfOver.toScheme B S hS).map
      (twistRelationIncl hnat φ hrep hfree k) ≫ (BigFppfOver.toScheme B S hS).map f)) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f := by
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  exact IsZariskiLocalAtSource.of_openCover (twistRelationCover hnat φ hrep hfree) h

/-- **Both projections of the relation of Tag 071S are étale**, being étale on each twisted
relation, where they are the projections of a base change of the chart. -/
theorem etale_twistRelationSource (hetale : IsChartEtale φ) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (twistRelationSource hnat φ hrep hfree) :=
  etale_twistRelation_of_incl hnat φ hrep hfree _ fun k => by
    rw [← Functor.map_comp, twistRelationIncl_source]
    exact etale_twistSource hnat φ hrep hetale k.1

/-- The target map of the relation of Tag 071S is étale when the chart is. -/
theorem etale_twistRelationTarget (hetale : IsChartEtale φ) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (twistRelationTarget hnat φ hrep hfree) :=
  etale_twistRelation_of_incl hnat φ hrep hfree _ fun k => by
    rw [← Functor.map_comp, twistRelationIncl_target]
    exact etale_twistTarget hnat φ hrep hetale k.1

/-! ### Open subobjects and empty objects of the site -/

/-- Two morphisms of the site out of an object with empty underlying scheme are equal: that
scheme is initial. -/
theorem hom_ext_of_isEmpty {W Y : BigFppfOver B S hS}
    (hW : IsEmpty ((BigFppfOver.toScheme B S hS).obj W)) (a b : W ⟶ Y) : a = b := by
  have := hW
  exact (BigFppfOver.toScheme B S hS).map_injective
    ((isInitialOfIsEmpty (X := (BigFppfOver.toScheme B S hS).obj W)).hom_ext _ _)

/-- There is a morphism of the site out of an object with empty underlying scheme into any
object: the initial morphism of schemes is compatible with the structure morphisms. -/
theorem nonempty_hom_of_isEmpty {W Y : BigFppfOver B S hS}
    (hW : IsEmpty ((BigFppfOver.toScheme B S hS).obj W)) : Nonempty (W ⟶ Y) := by
  have := hW
  obtain ⟨ψ, -⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := W) (Y := Y)
    ((isInitialOfIsEmpty (X := (BigFppfOver.toScheme B S hS).obj W)).to _)
    ((isInitialOfIsEmpty (X := (BigFppfOver.toScheme B S hS).obj W)).hom_ext _ _)
  exact ⟨ψ⟩

/-- The base change of an open immersion of the site along any morphism is again an open
immersion, the functor to schemes preserving fibre products. -/
theorem isOpenImmersion_pullbackFst {T Y Z : BigFppfOver B S hS} (r : T ⟶ Z) (c : Y ⟶ Z)
    (hc : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map c)) :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.fst r c)) :=
  MorphismProperty.of_isPullback
    (((IsPullback.of_hasPullback r c).map (BigFppfOver.toScheme B S hS)).flip) hc

/-- A point of a test object lies in the image of the base change of an open immersion of the
site exactly when its image lies in the image of that open immersion. -/
theorem mem_range_pullbackFst {T Y Z : BigFppfOver B S hS} (r : T ⟶ Z) (c : Y ⟶ Z)
    (hc : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map c))
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pullback.fst r c)).base ↔
      ((BigFppfOver.toScheme B S hS).map r).base x ∈
        Set.range ((BigFppfOver.toScheme B S hS).map c).base := by
  have := hc
  have := isOpenImmersion_pullbackFst r c hc
  have hp : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst r c))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd r c))
      ((BigFppfOver.toScheme B S hS).map r) ((BigFppfOver.toScheme B S hS).map c) :=
    (IsPullback.of_hasPullback r c).map (BigFppfOver.toScheme B S hS)
  have h : ((BigFppfOver.toScheme B S hS).map (pullback.fst r c)).opensRange =
      (BigFppfOver.toScheme B S hS).map r ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map c).opensRange := by
    rw [← Scheme.Hom.opensRange_pullbackFst ((BigFppfOver.toScheme B S hS).map c)
      ((BigFppfOver.toScheme B S hS).map r)]
    simpa only [hp.isoPullback_hom_fst] using Scheme.Hom.opensRange_comp_of_isIso
      hp.isoPullback.hom (pullback.fst ((BigFppfOver.toScheme B S hS).map r)
        ((BigFppfOver.toScheme B S hS).map c))
  exact SetLike.ext_iff.mp h x

/-! ### The relation is the kernel pair of the quotient map -/

/-- **A point of a twisted relation is determined by its two projections**: the twisted
relation is a fibre product, and these are its two projections. -/
theorem twistObj_hom_ext (g : G) {Y : BigFppfOver B S hS}
    {a b : Y ⟶ twistObj hnat φ hrep g}
    (ht : a ≫ twistTarget hnat φ hrep g = b ≫ twistTarget hnat φ hrep g)
    (hs : a ≫ twistSource hnat φ hrep g = b ≫ twistSource hnat φ hrep g) : a = b :=
  (mono_twistPre_aux hnat φ hrep g).right_cancellation a b (prod.hom_ext (by simpa using ht)
    (by simpa using hs))

/-- A point of a twisted relation over a test object, read off its defining property: two
points of `U` whose images in `X` differ by the group element form a point of its relation. -/
noncomputable def twistObjLift (g : G) {T : BigFppfOver B S hS} (x y : T ⟶ U)
    (hxy : φ.app (Opposite.op T) x = g • φ.app (Opposite.op T) y) :
    T ⟶ twistObj hnat φ hrep g :=
  yoneda.preimage ((isPullback_twistObj hnat φ hrep g).lift (yoneda.map x) (yoneda.map y)
    (by
      apply yonedaEquiv.injective
      simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, twistedChart, NatTrans.comp_app,
        ConcreteCategory.comp_apply, spaceActionHom_app] using hxy))

/-- The first projection of `twistObjLift` is the first given point. -/
@[simp]
theorem twistObjLift_target (g : G) {T : BigFppfOver B S hS} (x y : T ⟶ U)
    (hxy : φ.app (Opposite.op T) x = g • φ.app (Opposite.op T) y) :
    twistObjLift hnat φ hrep g x y hxy ≫ twistTarget hnat φ hrep g = x := by
  apply yoneda.map_injective
  rw [Functor.map_comp, twistObjLift, Functor.map_preimage]
  exact (isPullback_twistObj hnat φ hrep g).lift_fst _ _ _

/-- The second projection of `twistObjLift` is the second given point. -/
@[simp]
theorem twistObjLift_source (g : G) {T : BigFppfOver B S hS} (x y : T ⟶ U)
    (hxy : φ.app (Opposite.op T) x = g • φ.app (Opposite.op T) y) :
    twistObjLift hnat φ hrep g x y hxy ≫ twistSource hnat φ hrep g = y := by
  apply yoneda.map_injective
  rw [Functor.map_comp, twistObjLift, Functor.map_preimage]
  exact (isPullback_twistObj hnat φ hrep g).lift_snd _ _ _

/-- **Two points of the relation of Tag 071S with the same source and target agree** over any
object which maps into twisted relations under both of them.

Freeness makes the two indices agree as soon as the object is nonempty, and then a point of a
twisted relation is determined by its projections; over an object with empty underlying
scheme any two morphisms are equal. -/
theorem twistRelation_eq_of_lifts {W T : BigFppfOver B S hS} (w : W ⟶ T)
    {r r' : T ⟶ twistRelation hnat φ hrep hfree}
    (ht : r ≫ twistRelationTarget hnat φ hrep hfree =
      r' ≫ twistRelationTarget hnat φ hrep hfree)
    (hs : r ≫ twistRelationSource hnat φ hrep hfree =
      r' ≫ twistRelationSource hnat φ hrep hfree)
    {k k' : twistSupport hnat φ hrep}
    (a : W ⟶ twistObj hnat φ hrep k.1) (b : W ⟶ twistObj hnat φ hrep k'.1)
    (ha : a ≫ twistRelationIncl hnat φ hrep hfree k = w ≫ r)
    (hb : b ≫ twistRelationIncl hnat φ hrep hfree k' = w ≫ r') :
    w ≫ r = w ≫ r' := by
  by_cases hempty : IsEmpty ((BigFppfOver.toScheme B S hS).obj W)
  · exact hom_ext_of_isEmpty hempty _ _
  · have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj W) := not_isEmpty_iff.mp hempty
    have key (π : twistRelation hnat φ hrep hfree ⟶ U)
        (f : ∀ k : twistSupport hnat φ hrep, twistObj hnat φ hrep k.1 ⟶ U)
        (hf : ∀ k, twistRelationIncl hnat φ hrep hfree k ≫ π = f k) (h : r ≫ π = r' ≫ π) :
        a ≫ f k = b ≫ f k' := by
      rw [← hf, ← hf, ← Category.assoc, ← Category.assoc, ha, hb, Category.assoc,
        Category.assoc, h]
    have htgt := key _ _ (twistRelationIncl_target hnat φ hrep hfree) ht
    have hsrc := key _ _ (twistRelationIncl_source hnat φ hrep hfree) hs
    have hkk' : k = k' :=
      Subtype.ext (eq_of_common_twistPoint hnat φ hrep hfree W hne a b htgt hsrc)
    subst hkk'
    rw [← ha, ← hb, twistObj_hom_ext hnat φ hrep k.1 htgt hsrc]

/-- **A point of the relation of Tag 071S is determined by its source and its target.** This
is the monomorphism `∐_{g ∈ G} R g ⟶ U ×_S U` of the source's proof, read on the test objects
of the site.

The test object is covered by the parts over which the two given points lie in twisted
relations with given indices, and there the previous result applies. -/
theorem twistRelation_point_ext {T : BigFppfOver B S hS}
    {r r' : T ⟶ twistRelation hnat φ hrep hfree}
    (ht : r ≫ twistRelationTarget hnat φ hrep hfree =
      r' ≫ twistRelationTarget hnat φ hrep hfree)
    (hs : r ≫ twistRelationSource hnat φ hrep hfree =
      r' ≫ twistRelationSource hnat φ hrep hfree) : r = r' := by
  classical
  have hoi : ∀ (z : T ⟶ twistRelation hnat φ hrep hfree) (k : twistSupport hnat φ hrep),
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
        (pullback.fst z (twistRelationIncl hnat φ hrep hfree k))) :=
    fun z k => isOpenImmersion_pullbackFst _ _
      (isOpenImmersion_twistRelationIncl hnat φ hrep hfree k)
  refine BigFppfOver.hom_ext_of_openCover
    (W := fun p : twistSupport hnat φ hrep × twistSupport hnat φ hrep =>
      pullback (pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1))
        (pullback.fst r' (twistRelationIncl hnat φ hrep hfree p.2)))
    (fun p => pullback.fst _ _ ≫ pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1))
    (fun p => ?_) (fun x => ?_) (fun p => ?_)
  · rw [Functor.map_comp]
    have := hoi r p.1
    have := isOpenImmersion_pullbackFst
      (pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1))
      (pullback.fst r' (twistRelationIncl hnat φ hrep hfree p.2)) (hoi r' p.2)
    infer_instance
  · obtain ⟨k, y, hy⟩ := exists_mem_range_twistRelationIncl hnat φ hrep hfree
      (((BigFppfOver.toScheme B S hS).map r).base x)
    obtain ⟨k', y', hy'⟩ := exists_mem_range_twistRelationIncl hnat φ hrep hfree
      (((BigFppfOver.toScheme B S hS).map r').base x)
    obtain ⟨z, hz⟩ := (mem_range_pullbackFst r (twistRelationIncl hnat φ hrep hfree k)
      (isOpenImmersion_twistRelationIncl hnat φ hrep hfree k) x).2 ⟨y, hy⟩
    obtain ⟨v, hv⟩ := (mem_range_pullbackFst
      (pullback.fst r (twistRelationIncl hnat φ hrep hfree k))
      (pullback.fst r' (twistRelationIncl hnat φ hrep hfree k')) (hoi r' k') z).2
      (by
        rw [hz]
        exact (mem_range_pullbackFst r' (twistRelationIncl hnat φ hrep hfree k')
          (isOpenImmersion_twistRelationIncl hnat φ hrep hfree k') x).2 ⟨y', hy'⟩)
    refine ⟨(k, k'), v, ?_⟩
    rw [Functor.map_comp]
    change ((BigFppfOver.toScheme B S hS).map
      (pullback.fst r (twistRelationIncl hnat φ hrep hfree k))).base
        (((BigFppfOver.toScheme B S hS).map (pullback.fst _ _)).base v) = x
    rw [hv, hz]
  · have hcond : pullback.fst (pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1))
          (pullback.fst r' (twistRelationIncl hnat φ hrep hfree p.2)) ≫
          pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1) =
        pullback.snd (pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1))
          (pullback.fst r' (twistRelationIncl hnat φ hrep hfree p.2)) ≫
          pullback.fst r' (twistRelationIncl hnat φ hrep hfree p.2) := pullback.condition
    refine twistRelation_eq_of_lifts hnat φ hrep hfree _ ht hs
      (pullback.fst (pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1))
          (pullback.fst r' (twistRelationIncl hnat φ hrep hfree p.2)) ≫
        pullback.snd r (twistRelationIncl hnat φ hrep hfree p.1))
      (pullback.snd (pullback.fst r (twistRelationIncl hnat φ hrep hfree p.1))
          (pullback.fst r' (twistRelationIncl hnat φ hrep hfree p.2)) ≫
        pullback.snd r' (twistRelationIncl hnat φ hrep hfree p.2)) ?_ ?_
    · rw [Category.assoc, Category.assoc, pullback.condition]
    · rw [hcond, Category.assoc, Category.assoc, pullback.condition]

/-! ### The kernel pair of the quotient map -/

section Quotient

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- The chart of `X`, followed by the projection onto the quotient `X/G`. -/
noncomputable abbrev twistQuotientChart :
    yoneda.obj U ⟶ (orbitQuotientSheaf B S hS G X hnat).obj :=
  φ ≫ toOrbitQuotient B S hS G X hnat

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **A point of the relation of Tag 071S over an object carrying two points of `U` which a
group element identifies in `X`.** Over an object with empty underlying scheme there is a
point for lack of anything to check; otherwise the twisted relation of that group element is
nonempty, so it is one of the summands of the relation. -/
theorem exists_twistRelation_point {W : BigFppfOver B S hS} (x y : W ⟶ U) (g : G)
    (hxy : φ.app (Opposite.op W) x = g • φ.app (Opposite.op W) y) :
    ∃ ρ : W ⟶ twistRelation hnat φ hrep hfree,
      ρ ≫ twistRelationTarget hnat φ hrep hfree = x ∧
        ρ ≫ twistRelationSource hnat φ hrep hfree = y := by
  classical
  by_cases hW : IsEmpty ((BigFppfOver.toScheme B S hS).obj W)
  · obtain ⟨ρ⟩ := nonempty_hom_of_isEmpty (Y := twistRelation hnat φ hrep hfree) hW
    exact ⟨ρ, hom_ext_of_isEmpty hW _ _, hom_ext_of_isEmpty hW _ _⟩
  · have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj W) := not_isEmpty_iff.mp hW
    have hk : Nonempty ((BigFppfOver.toScheme B S hS).obj (twistObj hnat φ hrep g)) :=
      ⟨((BigFppfOver.toScheme B S hS).map (twistObjLift hnat φ hrep g x y hxy)).base
        (Classical.choice hne)⟩
    refine ⟨twistObjLift hnat φ hrep g x y hxy ≫
      twistRelationIncl hnat φ hrep hfree ⟨g, hk⟩, ?_, ?_⟩
    · rw [Category.assoc, twistRelationIncl_target, twistObjLift_target]
    · rw [Category.assoc, twistRelationIncl_source, twistObjLift_source]

/-- **The two projections of the relation of Tag 071S agree after the quotient map.** On the
`g`-th twisted relation the two projections differ by `g` in `X`, and the quotient map is
invariant; the twisted relations cover the relation and the quotient is a sheaf. -/
theorem twistRelation_comp_quotientChart :
    yoneda.map (twistRelationTarget hnat φ hrep hfree) ≫ twistQuotientChart hnat φ =
      yoneda.map (twistRelationSource hnat φ hrep hfree) ≫ twistQuotientChart hnat φ := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
  refine (((isSheaf_iff_isSheaf_of_type _ _).1
    (orbitQuotientSheaf B S hS G X hnat).property _
      (ofArrows_twistRelationIncl_mem hnat φ hrep hfree)).isSeparatedFor).ext ?_
  rintro W e ⟨Y, l, e', ⟨k⟩, hcomp⟩
  have hnat₁ := NatTrans.naturality_apply (twistQuotientChart hnat φ) e.op
    (twistRelationTarget hnat φ hrep hfree)
  have hnat₂ := NatTrans.naturality_apply (twistQuotientChart hnat φ) e.op
    (twistRelationSource hnat φ hrep hfree)
  rw [← hnat₁, ← hnat₂]
  change (toOrbitQuotient B S hS G X hnat).app (Opposite.op W)
      (φ.app (Opposite.op W) (e ≫ twistRelationTarget hnat φ hrep hfree)) =
    (toOrbitQuotient B S hS G X hnat).app (Opposite.op W)
      (φ.app (Opposite.op W) (e ≫ twistRelationSource hnat φ hrep hfree))
  have he : e = l ≫ twistRelationIncl hnat φ hrep hfree k := hcomp.symm
  rw [he, Category.assoc, Category.assoc, twistRelationIncl_target, twistRelationIncl_source,
    twistObj_w hnat φ hrep k.1 W l]
  exact toOrbitQuotient_smul B S hS G X hnat k.1 _

/-- **The relation of Tag 071S is the kernel pair of the quotient map.** Two points of the
chart with the same image in `X/G` differ, locally on a covering sieve, by a group element,
by local injectivity of the sheafification map; the resulting local points of the relation
glue, being compatible because a point of the relation is determined by its source and its
target. -/
theorem isPullback_twistRelation :
    IsPullback (yoneda.map (twistRelationTarget hnat φ hrep hfree))
      (yoneda.map (twistRelationSource hnat φ hrep hfree))
      (twistQuotientChart hnat φ) (twistQuotientChart hnat φ) := by
  classical
  refine IsPullback.of_forall_isPullback_app fun Top => ?_
  obtain ⟨T⟩ := Top
  refine (Limits.Types.isPullback_iff _ _ _ _).2
    ⟨NatTrans.congr_app (twistRelation_comp_quotientChart hnat φ hrep hfree) (Opposite.op T),
      fun r r' hrr' => twistRelation_point_ext hnat φ hrep hfree hrr'.1 hrr'.2, ?_⟩
  intro x y hxy
  have hq : (toOrbitQuotient B S hS G X hnat).app (Opposite.op T) (φ.app (Opposite.op T) x) =
      (toOrbitQuotient B S hS G X hnat).app (Opposite.op T) (φ.app (Opposite.op T) y) := hxy
  have hlocal : ∀ ⦃W : BigFppfOver B S hS⦄ (f : W ⟶ T),
      (orbitSieve B S hS G X hnat (φ.app (Opposite.op T) x)
        (φ.app (Opposite.op T) y)).arrows f →
      ∃ ρ : W ⟶ twistRelation hnat φ hrep hfree,
        ρ ≫ twistRelationTarget hnat φ hrep hfree = f ≫ x ∧
          ρ ≫ twistRelationSource hnat φ hrep hfree = f ≫ y := by
    intro W f hf
    obtain ⟨g, hg⟩ := hf
    refine exists_twistRelation_point hnat φ hrep hfree (f ≫ x) (f ≫ y) g ?_
    rw [show φ.app (Opposite.op W) (f ≫ x) =
        X.map f.op (φ.app (Opposite.op T) x) from NatTrans.naturality_apply φ f.op x,
      show φ.app (Opposite.op W) (f ≫ y) =
        X.map f.op (φ.app (Opposite.op T) y) from NatTrans.naturality_apply φ f.op y]
    exact hg.symm
  choose ρ hρt hρs using hlocal
  have hcompat : Presieve.FamilyOfElements.Compatible
      (P := yoneda.obj (twistRelation hnat φ hrep hfree))
      (R := (orbitSieve B S hS G X hnat (φ.app (Opposite.op T) x)
        (φ.app (Opposite.op T) y)).arrows)
      (fun _ f hf => ρ f hf) := by
    intro W₁ W₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    refine twistRelation_point_ext hnat φ hrep hfree ?_ ?_ <;>
    · change (g₁ ≫ ρ f₁ h₁) ≫ _ = (g₂ ≫ ρ f₂ h₂) ≫ _
      simp only [Category.assoc, hρt, hρs]
      rw [← Category.assoc, ← Category.assoc, hcomm]
  obtain ⟨σ, hσ, -⟩ := (isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_yoneda_obj B S hS (twistRelation hnat φ hrep hfree)) _
    (orbitSieve_mem B S hS G X hnat (φ.app (Opposite.op T) x) (φ.app (Opposite.op T) y) hq)
    (fun W f hf => ρ f hf) hcompat
  have hsepU := ((isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_yoneda_obj B S hS U) _
      (orbitSieve_mem B S hS G X hnat (φ.app (Opposite.op T) x)
        (φ.app (Opposite.op T) y) hq)).isSeparatedFor
  refine ⟨σ, hsepU.ext ?_, hsepU.ext ?_⟩
  · intro W f hf
    change f ≫ σ ≫ twistRelationTarget hnat φ hrep hfree = f ≫ x
    rw [← Category.assoc, show f ≫ σ = ρ f hf from hσ f hf, hρt f hf]
  · intro W f hf
    change f ≫ σ ≫ twistRelationSource hnat φ hrep hfree = f ≫ y
    rw [← Category.assoc, show f ≫ σ = ρ f hf from hσ f hf, hρs f hf]

/-- **The relation of Tag 071S is an étale equivalence relation on the chart.** Its two
projections are étale, and it is the kernel pair of a morphism out of the chart. -/
theorem isEtaleEquivalenceRelation_twistRelation (hetale : IsChartEtale φ) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS
      (twistRelationSource hnat φ hrep hfree) (twistRelationTarget hnat φ hrep hfree)) := by
  have htgt : (relation B S hS (twistRelationSource hnat φ hrep hfree)
        (twistRelationTarget hnat φ hrep hfree)).target =
      (Over.post B.inclusion).map (twistRelationTarget hnat φ hrep hfree) := by
    simp only [Stacks.Groupoids.PreRelation.target, relation, prod.lift_fst]
  have hsrc : (relation B S hS (twistRelationSource hnat φ hrep hfree)
        (twistRelationTarget hnat φ hrep hfree)).source =
      (Over.post B.inclusion).map (twistRelationSource hnat φ hrep hfree) := by
    simp only [Stacks.Groupoids.PreRelation.source, relation, prod.lift_snd]
  have : IsEquivalenceRelation
      (relation B S hS (twistRelationSource hnat φ hrep hfree)
        (twistRelationTarget hnat φ hrep hfree)).target
      (relation B S hS (twistRelationSource hnat φ hrep hfree)
        (twistRelationTarget hnat φ hrep hfree)).source := by
    rw [htgt, hsrc]
    exact isEquivalenceRelation_of_isPullback B S hS (twistQuotientChart hnat φ) _ _
      (isPullback_twistRelation hnat φ hrep hfree)
  have : Etale (relation B S hS (twistRelationSource hnat φ hrep hfree)
      (twistRelationTarget hnat φ hrep hfree)).source.left := by
    rw [hsrc]
    exact etale_twistRelationSource hnat φ hrep hfree hetale
  have : Etale (relation B S hS (twistRelationSource hnat φ hrep hfree)
      (twistRelationTarget hnat φ hrep hfree)).target.left := by
    rw [htgt]
    exact etale_twistRelationTarget hnat φ hrep hfree hetale
  exact ⟨⟩

end Quotient

end Twist

section Tag071S

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Stacks 071S.** Let `S` be a scheme, `X` an algebraic space over `S` and `G` an abstract
group acting on `X` by a natural pointwise action. If the action is free then the quotient
`X/G`, the fppf sheafification of the presheaf `T ↦ X(T)/G` of pointwise orbits, is an
algebraic space over `S`.

Freeness is read on the points over the test objects with nonempty underlying scheme
(`AlgebraicGeometry.Space.IsFreeOnNonemptyPoints`); over a test object with empty underlying
scheme a sheaf is terminal, so asking it there would force `G` to be trivial, by
`AlgebraicGeometry.Space.forall_isCancelSMul_iff_subsingleton`.

The proof is the source's. At a surjective étale chart `φ : U ⟶ X` the relation
`R = ∐_{g ∈ G} U ×_{φ, X, g • φ} U` is an object of the site — freeness bounds the index set
by the points of `U ×_S U` — and it is the kernel pair of `U ⟶ X/G`, so it is an étale
equivalence relation, `U/R` is an algebraic space by Tag 02WW, and `X/G ≅ U/R` because both
are the coequalizer of `h_R ⇉ h_U` in fppf sheaves. -/
@[stacks 071S "with freeness read on the points over the test objects with nonempty \
underlying scheme"]
theorem isAlgebraicSpace_orbitQuotientSheaf_of_isFreeOnNonemptyPoints
    (hnat : IsNaturalAction B S hS G X) (hX : IsAlgebraicSpace B S hS X)
    (hfree : IsFreeOnNonemptyPoints B S hS G X) :
    IsAlgebraicSpace B S hS (orbitQuotientSheaf B S hS G X hnat).obj := by
  classical
  obtain ⟨U, φ, hsurj, hetale⟩ := hX.exists_atlas
  have hrep : yoneda.relativelyRepresentable φ := by
    have hall : ∀ (V : BigFppfOver B S hS) (ξ : X.obj (Opposite.op V)),
        yoneda.relativelyRepresentable (yonedaEquiv.symm ξ) :=
      ((yoneda_relativelyRepresentable_diag_tfae_bigFppfOver B S hS X).out 1 2).mp
        hX.diagonal_representable
    simpa only [Equiv.symm_apply_apply] using hall U (yonedaEquiv φ)
  set s := twistRelationSource hnat φ hrep hfree
  set t := twistRelationTarget hnat φ hrep hfree
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation (relation B S hS s t) :=
    isEtaleEquivalenceRelation_twistRelation hnat φ hrep hfree hetale
  let RF : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj (twistRelation hnat φ hrep hfree), BigFppfOver.isSheaf_yoneda_obj B S hS _⟩
  let UF : Sheaf (BigFppfOver.topology B S hS) (Type u) :=
    ⟨yoneda.obj U, BigFppfOver.isSheaf_yoneda_obj B S hS U⟩
  let tf : RF ⟶ UF := ⟨yoneda.map t⟩
  let sf : RF ⟶ UF := ⟨yoneda.map s⟩
  let qf : UF ⟶ orbitQuotientSheaf B S hS G X hnat := ⟨twistQuotientChart hnat φ⟩
  let pf : UF ⟶ Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
      (Over.post B.inclusion) (relation B S hS s t) := ⟨quotientMap B S hS s t⟩
  have hsq := isPullback_twistRelation hnat φ hrep hfree
  have hsq' := quotientMap_isPullback B S hS s t
  have hwq : tf ≫ qf = sf ≫ qf := Sheaf.hom_ext hsq.w
  have hwp : tf ≫ pf = sf ≫ pf := Sheaf.hom_ext hsq'.w
  have hlocq : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (twistQuotientChart hnat φ) := by
    have h1 : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ :=
      isLocallySurjective_of_surjective_etale B S hS φ hsurj hetale
    have h2 := isLocallySurjective_toOrbitQuotient B S hS G X hnat
    exact Presheaf.isLocallySurjective_comp (BigFppfOver.topology B S hS) φ
      (toOrbitQuotient B S hS G X hnat)
  have hlocp : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (quotientMap B S hS s t) :=
    isLocallySurjective_of_surjective_etale B S hS _
      (quotientMap_surjective_unconditional B S hS s t)
      (quotientMap_etale_unconditional B S hS s t)
  have hcq := Sheaf.isColimitCoforkOfKernelPair tf sf qf hwq
    (fun V x y hxy => Limits.Types.exists_of_isPullback (hsq.app (Opposite.op V)) x y hxy) hlocq
  have hcp := Sheaf.isColimitCoforkOfKernelPair tf sf pf hwp
    (fun V x y hxy => Limits.Types.exists_of_isPullback (hsq'.app (Opposite.op V)) x y hxy) hlocp
  exact isAlgebraicSpace_of_iso B S hS
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso
      (IsColimit.coconePointUniqueUpToIso hcp hcq))
    (isAlgebraicSpace_quotient_unconditional B S hS s t)

end Tag071S

end AlgebraicGeometry.Space

end
