module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.Topology.Maps.OpenSurjectiveDescent

/-!
# The points of an immersion of algebraic stacks (Stacks 0H20)

Let `f : 𝒳 ⟶ 𝒴` be an immersion of algebraic stacks over `S` (**Stacks 04YL**, part (3)).
**Stacks 0H20** asserts that the induced map `|f| : |𝒳| → |𝒴|` on the topological spaces of
points of **Stacks 04XG** and **Stacks 04XL** is a homeomorphism onto a locally closed subset of
`|𝒴|`, and that `|f|` is closed, respectively open, when `f` is a closed, respectively open,
immersion. The source leaves the proof out; the one below is the usual chart argument.

Choose a chart `c : 𝒰 ⟶ 𝒴` by the slice `𝒰` of the big fppf site of `S` over a scheme `U`, open
and surjective on points; `𝒰` is represented by the presheaf `h_U` that `U` represents. Because
`f` is representable by algebraic spaces, the 2-fibre product `𝒰 ×_𝒴 𝒳` is represented by an
algebraic space `F`, and the morphism `i : F ⟶ h_U` of representing presheaves induced by its
projection to `𝒰` is an immersion of algebraic spaces — the condition of **Stacks 04XB** *is*
that condition, read at the scheme-valued point of `𝒴` that `c` names. The two representing
charts are homeomorphisms on points, so `|i|` sits in a square

```text
|F| --a--> |𝒳|
 |          |
|i|        |f|
 v          v
|h_U| --b-> |𝒴|
```

with `b` continuous, open and surjective, `a` continuous, and with `|F| → |h_U| ×_{|𝒴|} |𝒳|`
surjective by **Stacks 04XH**. All four conclusions descend along such a square. Openness and
closedness are `StacksFrontier.Topology.Maps.OpenSurjectiveDescent`; the embedding property and
local closedness of the image are the two statements added here, and the space-level inputs for
them are **Stacks 0ABJ** and **Stacks 04CD**.

Both added descent statements turn on the same two set computations. For the embedding, an open
set of `|𝒳|` pulls back along `a` to an open set of `|F|`, which is the `|i|`-preimage of an open
set `Ω` of `|h_U|` because `|i|` is inducing; then `b '' Ω` is open and its `|f|`-preimage is the
original open set, both inclusions by the surjectivity of the canonical map. For the image, the
`b`-preimage of the image of `|f|` is the image of `|i|`, and local closedness descends along a
continuous open surjection by Topology, Lemma 02YB. Injectivity of `|f|` is read off the square
as well, rather than from `f` being a monomorphism (**Stacks 0504**): a point of `|𝒳|` lifts to
`|F|` because `b` is surjective and the canonical map is, and two lifts over one point of `|h_U|`
agree because `|i|` is injective.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isEmbedding_pointsMap_of_isImmersion` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyClosed_range_pointsMap_of_isImmersion`:
  **Stacks 0H20**, the homeomorphism onto a locally closed subset, in the two halves such a
  statement splits into.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isClosedMap_pointsMap_of_isClosedImmersion` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion`:
  **Stacks 0H20**, closedness and openness of `|f|`.

## Implementation notes

The chart is taken on the *slice* of the ambient site over `U` rather than on the big fppf site
of `U`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion`: the bridge
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`, which identifies the morphism of
representing presheaves induced by the projection of the base change with the structural
morphism `Λ_U T ⟶ h_U` of the lower-shriek extension, is stated for that model, and
`AlgebraicGeometry.Stack.exists_sliceChart_isOpenMap_surjective` supplies a chart there which is
open and surjective on points.

`AlgebraicGeometry.Stack.exists_pointsMap_descent_square` isolates the square once, for an
arbitrary property of morphisms of algebraic spaces respecting isomorphisms, so that the four
conclusions differ only in the space-level input they feed to it. Its hypothesis is the
quantifier of Stacks 04XB written out rather than `AlgebraicGeometry.Stack.HasRelativeProperty`,
which carries an instance hypothesis of locality at the target for the fppf precoverage — for
the three immersion properties that is Stacks 041X, 0420 and 042U, which this library does not
have. Writing the quantifier out gives the same proposition with no hypothesis on the property,
exactly as in `StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack`, so none of the four
results below is gated on those tags. Only `MorphismProperty.RespectsIso` is used, through
`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`. The presheaf `F` it produces is the
lower-shriek extension of a presheaf representing the base change of `f` along the scheme-valued
point the chart names, `G` is the presheaf that scheme represents, and `i` is the structural
morphism of the extension.

## References

* [Stacks Project, Tag 02YB](https://stacks.math.columbia.edu/tag/02YB)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 0H20](https://stacks.math.columbia.edu/tag/0H20)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

/-! ### Descent of an embedding and of local closedness along an open surjection -/

section Descent

/-- In a commutative square `b ∘ p = q ∘ a` with `b` surjective and the canonical map
`A → A' ×_{C'} C` surjective, `q` is injective as soon as `p` is: a point of `C` lifts to `A`,
and two lifts over one point of `A'` agree. -/
private theorem injective_of_comm_of_fibreSurjective {A A' C C' : Type*}
    {p : A → A'} {a : A → C} {q : C → C'} {b : A' → C'} (hbsurj : Function.Surjective b)
    (hfib : ∀ (y : A') (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (hp : Function.Injective p) : Function.Injective q := by
  intro c₁ c₂ h
  obtain ⟨y, hy⟩ := hbsurj (q c₁)
  obtain ⟨x₁, hx₁p, hx₁a⟩ := hfib y c₁ hy
  obtain ⟨x₂, hx₂p, hx₂a⟩ := hfib y c₂ (hy.trans h)
  rw [← hx₁a, ← hx₂a, hp (hx₁p.trans hx₂p.symm)]

/-- Being a topological embedding descends along an open surjection: in a commutative square
`b ∘ p = q ∘ a` with `b` open and surjective, `a` and `q` continuous, and the canonical map
`A → A' ×_{C'} C` surjective, `q` is an embedding as soon as `p` is. -/
private theorem isEmbedding_of_comm_of_fibreSurjective {A A' C C' : Type*}
    [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace C] [TopologicalSpace C']
    {p : A → A'} {a : A → C} {q : C → C'} {b : A' → C'} (hbopen : IsOpenMap b)
    (hbsurj : Function.Surjective b) (hacont : Continuous a) (hqcont : Continuous q)
    (hfib : ∀ (y : A') (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (hp : Topology.IsEmbedding p) : Topology.IsEmbedding q := by
  refine ⟨?_, injective_of_comm_of_fibreSurjective hbsurj hfib hp.injective⟩
  refine (Topology.isInducing_iff q).mpr (le_antisymm (continuous_iff_le_induced.mp hqcont)
    (TopologicalSpace.le_def.mpr fun W hW => isOpen_induced_iff.mpr ?_))
  obtain ⟨Ω, hΩ, hΩeq⟩ := hp.isInducing.isOpen_iff.mp (hW.preimage hacont)
  have key : ∀ (y : A') (c : C), b y = q c → (y ∈ Ω ↔ c ∈ W) := fun y c hy => by
    obtain ⟨x, hxp, hxa⟩ := hfib y c hy
    rw [← hxp, ← hxa, ← Set.mem_preimage, ← Set.mem_preimage (f := a), hΩeq]
  refine ⟨b '' Ω, hbopen _ hΩ, Set.ext fun c => ⟨?_, fun hc => ?_⟩⟩
  · rintro ⟨y, hyΩ, hy⟩
    exact (key y c hy).mp hyΩ
  · obtain ⟨y, hy⟩ := hbsurj (q c)
    exact ⟨y, (key y c hy).mpr hc, hy⟩

/-- Local closedness of the image descends along a continuous open surjection: in a commutative
square `b ∘ p = q ∘ a` with `b` continuous, open and surjective and the canonical map
`A → A' ×_{C'} C` surjective, the image of `q` is locally closed as soon as the image of `p` is. -/
private theorem isLocallyClosed_range_of_comm_of_fibreSurjective {A A' C C' : Type*}
    [TopologicalSpace A'] [TopologicalSpace C']
    {p : A → A'} {a : A → C} {q : C → C'} {b : A' → C'}
    (hcomm : ∀ x, b (p x) = q (a x)) (hbcont : Continuous b) (hbopen : IsOpenMap b)
    (hbsurj : Function.Surjective b)
    (hfib : ∀ (y : A') (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (hp : IsLocallyClosed (Set.range p)) : IsLocallyClosed (Set.range q) := by
  refine Space.isLocallyClosed_of_isLocallyClosed_preimage hbcont hbopen hbsurj ?_
  rw [← Set.image_univ, preimage_image_eq_image_preimage_of_comm_of_surjective hcomm hfib,
    Set.preimage_univ, Set.image_univ]
  exact hp

end Descent

/-! ### The square attached to a chart of the target -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks whose base changes along scheme-valued points
of `𝒴` all have `P` fits in a commutative square `b ∘ |i| = |f| ∘ a` with `i` a morphism of
algebraic spaces having `P`, `b` continuous open surjective, `a` continuous, and the canonical
map `|F| → |G| ×_{|𝒴|} |𝒳|` surjective. -/
private theorem exists_pointsMap_descent_square
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
      (_hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
      (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
          (CatFiberedInGroupoids.homFunctor f.hom))
        (presheafOfCategories (T ⋙ typeToCat)).p) →
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩))) :
    ∃ (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
      (hG : IsAlgebraicSpace B S hS G) (i : F ⟶ G)
      (a : Space.points B S hS F → points B S hS 𝒳.val.val 𝒳.val.property)
      (b : Space.points B S hS G → points B S hS 𝒴.val.val 𝒴.val.property),
      P (ObjectProperty.homMk i : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) ∧
      (∀ x, b (Space.pointsMap B S hS F i x) =
        pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom (a x)) ∧
      @Continuous _ _ (Space.pointTopology B S hS G) (pointTopology B S hS 𝒴.val) b ∧
      @IsOpenMap _ _ (Space.pointTopology B S hS G) (pointTopology B S hS 𝒴.val) b ∧
      Function.Surjective b ∧
      @Continuous _ _ (Space.pointTopology B S hS F) (pointTopology B S hS 𝒳.val) a ∧
      ∀ (z : Space.points B S hS G) (x : points B S hS 𝒳.val.val 𝒳.val.property),
        b z = pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom x →
        ∃ v, Space.pointsMap B S hS F i v = z ∧ a v = x := by
  classical
  obtain ⟨U, c, hcsurj, hcopen⟩ := exists_sliceChart_isOpenMap_surjective B S hS 𝒴
  let cMor : schemeSlice B S hS U ⟶ 𝒴.val := Bicategory.InducedBicategory.mkHom c
  let y := CatFiberedInGroupoids.homFunctor cMor
  have hy : y ⋙ 𝒴.val.val.p = Over.map U.hom := CatFiberedInGroupoids.homFunctor_comp_p cMor
  obtain ⟨T, hT, ⟨eT⟩⟩ := hf U y hy
  let F := (OverShriek.relocalizePresheafFunctor U.hom).obj T
  have hF : IsAlgebraicSpace B S hS F :=
    isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT
  have hG : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) f.hom
  have hQ := CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) f.hom
  let eF := relocalizeFibreEquivalence B S hS U f.hom y T eT
  let eG := schemeSliceEquivalenceOver B S hS U
  have hi : representingMap B S hS Q.pt (schemeSlice B S hS U) F (yoneda.obj U) eF eG Q.fst =
      OverShriek.relocalizeToYoneda U.hom T :=
    representingMap_relocalizeFibre B S hS U f.hom y T eT hy
  let _ := Space.pointTopology B S hS F
  let _ := Space.pointTopology B S hS (yoneda.obj U)
  let _ := pointTopology B S hS Q.pt
  let _ := pointTopology B S hS (schemeSlice B S hS U)
  let _ := pointTopology B S hS 𝒳.val
  let _ := pointTopology B S hS 𝒴.val
  obtain ⟨σ, τ, hσ, hτ, hnat⟩ :
      ∃ (σ : Space.points B S hS F → points B S hS Q.pt.val Q.pt.property)
        (τ : Space.points B S hS (yoneda.obj U) →
          points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property),
        IsHomeomorph σ ∧ IsHomeomorph τ ∧
        ∀ v, τ (Space.pointsMap B S hS F (OverShriek.relocalizeToYoneda U.hom T) v) =
          pointsMap B S hS Q.pt.val Q.pt.property (schemeSlice B S hS U).property
            Q.fst.hom (σ v) :=
    ⟨_, _, isHomeomorph_spacePointMap_representing B S hS F hF Q.pt eF,
      isHomeomorph_spacePointMap_representing B S hS (yoneda.obj U) hG
        (schemeSlice B S hS U) eG, fun v => by
        rw [← hi]
        exact spacePointMap_representing_naturality B S hS F (yoneda.obj U) Q.pt
          (schemeSlice B S hS U) eF eG Q.fst v⟩
  have hsq : ∀ r, pointsMap B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property
        𝒴.val.property cMor.hom
        (pointsMap B S hS Q.pt.val Q.pt.property (schemeSlice B S hS U).property Q.fst.hom r) =
      pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom
        (pointsMap B S hS Q.pt.val Q.pt.property 𝒳.val.property Q.snd.hom r) := fun r =>
    (pointsMap_comp B S hS _ _ (schemeSlice B S hS U).property 𝒴.val.property
        Q.fst.hom cMor.hom r).trans
      ((congrFun (pointsMap_eq_of_basedNatTrans B S hS Q.pt.val Q.pt.property 𝒴.val.property
          Q.iso.hom.hom) r).trans
        (pointsMap_comp B S hS _ _ 𝒳.val.property 𝒴.val.property
          Q.snd.hom f.hom.hom r).symm)
  refine ⟨F, yoneda.obj U, hF, hG, OverShriek.relocalizeToYoneda U.hom T,
    fun v => pointsMap B S hS Q.pt.val Q.pt.property 𝒳.val.property Q.snd.hom (σ v),
    fun z => pointsMap B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property
      𝒴.val.property cMor.hom (τ z),
    (prop_algebraicSpaceMap_iff B S hS P U T hT).mp (hP U y hy T hT ⟨eT⟩),
    fun v => (congrArg (pointsMap B S hS (schemeSlice B S hS U).val
        (schemeSlice B S hS U).property 𝒴.val.property cMor.hom) (hnat v)).trans (hsq (σ v)),
    (continuous_pointsMap B S hS (schemeSlice B S hS U) 𝒴.val cMor.hom).comp hτ.continuous,
    hcopen.comp hτ.isOpenMap, hcsurj.comp hτ.bijective.surjective,
    (continuous_pointsMap B S hS Q.pt 𝒳.val Q.snd.hom).comp hσ.continuous, fun z x hz => ?_⟩
  obtain ⟨r, hr₁, hr₂⟩ := exists_point_of_isTwoFibreProduct B S hS Q hQ (τ z) x hz
  obtain ⟨v, hv⟩ := hσ.bijective.surjective r
  exact ⟨v, hτ.bijective.injective ((hnat v).trans (by rw [hv]; exact hr₁)), by
    change pointsMap B S hS Q.pt.val Q.pt.property 𝒳.val.property Q.snd.hom (σ v) = x
    rw [hv]; exact hr₂⟩

/-! ### Stacks 0H20 -/

namespace AlgebraicStacks

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0H20, the homeomorphism onto the image.** An immersion of algebraic stacks over `S`
is a topological embedding on the spaces of points of Stacks 04XG and 04XL. -/
@[stacks 0H20 "homeomorphism onto the image"]
theorem isEmbedding_pointsMap_of_isImmersion (f : 𝒳 ⟶ 𝒴) (hf : IsImmersion B S hS f) :
    @Topology.IsEmbedding _ _ (Stack.pointTopology B S hS 𝒳.val)
      (Stack.pointTopology B S hS 𝒴.val)
      (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom) := by
  obtain ⟨F, G, hF, hG, i, a, b, hP, hcomm, hbcont, hbopen, hbsurj, hacont, hfib⟩ :=
    Stack.exists_pointsMap_descent_square B S hS (Space.immersionProperty B S hS) f hf.1 hf.2
  let _ := Space.pointTopology B S hS F
  let _ := Space.pointTopology B S hS G
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  exact Stack.isEmbedding_of_comm_of_fibreSurjective hbopen hbsurj hacont
    (Stack.continuous_pointsMap B S hS 𝒳.val 𝒴.val f.hom.hom) hfib
    (Space.isEmbedding_pointsMap_of_isImmersion B S hS hG i hP)

/-- **Stacks 0H20, the locally closed image.** The image on points of an immersion of algebraic
stacks over `S` is a locally closed subset of the space of points of the target. -/
@[stacks 0H20 "locally closed image"]
theorem isLocallyClosed_range_pointsMap_of_isImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : IsImmersion B S hS f) :
    @IsLocallyClosed _ (Stack.pointTopology B S hS 𝒴.val)
      (Set.range (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom)) := by
  obtain ⟨F, G, hF, hG, i, a, b, hP, hcomm, hbcont, hbopen, hbsurj, hacont, hfib⟩ :=
    Stack.exists_pointsMap_descent_square B S hS (Space.immersionProperty B S hS) f hf.1 hf.2
  let _ := Space.pointTopology B S hS F
  let _ := Space.pointTopology B S hS G
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  exact Stack.isLocallyClosed_range_of_comm_of_fibreSurjective hcomm hbcont hbopen hbsurj hfib
    (Space.isLocallyClosed_range_pointsMap_of_isImmersion B S hS hG i hP)

/-- **Stacks 0H20, closed immersions.** A closed immersion of algebraic stacks over `S` is a
closed map on the spaces of points of Stacks 04XG and 04XL. -/
@[stacks 0H20 "closed immersions are closed on points"]
theorem isClosedMap_pointsMap_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : IsClosedImmersion B S hS f) :
    @IsClosedMap _ _ (Stack.pointTopology B S hS 𝒳.val) (Stack.pointTopology B S hS 𝒴.val)
      (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom) := by
  obtain ⟨F, G, hF, hG, i, a, b, hP, hcomm, hbcont, hbopen, hbsurj, hacont, hfib⟩ :=
    Stack.exists_pointsMap_descent_square B S hS (Space.closedImmersionProperty B S hS) f
      hf.1 hf.2
  let _ := Space.pointTopology B S hS F
  let _ := Space.pointTopology B S hS G
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  refine isClosedMap_of_isClosedMap_comm_of_isOpenMap_surjective hcomm hbopen hbsurj hacont
    hfib ?_
  exact (Topology.IsClosedEmbedding.mk
    (Space.isEmbedding_pointsMap_of_isImmersion B S hS hG i
      (Space.isImmersion_of_isClosedImmersion B S hS hP))
    (Space.isClosed_range_pointsMap_of_isClosedImmersion B S hS hG i hP)).isClosedMap

/-- **Stacks 0H20, open immersions.** An open immersion of algebraic stacks over `S` is an open
map on the spaces of points of Stacks 04XG and 04XL. -/
@[stacks 0H20 "open immersions are open on points"]
theorem isOpenMap_pointsMap_of_isOpenImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : IsOpenImmersion B S hS f) :
    @IsOpenMap _ _ (Stack.pointTopology B S hS 𝒳.val) (Stack.pointTopology B S hS 𝒴.val)
      (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom) := by
  obtain ⟨F, G, hF, hG, i, a, b, hP, hcomm, hbcont, hbopen, hbsurj, hacont, hfib⟩ :=
    Stack.exists_pointsMap_descent_square B S hS (Space.openImmersionProperty B S hS) f
      hf.1 hf.2
  let _ := Space.pointTopology B S hS F
  let _ := Space.pointTopology B S hS G
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  exact isOpenMap_of_isOpenMap_comm_of_isOpenMap_surjective hcomm hbopen hbsurj hacont hfib
    (Space.isOpenMap_pointsMap_of_isOpenImmersion B S hS i hP)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
