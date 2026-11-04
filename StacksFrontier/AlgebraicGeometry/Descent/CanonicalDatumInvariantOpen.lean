module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvariantOpen

/-!
# Invariant opens of a canonical descent datum come from the base

Let `f i : X i ⟶ S` be a family of morphisms of schemes with common target and let `U` be a
scheme over `S`. The canonical descent datum of `U` has `U ×_S X i` for its component at `i`,
and a family of open subschemes `W i ⊆ U ×_S X i` is invariant exactly when the canonical
gluing isomorphisms carry `W i ×_S X j` onto `X i ×_S W j`. When the family is an fpqc covering
of `S`, such a family of opens is the family of inverse images of one open subscheme of `U`,
and that open subscheme is unique.

This is the step in the proof of Stacks 0AP4 which produces the opens `U_{ij} ⊆ U_i` from the
opens `α_i^{-1}(W_i ∩ W_j)` of `X ×_S U_i`.

## Main definitions

* `AlgebraicGeometry.CanonicalDatum.componentPair` is the fibre product over `U` of two
  components of the canonical descent datum, with projections
  `AlgebraicGeometry.CanonicalDatum.componentPairFst` and
  `AlgebraicGeometry.CanonicalDatum.componentPairSnd` and the universal map
  `AlgebraicGeometry.CanonicalDatum.componentPairLift`.
* `AlgebraicGeometry.CanonicalDatum.componentPairToSource` and
  `AlgebraicGeometry.CanonicalDatum.componentPairToTarget` identify it with the source
  `(U ×_S X) ×_S Y` and the target `X ×_S (U ×_S Y)` of a canonical gluing isomorphism; they are
  isomorphisms, `AlgebraicGeometry.CanonicalDatum.componentPairToSourceIso` and
  `AlgebraicGeometry.CanonicalDatum.componentPairToTargetIso`.

## Main results

* `AlgebraicGeometry.CanonicalDatum.componentPairToSource_comp_transition`: under these
  identifications the canonical gluing isomorphism is the swap of the two outer factors, that
  is, it is the identity of `componentPair` read through the two descriptions. This is the
  identification which converts invariance into the hypothesis of Stacks 03N0.
* `AlgebraicGeometry.CanonicalDatum.preimage_fst_eq_preimage_snd_of_preimage_eq` and
  `AlgebraicGeometry.CanonicalDatum.preimage_fst_eq_preimage_snd_of_isInvariantOpens`: an
  invariant family of opens of the components of the canonical datum has the same inverse image
  under the two projections of `(U ×_S X i) ×_U (U ×_S X j)`.
* `AlgebraicGeometry.ofArrows_pullback_fst_mem_fpqcPrecoverage`: an fpqc covering stays one
  after base change.
* `AlgebraicGeometry.CanonicalDatum.existsUnique_preimage_eq_of_isInvariantOpens` and
  `AlgebraicGeometry.CanonicalDatum.existsUnique_preimage_eq_opensRange`: for an fpqc covering
  family, an invariant family of opens — given either directly or as the images of a morphism
  of descent data with open-immersion components — is the family of inverse images of a unique
  open subscheme of `U`. The specializations to a single surjective quasi-compact flat morphism
  are `AlgebraicGeometry.CanonicalDatum.existsUnique_preimage_eq_of_isInvariantOpens_of_flat`
  and `AlgebraicGeometry.CanonicalDatum.existsUnique_preimage_eq_opensRange_of_flat`.
* `AlgebraicGeometry.CanonicalDatum.existsUnique_preimage_eq_of_preimage_eq` is the same
  conclusion for an arbitrary family of gluing maps between the two products which preserves the
  projection to `U` and the projection to the member of the family. Only those two properties
  of the canonical gluing isomorphism are used, so the statement applies to every realization of
  the canonical descent datum and not only to `AlgebraicGeometry.CanonicalDatum.datum`.

## Implementation notes

Invariance is a condition on the products `(U ×_S X i) ×_S X j` in `Over S` which carry the
gluing isomorphisms, while Stacks 03N0 is a condition on the fibre products
`(U ×_S X i) ×_U (U ×_S X j)` over `U`. The two are matched by `componentPair`, which is the
latter viewed as a scheme over `S`: the comparison `componentPairToSource` carries its first
projection to the projection of the product, and the composite of the gluing isomorphism with
the second projection of the product to its second projection. So the gluing isomorphism is
nothing but the exchange of the two descriptions, which is the content of
`componentPairToSource_comp_transition`.

Every statement is written in the single coordinate system of the literal fibre products
`pullback U.hom (f i)` and their projections `pullback.fst U.hom (f i)`, which is what the
components of the canonical datum are; `componentPair` pins that choice by its declared type.
The passage from the unfolded canonical datum to the datum itself happens only in hypothesis
position, where definitional unfolding suffices.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- **An fpqc covering stays an fpqc covering after base change.** -/
lemma ofArrows_pullback_fst_mem_fpqcPrecoverage {I : Type v} {S T : Scheme.{u}}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S) (g : T ⟶ S) :
    Presieve.ofArrows (fun i ↦ pullback g (f i)) (fun i ↦ pullback.fst g (f i)) ∈
      Scheme.fpqcPrecoverage T :=
  Precoverage.mem_coverings_of_isPullback f hf g _ (fun i ↦ pullback.snd g (f i))
    fun i ↦ IsPullback.of_hasPullback g (f i)

namespace CanonicalDatum

variable {S X Y : Scheme.{u}} (U : Over S) (f : X ⟶ S) (g : Y ⟶ S)

/-- The morphism underlying `originalProjection U f` is the first projection of `U ×_S X`. -/
@[simp]
lemma originalProjection_left : (originalProjection U f).left = pullback.fst U.hom f := rfl

/-- The fibre product over `U` of two components of the canonical descent datum of `U`, viewed
as a scheme over `S`. Its points are the triples of a point of `U`, a point of `X` and a point
of `Y` lying over one point of `S`. -/
abbrev componentPair : Over S :=
  Over.mk (pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) ≫
    pullback.snd U.hom f ≫ f)

/-- The projection of `componentPair U f g` to the component `U ×_S X`. -/
def componentPairFst : componentPair U f g ⟶ component U f :=
  Over.homMk (pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g)) rfl

/-- The morphism underlying `componentPairFst U f g` is the first projection of the fibre
product. -/
@[simp]
lemma componentPairFst_left :
    (componentPairFst U f g).left =
      pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) := rfl

/-- The projection of `componentPair U f g` to the component `U ×_S Y`. -/
def componentPairSnd : componentPair U f g ⟶ component U g :=
  Over.homMk (pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g))
    (by
      have hw : (componentPair U f g).hom =
          pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) ≫
            pullback.snd U.hom f ≫ f := rfl
      have ht : (component U g).hom = pullback.snd U.hom g ≫ g := rfl
      rw [hw, ht, ← pullback.condition (f := U.hom) (g := g),
        ← pullback.condition (f := U.hom) (g := f)]
      simp only [← Category.assoc]
      rw [pullback.condition])

/-- The morphism underlying `componentPairSnd U f g` is the second projection of the fibre
product. -/
@[simp]
lemma componentPairSnd_left :
    (componentPairSnd U f g).left =
      pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g) := rfl

/-- The two projections of `componentPair U f g` agree after projecting further to `U`. -/
@[reassoc]
lemma componentPairFst_comp_originalProjection :
    componentPairFst U f g ≫ originalProjection U f =
      componentPairSnd U f g ≫ originalProjection U g :=
  Over.OverMorphism.ext
    (by simpa using pullback.condition (f := pullback.fst U.hom f) (g := pullback.fst U.hom g))

/-- A map into `componentPair U f g`, given its two projections. -/
def componentPairLift {T : Over S} (a : T ⟶ component U f) (b : T ⟶ component U g)
    (h : a ≫ originalProjection U f = b ≫ originalProjection U g) :
    T ⟶ componentPair U f g :=
  Over.homMk (pullback.lift a.left b.left (by simpa using congrArg Over.Hom.left h))
    (by
      have hw : (componentPair U f g).hom =
          pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) ≫
            pullback.snd U.hom f ≫ f := rfl
      rw [hw, ← Category.assoc, pullback.lift_fst]
      exact Over.w a)

/-- The first projection of `componentPairLift U f g a b h` is `a`. -/
@[reassoc (attr := simp)]
lemma componentPairLift_fst {T : Over S} (a : T ⟶ component U f) (b : T ⟶ component U g)
    (h : a ≫ originalProjection U f = b ≫ originalProjection U g) :
    componentPairLift U f g a b h ≫ componentPairFst U f g = a :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- The second projection of `componentPairLift U f g a b h` is `b`. -/
@[reassoc (attr := simp)]
lemma componentPairLift_snd {T : Over S} (a : T ⟶ component U f) (b : T ⟶ component U g)
    (h : a ≫ originalProjection U f = b ≫ originalProjection U g) :
    componentPairLift U f g a b h ≫ componentPairSnd U f g = b :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- Maps into `componentPair U f g` are determined by their two projections. -/
lemma componentPair_hom_ext {T : Over S} {a b : T ⟶ componentPair U f g}
    (h₁ : a ≫ componentPairFst U f g = b ≫ componentPairFst U f g)
    (h₂ : a ≫ componentPairSnd U f g = b ≫ componentPairSnd U f g) : a = b :=
  Over.OverMorphism.ext
    (pullback.hom_ext (congrArg Over.Hom.left h₁) (congrArg Over.Hom.left h₂))

/-- The comparison of `componentPair U f g` with the source `(U ×_S X) ×_S Y` of the canonical
gluing isomorphism. -/
def componentPairToSource : componentPair U f g ⟶ component U f ⨯ Over.mk g :=
  prod.lift (componentPairFst U f g)
    (componentPairSnd U f g ≫ structureMap g ((Over.pullback g).obj U))

/-- The first component of `componentPairToSource U f g` is `componentPairFst U f g`. -/
@[reassoc (attr := simp)]
lemma componentPairToSource_fst :
    componentPairToSource U f g ≫ prod.fst = componentPairFst U f g := by
  simp [componentPairToSource]

/-- The second component of `componentPairToSource U f g` is `componentPairSnd U f g` followed
by the projection of `U ×_S Y` to `Y`. -/
@[reassoc (attr := simp)]
lemma componentPairToSource_snd :
    componentPairToSource U f g ≫ prod.snd =
      componentPairSnd U f g ≫ structureMap g ((Over.pullback g).obj U) := by
  simp [componentPairToSource]

/-- The comparison of `componentPair U f g` with the target `X ×_S (U ×_S Y)` of the canonical
gluing isomorphism. -/
def componentPairToTarget : componentPair U f g ⟶ Over.mk f ⨯ component U g :=
  prod.lift (componentPairFst U f g ≫ structureMap f ((Over.pullback f).obj U))
    (componentPairSnd U f g)

/-- The first component of `componentPairToTarget U f g` is `componentPairFst U f g` followed
by the projection of `U ×_S X` to `X`. -/
@[reassoc (attr := simp)]
lemma componentPairToTarget_fst :
    componentPairToTarget U f g ≫ prod.fst =
      componentPairFst U f g ≫ structureMap f ((Over.pullback f).obj U) := by
  simp [componentPairToTarget]

/-- The second component of `componentPairToTarget U f g` is `componentPairSnd U f g`. -/
@[reassoc (attr := simp)]
lemma componentPairToTarget_snd :
    componentPairToTarget U f g ≫ prod.snd = componentPairSnd U f g := by
  simp [componentPairToTarget]

/-- **The canonical gluing isomorphism is the swap of the two outer factors.** Read through the
identifications of `componentPair U f g` with the source and the target of the gluing
isomorphism of the canonical descent datum, that isomorphism is the identity: it preserves the
point of `U` and the points of `X` and of `Y`, exchanging only which of the latter two is
grouped with the point of `U`. -/
@[reassoc]
theorem componentPairToSource_comp_transition :
    componentPairToSource U f g ≫ transition U f g = componentPairToTarget U f g := by
  apply prod.hom_ext
  · simp
  · apply component_hom_ext <;> simp [componentPairFst_comp_originalProjection]

/-- The comparison with the source of the gluing isomorphism is an isomorphism. -/
def componentPairToSourceIso : componentPair U f g ≅ component U f ⨯ Over.mk g where
  hom := componentPairToSource U f g
  inv := componentPairLift U f g prod.fst
    (componentLift (prod.fst ≫ originalProjection U f) prod.snd) (by simp)
  hom_inv_id := by
    apply componentPair_hom_ext
    · simp
    · apply component_hom_ext <;> simp [componentPairFst_comp_originalProjection]
  inv_hom_id := by apply prod.hom_ext <;> simp

/-- The comparison with the target of the gluing isomorphism is an isomorphism. -/
def componentPairToTargetIso : componentPair U f g ≅ Over.mk f ⨯ component U g where
  hom := componentPairToTarget U f g
  inv := componentPairLift U f g
    (componentLift (prod.snd ≫ originalProjection U g) prod.fst) prod.snd (by simp)
  hom_inv_id := by
    apply componentPair_hom_ext
    · apply component_hom_ext <;> simp [componentPairFst_comp_originalProjection]
    · simp
  inv_hom_id := by apply prod.hom_ext <;> simp

/-- On underlying schemes, `componentPairToSource U f g` followed by the first projection of the
product is the first projection of the fibre product. -/
@[simp]
lemma componentPairToSource_left_fst :
    (componentPairToSource U f g).left ≫
        (prod.fst : component U f ⨯ Over.mk g ⟶ _).left =
      pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) := by
  rw [← Over.comp_left, componentPairToSource_fst, componentPairFst_left]

/-- On underlying schemes, `componentPairToSource U f g` followed by the canonical gluing
isomorphism and the second projection of the product is the second projection of the fibre
product. -/
@[simp]
lemma componentPairToSource_left_transition_snd :
    (componentPairToSource U f g).left ≫ (transition U f g).left ≫
        (prod.snd : Over.mk f ⨯ component U g ⟶ _).left =
      pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g) := by
  simp only [← Over.comp_left]
  rw [componentPairToSource_comp_transition_assoc, componentPairToTarget_snd,
    componentPairSnd_left]

/-- A map between the source and the target of a canonical gluing isomorphism which preserves
both the projection to `U` and the projection to the second member of the family agrees with
the gluing isomorphism on the second projection of `componentPair`. These are the only two
properties of the gluing isomorphism the comparison needs, so the conclusion holds for any
realization of the canonical descent datum, not only for
`AlgebraicGeometry.CanonicalDatum.transition`. -/
lemma componentPairToSource_comp_snd_of_originalProjection
    (ψ : component U f ⨯ Over.mk g ⟶ Over.mk f ⨯ component U g)
    (horig : ψ ≫ prod.snd ≫ originalProjection U g = prod.fst ≫ originalProjection U f)
    (hstr : ψ ≫ prod.snd ≫ structureMap g ((Over.pullback g).obj U) = prod.snd) :
    componentPairToSource U f g ≫ ψ ≫ prod.snd = componentPairSnd U f g := by
  apply component_hom_ext
  · simp only [Category.assoc]
    rw [horig, componentPairToSource_fst_assoc, componentPairFst_comp_originalProjection]
  · simp only [Category.assoc]
    rw [hstr, componentPairToSource_snd]

/-- **Invariance of a pair of opens under a canonical gluing isomorphism, transported to the
fibre product over `U` of the two components.** The gluing isomorphism enters only through the
two properties required by
`AlgebraicGeometry.CanonicalDatum.componentPairToSource_comp_snd_of_originalProjection`. -/
lemma preimage_fst_eq_preimage_snd_of_preimage_eq
    (ψ : component U f ⨯ Over.mk g ⟶ Over.mk f ⨯ component U g)
    (horig : ψ ≫ prod.snd ≫ originalProjection U g = prod.fst ≫ originalProjection U f)
    (hstr : ψ ≫ prod.snd ≫ structureMap g ((Over.pullback g).obj U) = prod.snd)
    (W₁ : (pullback U.hom f).Opens) (W₂ : (pullback U.hom g).Opens)
    (h : ψ.left ⁻¹ᵁ ((prod.snd : Over.mk f ⨯ component U g ⟶ _).left ⁻¹ᵁ W₂) =
      (prod.fst : component U f ⨯ Over.mk g ⟶ _).left ⁻¹ᵁ W₁) :
    pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) ⁻¹ᵁ W₁ =
      pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g) ⁻¹ᵁ W₂ := by
  have hs : (componentPairToSource U f g).left ≫ ψ.left ≫
      (prod.snd : Over.mk f ⨯ component U g ⟶ _).left =
      pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g) :=
    congrArg Over.Hom.left (componentPairToSource_comp_snd_of_originalProjection U f g ψ horig hstr)
  simpa only [← Scheme.Hom.comp_preimage, componentPairToSource_left_fst, hs] using
    (congrArg (fun T ↦ (componentPairToSource U f g).left ⁻¹ᵁ T) h).symm

/-- Invariance of a pair of opens under the gluing isomorphism of the canonical descent datum,
transported to the fibre product over `U` of the two components. -/
private lemma preimage_fst_eq_preimage_snd_of_preimage_transition
    (W₁ : (pullback U.hom f).Opens) (W₂ : (pullback U.hom g).Opens)
    (h : (transition U f g).left ⁻¹ᵁ
        ((prod.snd : Over.mk f ⨯ component U g ⟶ _).left ⁻¹ᵁ W₂) =
      (prod.fst : component U f ⨯ Over.mk g ⟶ _).left ⁻¹ᵁ W₁) :
    pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) ⁻¹ᵁ W₁ =
      pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g) ⁻¹ᵁ W₂ :=
  preimage_fst_eq_preimage_snd_of_preimage_eq U f g (transition U f g)
    (transition_original U f g) (transition_structure U f g) W₁ W₂ h

variable {I : Type v} {Z : I → Scheme.{u}}

/-- **An invariant family of opens of a realization of the canonical descent datum of `U` along
an fpqc covering comes from a unique open subscheme of `U`.** The gluing isomorphisms are given
as maps `ψ i j` between the two products which preserve the projection to `U` — the
characteristic property of the canonical datum — and the projection to the `j`-th member of the
family, which every gluing isomorphism of a descent datum satisfies. -/
theorem existsUnique_preimage_eq_of_preimage_eq (f : ∀ i, Z i ⟶ S)
    (hf : Presieve.ofArrows Z f ∈ Scheme.fpqcPrecoverage S) (U : Over S)
    (ψ : ∀ i j, component U (f i) ⨯ Over.mk (f j) ⟶ Over.mk (f i) ⨯ component U (f j))
    (horig : ∀ i j, ψ i j ≫ prod.snd ≫ originalProjection U (f j) =
      prod.fst ≫ originalProjection U (f i))
    (hstr : ∀ i j, ψ i j ≫ prod.snd ≫
      structureMap (f j) ((Over.pullback (f j)).obj U) = prod.snd)
    (W : ∀ i, (pullback U.hom (f i)).Opens)
    (hW : ∀ i j, (ψ i j).left ⁻¹ᵁ
        ((prod.snd : Over.mk (f i) ⨯ component U (f j) ⟶ _).left ⁻¹ᵁ W j) =
      (prod.fst : component U (f i) ⨯ Over.mk (f j) ⟶ _).left ⁻¹ᵁ W i) :
    ∃! U' : U.left.Opens, ∀ i, pullback.fst U.hom (f i) ⁻¹ᵁ U' = W i :=
  existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage _ _
    (ofArrows_pullback_fst_mem_fpqcPrecoverage f hf U.hom) W fun i j ↦
      preimage_fst_eq_preimage_snd_of_preimage_eq U (f i) (f j) (ψ i j) (horig i j) (hstr i j)
        (W i) (W j) (hW i j)

/-- **An invariant family of opens of the canonical descent datum satisfies the compatibility
hypothesis of Stacks 03N0.** The two projections of `(U ×_S X i) ×_U (U ×_S X j)` pull the
opens `W i` and `W j` back to the same open subscheme. -/
theorem preimage_fst_eq_preimage_snd_of_isInvariantOpens (f : ∀ i, Z i ⟶ S) (U : Over S)
    (W : ∀ i, (pullback U.hom (f i)).Opens) (hW : (datum f U).IsInvariantOpens W) (i j : I) :
    pullback.fst (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ⁻¹ᵁ W i =
      pullback.snd (pullback.fst U.hom (f i)) (pullback.fst U.hom (f j)) ⁻¹ᵁ W j :=
  preimage_fst_eq_preimage_snd_of_preimage_transition U (f i) (f j) (W i) (W j)
    ((DescentData.isInvariantOpens_iff_gluing (datum f U) W).mp hW i j)

/-- **An invariant family of opens of the canonical descent datum of `U` along an fpqc covering
comes from a unique open subscheme of `U`.** This is the application of Stacks 03N0 inside the
proof of Stacks 0AP4. -/
theorem existsUnique_preimage_eq_of_isInvariantOpens (f : ∀ i, Z i ⟶ S)
    (hf : Presieve.ofArrows Z f ∈ Scheme.fpqcPrecoverage S) (U : Over S)
    (W : ∀ i, (pullback U.hom (f i)).Opens) (hW : (datum f U).IsInvariantOpens W) :
    ∃! U' : U.left.Opens, ∀ i, pullback.fst U.hom (f i) ⁻¹ᵁ U' = W i :=
  existsUnique_isOpen_preimage_eq_of_mem_fpqcPrecoverage _ _
    (ofArrows_pullback_fst_mem_fpqcPrecoverage f hf U.hom) W
    (preimage_fst_eq_preimage_snd_of_isInvariantOpens f U W hW)

/-- **A descent datum mapping to the canonical datum of `U` by open immersions is the canonical
datum of a unique open subscheme of `U`, as far as the underlying opens go.** -/
theorem existsUnique_preimage_eq_opensRange (f : ∀ i, Z i ⟶ S)
    (hf : Presieve.ofArrows Z f ∈ Scheme.fpqcPrecoverage S) (U : Over S)
    {E : DescentData f} (φ : E ⟶ datum f U) [∀ i, IsOpenImmersion (φ.hom i).left] :
    ∃! U' : U.left.Opens, ∀ i, pullback.fst U.hom (f i) ⁻¹ᵁ U' = (φ.hom i).left.opensRange :=
  existsUnique_preimage_eq_of_isInvariantOpens f hf U _
    (DescentData.isInvariantOpens_opensRange φ)

section Single

variable {S X : Scheme.{u}} (f : X ⟶ S) [Surjective f] [QuasiCompact f] [Flat f]

/-- **An invariant open of the canonical descent datum of `U` relative to a surjective
quasi-compact flat morphism `f : X ⟶ S` is the inverse image of a unique open subscheme of
`U`.** This is the application of Stacks 03N0 inside the proof of Stacks 0AP4. -/
theorem existsUnique_preimage_eq_of_isInvariantOpens_of_flat (U : Over S)
    (W : (pullback U.hom f).Opens)
    (hW : (datum (fun _ : Unit ↦ f) U).IsInvariantOpens fun _ ↦ W) :
    ∃! U' : U.left.Opens, pullback.fst U.hom f ⁻¹ᵁ U' = W := by
  obtain ⟨U', hU', huniq⟩ := existsUnique_preimage_eq_of_isInvariantOpens (fun _ : Unit ↦ f)
    (ofArrows_unit_mem_fpqcPrecoverage f) U (fun _ ↦ W) hW
  exact ⟨U', hU' (), fun V hV ↦ huniq V fun _ ↦ hV⟩

/-- **A descent datum mapping to the canonical datum of `U` by an open immersion determines a
unique open subscheme of `U`** with the same inverse image in `X ×_S U`. -/
theorem existsUnique_preimage_eq_opensRange_of_flat (U : Over S)
    {E : DescentData (fun _ : Unit ↦ f)} (φ : E ⟶ datum (fun _ : Unit ↦ f) U)
    [IsOpenImmersion (φ.hom ()).left] :
    ∃! U' : U.left.Opens, pullback.fst U.hom f ⁻¹ᵁ U' = (φ.hom ()).left.opensRange := by
  have : ∀ i : Unit, IsOpenImmersion (φ.hom i).left := fun _ ↦ ‹_›
  exact existsUnique_preimage_eq_of_isInvariantOpens_of_flat f U _
    (DescentData.isInvariantOpens_opensRange φ)

end Single

end CanonicalDatum

end AlgebraicGeometry

end

end
