module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineComponents
public import StacksFrontier.AlgebraicGeometry.LocallyPrincipalPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction

/-!
# Reduction of Stacks 053R to the case of integral schemes

The first paragraph of the proof of Stacks 053R replaces `f : X ⟶ S` by the induced morphism
`X_red ⟶ S_red` of reductions: the inverse image of a locally principal closed subscheme is
locally principal (Stacks 053P), a morphism from a reduced scheme factors through the reduction
of its target (Stacks 0356), and an irreducible reduced scheme is integral (Stacks 01ON, in
Mathlib as `AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced`). This file carries
out that replacement.

Both `X_red ⟶ X` and `S_red ⟶ S` are surjective closed immersions, hence homeomorphisms on
points, so every hypothesis of Stacks 053R and its conclusion transport across the square

```
X_red ⟶ X
  |        |
  v        v
S_red ⟶ S
```

The transport of the conclusion is an *equivalence*, not merely an implication: the two fibres
are homeomorphic by a homeomorphism matching the two supports, so the reduction step neither
weakens nor strengthens the assertion. That is
`Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_reduction_iff`, and it is what
makes `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_of_isIntegral` a genuine
reduction rather than a vacuous implication.

## Main definitions

* `AlgebraicGeometry.fiberHomeoOfSquare`: the comparison of scheme-theoretic fibres across a
  commutative square of schemes whose horizontal maps are a homeomorphism and an injection.
* `AlgebraicGeometry.Scheme.reductionHomeo`: the homeomorphism `X_red ≃ₜ X`.
* `AlgebraicGeometry.Scheme.reductionMap`: the morphism `X_red ⟶ S_red` induced by `f : X ⟶ S`.

## Main results

* `AlgebraicGeometry.fiberι_fiberHomeoOfSquare` and
  `AlgebraicGeometry.fiberHomeoOfSquare_image_preimage`: the fibre comparison is compatible with
  the embeddings of the fibres into the two sources, hence matches the parts of the two fibres
  lying over a subset of the target of the horizontal homeomorphism.
* `AlgebraicGeometry.Scheme.isHomeomorph_reductionι`: `X_red ⟶ X` is a homeomorphism on points.
* `AlgebraicGeometry.Scheme.isIntegral_reduction`: the reduction of an irreducible scheme is
  integral.
* `AlgebraicGeometry.Scheme.reductionι_genericPoint`: `X_red ⟶ X` carries the generic point to
  the generic point.
* `AlgebraicGeometry.Scheme.reductionMap_apply`, and the instances
  `AlgebraicGeometry.Scheme.isDominant_reductionMap` and
  `AlgebraicGeometry.Scheme.locallyOfFiniteType_reductionMap`: dominance and local finite type
  pass to the morphism of reductions.
* `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_reduction_iff`: the conclusion of
  Stacks 053R for `f` and for the induced morphism of reductions are equivalent.
* `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_of_isIntegral`: **the first
  paragraph of the proof of Stacks 053R.** The general case of Stacks 053R follows from the case
  of integral `X` and `S`.

## Implementation notes

No declaration in this file carries a `@[stacks 053R]` attribute: the main result is a
*conditional* statement — it assumes the conclusion of Stacks 053R for integral source and target
— and a conditional statement is not a proof of the tag, however much of the source's argument it
reproduces. Its hypothesis is discharged in
`StacksFrontier.AlgebraicGeometry.FibreDimension.GeneralCase`, where the two combine into
`Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_general`, the general case of the
tag.

`AlgebraicGeometry.fiberHomeoOfSquare` takes the left-hand map of the square as a `Homeomorph`
rather than as a morphism of schemes together with `IsHomeomorph`, because that is what
`Homeomorph.subtype` consumes; the morphism of schemes enters only through the commutativity
hypothesis, which is stated pointwise. The right-hand map is only required to be injective,
which is all that identifies the two set-theoretic fibres.

The point `s` of `S` over which the fibre is taken is *not* an argument of the reduction theorem's
transport step: instead `AlgebraicGeometry.Scheme.surjective_reductionι` produces a point of
`S_red` above it and the equation is substituted away, so that the fibre comparison can be used
at the type it has rather than transported along an equality of base points.

## References

* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
* [Stacks Project, Tag 053P](https://stacks.math.columbia.edu/tag/053P)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- The preimage of a dense set under a homeomorphism is dense. -/
public theorem Homeomorph.dense_preimage {α : Type*} {β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (e : α ≃ₜ β) {s : Set β} (hs : Dense s) : Dense (e ⁻¹' s) := by
  rw [dense_iff_closure_eq, ← e.preimage_closure, hs.closure_eq, Set.preimage_univ]

namespace AlgebraicGeometry

/-! ### Fibres across a square of schemes with homeomorphic sources -/

/-- **Comparison of fibres across a square.** Let

```
X' --eρ--> X
|          |
f'         f
v          v
S' --σ---> S
```

commute on points, with `eρ` a homeomorphism and `σ` injective. Then the fibre of `f'` over a
point `s'` of `S'` is homeomorphic to the fibre of `f` over its image `σ s'`: both are
set-theoretic fibres, and `eρ` carries the one onto the other because `σ` is injective. -/
public noncomputable def fiberHomeoOfSquare {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (eρ : X' ≃ₜ X) (σ : S' ⟶ S) (hσ : Function.Injective σ.base)
    (hcomm : ∀ x' : X', f (eρ x') = σ (f' x')) (s' : S') :
    f'.fiber s' ≃ₜ f.fiber (σ s') :=
  (f'.fiberHomeo s').trans
    ((eρ.subtype (p := fun x' : X' => x' ∈ f' ⁻¹' {s'})
        (q := fun x : X => x ∈ f ⁻¹' {σ s'})
        (fun x' => by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hcomm x']
          exact ⟨fun h => by rw [h], fun h => hσ h⟩)).trans
      (f.fiberHomeo (σ s')).symm)

/-- The fibre comparison of `AlgebraicGeometry.fiberHomeoOfSquare` is compatible with the
embeddings of the two fibres into the two sources. -/
public theorem fiberι_fiberHomeoOfSquare {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (eρ : X' ≃ₜ X) (σ : S' ⟶ S) (hσ : Function.Injective σ.base)
    (hcomm : ∀ x' : X', f (eρ x') = σ (f' x')) (s' : S') (w : f'.fiber s') :
    f.fiberι (σ s') (fiberHomeoOfSquare f f' eρ σ hσ hcomm s' w) = eρ (f'.fiberι s' w) := by
  rw [fiberHomeoOfSquare, Homeomorph.trans_apply, Homeomorph.trans_apply,
    Scheme.Hom.fiberι_fiberHomeo_symm]
  exact congrArg eρ (f'.fiberHomeo_apply s' w)

/-- The fibre comparison of `AlgebraicGeometry.fiberHomeoOfSquare` carries the part of the fibre
of `f'` lying over a subset `W` of `X` onto the part of the fibre of `f` lying in `W`. -/
public theorem fiberHomeoOfSquare_image_preimage {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (eρ : X' ≃ₜ X) (σ : S' ⟶ S) (hσ : Function.Injective σ.base)
    (hcomm : ∀ x' : X', f (eρ x') = σ (f' x')) (s' : S') (W : Set X) :
    fiberHomeoOfSquare f f' eρ σ hσ hcomm s' '' (f'.fiberι s' ⁻¹' (eρ ⁻¹' W)) =
      f.fiberι (σ s') ⁻¹' W := by
  have h : fiberHomeoOfSquare f f' eρ σ hσ hcomm s' ⁻¹' (f.fiberι (σ s') ⁻¹' W) =
      f'.fiberι s' ⁻¹' (eρ ⁻¹' W) := by
    ext w
    simp only [Set.mem_preimage, fiberι_fiberHomeoOfSquare]
  rw [← h]
  exact (fiberHomeoOfSquare f f' eρ σ hσ hcomm s').image_preimage _

/-- Fibres compared by `AlgebraicGeometry.fiberHomeoOfSquare` have the same dimension. -/
public theorem topologicalKrullDim_fiber_eq_of_square {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (eρ : X' ≃ₜ X) (σ : S' ⟶ S) (hσ : Function.Injective σ.base)
    (hcomm : ∀ x' : X', f (eρ x') = σ (f' x')) (s' : S') :
    topologicalKrullDim (f'.fiber s') = topologicalKrullDim (f.fiber (σ s')) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (fiberHomeoOfSquare f f' eρ σ hσ hcomm s').isHomeomorph

namespace Scheme

/-! ### The reduction as a homeomorphism -/

/-- `X_red ⟶ X` is a homeomorphism on points: it is a closed immersion, hence a closed
embedding, and it is surjective. -/
public theorem isHomeomorph_reductionι (X : Scheme.{u}) : IsHomeomorph X.reductionι.base :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(Scheme.Hom.isClosedEmbedding X.reductionι).isEmbedding, X.surjective_reductionι⟩

/-- The homeomorphism `X_red ≃ₜ X` underlying the closed immersion `X_red ⟶ X`. -/
public noncomputable def reductionHomeo (X : Scheme.{u}) : X.reduction ≃ₜ X :=
  (isHomeomorph_reductionι X).homeomorph

/-- The homeomorphism `X_red ≃ₜ X` acts on points as the closed immersion `X_red ⟶ X`. -/
@[simp]
public theorem reductionHomeo_apply (X : Scheme.{u}) (x : X.reduction) :
    reductionHomeo X x = X.reductionι x := rfl

/-- The closed immersion `X_red ⟶ X` is injective on points. -/
public theorem injective_reductionι (X : Scheme.{u}) : Function.Injective X.reductionι.base :=
  (isHomeomorph_reductionι X).bijective.injective

/-- The closed immersion `X_red ⟶ X` is dominant, being surjective on points. -/
public instance isDominant_reductionι (X : Scheme.{u}) : IsDominant X.reductionι :=
  (isDominant_iff X.reductionι).mpr X.surjective_reductionι.denseRange

/-- The reduction of an irreducible scheme is irreducible, being homeomorphic to it. -/
public instance irreducibleSpace_reduction (X : Scheme.{u}) [IrreducibleSpace X] :
    IrreducibleSpace X.reduction :=
  (reductionHomeo X).irreducibleSpace_iff.mpr ‹_›

/-- **Stacks 01ON for the reduction.** The reduction of an irreducible scheme is integral: it is
reduced by construction and irreducible because `X_red ⟶ X` is a homeomorphism. -/
public instance isIntegral_reduction (X : Scheme.{u}) [IrreducibleSpace X] :
    IsIntegral X.reduction :=
  isIntegral_of_irreducibleSpace_of_isReduced X.reduction

/-- `X_red ⟶ X` carries the generic point of `X_red` to the generic point of `X`, being a
dominant morphism of irreducible schemes. -/
public theorem reductionι_genericPoint (X : Scheme.{u}) [IrreducibleSpace X] :
    X.reductionι (genericPoint X.reduction) = genericPoint X :=
  apply_genericPoint_eq_genericPoint X.reductionι

/-! ### The morphism of reductions induced by a morphism -/

/-- The morphism `X_red ⟶ S_red` induced by `f : X ⟶ S`: the composite `X_red ⟶ X ⟶ S` has
reduced source, so it factors uniquely through `S_red` by Stacks 0356. -/
@[ega "I 5.1.5"]
public noncomputable def reductionMap {X S : Scheme.{u}} (f : X ⟶ S) :
    X.reduction ⟶ S.reduction :=
  (Scheme.existsUnique_lift_nilradical_subschemeι (X.reductionι ≫ f)).exists.choose

/-- The defining square of the morphism of reductions. -/
@[reassoc]
public theorem reductionMap_comp_reductionι {X S : Scheme.{u}} (f : X ⟶ S) :
    reductionMap f ≫ S.reductionι = X.reductionι ≫ f :=
  (Scheme.existsUnique_lift_nilradical_subschemeι (X.reductionι ≫ f)).exists.choose_spec

/-- On points, the morphism of reductions is `f` transported along `X_red ⟶ X` and `S_red ⟶ S`. -/
public theorem reductionMap_apply {X S : Scheme.{u}} (f : X ⟶ S) (x : X.reduction) :
    S.reductionι (reductionMap f x) = f (X.reductionι x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, reductionMap_comp_reductionι]

/-- The morphism of reductions induced by a morphism locally of finite type is locally of finite
type. -/
public instance locallyOfFiniteType_reductionMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] : LocallyOfFiniteType (reductionMap f) :=
  have : LocallyOfFiniteType (reductionMap f ≫ S.reductionι) := by
    rw [reductionMap_comp_reductionι]; infer_instance
  locallyOfFiniteType_of_comp (reductionMap f) S.reductionι

/-- The morphism of reductions induced by a dominant morphism is dominant. -/
public instance isDominant_reductionMap {X S : Scheme.{u}} (f : X ⟶ S) [IsDominant f] :
    IsDominant (reductionMap f) := by
  rw [isDominant_iff, DenseRange]
  have hrange : Set.range (reductionMap f).base = reductionHomeo S ⁻¹' Set.range f.base := by
    ext t
    simp only [Set.mem_range, Set.mem_preimage, reductionHomeo_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      exact ⟨X.reductionι x, (reductionMap_apply f x).symm⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x', rfl⟩ := X.surjective_reductionι x
      exact ⟨x', S.injective_reductionι ((reductionMap_apply f x').trans hx)⟩
  rw [hrange]
  exact (reductionHomeo S).dense_preimage ((isDominant_iff f).mp ‹_›)

end Scheme

end AlgebraicGeometry

namespace Stacks.Divisors

open AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The square of reductions commutes on points, in the form
`AlgebraicGeometry.fiberHomeoOfSquare` consumes. -/
public theorem apply_reductionHomeo (x : X.reduction) :
    f (Scheme.reductionHomeo X x) = S.reductionι (Scheme.reductionMap f x) :=
  (Scheme.reductionMap_apply f x).symm

/-- The comparison of the fibres of `f : X ⟶ S` and of the induced morphism of reductions
`X_red ⟶ S_red`: the fibre of `X_red ⟶ S_red` over `s'` is homeomorphic to the fibre of `f` over
the image of `s'` in `S`. -/
public noncomputable def fiberReductionHomeo (s' : S.reduction) :
    (Scheme.reductionMap f).fiber s' ≃ₜ f.fiber (S.reductionι s') :=
  fiberHomeoOfSquare f (Scheme.reductionMap f) (Scheme.reductionHomeo X) S.reductionι
    (S.injective_reductionι) (apply_reductionHomeo f) s'

/-- The comparison `Stacks.Divisors.fiberReductionHomeo` matches the part of the fibre of
`X_red ⟶ S_red` lying in the support of the inverse image of an ideal sheaf `I` with the part of
the fibre of `f` lying in the support of `I`. -/
public theorem fiberReductionHomeo_image_preimage_support (I : X.IdealSheafData)
    (s' : S.reduction) :
    fiberReductionHomeo f s' ''
        ((Scheme.reductionMap f).fiberι s' ⁻¹'
          ((I.comap X.reductionι).support : Set X.reduction)) =
      f.fiberι (S.reductionι s') ⁻¹' (I.support : Set X) := by
  rw [Scheme.IdealSheafData.support_comap]
  exact fiberHomeoOfSquare_image_preimage f (Scheme.reductionMap f) (Scheme.reductionHomeo X)
    S.reductionι S.injective_reductionι (apply_reductionHomeo f) s' (I.support : Set X)

/-- The fibres of `f` and of the induced morphism of reductions have the same dimension. -/
public theorem topologicalKrullDim_fiber_reductionMap_eq (s' : S.reduction) :
    topologicalKrullDim ((Scheme.reductionMap f).fiber s') =
      topologicalKrullDim (f.fiber (S.reductionι s')) :=
  topologicalKrullDim_fiber_eq_of_square f (Scheme.reductionMap f) (Scheme.reductionHomeo X)
    S.reductionι S.injective_reductionι (apply_reductionHomeo f) s'

/-- **The reduction step of Stacks 053R loses no information.** The conclusion of Stacks 053R
holds for `f : X ⟶ S` at the image of `s'` exactly when it holds for the induced morphism of
reductions `X_red ⟶ S_red` at `s'`: the two fibres are homeomorphic by
`Stacks.Divisors.fiberReductionHomeo`, which matches the two supports.

This is what makes `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_of_isIntegral`
a genuine reduction: it is not an implication that could hold because the hypothesis is
unsatisfiable or because the transported conclusion is weaker. -/
public theorem fiber_support_eq_union_irreducibleComponents_reduction_iff (I : X.IdealSheafData)
    (s' : S.reduction) :
    ((Scheme.reductionMap f).fiberι s' ⁻¹'
          ((I.comap X.reductionι).support : Set X.reduction) =
        ⋃₀ {C : Set ((Scheme.reductionMap f).fiber s') |
          C ∈ irreducibleComponents ((Scheme.reductionMap f).fiber s') ∧
          C ⊆ (Scheme.reductionMap f).fiberι s' ⁻¹'
            ((I.comap X.reductionι).support : Set X.reduction)}) ↔
      (f.fiberι (S.reductionι s') ⁻¹' (I.support : Set X) =
        ⋃₀ {C : Set (f.fiber (S.reductionι s')) |
          C ∈ irreducibleComponents (f.fiber (S.reductionι s')) ∧
          C ⊆ f.fiberι (S.reductionι s') ⁻¹' (I.support : Set X)}) := by
  have himage := fiberReductionHomeo_image_preimage_support f I s'
  refine ⟨(fiberReductionHomeo f s').eq_sUnion_irreducibleComponents_of_image himage, ?_⟩
  refine (fiberReductionHomeo f s').symm.eq_sUnion_irreducibleComponents_of_image ?_
  rw [← himage, Set.image_image]
  simp

/-- **The first paragraph of the proof of Stacks 053R: reduction to the integral case.** If the
conclusion of Stacks 053R holds whenever the source and the target are integral, then it holds in
the generality of the statement, with `X` and `S` merely irreducible.

Passing to the reductions `X_red ⟶ S_red` makes both schemes integral — reduced by construction,
irreducible because `X_red ⟶ X` and `S_red ⟶ S` are homeomorphisms — and preserves every
hypothesis: the inverse image of `I` is locally principal by Stacks 053P, the morphism of
reductions is dominant and locally of finite type, and the generic fibre of the inverse image is
still empty because `S_red ⟶ S` matches the two generic points. The conclusion transports back by
`Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_reduction_iff`. -/
public theorem fiber_support_eq_union_irreducibleComponents_of_isIntegral
    (H : ∀ (X₀ S₀ : Scheme.{u}) (f₀ : X₀ ⟶ S₀) [IsIntegral X₀] [IsIntegral S₀] [IsDominant f₀]
      [LocallyOfFiniteType f₀] (I₀ : X₀.IdealSheafData), IsLocallyPrincipal I₀ →
      IsEmpty ((I₀.subschemeι ≫ f₀).fiber (genericPoint S₀)) → ∀ s₀ : S₀,
      topologicalKrullDim (f₀.fiber s₀) ≤ topologicalKrullDim (f₀.fiber (genericPoint S₀)) →
      (f₀.fiberι s₀) ⁻¹' (I₀.support : Set X₀) =
        ⋃₀ {C : Set (f₀.fiber s₀) | C ∈ irreducibleComponents (f₀.fiber s₀) ∧
          C ⊆ (f₀.fiberι s₀) ⁻¹' (I₀.support : Set X₀)})
    [IrreducibleSpace S] [IrreducibleSpace X] [IsDominant f] [LocallyOfFiniteType f]
    (I : X.IdealSheafData) (hI : IsLocallyPrincipal I)
    (hgeneric : IsEmpty ((I.subschemeι ≫ f).fiber (genericPoint S))) (s : S)
    (hdim : topologicalKrullDim (f.fiber s) ≤
      topologicalKrullDim (f.fiber (genericPoint S))) :
    (f.fiberι s) ⁻¹' (I.support : Set X) =
      ⋃₀ {C : Set (f.fiber s) | C ∈ irreducibleComponents (f.fiber s) ∧
        C ⊆ (f.fiberι s) ⁻¹' (I.support : Set X)} := by
  obtain ⟨s', rfl⟩ := S.surjective_reductionι s
  set f' := Scheme.reductionMap f with hf'
  set I' := I.comap X.reductionι with hI'def
  -- The inverse image of `I` is locally principal, by Stacks 053P.
  have hI' : IsLocallyPrincipal I' := isLocallyPrincipal_comap X.reductionι I hI
  -- The generic fibre of the inverse image is still empty.
  have hgen : ∀ y ∈ (I.support : Set X), f y ≠ genericPoint S :=
    (I.isEmpty_fiber_comp_iff f (genericPoint S)).mp hgeneric
  have hgeneric' : IsEmpty ((I'.subschemeι ≫ f').fiber (genericPoint S.reduction)) := by
    refine (I'.isEmpty_fiber_comp_iff f' (genericPoint S.reduction)).mpr fun y hy hcon => ?_
    rw [hI'def, Scheme.IdealSheafData.support_comap] at hy
    refine hgen (X.reductionι y) hy ?_
    rw [← Scheme.reductionMap_apply f y, ← hf', hcon, Scheme.reductionι_genericPoint]
  -- The dimension inequality transports because the fibres are homeomorphic.
  have hdim' : topologicalKrullDim (f'.fiber s') ≤
      topologicalKrullDim (f'.fiber (genericPoint S.reduction)) := by
    rw [hf', topologicalKrullDim_fiber_reductionMap_eq f s',
      topologicalKrullDim_fiber_reductionMap_eq f (genericPoint S.reduction),
      Scheme.reductionι_genericPoint]
    exact hdim
  exact (fiber_support_eq_union_irreducibleComponents_reduction_iff f I s').mp
    (H X.reduction S.reduction f' I' hI' hgeneric' s' hdim')

end Stacks.Divisors

end
