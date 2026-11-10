module

public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.Reduction
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion
public import StacksFrontier.CategoryTheory.DottedArrows.Defs

/-!
# Factoring a dotted arrow through a substack

A dotted arrow for a 2-commutative square whose right edge is a composite `i ≫ f` is the same
thing as a dotted arrow for the square with right edge `f` whose diagonal factors through `i`,
compatibly with the two triangles. This file supplies that passage in an arbitrary bicategory,
and the three geometric inputs which make it applicable when `i` is the inclusion of a closed
substack of an algebraic stack: the inclusion is bijective on 2-morphisms after whiskering, a
1-morphism whose image lies in the substack factors through it on the nose, and the image of a
1-morphism out of a reduced source lies in a closed set of points as soon as the image of a
dense set of its points does.

## Main definitions

* `CategoryTheory.DottedArrow.congrDiagonal`: transport of a dotted arrow along an isomorphism
  of its diagonal.
* `CategoryTheory.DottedArrow.ofFactorization`: a dotted arrow for the square with right edge
  `i ≫ f`, out of one for the square with right edge `f` whose diagonal factors through `i`.
* `AlgebraicGeometry.Stack.substackLift`: the factorization of a 1-morphism through a strictly
  full subcategory of its target containing its image, as a 1-morphism of algebraic stacks.

## Main results

* `AlgebraicGeometry.Stack.exists_whiskerRight_fullSubcategoryInclusion`: every 2-morphism
  between two 1-morphisms into a substack, whiskered by its inclusion, comes from a 2-morphism
  between the 1-morphisms themselves.
* `AlgebraicGeometry.Stack.substackLift_comp`: the factorization composed with the inclusion is
  the original 1-morphism, on the nose.
* `AlgebraicGeometry.Stack.factorsThroughSubstack_of_isReducedInducedStackStructure`:
  **Stacks 050B** at the reduced induced algebraic stack structure of **Stacks 050C**.
* `AlgebraicGeometry.Stack.range_pointsMap_subset_of_dense`: a 1-morphism has its image on
  points inside a closed set as soon as its restriction to a dense set of points does.
* `AlgebraicGeometry.Stack.dense_range_pointsMap_schemeStackMap` and
  `AlgebraicGeometry.Stack.dense_range_pointsMap_schemeStackMap_fractionField`: a morphism of
  the site with dense image on schemes induces a 1-morphism with dense image on points, and the
  inclusion of a domain into its fraction field is such a morphism.

## Implementation notes

`CategoryTheory.DottedArrow.ofFactorization` is stated over an arbitrary bicategory, with every
associator written out, so that its one nontrivial step — the compatibility triangle of
**Stacks 0H18** — is pure coherence and is discharged by the `bicategory` tactic. The
factorization of the diagonal is given as a 1-morphism `g` with an isomorphism `g ≫ i ≅ d.a`
rather than an equality, and the comparison of the two `α`s is the hypothesis `hα`; the proof
first replaces `d` by the isomorphic dotted arrow with diagonal `g ≫ i`, which is
`CategoryTheory.DottedArrow.congrDiagonal`.

`AlgebraicGeometry.Stack.exists_whiskerRight_fullSubcategoryInclusion` is the 2-categorical
content of full faithfulness of a full-subcategory inclusion: a 2-morphism of the ambient
2-category of categories fibred in groupoids is a `CategoryTheory.BasedNatTrans`, whose
components after whiskering are already morphisms of the full subcategory, so the reflected
2-morphism is built by tagging each component with `CategoryTheory.ObjectProperty.homMk`. The
lifting condition on components transfers by `CategoryTheory.BasedFunctor.isHomLift_map`.

`AlgebraicGeometry.Stack.substackLift` uses `CategoryTheory.ObjectProperty.lift`, whose
composite with the inclusion is the original functor definitionally; the based functor it builds
therefore reuses the `w` field of the original, and
`AlgebraicGeometry.Stack.substackLift_comp` holds by `rfl`. This is what
`AlgebraicGeometry.Stack.FactorsThroughSubstack` does not record: it supplies the factorization
only up to a 2-isomorphism.

The point topology of **Stacks 04Y8** is not a global instance and is written out in the
hypotheses that mention it, as in
`StacksFrontier/AlgebraicGeometry/Stacks/Reduction.lean`.

## References

* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
* [Stacks Project, Tag 050B](https://stacks.math.columbia.edu/tag/050B)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
-/

@[expose] public section

namespace CategoryTheory.DottedArrow

open CategoryTheory.Bicategory

universe w v u

variable {Bc : Type u} [Bicategory.{w, v} Bc]

variable {s t G Pp Y : Bc}

/-- A dotted arrow transported along an isomorphism `ψ` of its diagonal: the new diagonal is the
source of `ψ`, and the two triangles are the old ones conjugated by `ψ`. -/
def congrDiagonal {x : s ⟶ G} {j : s ⟶ t} {f : G ⟶ Y} {y : t ⟶ Y}
    {γ : (j ≫ y) ⟶ (x ≫ f)} (d : DottedArrow x j f y γ) {a' : t ⟶ G} (ψ : a' ≅ d.a) :
    DottedArrow x j f y γ where
  a := a'
  α := (j ◁ ψ.hom) ≫ d.α
  β := d.β ≫ (ψ.inv ▷ f)
  compat := by
    refine d.compat.trans (Eq.symm ?_)
    simp

/-- The diagonal of a transported dotted arrow is the source of the isomorphism. -/
@[simp] theorem congrDiagonal_a {x : s ⟶ G} {j : s ⟶ t} {f : G ⟶ Y} {y : t ⟶ Y}
    {γ : (j ≫ y) ⟶ (x ≫ f)} (d : DottedArrow x j f y γ) {a' : t ⟶ G} (ψ : a' ≅ d.a) :
    (d.congrDiagonal ψ).a = a' := rfl

/-- The upper triangle of a transported dotted arrow. -/
@[simp] theorem congrDiagonal_α {x : s ⟶ G} {j : s ⟶ t} {f : G ⟶ Y} {y : t ⟶ Y}
    {γ : (j ≫ y) ⟶ (x ≫ f)} (d : DottedArrow x j f y γ) {a' : t ⟶ G} (ψ : a' ≅ d.a) :
    (d.congrDiagonal ψ).α = (j ◁ ψ.hom) ≫ d.α := rfl

/-- The lower triangle of a transported dotted arrow. -/
@[simp] theorem congrDiagonal_β {x : s ⟶ G} {j : s ⟶ t} {f : G ⟶ Y} {y : t ⟶ Y}
    {γ : (j ≫ y) ⟶ (x ≫ f)} (d : DottedArrow x j f y γ) {a' : t ⟶ G} (ψ : a' ≅ d.a) :
    (d.congrDiagonal ψ).β = d.β ≫ (ψ.inv ▷ f) := rfl

/-- A dotted arrow for the square `(x, j, i ≫ f, y)` built from one for the square
`(x ≫ i, j, f, y)` whose diagonal factors through `i` as `g ≫ i`, with `hα` comparing the two
upper triangles. Its diagonal is `g`, its upper triangle is the given `α` and its lower triangle
is that of the given dotted arrow, reassociated. -/
def ofFactorization (x : s ⟶ G) (j : s ⟶ t) (i : G ⟶ Pp) (f : Pp ⟶ Y)
    (y : t ⟶ Y) (γ : (j ≫ y) ⟶ (x ≫ (i ≫ f)))
    (d : DottedArrow (x ≫ i) j f y (γ ≫ (α_ x i f).inv))
    (g : t ⟶ G) (ψ : g ≫ i ≅ d.a) (α : (j ≫ g) ⟶ x)
    (hα : α ▷ i = (α_ j g i).hom ≫ (j ◁ ψ.hom) ≫ d.α) :
    DottedArrow x j (i ≫ f) y γ where
  a := g
  α := α
  β := (d.congrDiagonal ψ).β ≫ (α_ g i f).hom
  compat := by
    have hα' : (j ◁ ψ.hom) ≫ d.α = (α_ j g i).inv ≫ (α ▷ i) := by rw [hα]; simp
    refine (cancel_mono (α_ x i f).inv).1 (((d.congrDiagonal ψ).compat).trans ?_)
    rw [congrDiagonal_α, congrDiagonal_β, hα']
    bicategory

end CategoryTheory.DottedArrow

namespace AlgebraicGeometry.Stack

open CategoryTheory CategoryTheory.Bicategory

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Whiskering by the inclusion of a substack is surjective on 2-morphisms.** Every
2-morphism between the composites of two 1-morphisms into the full subcategory of `𝒳` cut out by
`P` with the canonical inclusion is the whiskering of a 2-morphism between those 1-morphisms. -/
theorem exists_whiskerRight_fullSubcategoryInclusion {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (P : ObjectProperty 𝒳.val.val.obj)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    {𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {p q : 𝒵 ⟶ (fullSubcategoryAlgebraicStack 𝒳 P hA).val}
    (θ : p ≫ (fullSubcategoryInclusion 𝒳 P hA).hom ⟶
      q ≫ (fullSubcategoryInclusion 𝒳 P hA).hom) :
    ∃ η : p ⟶ q, η ▷ (fullSubcategoryInclusion 𝒳 P hA).hom = θ := by
  refine ⟨Bicategory.InducedBicategory.Hom₂.mk
    { toNatTrans :=
        { app := fun a => ObjectProperty.homMk (θ.hom.app a)
          naturality := fun a b g => ObjectProperty.hom_ext _
            (by exact θ.hom.naturality g) }
      isHomLift' := fun a => by
        have h : 𝒳.val.val.p.IsHomLift (𝟙 (𝒵.val.p.obj a))
            ((fullSubcategoryBasedInclusion 𝒳 P).map
              (ObjectProperty.homMk (θ.hom.app a))) := θ.hom.isHomLift' a
        exact BasedFunctor.isHomLift_map (fullSubcategoryBasedInclusion 𝒳 P) _ _ }, ?_⟩
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  rfl

/-- The factorization of a 1-morphism of algebraic stacks through the full subcategory of its
target cut out by a property holding at every object in its image, as a 1-morphism of algebraic
stacks. -/
def substackLift {𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS} (a : 𝒵 ⟶ 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (h : ∀ X : 𝒵.val.val.obj, P (a.hom.hom.obj X)) :
    𝒵 ⟶ fullSubcategoryAlgebraicStack 𝒳 P hA :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := P.lift a.hom.hom.toFunctor h
      w := a.hom.hom.w })

/-- The factorization of a 1-morphism through a substack, composed with the canonical inclusion
of the substack, is the original 1-morphism on the nose. -/
theorem substackLift_comp {𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS} (a : 𝒵 ⟶ 𝒳)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (h : ∀ X : 𝒵.val.val.obj, P (a.hom.hom.obj X)) :
    substackLift B S hS a hA h ≫ fullSubcategoryInclusion 𝒳 P hA = a :=
  rfl

/-- **Stacks 050B at the reduced induced algebraic stack structure.** A 1-morphism of algebraic
stacks with reduced source whose image on points lies in a set carrying the reduced induced
algebraic stack structure of **Stacks 050C** factors through that structure. -/
theorem factorsThroughSubstack_of_isReducedInducedStackStructure
    {𝒳 𝒵 : AlgebraicStacks.{u, w} B S hS} (a : 𝒵 ⟶ 𝒳)
    {T : Set (AlgebraicStacks.points B S hS 𝒳)} {P : ObjectProperty 𝒳.val.val.obj}
    (hP : IsReducedInducedStackStructure B S hS T P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
    (hred : IsReducedStack B S hS 𝒵)
    (hsub : Set.range (AlgebraicStacks.pointsMap B S hS a) ⊆ T) :
    FactorsThroughSubstack a P :=
  (factorsThroughSubstack_iff_range_pointsMap_subset B S hS a hP.1.1 hA hred).2
    (by rwa [hP.1.2 hA])

/-- **The image on points of a 1-morphism lies in a closed set as soon as its restriction to a
dense set of points does.** The preimage of the closed set is closed, by continuity of the map
on points of **Stacks 04XL**, and contains a dense set, hence is everything. -/
theorem range_pointsMap_subset_of_dense {𝒲 𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (b : 𝒲 ⟶ 𝒵) (a : 𝒵 ⟶ 𝒳)
    (hb : @Dense _ (pointTopology B S hS 𝒵.val)
      (Set.range (AlgebraicStacks.pointsMap B S hS b)))
    {T : Set (AlgebraicStacks.points B S hS 𝒳)}
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T)
    (hsub : Set.range (AlgebraicStacks.pointsMap B S hS (b ≫ a)) ⊆ T) :
    Set.range (AlgebraicStacks.pointsMap B S hS a) ⊆ T := by
  let _ := pointTopology B S hS 𝒵.val
  let _ := pointTopology B S hS 𝒳.val
  have hcont : Continuous (AlgebraicStacks.pointsMap B S hS a) :=
    continuous_pointsMap B S hS 𝒵.val 𝒳.val a.hom.hom
  have hsubA : Set.range (AlgebraicStacks.pointsMap B S hS b) ⊆
      (AlgebraicStacks.pointsMap B S hS a) ⁻¹' T := by
    rintro _ ⟨wz, rfl⟩
    exact hsub ⟨wz, congrFun (AlgebraicStacks.pointsMap_comp B S hS b a) wz⟩
  have huniv : (AlgebraicStacks.pointsMap B S hS a) ⁻¹' T = Set.univ := by
    rw [← (hT.preimage hcont).closure_eq, (Dense.mono hsubA hb).closure_eq]
  exact Set.range_subset_iff.2 (Set.eq_univ_iff_forall.1 huniv)

/-- **A morphism of the site with dense image induces a 1-morphism with dense image on points.**
The identification of the points of the algebraic stack of a scheme of the site with the scheme
is a homeomorphism natural in the scheme. -/
theorem dense_range_pointsMap_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : DenseRange ((BigFppfOver.toScheme B S hS).map g).base) :
    @Dense _ (pointTopology B S hS (schemeStack.{u, w} B S hS V).val)
      (Set.range (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g))) := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  let _ := pointTopology B S hS (schemeFibredCategory B S hS V)
  have hfun : (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g)) =
      (pointsHomeomorphScheme B S hS V).symm ∘
        (((BigFppfOver.toScheme B S hS).map g).base ∘ (pointsHomeomorphScheme B S hS U)) := by
    refine funext fun z => (pointsHomeomorphScheme B S hS V).injective ?_
    rw [Function.comp_apply, Function.comp_apply, Homeomorph.apply_symm_apply]
    exact pointsHomeomorphScheme_naturality B S hS g z
  rw [hfun]
  refine DenseRange.comp (pointsHomeomorphScheme B S hS V).symm.surjective.denseRange ?_
    (pointsHomeomorphScheme B S hS V).symm.continuous
  rwa [DenseRange, (pointsHomeomorphScheme B S hS U).surjective.range_comp]

/-- **The generic point of the spectrum of a domain in the site is dense on points.** The
1-morphism induced by a morphism of the site realising the inclusion of a domain into its
fraction field has dense image on points: its image on schemes is the generic point, whose
closure is everything because the spectrum of a domain is irreducible. -/
theorem dense_range_pointsMap_schemeStackMap_fractionField
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) (hK : B.Contains (Spec (.of K)))
    (base : Spec (.of R) ⟶ S)
    (g : siteObject B S hS hK (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ base) ⟶
      siteObject B S hS hR base)
    (hg : (B.inclusion).map g.left = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    @Dense _ (pointTopology B S hS (schemeStack.{u, w} B S hS (siteObject B S hS hR base)).val)
      (Set.range (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g))) := by
  refine dense_range_pointsMap_schemeStackMap.{u, w} B S hS g ?_
  rw [show ((BigFppfOver.toScheme B S hS).map g) =
    Spec.map (CommRingCat.ofHom (algebraMap R K)) from hg]
  have hgen : (Spec.map (CommRingCat.ofHom (algebraMap R K)) :
      Spec (.of K) ⟶ Spec (.of R)) (IsLocalRing.closedPoint K) =
      genericPoint (Spec (.of R)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = _
    rw [genericPoint_eq_bot_of_affine, IsLocalRing.maximalIdeal_eq_bot,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]
    rfl
  exact Dense.mono (Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint K, hgen⟩)
    (dense_iff_closure_eq.2 (genericPoint_closure (Spec (.of R))))

end AlgebraicGeometry.Stack

end
