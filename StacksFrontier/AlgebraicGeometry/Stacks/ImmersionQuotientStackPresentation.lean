module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.RestrictionFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothGroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackImmersionBaseChangeSpace
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.EssentialImageFibered
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FullyFaithfulEquivalence

/-!
# Stacks 0505: an immersion into a quotient stack is presented by a restriction

Let `G = (U, R, s, t, c)` be a smooth groupoid in algebraic spaces over a scheme `S` of a big
fppf site and let `i : 𝒵 ⟶ [U/R]` be an immersion. **Stacks 0505** produces an `R`-invariant
locally closed subspace `Z ⊆ U` and a presentation `[Z/R_Z] ⟶ 𝒵` by the restriction of `G` to
`Z`, making the triangle over `[U/R]` 2-commutative, and asserts that `Z` is closed —
respectively open — when `i` is a closed — respectively open — immersion.

## Main results

* `AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_groupoidPresentation_of_isImmersion`:
  **Stacks 0505**, with nothing carried.
* `AlgebraicGeometry.Stack.exists_equivalenceOver_quotientStack_restrict`: the presentation and
  the 2-commutative triangle, for `Z` the locus of `U` whose image in `[U/R]` is in the essential
  image of `i`.
* `AlgebraicGeometry.Stack.essImage_quotientStackMap_restrict`: the 1-morphism
  `[Z/R_Z] ⟶ [U/R]` of Stacks 046Q lands in the essential image of `i`.
* `AlgebraicGeometry.Stack.locallyEssSurjOnFibers_comparison`: the hypothesis of Stacks 046N for
  the comparison `[Z/R_Z] ⟶ 𝒵`.
* `AlgebraicGeometry.Stack.essImage_of_locally_essImage`: membership in the essential image of a
  fully faithful 1-morphism into a quotient stack is local on the site.
* `AlgebraicGeometry.Stack.exists_fiber_iso_of_essImage`: an object in the essential image of a
  1-morphism of categories fibred in groupoids is *vertically* isomorphic to an object of the
  image.

## How the proof runs

The source applies Stacks 04Y6 and reads the base change `U' = 𝒵 ×_{[U/R]} U` as a locally closed
subspace of `U`. The subspace half of that is already in the library, with nothing carried:
`AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_range_of_isImmersion_quotientStack` of
`StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackImmersionBaseChangeSpace` produces the
`R`-invariant locally closed `Z ⊆ U`, together with its pointwise description: a point of `U` lies
in `Z` exactly when its image in `[U/R]` lies in the essential image of `i`.

What is proved here is the other half — that the restriction of `G` to `Z` *presents* `𝒵`, and
2-commutatively over `[U/R]`. Rather than construct the groupoid `R' = 𝒵 ×_{[U/R]} R` and
identify it with `R_Z`, which is how the source gets there through Stacks 04T4, 04T5 and 046Q, the
comparison is obtained from the 1-morphism `[Z/R_Z] ⟶ [U/R]` that Stacks 046Q already provides:

* it is **fully faithful**, by Stacks 046S, whose cartesian-square hypothesis holds for every
  restriction (`AlgebraicGeometry.Stack.fullyFaithful_quotientStackMap_restrict`);
* `i` is fully faithful too, being a monomorphism (**Stacks 0504**, recreated from **Stacks 042R**
  and **Stacks 05UK** as in `StacksFrontier.AlgebraicGeometry.Stacks.ImmersionSubstack`);
* every object of `[Z/R_Z]` is carried into the **essential image of `i`**: it is locally the
  image of a point of `Z` (part (1) of **Stacks 044X**), such a point goes to a point of `U` lying
  in `Z`, and membership in the essential image of a fully faithful 1-morphism is local, because
  `𝒵` satisfies descent and `[U/R]` has `Mor`-sheaves;
* so `[Z/R_Z] ⟶ [U/R]` factors through the full subcategory of `[U/R]` cut out by that essential
  image, which `CategoryTheory.CatFiberedInGroupoids.exists_inverse_toEssImageBased`
  (**Stacks 003Z**) identifies with `𝒵` over the site. The composite `k : [Z/R_Z] ⟶ 𝒵` is fully
  faithful, and its composite with `i` is 2-isomorphic to `[Z/R_Z] ⟶ [U/R]` — the 2-commutative
  triangle, with no further work;
* `k` is an equivalence over the site by **Stacks 046N**: every object of a fibre of `𝒵` is
  locally the image of a point of `U` lying in `Z`, hence locally in the essential image of `k` on
  fibres.

Smoothness of `G` is used in exactly one place, and it is the place the source uses it: the
restricted groupoid is smooth, so the equivalence is a *presentation* in the sense of
Stacks 04TI. Everything else holds for an arbitrary groupoid in algebraic spaces.

`𝒵` is asked to satisfy descent rather than to be an algebraic stack. That is weaker, and it is
all the argument uses; the hypothesis is not avoidable, since it is what Stacks 046N and the
locality of the essential image consume, and it is implied by the hypothesis of Stacks 0505 —
Definition 100.9.1 reads "immersion" for a 1-morphism of *algebraic stacks*, and an algebraic
stack is a stack.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 042R](https://stacks.math.columbia.edu/tag/042R)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044F](https://stacks.math.columbia.edu/tag/044F)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 0505](https://stacks.math.columbia.edu/tag/0505)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
-/

@[expose] public section

open CategoryTheory

universe u v w t

namespace AlgebraicGeometry.Stack

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- **An object of the target in the essential image of a 1-morphism of categories fibred in
groupoids is vertically isomorphic to an object of the image.** The essential image is taken with
respect to arbitrary isomorphisms; because both ends are fibred in groupoids, the witness may be
moved to lie over the same object of the base, and the comparison isomorphism may then be taken
over an identity.

This is the forward direction of
`CategoryTheory.TwoFibreProductOver.essImage_obj_iff_exists_x_eq` at the cospan whose first leg
is the identity of the target. -/
theorem exists_fiber_iso_of_essImage
    {𝒵 𝒳 : BasedCategory.{u + 1, u + 1} (BigFppfOver C S hS)} (f : 𝒵 ⥤ᵇ 𝒳)
    (h𝒵 : 𝒵.p.IsFiberedInGroupoids) (h𝒳 : 𝒳.p.IsFiberedInGroupoids)
    [𝒵.p.IsFibered] {V : BigFppfOver C S hS} (y : 𝒳.p.Fiber V)
    (hy : f.toFunctor.essImage y.1) :
    ∃ z : 𝒵.p.Fiber V,
      Nonempty ((Functor.Fiber.mapOfComp 𝒵.p 𝒳.p f.toFunctor f.w V).obj z ≅ y) := by
  obtain ⟨yo, hyo⟩ := y
  obtain ⟨P, hP⟩ :=
    (TwoFibreProductOver.essImage_obj_iff_exists_x_eq (BasedFunctor.id 𝒳) f h𝒵 h𝒳 yo).mp hy
  subst hP
  have hbase : P.base = V := P.hx.symm.trans hyo
  refine ⟨⟨P.y, P.hy.trans hbase⟩, ⟨Functor.Fiber.isoMk P.iso.symm ?_⟩⟩
  have hv : 𝒳.p.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
  have hinv : 𝒳.p.IsHomLift (𝟙 P.base) P.iso.inv := by
    simpa using IsHomLift.inv 𝒳.p (𝟙 P.base) P.iso.hom
  rwa [hbase] at hinv

variable {B : AlgebraicSpaces C S hS}

/-- The underlying functor of a 1-morphism `i : 𝒵 ⟶ [U/R]` of categories fibred in groupoids is
a fibred 1-morphism. -/
private theorem isFibredOneMorphism_homFunctor
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    {G : GroupoidInAlgebraicSpaces C S hS B}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G)) :
    Functor.IsFibredOneMorphism 𝒵.val.p (quotientStack G).p
      (CatFiberedInGroupoids.homFunctor i) :=
  Functor.IsFiberedInGroupoids.isFibredOneMorphism (isFiberedInGroupoids_quotientStack G)
    (CatFiberedInGroupoids.homFunctor_comp_p i)

/-- **Membership in the essential image of a fully faithful 1-morphism into a quotient stack is
local on the big fppf site.** Let `i : 𝒵 ⟶ [U/R]` be a 1-morphism of categories fibred in
groupoids whose source satisfies descent and whose underlying functor is full and faithful. If
the chosen pullbacks of an object of a fibre of `[U/R]`, along the members of some fppf covering
sieve, are in the essential image of `i`, then so is the object itself.

This is `CategoryTheory.Functor.exists_iso_of_locally_essImage` — effective descent for `𝒵` and
the `Mor`-sheaf condition for `[U/R]`, the latter holding for every quotient stack with no
hypothesis by `AlgebraicGeometry.Stack.isStack_quotientStack`. The local hypothesis is converted
from the essential-image form to the fibrewise form by
`AlgebraicGeometry.Stack.exists_fiber_iso_of_essImage`. -/
theorem essImage_of_locally_essImage
    {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
    {G : GroupoidInAlgebraicSpaces C S hS B}
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (h𝒵 : 𝒵.val.p.IsStack (BigFppfOver.topology C S hS))
    (hfull : (CatFiberedInGroupoids.homFunctor i).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor i).Faithful)
    {V : BigFppfOver C S hS} (x : (quotientStack G).p.Fiber V)
    {R : Sieve V} (hR : R ∈ BigFppfOver.topology C S hS V)
    (hloc : ∀ ⦃V' : BigFppfOver C S hS⦄ (k : V' ⟶ V), R.arrows k →
      (CatFiberedInGroupoids.homFunctor i).essImage
        (Functor.pullbackFiber (quotientStack G).p x k).1) :
    (CatFiberedInGroupoids.homFunctor i).essImage x.1 := by
  have hFib𝒵 : 𝒵.val.p.IsFibered := h𝒵.isFibered
  have hF := isFibredOneMorphism_homFunctor i
  have _h1 := hfull
  have _h2 := hfaithful
  obtain ⟨x₁, ⟨e⟩⟩ := Functor.exists_iso_of_locally_essImage hF h𝒵.hasEffectiveDescent
    ((isStack_quotientStack G).isMorSheaf V) x hR
    (fun {V'} k hk => exists_fiber_iso_of_essImage i.hom 𝒵.property
      (isFiberedInGroupoids_quotientStack G) _ (hloc k hk))
  exact ⟨x₁.1, ⟨(Functor.Fiber.fiberInclusion (p := (quotientStack G).p)).mapIso e⟩⟩

/-- A section of a subfunctor, read in the ambient presheaf, lies in that subfunctor. -/
theorem subfunctor_ι_app_mem {D : Type w} [Category.{t} D] {F : Dᵒᵖ ⥤ Type v}
    (A : Subfunctor F) (T : Dᵒᵖ) (y : A.toFunctor.obj T) : A.ι.app T y ∈ A.obj T := y.2

/-- Two subfunctors with the same membership predicate are equal. -/
private theorem subfunctor_eq_of_mem_iff {D : Type w} [Category.{t} D] {F : Dᵒᵖ ⥤ Type v}
    {A A' : Subfunctor F} (P : ∀ T : Dᵒᵖ, F.obj T → Prop)
    (h : ∀ T u, u ∈ A.obj T ↔ P T u) (h' : ∀ T u, u ∈ A'.obj T ↔ P T u) : A = A' :=
  Subfunctor.ext (funext fun T => Set.ext fun u => (h T u).trans (h' T u).symm)

section Restriction

variable {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}
  {G : GroupoidInAlgebraicSpaces C S hS B}
  (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
  (Z : Subfunctor G.objects.obj) (hZalg : IsAlgebraicSpace C S hS Z.toFunctor)

/-- The map on objects of the canonical morphism from the restriction of `G` to a subspace `Z` of
its object space lands, pointwise, in `Z`. -/
theorem mapObjects_restrict_mem (T : (BigFppfOver C S hS)ᵒᵖ)
    (ζ : (G.restrict (subspaceInclusion G Z hZalg)).groupoid.objects.obj.obj T) :
    (G.restrict (subspaceInclusion G Z hZalg)).hom.toGroupoidHom.mapObjects.app T ζ ∈
      Z.obj T := by
  rw [(G.restrict (subspaceInclusion G Z hZalg)).mapObjects_eq]
  exact subfunctor_ι_app_mem Z T _

/-- **The image of a point of `Z` under `[Z/R_Z] ⟶ [U/R]` is in the essential image of `i`.**
The 1-morphism `[Z/R_Z] ⟶ [U/R]` of Stacks 046Q carries the image of a point of `Z` under the
projection of Stacks 044R to the image of the same point of `U`, up to a 2-isomorphism, and that
point lies in `Z`, which is by hypothesis the locus whose image in `[U/R]` is in the essential
image of `i`. -/
theorem essImage_quotientStackMap_quotientStackProjection
    (hmem : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ Z.obj W ↔ (CatFiberedInGroupoids.homFunctor i).essImage
        ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩))
    (x₀ : (fibredCategory C S hS
      (G.restrict (subspaceInclusion G Z hZalg)).groupoid.objects.obj).val.obj) :
    (CatFiberedInGroupoids.homFunctor i).essImage
      ((quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).obj
        ((quotientStackProjection
          (G.restrict (subspaceInclusion G Z hZalg)).groupoid).obj x₀)) := by
  set f := (G.restrict (subspaceInclusion G Z hZalg)).hom with hf
  have hcell := (functorialityProjectionCellUnlifted f).app x₀
  have hobj := associatedMap_obj C S hS f.toGroupoidHom.mapObjects x₀
  have hmemx : f.toGroupoidHom.mapObjects.app (Opposite.op x₀.base) x₀.fiber.as ∈
      Z.obj (Opposite.op x₀.base) := mapObjects_restrict_mem Z hZalg _ _
  have hess := (hmem (Opposite.op x₀.base)
    (f.toGroupoidHom.mapObjects.app (Opposite.op x₀.base) x₀.fiber.as)).mp hmemx
  refine (CatFiberedInGroupoids.homFunctor i).essImage.prop_of_iso ?_ hess
  refine (eqToIso (congrArg (quotientStackProjection G).obj hobj)).symm ≪≫ hcell.symm

/-- **The 1-morphism `[Z/R_Z] ⟶ [U/R]` lands in the essential image of `i`.** Every object of
`[Z/R_Z]` is, over the members of some fppf covering sieve, in the essential image of the
projection `Z ⟶ [Z/R_Z]` of Stacks 044R (part (1) of Stacks 044X); the images of those points lie
in the essential image of `i` by
`AlgebraicGeometry.Stack.essImage_quotientStackMap_quotientStackProjection`, and membership in
that essential image is local by
`AlgebraicGeometry.Stack.essImage_of_locally_essImage`. -/
theorem essImage_quotientStackMap_restrict
    (h𝒵 : 𝒵.val.p.IsStack (BigFppfOver.topology C S hS))
    (hfull : (CatFiberedInGroupoids.homFunctor i).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor i).Faithful)
    (hmem : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ Z.obj W ↔ (CatFiberedInGroupoids.homFunctor i).essImage
        ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩))
    (w : (quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).obj) :
    (CatFiberedInGroupoids.homFunctor i).essImage
      ((quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).obj w) := by
  have hj : Functor.IsFibredOneMorphism
      (quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p
      (quotientStack G).p
      (quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).toFunctor :=
    isFibredOneMorphism_quotientStackMap _
  obtain ⟨R, hR, hess⟩ := essImage_quotientStackProjectionHom
    (G.restrict (subspaceInclusion G Z hZalg)).groupoid
    ((quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p.obj w) ⟨w, rfl⟩
  refine essImage_of_locally_essImage i h𝒵 hfull hfaithful
    ((Functor.fiberFunctorOfCompEq hj.comp_eq
      ((quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p.obj w)).obj
      ⟨w, rfl⟩) hR ?_
  intro V' k hk
  obtain ⟨zl, ⟨e0⟩⟩ := hess hk
  have e1 := hj.mapPullbackFiberIso (⟨w, rfl⟩ :
    (quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p.Fiber
      ((quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p.obj w)) k
  refine (CatFiberedInGroupoids.homFunctor i).essImage.prop_of_iso
    ((quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).toFunctor.mapIso
        (Functor.Fiber.fiberInclusion.mapIso e0) ≪≫
      (Functor.Fiber.fiberInclusion.mapIso e1).symm)
    (essImage_quotientStackMap_quotientStackProjection i Z hZalg hmem _)

/-- **Local essential surjectivity on fibres of a comparison `[Z/R_Z] ⟶ 𝒵` over `[U/R]`.** Let
`i : 𝒵 ⟶ [U/R]` have full and faithful underlying functor, let `Z ⊆ U` be, pointwise, the locus
whose image in `[U/R]` is in the essential image of `i`, and let `k : [Z/R_Z] ⟶ 𝒵` be a
1-morphism whose composite with `i` is 2-isomorphic to the 1-morphism `[Z/R_Z] ⟶ [U/R]` of
Stacks 046Q. Then every object of a fibre of `𝒵` is, over the members of some fppf covering
sieve, in the essential image of `k` on fibres.

The object is carried by `i` into `[U/R]`, where part (1) of Stacks 044X makes it locally the
image of a point `u` of `U`; that point lies in `Z` by hypothesis, so the image under
`[Z/R_Z] ⟶ [U/R]` of the corresponding point of `Z` is the same object of `[U/R]`, and the
2-isomorphism identifies it with the image under `i` of the value of `k` there. Full faithfulness
of `i` then transports the identification back to `𝒵`, and
`AlgebraicGeometry.Stack.exists_fiber_iso_of_essImage` turns it into a fibrewise one.

This is the hypothesis of **Stacks 046N** for `k`. -/
theorem locallyEssSurjOnFibers_comparison
    (hfull : (CatFiberedInGroupoids.homFunctor i).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor i).Faithful)
    (hmem : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ Z.obj W ↔ (CatFiberedInGroupoids.homFunctor i).essImage
        ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩))
    (k : quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid ⥤ᵇ 𝒵.val)
    (γ : k.comp i.hom ≅ quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom) :
    Functor.LocallyEssSurjOnFibers 𝒵.property.isFibered k.w
      (BigFppfOver.topology C S hS) := by
  have _h1 := hfull
  have _h2 := hfaithful
  have hFib𝒵 : 𝒵.val.p.IsFibered := 𝒵.property.isFibered
  have hFi := isFibredOneMorphism_homFunctor i
  intro U x
  obtain ⟨R, hR, hess⟩ := essImage_quotientStackProjectionHom G U
    ((Functor.fiberFunctorOfCompEq hFi.comp_eq U).obj x)
  refine ⟨R, hR, ?_⟩
  intro V kk hkk
  obtain ⟨zl, ⟨e0⟩⟩ := hess hkk
  have e1 := hFi.mapPullbackFiberIso x kk
  refine exists_fiber_iso_of_essImage k
    (isFiberedInGroupoids_quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid)
    𝒵.property _ ?_
  -- the comparison, in `[U/R]`, of the image of the chosen pullback with the image of a point
  -- of `U`
  have ecmp : (quotientStackProjection G).obj ((objectSpaceLiftDown G).obj zl.1) ≅
      (CatFiberedInGroupoids.homFunctor i).obj (Functor.pullbackFiber 𝒵.val.p x kk).1 :=
    Functor.Fiber.fiberInclusion.mapIso e0 ≪≫ Functor.Fiber.fiberInclusion.mapIso e1
  -- that point lies in `Z`
  have hmemu : ((objectSpaceLiftDown G).obj zl.1).fiber.as ∈
      Z.obj (Opposite.op ((objectSpaceLiftDown G).obj zl.1).base) :=
    (hmem (Opposite.op ((objectSpaceLiftDown G).obj zl.1).base)
      ((objectSpaceLiftDown G).obj zl.1).fiber.as).mpr
      ⟨(Functor.pullbackFiber 𝒵.val.p x kk).1, ⟨ecmp.symm⟩⟩
  -- the point of `Z` above it, and the object of `[Z/R_Z]` it presents
  have hmapζ : (G.restrict (subspaceInclusion G Z hZalg)).hom.toGroupoidHom.mapObjects.app
      (Opposite.op ((objectSpaceLiftDown G).obj zl.1).base)
      ⟨((objectSpaceLiftDown G).obj zl.1).fiber.as, hmemu⟩ =
        ((objectSpaceLiftDown G).obj zl.1).fiber.as := by
    rw [(G.restrict (subspaceInclusion G Z hZalg)).mapObjects_eq]
    rfl
  have hobj : (objectSpaceMap (G.restrict (subspaceInclusion G Z hZalg)).hom).obj
      ⟨((objectSpaceLiftDown G).obj zl.1).base,
        Discrete.mk ⟨((objectSpaceLiftDown G).obj zl.1).fiber.as, hmemu⟩⟩ =
      (objectSpaceLiftDown G).obj zl.1 := by
    rw [associatedMap_obj C S hS
      (G.restrict (subspaceInclusion G Z hZalg)).hom.toGroupoidHom.mapObjects
      (⟨((objectSpaceLiftDown G).obj zl.1).base,
        Discrete.mk ⟨((objectSpaceLiftDown G).obj zl.1).fiber.as, hmemu⟩⟩ :
        (fibredCategory C S hS
          (G.restrict (subspaceInclusion G Z hZalg)).groupoid.objects.obj).val.obj)]
    exact congrArg (fun y => (⟨((objectSpaceLiftDown G).obj zl.1).base, Discrete.mk y⟩ :
      (fibredCategory C S hS G.objects.obj).val.obj)) hmapζ
  refine ⟨(quotientStackProjection (G.restrict (subspaceInclusion G Z hZalg)).groupoid).obj
    ⟨((objectSpaceLiftDown G).obj zl.1).base,
      Discrete.mk ⟨((objectSpaceLiftDown G).obj zl.1).fiber.as, hmemu⟩⟩, ⟨?_⟩⟩
  refine (CatFiberedInGroupoids.homFunctor i).preimageIso ?_
  exact ((BasedNatTrans.forgetful
      (quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid)
      (quotientStack G)).mapIso γ).app _ ≪≫
    (functorialityProjectionCellUnlifted
      (G.restrict (subspaceInclusion G Z hZalg)).hom).app _ ≪≫
    eqToIso (congrArg (quotientStackProjection G).obj hobj) ≪≫ ecmp

/-- **The presentation of `𝒵` by the restriction of `G` to `Z`, and its 2-commutative triangle
over `[U/R]`.** Let `i : 𝒵 ⟶ [U/R]` be a 1-morphism of categories fibred in groupoids whose
source satisfies descent and whose underlying functor is full and faithful, and let `Z ⊆ U` be,
pointwise, the locus whose image in `[U/R]` is in the essential image of `i`. Then the quotient
stack of the restriction of `G` to `Z` is equivalent, over the big fppf site of `S`, to `𝒵`, by an
equivalence whose composite with `i` is 2-isomorphic to the 1-morphism `[Z/R_Z] ⟶ [U/R]` of
Stacks 046Q.

The comparison is built by factoring `[Z/R_Z] ⟶ [U/R]` through the full subcategory of `[U/R]`
cut out by the essential image of `i` — which is possible by
`AlgebraicGeometry.Stack.essImage_quotientStackMap_restrict` — and composing with the
quasi-inverse over the site of the comparison of `𝒵` with that same full subcategory
(`CategoryTheory.CatFiberedInGroupoids.exists_inverse_toEssImageBased`, which is **Stacks 003Z**).
It is fully faithful because `[Z/R_Z] ⟶ [U/R]` is (**Stacks 046S**,
`AlgebraicGeometry.Stack.fullyFaithful_quotientStackMap_restrict`), and an equivalence over the
site by **Stacks 046N** together with
`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_comparison`. -/
theorem exists_equivalenceOver_quotientStack_restrict
    (h𝒵 : 𝒵.val.p.IsStack (BigFppfOver.topology C S hS))
    (hfull : (CatFiberedInGroupoids.homFunctor i).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor i).Faithful)
    (hmem : ∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
      u ∈ Z.obj W ↔ (CatFiberedInGroupoids.homFunctor i).essImage
        ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩)) :
    ∃ e : StacksRepresentableCFG.EquivalenceOver
        (quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p 𝒵.val.p,
      Nonempty ((⟨e.hom.functor, e.hom.w⟩ :
            quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid ⥤ᵇ
              𝒵.val).comp i.hom ≅
        quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom) := by
  have _h1 := hfull
  have _h2 := hfaithful
  obtain ⟨K, η, ε, hη, hε⟩ :=
    CatFiberedInGroupoids.exists_inverse_toEssImageBased i hfull hfaithful
  have hιfull : ((CatFiberedInGroupoids.homFunctor i).essImage).ι.Full :=
    CatFiberedInGroupoids.full_essImage_ι i
  have hιfaithful : ((CatFiberedInGroupoids.homFunctor i).essImage).ι.Faithful :=
    CatFiberedInGroupoids.faithful_essImage_ι i
  have hland := essImage_quotientStackMap_restrict i Z hZalg h𝒵 hfull hfaithful hmem
  -- the factorization of `[Z/R_Z] ⟶ [U/R]` through the essential image of `i`
  let jSub : quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid ⥤ᵇ
      CatFiberedInGroupoids.fullSubcategoryBased _
        (CatFiberedInGroupoids.homFunctor i).essImage :=
    ⟨((CatFiberedInGroupoids.homFunctor i).essImage).lift
        (quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).toFunctor
        hland,
      (quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).w⟩
  have hjff : Functor.FullyFaithful
      (quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).toFunctor :=
    (fullyFaithful_quotientStackMap_restrict G (subspaceInclusion G Z hZalg)).some
  have hjSubff : jSub.toFunctor.FullyFaithful :=
    CatFiberedInGroupoids.fullyFaithful_lift_essImage i
      (quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom)
      hland hjff
  have _h3 : jSub.toFunctor.Full := hjSubff.full
  have _h4 : jSub.toFunctor.Faithful := hjSubff.faithful
  have hKequiv : K.toFunctor.IsEquivalence :=
    (CategoryTheory.Equivalence.mk K.toFunctor
      (CatFiberedInGroupoids.toEssImageBased i).toFunctor ε.symm η).isEquivalence_functor
  have _h6 : (jSub.toFunctor ⋙ K.toFunctor).Full := inferInstance
  have _h7 : (jSub.toFunctor ⋙ K.toFunctor).Faithful := inferInstance
  -- the comparison and the triangle
  let k : quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid ⥤ᵇ 𝒵.val :=
    jSub.comp K
  have hbase : ∀ w, (CatFiberedInGroupoids.fullSubcategoryBased _
        (CatFiberedInGroupoids.homFunctor i).essImage).p.obj (jSub.toFunctor.obj w) =
      (quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p.obj w :=
    fun w => Functor.congr_obj
      (quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).w w
  let φ : (k.comp i.hom).toFunctor ≅
      (quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom).toFunctor :=
    Functor.isoWhiskerLeft jSub.toFunctor
      (Functor.isoWhiskerRight ε ((CatFiberedInGroupoids.homFunctor i).essImage).ι)
  have hφapp : ∀ w, φ.hom.app w =
      ((CatFiberedInGroupoids.homFunctor i).essImage).ι.map
        (ε.hom.app (jSub.toFunctor.obj w)) := fun _ => rfl
  have γ : k.comp i.hom ≅
      quotientStackMap (G.restrict (subspaceInclusion G Z hZalg)).hom :=
    BasedNatIso.mkNatIso φ (by
      intro w
      have hv : Functor.IsHomLift
          (((CatFiberedInGroupoids.homFunctor i).essImage).ι ⋙ (quotientStack G).p)
          (𝟙 ((CatFiberedInGroupoids.fullSubcategoryBased _
            (CatFiberedInGroupoids.homFunctor i).essImage).p.obj (jSub.toFunctor.obj w)))
          (ε.hom.app (jSub.toFunctor.obj w)) := hε (jSub.toFunctor.obj w)
      rw [hbase w] at hv
      have := hv
      rw [hφapp w]
      exact Functor.isHomLift_map_of_comp_eq rfl _ _)
  -- Stacks 046N
  have hFk : Functor.IsFibredOneMorphism
      (quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid).p 𝒵.val.p k.toFunctor :=
    Functor.IsFiberedInGroupoids.isFibredOneMorphism 𝒵.property k.w
  have _h8 : k.toFunctor.Full := _h6
  have _h9 : k.toFunctor.Faithful := _h7
  obtain ⟨E⟩ := (Functor.isEquivalenceOver_iff_locallyEssSurjOnFibers
    (isStack_quotientStack (G.restrict (subspaceInclusion G Z hZalg)).groupoid) h𝒵 hFk).mpr
    (locallyEssSurjOnFibers_comparison i Z hZalg hfull hfaithful hmem k γ)
  exact ⟨StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver k.w E, ⟨γ⟩⟩

end Restriction

section Main

variable {𝒵 : CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)}

/-- **Stacks 0505.** Let `G = (U, R, s, t, c)` be a smooth groupoid in algebraic spaces over a
scheme `S` of a big fppf site, and let `i : 𝒵 ⟶ [U/R]` be an immersion — a 1-morphism
representable by algebraic spaces with the relative immersion property of Stacks 04XB, that is
part (3) of Stacks 04YL — whose source satisfies descent. Then there are an `R`-invariant locally
closed subspace `Z ⊆ U` in the sense of Stacks 044F, part (2), a *presentation*
`[Z/R_Z] ⟶ 𝒵` of `𝒵` in the sense of Stacks 04TI by the restriction `R_Z` of `G` to `Z`
(Stacks 044B), and a 2-isomorphism making the triangle

    [Z/R_Z] ⟶ 𝒵 ⟶ [U/R]        [Z/R_Z] ⟶ [U/R]

2-commutative, the second leg being the 1-morphism of Stacks 046Q induced by the canonical
morphism of groupoids from the restriction. If `i` is a closed, respectively open, immersion then
`Z` is a closed, respectively open, subspace of `U`.

`Z` is pinned down by the conclusion: it is, pointwise, the locus of `U` whose image in `[U/R]`
lies in the essential image of `i`, which is the `𝒵 ×_{[U/R]} U` of Stacks 04Y6 read as a
subspace of `U`.

The subspace and its invariance are
`AlgebraicGeometry.Stack.exists_isInvariantLocallyClosed_range_of_isImmersion_quotientStack`;
smoothness of the restricted groupoid, the one place smoothness of `G` is used, is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSmoothGroupoid_restrict_invariant`; and the
equivalence together with the 2-commutative triangle is
`AlgebraicGeometry.Stack.exists_equivalenceOver_quotientStack_restrict`, whose two inputs are
full faithfulness of `i` (**Stacks 05UK** at the monomorphism **Stacks 042R** supplies, which is
**Stacks 0504**) and the pointwise description of `Z`. -/
@[stacks 0505 "for i an immersion (representable by algebraic spaces with the 04XB immersion \
property, Stacks 04YL part (3)) out of a stack, a 1-morphism into the quotient stack of a smooth \
groupoid: the R-invariant locally closed Z, the presentation [Z/R_Z] ≃ 𝒵 with its 2-commutative \
triangle over [U/R], and Z closed (resp. open) when i is a closed (resp. open) immersion"]
theorem exists_isInvariantLocallyClosed_groupoidPresentation_of_isImmersion
    (G : GroupoidInAlgebraicSpaces C S hS (baseSpace C S hS))
    (hG : GroupoidInAlgebraicSpaces.IsSmooth C S hS G)
    (h𝒵 : 𝒵.val.p.IsStack (BigFppfOver.topology C S hS))
    (i : 𝒵 ⟶ CatFiberedInGroupoids.mk (quotientStack G) (isFiberedInGroupoids_quotientStack G))
    (hi : IsRepresentableByAlgebraicSpaces C S hS i.hom)
    (himm : IsImmersion C S hS i) :
    ∃ (Z : Subfunctor G.objects.obj) (hZ : IsInvariantLocallyClosed G Z)
      (hsm : GroupoidInAlgebraicSpaces.IsSmooth C S hS
        (G.restrict (subspaceInclusion G Z hZ.1.1)).groupoid)
      (e : StacksRepresentableCFG.EquivalenceOver
        (quotientStack (G.restrict (subspaceInclusion G Z hZ.1.1)).groupoid).p 𝒵.val.p),
      Nonempty ((GroupoidPresentation.basedFunctor
            (⟨(G.restrict (subspaceInclusion G Z hZ.1.1)).groupoid, hsm, e⟩ :
              GroupoidPresentation C S hS 𝒵.val)).comp i.hom ≅
          quotientStackMap (G.restrict (subspaceInclusion G Z hZ.1.1)).hom) ∧
        (∀ (W : (BigFppfOver C S hS)ᵒᵖ) (u : G.objects.obj.obj W),
          u ∈ Z.obj W ↔ (CatFiberedInGroupoids.homFunctor i).essImage
            ((quotientStackProjection G).obj ⟨W.unop, Discrete.mk u⟩)) ∧
        (IsClosedImmersion C S hS i → Space.IsClosedSubspace C S hS Z) ∧
        (IsOpenImmersion C S hS i → Space.IsOpenSubspace C S hS Z) := by
  obtain ⟨hfull, hfaithful⟩ :=
    full_and_faithful_homFunctor_of_mono_representingMaps C S hS i hi
      fun U y hy F hF he => Space.mono_of_isImmersion C S hS (himm U y hy F hF he)
  obtain ⟨U', m, hm, hinv, hmem⟩ :=
    exists_isInvariantLocallyClosed_range_of_isImmersion_quotientStack G i hi himm
  refine ⟨Subfunctor.range m.hom, hinv,
    GroupoidInAlgebraicSpaces.isSmoothGroupoid_restrict_invariant G hG hinv, ?_⟩
  obtain ⟨e, he⟩ := exists_equivalenceOver_quotientStack_restrict i (Subfunctor.range m.hom)
    hinv.1.1 h𝒵 hfull hfaithful hmem
  refine ⟨e, he, hmem, ?_, ?_⟩
  · intro hclosed
    obtain ⟨U'', m'', hm'', hinv'', hmem''⟩ :=
      exists_isInvariantClosed_range_of_isClosedImmersion_quotientStack G i hi hclosed
    exact subfunctor_eq_of_mem_iff _ hmem'' hmem ▸ hinv''.1
  · intro hopen
    obtain ⟨U'', m'', hm'', hinv'', hmem''⟩ :=
      exists_isInvariantOpen_range_of_isOpenImmersion_quotientStack G i hi hopen
    exact subfunctor_eq_of_mem_iff _ hmem'' hmem ▸ hinv''.1

end Main

end AlgebraicGeometry.Stack

end
