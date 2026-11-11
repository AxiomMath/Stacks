module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FiniteHilbertEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusFibered
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusInherited
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjectsLifting

/-!
# Formal smoothness on objects of the inclusion of the local complete intersection locus

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. A property of the objects of a category fibred in groupoids over
the big fppf site which is cut out, over every scheme-valued point, by an *open* subobject of the
base is inherited not only along arbitrary morphisms — that is
`CategoryTheory.Functor.prop_of_hom_of_sliceLocus` — but also *backwards* along a morphism whose
base component is surjective on points: the open subobject cut out at the target contains the
image of the base component, hence is the whole base.

A first-order thickening is surjective on points, so membership of the local complete
intersection locus `ℋ_{d,lci}(𝒳/𝒴)` of **Stacks 06CJ** propagates across a morphism of
quintuples whose base component is a first-order thickening. The inclusion
`ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` is therefore formally smooth on objects in the sense of
**Stacks 06D0**: a lifting problem for it over a first-order thickening is solved by the given
object of `ℋ_d(𝒳/𝒴)` itself, which the propagation puts in the locus.

This is the last paragraph of the proof of **Stacks 06D9**, isolated: there the quintuple
produced over the thickening is placed in the locus because the inclusion of the locus is an
"open substack".

## Main results

* `AlgebraicGeometry.Stack.prop_of_hom_of_surjective_of_openSliceLocus`: a property described
  slicewise by an *open* subobject propagates backwards along a morphism with surjective base.
* `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_hom_of_surjective` and
  `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_hom_of_isFirstOrderThickening`: that
  propagation for the local complete intersection locus.
* `AlgebraicGeometry.Stack.lciFiniteHilbertInclusionFibered`: the inclusion of the locus as a
  1-morphism of the 2-category of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_lciFiniteHilbertInclusion`: the inclusion
  `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` is formally smooth on objects.

## Implementation notes

The open locus is carried as `AlgebraicGeometry.Stack.FiniteHilbert.HasOpenLciLocus`, the output
of steps 1-3 of the source of Stacks 06CL, and is taken as an explicit argument here exactly as
it is in `AlgebraicGeometry.Stack.isFiberedInGroupoids_lciFiniteHilbertCategory`; at the
hypotheses of Stacks 06CL it is proved, from Stacks 05X8 and Stacks 06CE, by
`AlgebraicGeometry.Stack.FiniteHilbert.hasOpenLciLocus`. The witness
that the projection of the locus is fibred in groupoids is likewise an argument, as in
`AlgebraicGeometry.Stack.lciFiniteHilbertFibered`: the predicate
`AlgebraicGeometry.Stack.IsFormallySmoothOnObjects` is stated of a 1-morphism of the 2-category
`CategoryTheory.CatFiberedInGroupoids`, so bundling the locus is what makes the statement
possible at all.

Surjectivity of a first-order thickening is
`Stacks.Thickenings.IsFirstOrderThickening.isThickening`: the kernel ideal sheaf is square-zero,
so its support is the whole of the ambient scheme.

The lifting problem is solved in the shape of
`AlgebraicGeometry.Stack.HasFirstOrderObjectLifts` rather than directly in the fibre-theoretic
shape of `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`: no restriction has to be chosen,
because the solution is the given object and the vertical identification downstairs is an
identity.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w v₂ u₂

/-! ### Propagation of an open slicewise property along a surjective base -/

/-- **A property described slicewise by an open subobject propagates backwards along a morphism
whose base is surjective on points.** Let `p : 𝒵 ⥤ (Sch/S)_{fppf}` be fibred in groupoids and let
`P` be a property of the objects of `𝒵`, closed under isomorphism, such that for every
scheme-valued point of `p` over an object `U` of the site there is an *open* subobject `V` of the
big fppf site of `U` through which an object maps exactly when the value of the point there has
`P`. If `φ : x ⟶ y` is a morphism of `𝒵` whose base component is surjective on points and `x`
has `P`, then `y` has `P`.

Read `P` at the point of `p` attached to `y`: the value of that point at the object named by the
base of `φ` is isomorphic to `x`, so that object maps to `V`, so the image of the base of `φ`
lies in the open image of `V`. Surjectivity makes that image everything, so `V` is the whole base
and the terminal object maps to it as well; the value of the point there is `y`. -/
theorem prop_of_hom_of_surjective_of_openSliceLocus {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Z : Type u₂} [Category.{v₂} Z] (p : Z ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (P : ObjectProperty Z) [P.IsClosedUnderIsomorphisms]
    (hloc : ∀ (U : BigFppfOver B S hS) (W : BigFppfOver B U.left.1 U.left.2 ⥤ Z),
      W ⋙ p = Over.map U.hom →
        ∃ V : BigFppfOver B U.left.1 U.left.2, AlgebraicGeometry.IsOpenImmersion V.hom.hom ∧
          ∀ T : BigFppfOver B U.left.1 U.left.2, Nonempty (T ⟶ V) ↔ P (W.obj T))
    {x y : Z} (φ : x ⟶ y)
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map (p.map φ)))
    (hx : P x) : P y := by
  have : p.IsFibered := hp.isFibered
  obtain ⟨V, hVopen, hV⟩ := hloc (p.obj y) (Functor.slicePointOfObject p (p.obj y) y rfl)
    (Functor.slicePointOfObject_comp p (p.obj y) y rfl)
  -- the value of the point at the object named by the base of `φ` is isomorphic to `x`
  obtain ⟨e⟩ := Functor.nonempty_iso_slicePointObj p hp (rfl : p.obj y = p.obj y) (p.map φ) φ
    (CategoryTheory.IsHomLift.map p φ)
  obtain ⟨m⟩ := (hV (Over.mk (p.map φ).left)).2 (P.prop_of_iso e.symm hx)
  -- the open subobject has every point of the base in its image
  have hw : (m.left).hom ≫ (V.hom).hom = (BigFppfOver.toScheme B S hS).map (p.map φ) :=
    congrArg (fun t : (p.obj x).left ⟶ (p.obj y).left => t.hom) (Over.w m)
  have hrange : Set.range (V.hom.hom).base = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨t, ht⟩ := hsurj z
    refine ⟨((m.left).hom).base t, ?_⟩
    have hz : (((m.left).hom) ≫ (V.hom).hom).base t = z := by rw [hw]; exact ht
    simpa using hz
  have : AlgebraicGeometry.IsOpenImmersion (V.hom.hom) := hVopen
  have : IsIso (V.hom.hom) :=
    AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (TopologicalSpace.Opens.ext (by simpa using hrange))
  have : IsIso V.hom := (ObjectProperty.isIso_hom_iff V.hom).1 inferInstance
  have h0 := (hV (Over.mk (𝟙 (p.obj y).left))).1 ⟨Over.homMk (inv V.hom) (by simp)⟩
  have := Functor.isIso_slicePointUnit p hp (p.obj y) y rfl
  exact P.prop_of_iso (asIso (Functor.slicePointUnit p (p.obj y) y rfl)) h0

section Locus

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, v₂, u + 1, u₂} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

/-- **The local complete intersection locus propagates across a morphism with surjective base.**
If `φ : P ⟶ Q` is a morphism of quintuples of `ℋ_d(𝒳/𝒴)` whose base component is surjective on
points and `P` lies in the locus of **Stacks 06CJ**, then so does `Q`.

This is the converse direction to `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_hom`, and it
needs the *openness* of the locus cut out on the base, not only its existence. -/
theorem lciLocus_of_hom_of_surjective (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    {P Q : Object B S hS 𝒳 𝒴 F d} (φ : P ⟶ Q)
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map φ.f))
    (hP : lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) Q := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)) :=
    isClosedUnderIsomorphisms_lciLocus
  exact prop_of_hom_of_surjective_of_openSliceLocus
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    isFiberedInGroupoids_finiteHilbertProjection _ (fun U W hW => hopen U W hW) φ hsurj hP

/-- **The local complete intersection locus propagates across a first-order thickening.** If
`φ : P ⟶ Q` is a morphism of quintuples of `ℋ_d(𝒳/𝒴)` whose base component is a first-order
thickening and `P` lies in the locus of **Stacks 06CJ**, then so does `Q`.

A first-order thickening is a thickening, hence surjective on points. -/
theorem lciLocus_of_hom_of_isFirstOrderThickening (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    {P Q : Object B S hS 𝒳 𝒴 F d} (φ : P ⟶ Q)
    (hφ : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map φ.f))
    (hP : lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) Q :=
  lciLocus_of_hom_of_surjective hopen φ hφ.isThickening.2 hP

/-- **The local complete intersection locus propagates across a morphism lying over a surjective
morphism of the site.** This is
`AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_hom_of_surjective` with the surjectivity
imposed on a morphism of the site the morphism of quintuples lies over, rather than on its own
base component: the two base morphisms agree up to the identifications of the source and target
bases, which are what `CategoryTheory.Functor.IsHomLift` records. -/
theorem lciLocus_of_isHomLift_of_surjective (hopen : HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    {P Q : Object B S hS 𝒳 𝒴 F d} (φ : P ⟶ Q) {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    (hφ : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsHomLift i φ)
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map i))
    (hP : lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) Q := by
  have := hφ
  have hU := CategoryTheory.IsHomLift.domain_eq
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    i φ
  have hU' := CategoryTheory.IsHomLift.codomain_eq
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    i φ
  subst hU
  subst hU'
  have hfac := CategoryTheory.IsHomLift.fac'
    (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    i φ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hfac
  have hf : φ.f = i := hfac
  exact lciLocus_of_hom_of_surjective hopen φ (by rw [hf]; exact hsurj) hP

end FiniteHilbert

end Locus

/-! ### The inclusion of the locus is formally smooth on objects -/

section Fibered

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` of **Stacks 06CJ**, read as a 1-morphism of the
2-category of categories fibred in groupoids over the big fppf site of `S`.

As for `AlgebraicGeometry.Stack.lciFiniteHilbertFibered`, the witness that the projection of the
locus is fibred in groupoids is an argument: it is clause (1) of **Stacks 06CL**,
`AlgebraicGeometry.Stack.isFiberedInGroupoids_lciFiniteHilbertCategory`. -/
noncomputable abbrev lciFiniteHilbertInclusionFibered
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    lciFiniteHilbertFibered h ⟶ finiteHilbertFibered B S hS d 𝒳 𝒴 F :=
  Bicategory.InducedBicategory.mkHom
    (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))

/-- **Every first-order lifting problem for the inclusion of the local complete intersection
locus is solved by the given quintuple of `ℋ_d(𝒳/𝒴)` itself.** The base component of the given
morphism is the thickening, which is surjective on points, so the quintuple over the larger
scheme lies in the locus by
`AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_hom_of_isFirstOrderThickening`; the morphism
of the locus is then the given one and the identification downstairs is an identity. -/
theorem hasFirstOrderObjectLifts_lciFiniteHilbertInclusion
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    HasFirstOrderObjectLifts B S hS (lciFiniteHilbertInclusionFibered h) := by
  intro U U' i hU hU' hi x y' a ha
  have ha' : (finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).IsHomLift i (a : x.1.obj ⟶ y'.1) := ha
  have hQ : FiniteHilbert.lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d) y'.1 :=
    FiniteHilbert.lciLocus_of_isHomLift_of_surjective hopen (a : x.1.obj ⟶ y'.1) i ha'
      hi.isThickening.2 x.1.property
  exact ⟨⟨⟨y'.1, hQ⟩, y'.2⟩, ObjectProperty.homMk (X := x.1) (Y := ⟨y'.1, hQ⟩) (a : x.1.obj ⟶ y'.1),
    𝟙 y'.1, (Functor.isHomLift_restrict_iff _ _ _ _).2 ha', CategoryTheory.IsHomLift.id y'.2,
    Category.comp_id a⟩

/-- **The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⊂ ℋ_d(𝒳/𝒴)` of Stacks 06CJ is formally smooth on objects**
in the sense of **Stacks 06D0**, given the open locus of Stacks 05X8 and 06CE and the witness
that the projection of the locus is fibred in groupoids.

This is the step by which the last paragraph of the proof of **Stacks 06D9** places the quintuple
it has produced over the thickening in the locus. -/
theorem isFormallySmoothOnObjects_lciFiniteHilbertInclusion
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    IsFormallySmoothOnObjects B S hS (lciFiniteHilbertFibered h)
      (finiteHilbertFibered B S hS d 𝒳 𝒴 F) (lciFiniteHilbertInclusionFibered h) :=
  isFormallySmoothOnObjects_of_exists_homLift B S hS (lciFiniteHilbertInclusionFibered h)
    (hasFirstOrderObjectLifts_lciFiniteHilbertInclusion hopen h)

/-- **The 1-morphism `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is the inclusion of the locus followed by the
forgetful 1-morphism of Stacks 05WD**, read in the 2-category of categories fibred in groupoids
over the big fppf site of `S`. -/
theorem lciFiniteHilbertInclusionFibered_comp_forgetTargetFibered
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    lciFiniteHilbertInclusionFibered h ≫ forgetTargetFibered B S hS d 𝒳 𝒴 F =
      lciFiniteHilbertToTargetFibered h :=
  rfl

/-- **Formal smoothness on objects of `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` follows from solving the first-order
lifting problem in the unrestricted `ℋ_d(𝒳/𝒴)`.** Given the open locus of Stacks 05X8 and 06CE
and the witness that the projection of the locus is fibred in groupoids, it is enough that every
quintuple of the *locus* over an affine `U`, together with an object of `𝒴` over an affine
first-order thickening `U ⊂ U'` whose restriction carries the quintuple's object of `𝒴`, lift to
a quintuple of `ℋ_d(𝒳/𝒴)` over `U'` — no condition on the lifted quintuple is required.

Membership of the locus is restored by
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_lciFiniteHilbertInclusion`, which is exactly
what the reduction `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_comp_of_lifts_through`
consumes.

This is the division of labour in the proof of **Stacks 06D9**: the quintuple over `U'` is built
in `ℋ_d(𝒳/𝒴)` out of the deformation of the cover that **Stacks 06D8** for algebraic spaces
supplies, and the local complete intersection condition is recovered afterwards from the openness
of the locus. -/
theorem isFormallySmoothOnObjects_lciFiniteHilbertToTarget_of_lifts
    (hopen : FiniteHilbert.HasOpenLciLocus B S hS 𝒳 𝒴 F d)
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids)
    (hlift : ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
      ∀ (x : (lciFiniteHilbertFibered h).val.p.Fiber U)
        (z' : (stackFibered B S hS 𝒴).val.p.Fiber U')
        (a : (CatFiberedInGroupoids.homFunctor (lciFiniteHilbertInclusionFibered h ≫
          forgetTargetFibered B S hS d 𝒳 𝒴 F)).obj x.1 ⟶ z'.1),
        (stackFibered B S hS 𝒴).val.p.IsHomLift i a →
        ∃ (y' : (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val.p.Fiber U')
          (b : (CatFiberedInGroupoids.homFunctor
            (lciFiniteHilbertInclusionFibered h)).obj x.1 ⟶ y'.1)
          (c : (CatFiberedInGroupoids.homFunctor
            (forgetTargetFibered B S hS d 𝒳 𝒴 F)).obj y'.1 ⟶ z'.1),
          (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val.p.IsHomLift i b ∧
            (stackFibered B S hS 𝒴).val.p.IsHomLift (𝟙 U') c ∧
            (CatFiberedInGroupoids.homFunctor
              (forgetTargetFibered B S hS d 𝒳 𝒴 F)).map b ≫ c = a) :
    IsFormallySmoothOnObjects B S hS (lciFiniteHilbertFibered h) (stackFibered B S hS 𝒴)
      (lciFiniteHilbertToTargetFibered h) :=
  isFormallySmoothOnObjects_comp_of_lifts_through B S hS
    (lciFiniteHilbertInclusionFibered h) (forgetTargetFibered B S hS d 𝒳 𝒴 F)
    (isFormallySmoothOnObjects_lciFiniteHilbertInclusion hopen h) hlift

end Fibered

end AlgebraicGeometry.Stack

end
