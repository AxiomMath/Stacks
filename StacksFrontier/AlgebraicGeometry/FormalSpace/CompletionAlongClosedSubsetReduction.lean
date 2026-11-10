module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.ThickeningStage

/-!
# The reduction of the completion of an algebraic space along a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `T ⊆ |X|` be a closed subset. The completion `X_{/T}` of `X` along `T` is the fppf
sheafification of the subfunctor of sections of `X` whose point-set image lies in `T`, and `Z`
is the reduced induced closed subspace of `X` supported on `T`. **Stacks 0GB9** says that `Z`
is the reduction of `X_{/T}`.

The canonical morphism `Z ⟶ X_{/T}` exists because every section of `Z` has point-set image
`|Z| = T`. It is a representable thickening: a scheme-valued point of `X_{/T}` is, on an fppf
covering of its base, a section of `X` supported on `T`, so the base change of `Z ⟶ X_{/T}`
along it is the inverse image of `Z` along a morphism to `X` with image in `T`, which is a
closed immersion and surjective. A representable thickening from a reduced algebraic space is
the reduction of its target.

## Main definitions

* `AlgebraicGeometry.Space.completionSheafToAmbient` is the morphism `X_{/T} ⟶ X` of
  presheaves of `Type (u + 1)` for an `X` whose universe lift is already a sheaf.
* `AlgebraicGeometry.FormalSpace.reducedClosedSubsetSheaf` is the reduced closed subspace `Z`
  of `X` supported on `T`, viewed as an fppf sheaf of `Type (u + 1)`, and
  `AlgebraicGeometry.FormalSpace.reducedClosedSubsetToCompletionSheaf` is the canonical
  morphism `Z ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.Space.hasImageIn_ι_reducedClosedSubspace`: a section of the reduced
  closed subspace supported on `T` has point-set image in `T`.
* `AlgebraicGeometry.Space.range_pointsMap_subset_of_whiskerRight_eq`: a scheme-valued point
  of `X_{/T}` has point-set image in `T`.
* `AlgebraicGeometry.Space.isThickening_of_isPullback_of_range_subset`: the inverse image of
  `Z` along a scheme-valued point of `X` with image in `T` is a thickening of its base.
* the canonical morphism `Z ⟶ X_{/T}` is a representable thickening:
  `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_toCompletionSheaf`.
* `AlgebraicGeometry.FormalSpace.isReduction_completionSheaf`: **Stacks 0GB9**.

## Implementation notes

The reduction is expressed through `AlgebraicGeometry.FormalSpace.IsReduction`, the predicate
naming the defining properties of the reduction of a formal algebraic space, so the conclusion
is that a canonically constructed morphism has those properties and no choice of a reduction is
involved. In particular the statement needs neither the existence of reductions nor that
`X_{/T}` is a formal algebraic space.

`AlgebraicGeometry.Space.completionSheafToAmbient` is used in place of
`AlgebraicGeometry.Space.completionSheafInclusion`, which lands in the sheafification of the
universe lift of `X`: for `X` an algebraic space that sheafification is isomorphic to the
universe lift itself, and the lift of the inclusion of the completion subfunctor through the
universal property of sheafification avoids carrying the isomorphism.

The locality step reads a section of the sheafification over the spectrum of a field on an
fppf covering of that spectrum, by `CategoryTheory.Presheaf.isLocallySurjective_toSheafify`,
and picks a member of the covering through a point of the spectrum by
`AlgebraicGeometry.BigFppfOver.exists_mem_range_of_mem_topology`. The residue field at a point
of that member gives a field-valued point which dominates the original one, so the two
represent the same point of `X`, and the covering section carries the membership in `T`.

The private helpers transferring a relative property of presheaves of `Type u` to the value
universe of the formal algebraic spaces, and cancelling a monomorphism in a cartesian square,
duplicate helpers which
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction` declares
privately; promoting them is a refactor of that file rather than part of this result.

## References

* [Stacks Project, Tag 0GB9](https://stacks.math.columbia.edu/tag/0GB9)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The completion inside the universe lift of the ambient presheaf -/

/-- The morphism `X_{/T} ⟶ X` from the completion of `X` along a set of points into the
universe lift of `X`, for an `X` whose universe lift is already an fppf sheaf: the inclusion
of the completion subfunctor, lifted through the universal property of sheafification. -/
noncomputable def completionSheafToAmbient (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (points B S hS X)) :
    (completionSheaf B S hS X T).obj ⟶ X ⋙ uliftFunctor.{u + 1} :=
  (BigFppfOver.topology B S hS).sheafifyLift (completionSubfunctor B S hS X T).ι hXsheaf

/-- A section of the completion subfunctor is carried by `X_{/T} ⟶ X` to the section of `X`
underlying it: the morphism is a lift of the inclusion of the completion subfunctor. -/
@[simp]
theorem toSheafify_comp_completionSheafToAmbient (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (points B S hS X)) :
    (BigFppfOver.topology B S hS).toSheafify (completionSubfunctor B S hS X T).toFunctor ≫
        completionSheafToAmbient B S hS X hXsheaf T =
      (completionSubfunctor B S hS X T).ι :=
  (BigFppfOver.topology B S hS).toSheafify_sheafifyLift _ _

/-- The morphism `X_{/T} ⟶ X` is a monomorphism: sheafification is left exact, so it carries
the inclusion of the completion subfunctor to a monomorphism, and the sheafification of `X` is
isomorphic to the universe lift of `X`. -/
theorem mono_completionSheafToAmbient (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    (T : Set (points B S hS X)) :
    Mono (completionSheafToAmbient B S hS X hXsheaf T) := by
  have hmap : Mono ((BigFppfOver.topology B S hS).sheafifyMap
      (completionSubfunctor B S hS X T).ι) :=
    ((BigFppfOver.topology B S hS).sheafification (Type (u + 1))).map_mono _
  have _ : IsIso ((BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1})) :=
    (BigFppfOver.topology B S hS).isIso_toSheafify hXsheaf
  have heq : (BigFppfOver.topology B S hS).sheafifyMap (completionSubfunctor B S hS X T).ι ≫
      inv ((BigFppfOver.topology B S hS).toSheafify (X ⋙ uliftFunctor.{u + 1})) =
      completionSheafToAmbient B S hS X hXsheaf T := by
    refine (BigFppfOver.topology B S hS).sheafifyLift_unique _ _ _ ?_
    rw [← Category.assoc, ← (BigFppfOver.topology B S hS).toSheafify_naturality,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← heq]
  exact mono_comp ((BigFppfOver.topology B S hS).sheafifyMap
    (completionSubfunctor B S hS X T).ι) _

/-! ### The reduced closed subspace on a closed set of points -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (T : Set (points B S hS X)) (hT : IsClosed T)

/-- **A section of the reduced closed subspace supported on `T` has point-set image in `T`**,
the point set of that subspace being `T` by Stacks 03IQ. -/
theorem hasImageIn_ι_reducedClosedSubspace (U : BigFppfOver B S hS)
    (x : (reducedClosedSubspace B S hS X hX T hT).toFunctor.obj (op U)) :
    HasImageIn B S hS X T U
      ((reducedClosedSubspace B S hS X hX T hT).ι.app (op U) x) := by
  intro p
  have hsub : Set.range (pointsMap B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
      (reducedClosedSubspace B S hS X hX T hT).ι) ⊆ T :=
    (range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT).le
  refine hsub ⟨(⟨p.carrier, p.contained, p.toBase,
    (reducedClosedSubspace B S hS X hX T hT).toFunctor.map p.value.op x⟩ :
      FieldValuedPoint B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor).class B S hS
        _, ?_⟩
  rw [pointsMap_class]
  exact congrArg (fun q : FieldValuedPoint B S hS X => q.class B S hS X)
    (congrArg (fun v : X.obj (op (FieldValuedPoint.siteObject B S hS (yoneda.obj U) p)) =>
        (⟨p.carrier, p.contained, p.toBase, v⟩ : FieldValuedPoint B S hS X))
      (NatTrans.naturality_apply (reducedClosedSubspace B S hS X hX T hT).ι p.value.op x))

/-- **The inverse image of the reduced closed subspace supported on `T` along a scheme-valued
point of `X` with point-set image in `T` is a thickening of that scheme.** It is a closed
immersion because the subspace is a closed subspace, and it is surjective because every point
of the base maps into `T`, which is the point set of the subspace; Stacks 03H4 produces the
point of the inverse image and Stacks 03H5 turns surjectivity on points into surjectivity. -/
theorem isThickening_of_isPullback_of_range_subset {a : BigFppfOver B S hS}
    {gs : yoneda.obj a ⟶ X}
    (hgs : Set.range (pointsMap B S hS (yoneda.obj a) gs) ⊆ T)
    {b : BigFppfOver B S hS}
    {fst : yoneda.obj b ⟶ (reducedClosedSubspace B S hS X hX T hT).toFunctor} {snd : b ⟶ a}
    (sq : IsPullback fst (yoneda.map snd) (reducedClosedSubspace B S hS X hX T hT).ι gs) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map snd) := by
  refine ⟨(isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).2.property gs fst snd sq,
    ?_⟩
  rw [← surjective_pointsMap_yoneda_iff B S hS snd]
  intro pa
  have hmem : pointsMap B S hS (yoneda.obj a) gs pa ∈
      Set.range (pointsMap B S hS (reducedClosedSubspace B S hS X hX T hT).toFunctor
        (reducedClosedSubspace B S hS X hX T hT).ι) := by
    rw [range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT]
    exact hgs ⟨pa, rfl⟩
  obtain ⟨pz, hpz⟩ := hmem
  obtain ⟨v, -, hv⟩ := exists_point_of_isPullback_presheaf B S hS sq pz pa hpz
  exact ⟨v, hv⟩

/-- A scheme-valued point of `X_{/T}`, restricted along a morphism from an object `A` of the
site, comes from the completion subfunctor on a nonempty member of an fppf covering of `A`:
the restricted section lifts along the sheafification unit on a covering sieve of `A`, and a
member of that sieve carries a point of `A`. -/
private theorem exists_hasImageIn_restriction
    (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    {a : BigFppfOver B S hS}
    (g : (uliftYoneda.{u + 1}).obj a ⟶ (completionSheaf B S hS X T).obj)
    {gs : yoneda.obj a ⟶ X}
    (hgs : Functor.whiskerRight gs uliftFunctor.{u + 1} =
      g ≫ completionSheafToAmbient B S hS X hXsheaf T)
    (A : BigFppfOver B S hS) (k : A ⟶ a) (x : (BigFppfOver.toScheme B S hS).obj A) :
    ∃ (V : BigFppfOver B S hS) (h : V ⟶ A) (_ : (BigFppfOver.toScheme B S hS).obj V),
      HasImageIn B S hS X T V (gs.app (op V) (h ≫ k)) := by
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).toSheafify
        (completionSubfunctor B S hS X T).toFunctor) := inferInstance
  have hR := hls.imageSieve_mem
    (g.app (op A) (⟨k⟩ : ((uliftYoneda.{u + 1}).obj a).obj (op A)))
  obtain ⟨V, h, hhR, hrange⟩ :=
    BigFppfOver.exists_mem_range_of_mem_topology B S hS hR x
  obtain ⟨w, -⟩ := hrange
  obtain ⟨t, ht⟩ := hhR
  refine ⟨V, h, w, ?_⟩
  have e1 : (t : (X ⋙ uliftFunctor.{u + 1}).obj (op V)) =
      (completionSheafToAmbient B S hS X hXsheaf T).app (op V)
        (((BigFppfOver.topology B S hS).toSheafify
          (completionSubfunctor B S hS X T).toFunctor).app (op V) t) :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      (toSheafify_comp_completionSheafToAmbient B S hS X hXsheaf T) (op V)) t).symm
  rw [ht] at e1
  erw [NatTrans.naturality_apply (completionSheafToAmbient B S hS X hXsheaf T) h.op] at e1
  erw [(ConcreteCategory.congr_hom (NatTrans.congr_app hgs (op A))
    (⟨k⟩ : ((uliftYoneda.{u + 1}).obj a).obj (op A))).symm] at e1
  have hval : (t : (X ⋙ uliftFunctor.{u + 1}).obj (op V)).down =
      gs.app (op V) (h ≫ k) := by
    rw [congrArg ULift.down e1]
    exact (NatTrans.naturality_apply gs h.op k).symm
  rw [← hval]
  exact t.2

/-- **A scheme-valued point of the completion `X_{/T}` has point-set image in `T`.** A
field-valued point of the base restricts the section to the spectrum of a field, on an fppf
covering of which the section comes from the completion subfunctor; the residue field at a
point of a member of that covering gives a field-valued point which dominates the given one,
so the two represent the same point of `X`, and the member carries the membership in `T`. -/
theorem range_pointsMap_subset_of_whiskerRight_eq
    (hXsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}))
    {a : BigFppfOver B S hS}
    (g : (uliftYoneda.{u + 1}).obj a ⟶ (completionSheaf B S hS X T).obj)
    {gs : yoneda.obj a ⟶ X}
    (hgs : Functor.whiskerRight gs uliftFunctor.{u + 1} =
      g ≫ completionSheafToAmbient B S hS X hXsheaf T) :
    Set.range (pointsMap B S hS (yoneda.obj a) gs) ⊆ T := by
  rintro x ⟨z, rfl⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  obtain ⟨V, h, w, hfV⟩ := exists_hasImageIn_restriction B S hS T hXsheaf g hgs
    (p.siteObject B S hS (yoneda.obj a)) p.value (IsLocalRing.closedPoint p.carrier)
  -- the residue field at a point of the member gives a dominating field-valued point
  have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj a)
      (⟨(schemePointRepresentative B S hS V w).carrier,
        (schemePointRepresentative B S hS V w).contained,
        (schemePointRepresentative B S hS V w).toBase,
        (schemePointRepresentative B S hS V w).value ≫ h ≫ p.value⟩ :
          FieldValuedPoint B S hS (yoneda.obj a)) p :=
    ⟨(schemePointRepresentative B S hS V w).value ≫ h, by simp⟩
  have hvalue := hfV (schemePointRepresentative B S hS V w)
  simp only [← NatTrans.naturality_apply] at hvalue
  change pointsMap B S hS (yoneda.obj a) gs
    (FieldValuedPoint.class B S hS (yoneda.obj a) p) ∈ T
  rw [← FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj a)
    ⟨_, FieldValuedPoint.dominates_refl B S hS (yoneda.obj a) _, hdom⟩,
    pointsMap_class B S hS (yoneda.obj a) gs]
  exact hvalue

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
variable (T : Set (Space.points B S hS X)) (hT : IsClosed T)

include hX in
/-- The universe lift of `X` is an fppf sheaf, `X` being an algebraic space over `S`. -/
theorem isSheaf_comp_uliftFunctor :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1}) :=
  ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X).mpr hX).isSheaf

/-- **The reduced induced closed subspace `Z` of `X` supported on `T`**, viewed as an fppf
sheaf of `Type (u + 1)`, the value universe of the formal algebraic spaces. -/
noncomputable def reducedClosedSubsetSheaf : FppfSheaf B S hS :=
  sheafOfAlgebraicSpace B S hS (Space.reducedClosedSubspace B S hS X hX T hT).toFunctor
    (Space.isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).1

/-- The canonical morphism from the universe lift of `Z` into the completion subfunctor,
before sheafifying: a section of `Z` has point-set image `|Z| = T`. -/
noncomputable def reducedClosedSubsetToCompletionSubfunctor :
    (Space.reducedClosedSubspace B S hS X hX T hT).toFunctor ⋙ uliftFunctor.{u + 1} ⟶
      (Space.completionSubfunctor B S hS X T).toFunctor where
  app U := ↾fun x =>
    ⟨ULift.up ((Space.reducedClosedSubspace B S hS X hX T hT).ι.app U x.down),
      Space.hasImageIn_ι_reducedClosedSubspace B S hS hX T hT U.unop x.down⟩
  naturality U V i := by
    ext x
    exact Subtype.ext (congrArg ULift.up
      (NatTrans.naturality_apply (Space.reducedClosedSubspace B S hS X hX T hT).ι i x.down))

/-- The canonical morphism into the completion subfunctor is the inclusion of `Z` into `X`,
read in the value universe of the formal algebraic spaces. -/
theorem reducedClosedSubsetToCompletionSubfunctor_comp_ι :
    reducedClosedSubsetToCompletionSubfunctor B S hS hX T hT ≫
        (Space.completionSubfunctor B S hS X T).ι =
      Functor.whiskerRight (Space.reducedClosedSubspace B S hS X hX T hT).ι
        uliftFunctor.{u + 1} := rfl

/-- **The canonical morphism `Z ⟶ X_{/T}`** from the reduced closed subspace supported on `T`
into the completion of `X` along `T`. -/
noncomputable def reducedClosedSubsetToCompletionSheaf :
    reducedClosedSubsetSheaf B S hS hX T hT ⟶ Space.completionSheaf B S hS X T :=
  ObjectProperty.homMk (reducedClosedSubsetToCompletionSubfunctor B S hS hX T hT ≫
    (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS X T).toFunctor)

/-- The canonical morphism `Z ⟶ X_{/T}` is a morphism over `X`. -/
theorem reducedClosedSubsetToCompletionSheaf_comp_completionSheafToAmbient :
    (reducedClosedSubsetToCompletionSheaf B S hS hX T hT).hom ≫
        Space.completionSheafToAmbient B S hS X (isSheaf_comp_uliftFunctor B S hS hX) T =
      Functor.whiskerRight (Space.reducedClosedSubspace B S hS X hX T hT).ι
        uliftFunctor.{u + 1} := by
  have h1 : (reducedClosedSubsetToCompletionSheaf B S hS hX T hT).hom ≫
      Space.completionSheafToAmbient B S hS X (isSheaf_comp_uliftFunctor B S hS hX) T =
      reducedClosedSubsetToCompletionSubfunctor B S hS hX T hT ≫
        ((BigFppfOver.topology B S hS).toSheafify
            (Space.completionSubfunctor B S hS X T).toFunctor ≫
          Space.completionSheafToAmbient B S hS X
            (isSheaf_comp_uliftFunctor B S hS hX) T) :=
    Category.assoc _ _ _
  rw [h1, Space.toSheafify_comp_completionSheafToAmbient,
    reducedClosedSubsetToCompletionSubfunctor_comp_ι]

/-- **The canonical morphism `Z ⟶ X_{/T}` is a representable thickening.** A scheme-valued
point of `X_{/T}` is a scheme-valued point of `X` with point-set image in `T`, because
`X_{/T} ⟶ X` is a monomorphism and `X` is a sheaf; the base change of `Z ⟶ X_{/T}` along it is
therefore the inverse image of `Z` along a morphism to `X` supported on `T`, which is a
surjective closed immersion. -/
theorem isRepresentableThickeningULift_toCompletionSheaf :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (reducedClosedSubsetToCompletionSheaf B S hS hX T hT).hom := by
  have _ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hsheaf := isSheaf_comp_uliftFunctor B S hS hX
  have _ := Space.mono_completionSheafToAmbient B S hS X hsheaf T
  apply MorphismProperty.relative.of_exists
  intro a g
  obtain ⟨gs, hgs0⟩ := ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (u + 1))).obj uliftFunctor.{u + 1}).map_surjective
      (g ≫ Space.completionSheafToAmbient B S hS X hsheaf T)
  have hgs : Functor.whiskerRight gs uliftFunctor.{u + 1} =
      g ≫ Space.completionSheafToAmbient B S hS X hsheaf T := hgs0
  obtain ⟨b, snd, fst, sq⟩ :=
    (Space.isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).2.1 gs
  have hsq : IsPullback (Functor.whiskerRight fst uliftFunctor.{u + 1})
      ((uliftYoneda.{u + 1}).map snd)
      (Functor.whiskerRight (Space.reducedClosedSubspace B S hS X hX T hT).ι
        uliftFunctor.{u + 1})
      (Functor.whiskerRight gs uliftFunctor.{u + 1}) :=
    sq.map ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
      (Type (u + 1))).obj uliftFunctor.{u + 1})
  rw [hgs, ← reducedClosedSubsetToCompletionSheaf_comp_completionSheafToAmbient] at hsq
  exact ⟨b, Functor.whiskerRight fst uliftFunctor.{u + 1}, snd,
    isPullback_of_comp_mono (Space.completionSheafToAmbient B S hS X hsheaf T) hsq,
    Space.isThickening_of_isPullback_of_range_subset B S hS hX T hT
      (Space.range_pointsMap_subset_of_whiskerRight_eq B S hS T hsheaf g hgs) sq⟩

/-- **Stacks 0GB9.** Let `X` be an algebraic space over `S` and let `T ⊆ |X|` be a closed
subset. The reduction of the completion `X_{/T}` of `X` along `T` is the reduced induced
closed subspace `Z` of `X` supported on `T`: the canonical morphism `Z ⟶ X_{/T}` exhibits `Z`
as the reduction of `X_{/T}`. -/
@[stacks 0GB9]
theorem isReduction_completionSheaf :
    IsReduction B S hS (Space.completionSheaf B S hS X T)
      (reducedClosedSubsetSheaf B S hS hX T hT)
      (reducedClosedSubsetToCompletionSheaf B S hS hX T hT) :=
  isReduction_of_isRepresentableThickening B S hS _
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr
      (Space.isClosedSubspace_reducedClosedSubspace B S hS X hX T hT).1)
    (hasEtaleLocalPropertyULift_comp_uliftFunctor B S hS _
      (Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT))
    (isRepresentableThickeningULift_toCompletionSheaf B S hS hX T hT)

end FormalSpace

end AlgebraicGeometry

end
