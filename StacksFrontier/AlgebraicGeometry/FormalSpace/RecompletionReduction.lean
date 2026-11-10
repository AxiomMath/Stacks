module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubfunctorSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Recompletion

/-!
# The reduction of the completion of a formal algebraic space along a closed subset

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with reduction `i : X_red ⟶ X`, and let `T ⊆ |X_red|` be a closed subset. **Stacks 0GVU**
says that the reduction `(X_{/T})_red` of the completion `X_{/T}` of `X` along `T` is the
reduced induced closed subspace `Z` of `X_red` corresponding to `T`.

The completion is `AlgebraicGeometry.FormalSpace.completionAlong` of Stacks 0GVS: the fppf
sheafification of the subfunctor of `X` whose sections over an object `U` of the site are the
sections with `f(|U|) ⊆ T`. The subspace `Z` is the datum
`AlgebraicGeometry.Space.reducedClosedSubspace` of Stacks 03IQ, so nothing is redefined here and
no reduced closed subspace is chosen.

Both `Z` and `(X_{/T})_red` are reduced algebraic spaces singled out by one and the same mapping
property: a morphism from a reduced algebraic space to `X` factors through either one exactly
when its set of points lands in `T`. That is the argument of the source, and here it takes the
following form. The composite `Z ⟶ X_red ⟶ X` has point set `T`, so it factors through the
completion, giving a canonical morphism `c : Z ⟶ X_{/T}`; and `c` is a representable thickening,
because the base change of `Z ⟶ X` along a scheme-valued point of `X_{/T}` is a closed immersion
which is surjective, the point in question lying in `T`. A representable thickening of an fppf
sheaf by a reduced algebraic space exhibits its source as the reduction of its target, by
`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`, so the mapping property
of `(X_{/T})_red` is a consequence rather than an input, and any reduction of `X_{/T}` is
canonically isomorphic to `Z`.

## Main definitions

* `AlgebraicGeometry.Space.pointsEquivPointsULift` identifies the points of a presheaf of
  `Type u` with the points of its universe lift, the value universe of the formal algebraic
  spaces.
* `AlgebraicGeometry.Space.completionSheafULiftLift` is the factorization of a morphism of fppf
  sheaves into `X` whose set of points lands in `T` through the completion `X_{/T}`.
* `AlgebraicGeometry.FormalSpace.liftedPointSet` is a subset of `|X_red|` read in the value
  universe of the formal algebraic spaces, and
  `AlgebraicGeometry.FormalSpace.ambientPointSet` is its image inside `|X|`, which is the set
  along which the completion is taken.
* `AlgebraicGeometry.FormalSpace.reducedSubspaceSheaf` is the reduced induced closed subspace
  `Z` of `X_red` on a closed subset `T` of `|X_red|`, viewed as an fppf sheaf of `Type (u + 1)`,
  with `AlgebraicGeometry.FormalSpace.reducedSubspaceSheafInclusion` the inclusion `Z ⟶ X_red`
  and `AlgebraicGeometry.FormalSpace.reducedSubspaceToCompletionAlong` the canonical morphism
  `c : Z ⟶ X_{/T}`.

## Main results

* `AlgebraicGeometry.Space.mono_completionSheafULiftInclusion`: a completion includes into the
  ambient sheaf by a monomorphism.
* `AlgebraicGeometry.Space.range_pointsMapULift_completionSheafULiftInclusion_subset`: the set
  of points of a completion lies in the set along which the completion is taken.
* `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_reducedSubspaceToCompletionAlong`:
  the canonical morphism `Z ⟶ X_{/T}` is a representable thickening.
* `AlgebraicGeometry.FormalSpace.isReduction_completionAlong`: **Stacks 0GVU**, that `Z ⟶ X_{/T}`
  exhibits `Z` as the reduction of the completion, and
  `AlgebraicGeometry.FormalSpace.existsUnique_iso_reducedSubspaceSheaf`, the resulting canonical
  identification of any reduction of `X_{/T}` with `Z`.

## The form of the reduction of `X`

The reduction is written as the universe lift of an algebraic space over `S`, which is what
makes the reduced induced closed subspace of Stacks 03IQ — a notion about presheaves of
`Type u` — available for it. This costs no generality: an algebraic space in the value universe
of the formal algebraic spaces is, up to isomorphism, the universe lift of one in `Type u`,
since it is small, by
`AlgebraicGeometry.Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift`.

The one input the argument needs about the completion itself is that the subfunctor of `X` cut
out by the condition `f(|U|) ⊆ T` is an fppf sheaf, so that a field-valued point of `X_{/T}` is
a section of that subfunctor and therefore visibly lies in `T`. That is
`AlgebraicGeometry.Space.isSheaf_completionSubfunctorULift`, which holds for every fppf sheaf
and every set of its points because an fppf covering sieve is surjective on the points of
Stacks 03BU.

## Implementation notes

The mapping property of the reduced induced closed subspace is Stacks 03JJ,
`AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset`, for a source
which is a reduced algebraic space over `S` in `Type u`. It is not used here: the morphism
`c : Z ⟶ X_{/T}` is shown to be a representable thickening, and the unique factorization of a
morphism from a reduced algebraic space in the value universe of the formal algebraic spaces —
which 03JJ does not reach — then comes from
`AlgebraicGeometry.FormalSpace.isReduction_of_isRepresentableThickening`.

The base change of `Z ⟶ X` along a scheme-valued point of `X_{/T}` is computed in two steps.
First the point is base-changed along the reduction `X_red ⟶ X`, which is a representable
thickening, and the result is an object of the site mapping to `X_red`, that is a morphism of
presheaves of `Type u` into the reduction; then `Z ⟶ X_red` is base-changed along that, inside
presheaves of `Type u`, where the comparison of point sets needed for surjectivity is available.
The two cartesian squares are pasted and the inclusion `X_{/T} ⟶ X`, being a monomorphism, is
cancelled.

The private helpers of this file duplicate, at file scope, helpers which
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSurjective` declare privately; they are private
there, hence not importable, and promoting them is a refactor of those files rather than part of
this result. The identification of the points of a presheaf with those of its universe lift is
declared publicly here, since it occurs in the statements below.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 0GVS](https://stacks.math.columbia.edu/tag/0GVS)
* [Stacks Project, Tag 0GVU](https://stacks.math.columbia.edu/tag/0GVU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Points in the two value universes -/

/-- A field-valued point of a presheaf of `Type u` is the same thing as a field-valued point of
its universe lift: the section is transported along the bijection `ULift.up`. -/
def fieldValuedPointEquivULift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    FieldValuedPoint B S hS F ≃
      FieldValuedPointULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1}) where
  toFun p :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := ⟨p.value⟩ }
  invFun p :=
    { carrier := p.carrier
      field := p.field
      contained := p.contained
      toBase := p.toBase
      value := p.value.down }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The points of a presheaf of `Type u` are the points of its universe lift: the two relations
of having a common field-valued extension correspond. -/
def pointsEquivPointsULift (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    points B S hS F ≃ pointsULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1}) := by
  refine Quot.congr (fieldValuedPointEquivULift B S hS F) fun _ _ => ⟨?_, ?_⟩
  · rintro ⟨p, ⟨left, hleft⟩, ⟨right, hright⟩⟩
    exact ⟨fieldValuedPointEquivULift B S hS F p, ⟨left, congrArg ULift.up hleft⟩,
      ⟨right, congrArg ULift.up hright⟩⟩
  · rintro ⟨p, ⟨left, hleft⟩, ⟨right, hright⟩⟩
    exact ⟨(fieldValuedPointEquivULift B S hS F).symm p, ⟨left, congrArg ULift.down hleft⟩,
      ⟨right, congrArg ULift.down hright⟩⟩

/-- The identification of the points of a presheaf of `Type u` with those of its universe lift
is natural in the presheaf. -/
theorem pointsEquivPointsULift_pointsMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (p : points B S hS F) :
    pointsEquivPointsULift B S hS G (pointsMap B S hS F f p) =
      pointsMapULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1})
        (Functor.whiskerRight f uliftFunctor.{u + 1}) (pointsEquivPointsULift B S hS F p) := by
  induction p using Quot.ind with
  | _ p => rfl

/-- The set of points of the universe lift of a morphism of presheaves of `Type u` is the set of
points of that morphism, read through the identification of the two spaces of points. -/
theorem range_pointsMapULift_whiskerRight {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    Set.range (pointsMapULift.{u + 1} B S hS (F ⋙ uliftFunctor.{u + 1})
        (Functor.whiskerRight f uliftFunctor.{u + 1})) =
      pointsEquivPointsULift B S hS G '' Set.range (pointsMap B S hS F f) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := (pointsEquivPointsULift B S hS F).surjective p
    exact ⟨pointsMap B S hS F f q, ⟨q, rfl⟩, pointsEquivPointsULift_pointsMap B S hS f q⟩
  · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨pointsEquivPointsULift B S hS F q,
      (pointsEquivPointsULift_pointsMap B S hS f q).symm⟩

/-! ### Factoring a morphism through a completion -/

/-- A morphism of presheaves into `X` whose set of points lies in a set `T` of points of `X`
takes values in the subfunctor of sections with point-set image in `T`: a field-valued point of
the source restricted from the object carrying a section is carried to the field-valued point of
`X` cut out of the image of that section. -/
def completionSubfunctorULiftLift {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (T : Set (pointsULift.{u + 1} B S hS X)) (g : Y ⟶ X)
    (hg : Set.range (pointsMapULift.{u + 1} B S hS Y g) ⊆ T) :
    Y ⟶ (completionSubfunctorULift B S hS X T).toFunctor where
  app U := ↾fun y => ⟨g.app U y, by
    change HasImageInULift B S hS X T U.unop (g.app U y)
    intro p
    rw [show X.map p.value.op (g.app U y) = g.app _ (Y.map p.value.op y) from
      (NatTrans.naturality_apply g p.value.op y).symm]
    exact hg ⟨(⟨p.carrier, p.contained, p.toBase, Y.map p.value.op y⟩ :
      FieldValuedPointULift.{u + 1} B S hS Y).class B S hS Y, rfl⟩⟩
  naturality := by
    intro U V k
    ext y
    apply Subtype.ext
    exact NatTrans.naturality_apply g k y

/-- **A morphism of fppf sheaves into `X` whose set of points lies in `T` factors through the
completion `X_{/T}`.** The factorization is through the completion subfunctor, composed with the
unit of the sheafification; no choice is involved. -/
def completionSheafULiftLift (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) (Y : FormalSpace.FppfSheaf B S hS)
    (g : Y ⟶ X) (hg : Set.range (pointsMapULift.{u + 1} B S hS Y.obj g.hom) ⊆ T) :
    Y ⟶ completionSheafULift B S hS X T :=
  ObjectProperty.homMk (completionSubfunctorULiftLift B S hS T g.hom hg ≫
    (BigFppfOver.topology B S hS).toSheafify
      (completionSubfunctorULift B S hS X.obj T).toFunctor)

/-- The unit of the sheafification, followed by the inclusion of a completion into the ambient
sheaf, is the inclusion of the completion subfunctor. -/
theorem toSheafify_comp_completionSheafULiftInclusion (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) :
    (BigFppfOver.topology B S hS).toSheafify
          (completionSubfunctorULift B S hS X.obj T).toFunctor ≫
        (completionSheafULiftInclusion B S hS X T).hom =
      (completionSubfunctorULift B S hS X.obj T).ι := by
  rw [completionSheafULiftInclusion_hom]
  exact (BigFppfOver.topology B S hS).toSheafify_sheafifyLift _ _

/-- The factorization of a morphism through a completion is a factorization of it. -/
theorem completionSheafULiftLift_comp (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) (Y : FormalSpace.FppfSheaf B S hS)
    (g : Y ⟶ X) (hg : Set.range (pointsMapULift.{u + 1} B S hS Y.obj g.hom) ⊆ T) :
    completionSheafULiftLift B S hS X T Y g hg ≫ completionSheafULiftInclusion B S hS X T = g := by
  refine Sheaf.hom_ext ?_
  change completionSubfunctorULiftLift B S hS T g.hom hg ≫
      ((BigFppfOver.topology B S hS).toSheafify
          (completionSubfunctorULift B S hS X.obj T).toFunctor ≫
        (completionSheafULiftInclusion B S hS X T).hom) = g.hom
  rw [toSheafify_comp_completionSheafULiftInclusion]
  rfl

/-! ### The completion includes into the ambient sheaf by a monomorphism -/

/-- **A completion includes into the ambient sheaf by a monomorphism**: the inclusion of the
subfunctor of sections with point-set image in the given set is a monomorphism, and fppf
sheafification preserves finite limits, hence monomorphisms. -/
theorem mono_completionSheafULiftInclusion (X : FormalSpace.FppfSheaf B S hS)
    (T : Set (pointsULift.{u + 1} B S hS X.obj)) :
    Mono (completionSheafULiftInclusion B S hS X T) := by
  have h := (IsKernelPair.id_of_mono (completionSubfunctorULift B S hS X.obj T).ι).map
    (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  rw [CategoryTheory.Functor.map_id] at h
  have hm : Mono ((CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).map (completionSubfunctorULift B S hS X.obj T).ι) :=
    IsKernelPair.mono_of_isIso_fst h
  have hdef : completionSheafULiftInclusion B S hS X T =
      (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
          (completionSubfunctorULift B S hS X.obj T).ι ≫
        (isoSheafifySheaf B S hS X).inv := rfl
  rw [hdef]
  infer_instance

/-! ### The set of points of a completion -/

/-- An isomorphism of presheaves is surjective on points. -/
private theorem surjective_pointsMapULift_of_isIso
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ⟶ G) (he : IsIso e) :
    Function.Surjective (pointsMapULift.{u + 1} B S hS F e) := by
  intro p
  refine ⟨pointsMapULift.{u + 1} B S hS G (inv e) p, ?_⟩
  have h : pointsMapULift.{u + 1} B S hS G (inv e ≫ e) p = p := by
    rw [IsIso.inv_hom_id, pointsMapULift_id]
    rfl
  rwa [pointsMapULift_comp, Function.comp_apply] at h

/-- **The set of points of a completion lies in the set along which the completion is taken**,
given that the completion subfunctor is an fppf sheaf.

That hypothesis makes the unit of the sheafification an isomorphism, so the points of the
completion are the points of the subfunctor; and a field-valued point of the subfunctor is a
section whose point-set image lies in the given set, tested at the identity field-valued point of
the field spectrum carrying it. -/
theorem range_pointsMapULift_completionSheafULiftInclusion_subset
    (X : FormalSpace.FppfSheaf B S hS) (T : Set (pointsULift.{u + 1} B S hS X.obj))
    (hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (completionSubfunctorULift B S hS X.obj T).toFunctor) :
    Set.range (pointsMapULift.{u + 1} B S hS (completionSheafULift B S hS X T).obj
      (completionSheafULiftInclusion B S hS X T).hom) ⊆ T := by
  have hiso : IsIso ((BigFppfOver.topology B S hS).toSheafify
      (completionSubfunctorULift B S hS X.obj T).toFunctor) := by
    rw [← (BigFppfOver.topology B S hS).isoSheafify_hom hsh]
    infer_instance
  have hsub : Set.range (pointsMapULift.{u + 1} B S hS
      (completionSubfunctorULift B S hS X.obj T).toFunctor
      (completionSubfunctorULift B S hS X.obj T).ι) ⊆ T := by
    rintro _ ⟨p, rfl⟩
    induction p using Quot.ind with
    | _ p =>
      have hmem := p.value.2
        ({ carrier := p.carrier
           contained := p.contained
           toBase := p.toBase
           value := 𝟙 (p.siteObject B S hS
             (completionSubfunctorULift B S hS X.obj T).toFunctor) } :
          FieldValuedPoint B S hS
            (yoneda.obj (p.siteObject B S hS
              (completionSubfunctorULift B S hS X.obj T).toFunctor)))
      have hval : X.obj.map (𝟙 (p.siteObject B S hS
            (completionSubfunctorULift B S hS X.obj T).toFunctor)).op p.value.1 = p.value.1 := by
        rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
      refine Set.mem_of_eq_of_mem ?_ hmem
      exact congrArg (fun v => (⟨p.carrier, p.contained, p.toBase, v⟩ :
        FieldValuedPointULift.{u + 1} B S hS X.obj).class B S hS X.obj) hval.symm
  rintro _ ⟨q, rfl⟩
  obtain ⟨r, rfl⟩ := surjective_pointsMapULift_of_isIso B S hS
    ((BigFppfOver.topology B S hS).toSheafify
      (completionSubfunctorULift B S hS X.obj T).toFunctor) hiso q
  have h := congrFun (pointsMapULift_comp B S hS
      (completionSubfunctorULift B S hS X.obj T).toFunctor
      ((BigFppfOver.topology B S hS).toSheafify
        (completionSubfunctorULift B S hS X.obj T).toFunctor)
      (completionSheafULiftInclusion B S hS X T).hom) r
  rw [toSheafify_comp_completionSheafULiftInclusion] at h
  exact Set.mem_of_eq_of_mem h.symm (hsub ⟨r, rfl⟩)

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-! ### The reduced induced closed subspace of the reduction -/

variable {X : FppfSheaf B S hS} {Xred₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hXred₀ : IsAlgebraicSpace B S hS Xred₀)

/-- A subset of the points of an algebraic space over `S`, read as a subset of the points of its
universe lift. This is the form in which a closed subset of `|X_red|` enters the completion of a
formal algebraic space. -/
def liftedPointSet (T : Set (Space.points B S hS Xred₀)) :
    Set (Space.pointsULift.{u + 1} B S hS
      (sheafOfAlgebraicSpace B S hS Xred₀ hXred₀).obj) :=
  Space.pointsEquivPointsULift B S hS Xred₀ '' T

/-- **The reduced induced closed subspace `Z` of `X_red` on a closed subset `T` of its points**,
viewed as an fppf sheaf of `Type (u + 1)`. It is the datum
`AlgebraicGeometry.Space.reducedClosedSubspace` of Stacks 03IQ. -/
def reducedSubspaceSheaf (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T) :
    FppfSheaf B S hS :=
  sheafOfAlgebraicSpace B S hS
    (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).toFunctor
    (Space.isClosedSubspace_reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).1

/-- The inclusion `Z ⟶ X_red` of fppf sheaves. -/
def reducedSubspaceSheafInclusion (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T) :
    reducedSubspaceSheaf B S hS hXred₀ T hT ⟶ sheafOfAlgebraicSpace B S hS Xred₀ hXred₀ :=
  ObjectProperty.homMk (Functor.whiskerRight
    (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).ι uliftFunctor.{u + 1})

/-- The set of points of `Z`, read in the value universe of the formal algebraic spaces, is the
closed subset `T` read there. -/
theorem range_pointsMapULift_reducedSubspaceSheafInclusion
    (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T) :
    Set.range (Space.pointsMapULift.{u + 1} B S hS
        (reducedSubspaceSheaf B S hS hXred₀ T hT).obj
        (reducedSubspaceSheafInclusion B S hS hXred₀ T hT).hom) =
      liftedPointSet B S hS hXred₀ T := by
  change Set.range (Space.pointsMapULift.{u + 1} B S hS
      ((Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).toFunctor ⋙
        uliftFunctor.{u + 1})
      (Functor.whiskerRight (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).ι
        uliftFunctor.{u + 1})) = liftedPointSet B S hS hXred₀ T
  rw [Space.range_pointsMapULift_whiskerRight,
    Space.range_pointsMap_ι_reducedClosedSubspace]
  rfl

/-- A subset of the points of the reduction of `X`, read inside the points of `X` through the
inclusion of the reduction. The completion `X_{/T}` is the completion of `X` along this set. -/
def ambientPointSet (i : sheafOfAlgebraicSpace B S hS Xred₀ hXred₀ ⟶ X)
    (T : Set (Space.points B S hS Xred₀)) : Set (Space.pointsULift.{u + 1} B S hS X.obj) :=
  Space.pointsMapULift.{u + 1} B S hS (sheafOfAlgebraicSpace B S hS Xred₀ hXred₀).obj i.hom ''
    liftedPointSet B S hS hXred₀ T

variable {i : sheafOfAlgebraicSpace B S hS Xred₀ hXred₀ ⟶ X}

/-- The set of points of the composite `Z ⟶ X_red ⟶ X` is the closed subset `T`, read inside the
points of `X` through the inclusion of the reduction. -/
theorem range_pointsMapULift_reducedSubspaceSheafInclusion_comp
    (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T) :
    Set.range (Space.pointsMapULift.{u + 1} B S hS
        (reducedSubspaceSheaf B S hS hXred₀ T hT).obj
        (reducedSubspaceSheafInclusion B S hS hXred₀ T hT ≫ i).hom) =
      ambientPointSet B S hS hXred₀ i T := by
  change Set.range (Space.pointsMapULift.{u + 1} B S hS
      (reducedSubspaceSheaf B S hS hXred₀ T hT).obj
      ((reducedSubspaceSheafInclusion B S hS hXred₀ T hT).hom ≫ i.hom)) =
    ambientPointSet B S hS hXred₀ i T
  rw [Space.pointsMapULift_comp, Set.range_comp,
    range_pointsMapULift_reducedSubspaceSheafInclusion]
  rfl

/-- **The canonical morphism `c : Z ⟶ X_{/T}`.** The composite `Z ⟶ X_red ⟶ X` has set of points
`T`, so it factors through the completion of `X` along `T`. -/
def reducedSubspaceToCompletionAlong (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T) :
    reducedSubspaceSheaf B S hS hXred₀ T hT ⟶ completionAlong i (liftedPointSet B S hS hXred₀ T) :=
  Space.completionSheafULiftLift B S hS X _ _
    (reducedSubspaceSheafInclusion B S hS hXred₀ T hT ≫ i)
    (le_of_eq (range_pointsMapULift_reducedSubspaceSheafInclusion_comp B S hS hXred₀ T hT))

/-- The canonical morphism `Z ⟶ X_{/T}` is compatible with the inclusions into `X`. -/
theorem reducedSubspaceToCompletionAlong_comp
    (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T) :
    reducedSubspaceToCompletionAlong B S hS hXred₀ T hT ≫
        completionAlongInclusion i (liftedPointSet B S hS hXred₀ T) =
      reducedSubspaceSheafInclusion B S hS hXred₀ T hT ≫ i :=
  Space.completionSheafULiftLift_comp B S hS X _ _ _ _

/-! ### The canonical morphism is a representable thickening -/

/-- **The canonical morphism `Z ⟶ X_{/T}` is a representable thickening**, given that the
completion subfunctor is an fppf sheaf.

A scheme-valued point of `X_{/T}` has set of points inside `T`; base-changing it along the
reduction `X_red ⟶ X`, which is a representable thickening, gives an object of the site over
`X_red` whose set of points lies in `T`, and base-changing the closed subspace `Z` of `X_red`
along that gives a closed immersion of schemes which is surjective, because the set of points of
`Z` is exactly `T`. Pasting the two cartesian squares and cancelling the monomorphism
`X_{/T} ⟶ X` exhibits that composite as a represented base change of `Z ⟶ X_{/T}`. -/
theorem isRepresentableThickeningULift_reducedSubspaceToCompletionAlong
    (hi : IsReduction B S hS X (sheafOfAlgebraicSpace B S hS Xred₀ hXred₀) i)
    (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T)
    (hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Space.completionSubfunctorULift B S hS X.obj
        (ambientPointSet B S hS hXred₀ i T)).toFunctor) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (reducedSubspaceToCompletionAlong B S hS hXred₀ T hT (i := i)).hom := by
  classical
  let H : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
    (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}
  have _ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hZc : Space.IsClosedSubspace B S hS
      (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT) :=
    Space.isClosedSubspace_reducedClosedSubspace B S hS Xred₀ hXred₀ T hT
  have hZT : Set.range (Space.pointsMap B S hS
      (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).toFunctor
      (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).ι) = T :=
    Space.range_pointsMap_ι_reducedClosedSubspace B S hS Xred₀ hXred₀ T hT
  have hmono : Mono (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)) :=
    Space.mono_completionSheafULiftInclusion B S hS X _
  have hmonohom :
      Mono (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom := inferInstance
  have hdagger : Set.range (Space.pointsMapULift.{u + 1} B S hS
        (completionAlong i (liftedPointSet B S hS hXred₀ T)).obj
        (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom) ⊆
      ambientPointSet B S hS hXred₀ i T :=
    Space.range_pointsMapULift_completionSheafULiftInclusion_subset B S hS X _ hsh
  have hcι : H.map (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).ι ≫ i.hom =
      (reducedSubspaceToCompletionAlong B S hS hXred₀ T hT (i := i)).hom ≫
        (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom :=
    congrArg (fun k : reducedSubspaceSheaf B S hS hXred₀ T hT ⟶ X => k.hom)
      (reducedSubspaceToCompletionAlong_comp B S hS hXred₀ T hT (i := i)).symm
  apply MorphismProperty.relative.of_exists
  intro a g
  obtain ⟨a', snd₁, fst₁, sq₁⟩ :=
    hi.representable (g ≫ (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom)
  have hth₁ := hi.thickening
    (g ≫ (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom) fst₁ snd₁ sq₁
  obtain ⟨ψ, hψ⟩ := H.map_surjective fst₁
  have hψ' : Functor.whiskerRight ψ uliftFunctor.{u + 1} = fst₁ := hψ
  -- the chart `a'` of the reduction has its set of points inside `T`
  have hsq : ∀ pt : Space.pointsULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj a'),
      Space.pointsMapULift.{u + 1} B S hS _ i.hom
          (Space.pointsMapULift.{u + 1} B S hS _ fst₁ pt) =
        Space.pointsMapULift.{u + 1} B S hS _
          (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom
          (Space.pointsMapULift.{u + 1} B S hS _ g
            (Space.pointsMapULift.{u + 1} B S hS _ (uliftYoneda.{u + 1}.map snd₁) pt)) :=
    fun pt => by
      simpa only [Space.pointsMapULift_comp, Function.comp_apply] using
        congrFun (congrArg (Space.pointsMapULift.{u + 1} B S hS
          (uliftYoneda.{u + 1}.obj a')) sq₁.w) pt
  have hrange : Set.range (Space.pointsMap B S hS (yoneda.obj a') ψ) ⊆ T := by
    rintro _ ⟨q, rfl⟩
    refine (Space.pointsEquivPointsULift B S hS Xred₀).injective.mem_set_image.1
      (hi.bijective_pointsMapULift.1.mem_set_image.1 ?_)
    rw [Space.pointsEquivPointsULift_pointsMap, hψ']
    exact hdagger ⟨Space.pointsMapULift.{u + 1} B S hS _ g
      (Space.pointsMapULift.{u + 1} B S hS _ (uliftYoneda.{u + 1}.map snd₁)
        (Space.pointsEquivPointsULift B S hS (yoneda.obj a') q)),
      (hsq (Space.pointsEquivPointsULift B S hS (yoneda.obj a') q)).symm⟩
  -- base change the closed subspace `Z` along that chart
  obtain ⟨b, snd₂, fst₂, sq₂⟩ := hZc.2.1 ψ
  have hci := hZc.2.2 ψ fst₂ snd₂ sq₂
  have hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map snd₂) := by
    rw [← Space.surjective_pointsMap_yoneda_iff B S hS snd₂]
    intro pa
    have hmem : Space.pointsMap B S hS (yoneda.obj a') ψ pa ∈
        Set.range (Space.pointsMap B S hS
          (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).toFunctor
          (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).ι) := by
      rw [hZT]
      exact hrange ⟨pa, rfl⟩
    obtain ⟨pz, hpz⟩ := hmem
    obtain ⟨v, -, hv⟩ := Space.exists_point_of_isPullback_presheaf B S hS sq₂ pz pa hpz
    exact ⟨v, hv⟩
  -- transport the second square to the value universe of the formal algebraic spaces and paste
  have sq₂' : IsPullback (H.map fst₂) (uliftYoneda.{u + 1}.map snd₂)
      (H.map (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).ι) fst₁ := by
    rw [← hψ]
    exact sq₂.map H
  have sqpaste : IsPullback (H.map fst₂) (uliftYoneda.{u + 1}.map (snd₂ ≫ snd₁))
      (H.map (Space.reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).ι ≫ i.hom)
      (g ≫ (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom) := by
    rw [Functor.map_comp]
    exact sq₂'.paste_vert sq₁
  refine ⟨b, H.map fst₂, snd₂ ≫ snd₁,
    isPullback_of_comp_mono
      (completionAlongInclusion i (liftedPointSet B S hS hXred₀ T)).hom
      (by rwa [← hcι]), ?_, ?_⟩
  · rw [Functor.map_comp]
    have h1 : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd₂) := hci
    have h2 : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map snd₁) := hth₁.1
    infer_instance
  · rw [Functor.map_comp]
    intro z
    obtain ⟨y, hy⟩ := hth₁.2 z
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by rw [Scheme.Hom.comp_apply, hx, hy]⟩

/-! ### The reduction of the completion -/

/-- **Stacks 0GVU.** Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal
algebraic space over `S` with reduction `i : X_red ⟶ X`, and let `T ⊆ |X_red|` be a closed
subset. The reduction of the completion `X_{/T}` of `X` along `T` is the reduced induced closed
subspace `Z` of `X_red` corresponding to `T`: the canonical morphism `Z ⟶ X_{/T}` exhibits `Z`
as the reduction of the completion.

The conclusion contains the mapping property: every morphism to `X_{/T}` from a reduced
algebraic space over `S` factors uniquely through `Z`. -/
@[stacks 0GVU "with the reduction of `X` written as the universe lift of an algebraic space \
over `S`, the form in which the reduced induced closed subspace of Stacks 03IQ is available; \
that costs no generality, by `Space.exists_uliftFunctor_iso_of_isAlgebraicSpaceULift`",
  ega "I 10.8.6" "more general"]
theorem isReduction_completionAlong (_hX : IsFormalAlgebraicSpace B S hS X)
    (hi : IsReduction B S hS X (sheafOfAlgebraicSpace B S hS Xred₀ hXred₀) i)
    (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T) :
    IsReduction B S hS (completionAlong i (liftedPointSet B S hS hXred₀ T))
      (reducedSubspaceSheaf B S hS hXred₀ T hT)
      (reducedSubspaceToCompletionAlong B S hS hXred₀ T hT) :=
  isReduction_of_isRepresentableThickening B S hS _
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS _).mpr
      (Space.isClosedSubspace_reducedClosedSubspace B S hS Xred₀ hXred₀ T hT).1)
    (hasEtaleLocalPropertyULift_comp_uliftFunctor B S hS _
      (Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS Xred₀ hXred₀ T hT))
    (isRepresentableThickeningULift_reducedSubspaceToCompletionAlong B S hS hXred₀ hi T hT
      (Space.isSheaf_completionSubfunctorULift B S hS X _))

/-- **Stacks 0GVU, as a canonical identification.** Any reduction of the completion `X_{/T}` is
uniquely isomorphic, over `X_{/T}`, to the reduced induced closed subspace `Z` of `X_red` on `T`.

Two reductions of one fppf sheaf have the same mapping property, so each factors through the
other and the two factorizations are mutually inverse. -/
theorem existsUnique_iso_reducedSubspaceSheaf (hX : IsFormalAlgebraicSpace B S hS X)
    (hi : IsReduction B S hS X (sheafOfAlgebraicSpace B S hS Xred₀ hXred₀) i)
    (T : Set (Space.points B S hS Xred₀)) (hT : IsClosed T)
    (hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Space.completionSubfunctorULift B S hS X.obj
        (ambientPointSet B S hS hXred₀ i T)).toFunctor)
    {C : FppfSheaf B S hS} {r : C ⟶ completionAlong i (liftedPointSet B S hS hXred₀ T)}
    (hr : IsReduction B S hS (completionAlong i (liftedPointSet B S hS hXred₀ T)) C r) :
    ∃! e : C ≅ reducedSubspaceSheaf B S hS hXred₀ T hT,
      e.hom ≫ reducedSubspaceToCompletionAlong B S hS hXred₀ T hT = r := by
  -- `hsh` is redundant: `isReduction_completionAlong` now proves the sheaf condition itself.
  have _ := hsh
  have hZ := isReduction_completionAlong B S hS hXred₀ hX hi T hT
  obtain ⟨e, he, heuniq⟩ := hZ.universal C hr.algebraic hr.reduced r
  obtain ⟨d, hd, -⟩ := hr.universal _ hZ.algebraic hZ.reduced
    (reducedSubspaceToCompletionAlong B S hS hXred₀ T hT)
  have key : ∀ {P Q : FppfSheaf B S hS}
      {p : P ⟶ completionAlong i (liftedPointSet B S hS hXred₀ T)}
      {q : Q ⟶ completionAlong i (liftedPointSet B S hS hXred₀ T)},
      IsReduction B S hS _ P p → ∀ (a : P ⟶ Q) (b : Q ⟶ P), a ≫ q = p → b ≫ p = q →
        a ≫ b = 𝟙 P := by
    intro P Q p q hP a b ha hb
    obtain ⟨z, -, hz⟩ := hP.universal P hP.algebraic hP.reduced p
    rw [hz (a ≫ b) (by simp [hb, ha]), hz (𝟙 _) (Category.id_comp _)]
  exact ⟨⟨e, d, key hr e d he hd, key hZ d e hd he⟩, he, fun f hf => Iso.ext (heuniq f.hom hf)⟩

end FormalSpace

end AlgebraicGeometry

end
