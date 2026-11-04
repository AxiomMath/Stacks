module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesUnderComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite

/-!
# Local types of modules under restriction of scalars along an isomorphism of sheaves of rings

Two sheaves of rings on one site which are isomorphic, but not equal, carry categories of
modules which are not the same category, and a local condition proved for a module over one of
them says nothing *a priori* about the corresponding module over the other.  This file closes
that gap for the conditions of Stacks 03DE (6) and Stacks 03DL (1), (2), (3) and (6): a global
presentation, quasi-coherence, local freeness, finite local freeness and local generation by
sections are all carried by restriction of scalars along an isomorphism of sheaves of rings.

Both statements are instances of the restriction along a continuous and cocontinuous functor of
sites proved in `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite`, taken at
the *identity* functor of the site: `SheafOfModules.pushforward` along the identity functor is
restriction of scalars on the nose, and the identity functor of a site is continuous and
cocontinuous for any topology, as is the functor it induces on each slice.  Only one point needs
care, and it is why these two lines are worth a file: the change-of-scalars morphism which
`SheafOfModules.pushforward` consumes has type
`R' ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat J J).obj R`, which is *definitionally* but not
syntactically `R' ⟶ R`, so an `IsIso` instance on the isomorphism is not found by instance
synthesis at the required type and has to be supplied.

## Main definitions

* `Stacks.SheafOfModules.overRingHom`: a morphism of sheaves of rings restricted to a slice of
  the site.
* `Stacks.SheafOfModules.restrictScalarsUnitIsoOfHom`: **restriction of scalars along an
  isomorphism of sheaves of rings carries the structure sheaf to the structure sheaf**, through
  the sections comparison `Stacks.SheafOfModules.restrictScalarsUnitSectionsEquiv`.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_restrictScalars_of_isIso`: **a global presentation
  is carried by restriction of scalars along an isomorphism of sheaves of rings.**
* `Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso`: **quasi-coherence is
  carried by restriction of scalars along an isomorphism of sheaves of rings.**
* `Stacks.SheafOfModules.isLocallyFreeOnSite_restrictScalars_of_isIso`,
  `.isFiniteLocallyFreeOnSite_restrictScalars_of_isIso` and
  `.isLocallyGeneratedBySectionsOnSite_restrictScalars_of_isIso`: **local freeness, finite local
  freeness and local generation by sections are carried by restriction of scalars along an
  isomorphism of sheaves of rings**, which are the clauses 03DL (1), (2) and (3).

## Implementation notes

The last three clauses do not go through the pushforward along the identity functor, as the
first two do; they go through the *slices*, since what each of them asks is a condition of
Stacks 03DE on the restriction of the module to each member of a covering.  Restriction of
scalars commutes with restriction to a slice on the nose — both leave the sections untouched —
so the comparison needed on a slice is restriction of scalars along
`Stacks.SheafOfModules.overRingHom`, which is again an isomorphism, hence an equivalence of
categories of modules (`Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`) and in
particular preserves the colimits the three conditions are stated by.  With
`Stacks.SheafOfModules.restrictScalarsUnitIsoOfHom` in hand, each clause is one application of
`Stacks.Sheaves.GlobalTypeComparison.isColimitCofanMap` or of
`SheafOfModules.GeneratingSections.map`.

The structure-sheaf comparison is built from the sections comparison rather than from
`Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit`, which is the same morphism:
inverting the latter asks for a functor reflecting isomorphisms, and the ones available on
sheaves of modules carry sheafification or sheaf-composition hypotheses that the three clauses
below do not otherwise need.

The colimit preservation which the two source statements take as a hypothesis is discharged here
from `Stacks.SheafOfModules.pushforward_preservesColimits` at the identity functor, whose
sheafification data at the universe `max u v r m` in which a global presentation is indexed is
automatic on any site.  For the quasi-coherence statement the same discharge is needed on each
slice, where the functor is `Over.post (𝟭 C) ⋙ Over.map f`; it is cocontinuous as a composite of
the slice of the identity functor with the restriction along an arrow of the site.

No `stacks` attribute appears here.  What is proved is the invariance of two of the eight clauses
of Stacks 03DL under a change of presentation of the sheaf of rings, which is a fragment of the
assertion of Stacks 03DM rather than that assertion; the file exists to be used by the clauses
themselves.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{r}}

/-- The change-of-scalars morphism of an isomorphism of sheaves of rings, read at the type which
`SheafOfModules.pushforward` along the identity functor consumes, is an isomorphism. -/
theorem isIso_pushforwardId_hom (e : R' ⟶ R) [IsIso e] :
    IsIso (show R' ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{r} J J).obj R from e) :=
  inferInstanceAs (IsIso e)

/-- **A global presentation is carried by restriction of scalars along an isomorphism of sheaves
of rings.**  Restriction of scalars is the pushforward along the identity functor of the site,
which is continuous and cocontinuous, so the restriction functor preserves the coproducts and the
cokernel of the presentation and carries the structure sheaf to the structure sheaf. -/
theorem hasGlobalPresentation_restrictScalars_of_isIso (e : R' ⟶ R) [IsIso e]
    (M : SheafOfModules.{m} R) (hM : M.HasGlobalPresentation) :
    ((SheafOfModules.restrictScalars.{m} e).obj M).HasGlobalPresentation := by
  have _ : HasSheafify J AddCommGrpCat.{max u v r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, u} J
  have _ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m, u, v} J
  have _ := isIso_pushforwardId_hom e
  have _ : PreservesColimitsOfSize.{max u v r m, max u v r m}
      (SheafOfModules.pushforward.{max u v r m} (F := 𝟭 C) (S := R') e) :=
    pushforward_preservesColimits (𝟭 C) _
  exact hasGlobalPresentation_pushforward (G := 𝟭 C) e M hM

/-- **Quasi-coherence is carried by restriction of scalars along an isomorphism of sheaves of
rings.**  This is the invariance of Stacks 03DL (6) under a change of presentation of the sheaf of
rings: the two categories of modules are not the same category, and the restriction of scalars
functor between them is the pushforward along the identity functor of the site. -/
theorem isQuasicoherentOnSite_restrictScalars_of_isIso (e : R' ⟶ R) [IsIso e]
    (M : SheafOfModules.{m} R) (hM : M.IsQuasicoherentOnSite) :
    ((SheafOfModules.restrictScalars.{m} e).obj M).IsQuasicoherentOnSite := by
  have _ := isIso_pushforwardId_hom e
  refine isQuasicoherentOnSite_pushforward (𝟭 C) e ?_ M hM
  intro X Y f
  have h (W : C) : HasSheafify (J.over W) AddCommGrpCat.{max u v r m} ∧
      (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
    ⟨GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, max u v} (J.over W),
      AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m,
        max u v, v} (J.over W)⟩
  have _ := (h X).1
  have _ := (h X).2
  have _ := (h Y).1
  have _ := (h Y).2
  have _ : (Over.post (X := X) (𝟭 C) ⋙ Over.map f).IsCocontinuous (J.over X) (J.over Y) :=
    CategoryTheory.isCocontinuous_comp _ _ (J.over X) (J.over ((𝟭 C).obj X))
  exact pushforward_preservesColimits _ _

/-! ### The local clauses, through the slices -/

/-- **Restriction of scalars along an isomorphism of sheaves of rings, on the sections over one
object.**  The underlying map is the isomorphism itself; it is linear over the source sheaf of
rings because the scalar action on the restriction of the structure sheaf is multiplication after
applying the isomorphism. -/
noncomputable def restrictScalarsUnitSectionsEquiv (e : R' ⟶ R) [IsIso e] (U : Cᵒᵖ) :
    (SheafOfModules.unit R').val.obj U ≃ₗ[R'.obj.obj U]
      ((SheafOfModules.restrictScalars.{r} e).obj (SheafOfModules.unit R)).val.obj U :=
  letI ε : R'.obj ≅ R.obj := (sheafToPresheaf J RingCat.{r}).mapIso (asIso e)
  { toFun := (ε.hom.app U).hom
    map_add' := fun _ _ ↦ map_add _ _ _
    map_smul' a x := (ε.hom.app U).hom.map_mul a x
    invFun := (ε.inv.app U).hom
    left_inv x := congrArg (fun g : R'.obj.obj U ⟶ R'.obj.obj U ↦ g.hom x) (ε.hom_inv_id_app U)
    right_inv x := congrArg (fun g : R.obj.obj U ⟶ R.obj.obj U ↦ g.hom x) (ε.inv_hom_id_app U) }

/-- **Restriction of scalars along an isomorphism of sheaves of rings carries the structure sheaf
to the structure sheaf.**  On sections it is
`Stacks.SheafOfModules.restrictScalarsUnitSectionsEquiv`, and the naturality to be checked is the
equality of the two readings of the unit section, both of which are `1`. -/
noncomputable def restrictScalarsUnitIsoOfHom (e : R' ⟶ R) [IsIso e] :
    (SheafOfModules.restrictScalars.{r} e).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit R' :=
  letI α : SheafOfModules.unit R' ≅
      (SheafOfModules.restrictScalars.{r} e).obj (SheafOfModules.unit R) :=
    (SheafOfModules.fullyFaithfulForget R').preimageIso
      (PresheafOfModules.isoMk (fun U ↦ (restrictScalarsUnitSectionsEquiv e U).toModuleIso) (by
        intro U V f
        ext
        change (RingCat.Hom.hom (e.hom.app V)) ((RingCat.Hom.hom (R'.obj.map f)) 1) =
          (RingCat.Hom.hom (R.obj.map f)) ((RingCat.Hom.hom (e.hom.app U)) 1)
        rw [map_one, map_one, map_one, map_one]))
  α.symm

/-- A morphism of sheaves of rings restricted to the slice of the site at an object: the image of
the morphism under the pullback of sheaves to that slice. -/
noncomputable abbrev overRingHom (e : R' ⟶ R) (V : C) : R'.over V ⟶ R.over V :=
  (J.overPullback RingCat.{r} V).map e

/-- The restriction of an isomorphism of sheaves of rings to a slice of the site is again an
isomorphism. -/
instance isIso_overRingHom (e : R' ⟶ R) [IsIso e] (V : C) : IsIso (overRingHom e V) :=
  Functor.map_isIso _ e

/-- Restriction of scalars along the restriction of an isomorphism of sheaves of rings to a slice
is an equivalence of the categories of sheaves of modules on that slice, hence preserves all
colimits. -/
instance isEquivalence_restrictScalars_overRingHom (e : R' ⟶ R) [IsIso e] (V : C) :
    (SheafOfModules.restrictScalars.{r} (overRingHom e V)).IsEquivalence :=
  (Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso (overRingHom e V))).isEquivalence_inverse

/-- **Local freeness is carried by restriction of scalars along an isomorphism of sheaves of
rings.**  This is the invariance of Stacks 03DL (1) under a change of presentation of the sheaf of
rings.  The covering of the hypothesis is kept, and on each of its members the family of global
sections exhibiting the restricted module as a coproduct of copies of the structure sheaf is
carried across by restriction of scalars on that slice. -/
theorem isLocallyFreeOnSite_restrictScalars_of_isIso (e : R' ⟶ R) [IsIso e]
    (M : SheafOfModules.{r} R) (hM : M.IsLocallyFreeOnSite) :
    ((SheafOfModules.restrictScalars.{r} e).obj M).IsLocallyFreeOnSite := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := hM U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  exact (Stacks.Sheaves.GlobalTypeComparison.isFree_iff
    (SheafOfModules.restrictScalars.{r} (overRingHom e (V i)))
    (restrictScalarsUnitIsoOfHom (overRingHom e (V i))) _).1 (hV i)

/-- **Finite local freeness is carried by restriction of scalars along an isomorphism of sheaves
of rings.**  This is the invariance of Stacks 03DL (2) under a change of presentation of the sheaf
of rings; the index type of the cofan is unchanged, so the rank on each member of the covering is
unchanged as well. -/
theorem isFiniteLocallyFreeOnSite_restrictScalars_of_isIso (e : R' ⟶ R) [IsIso e]
    (M : SheafOfModules.{r} R) (hM : M.IsFiniteLocallyFreeOnSite) :
    ((SheafOfModules.restrictScalars.{r} e).obj M).IsFiniteLocallyFreeOnSite := by
  intro U
  obtain ⟨I, V, f, hf, hV⟩ := hM U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  exact (Stacks.Sheaves.GlobalTypeComparison.isFiniteFree_iff
    (SheafOfModules.restrictScalars.{r} (overRingHom e (V i)))
    (restrictScalarsUnitIsoOfHom (overRingHom e (V i))) _).1 (hV i)

/-- **Local generation by sections is carried by restriction of scalars along an isomorphism of
sheaves of rings.**  This is the invariance of Stacks 03DL (3) under a change of presentation of
the sheaf of rings.  The covering of the hypothesis is kept, and on each of its members the
generating family of global sections is carried across by
`SheafOfModules.GeneratingSections.map`, which leaves the index type unchanged. -/
theorem isLocallyGeneratedBySectionsOnSite_restrictScalars_of_isIso
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]
    (e : R' ⟶ R) [IsIso e]
    (M : SheafOfModules.{r} R) (hM : M.IsLocallyGeneratedBySectionsOnSite) :
    ((SheafOfModules.restrictScalars.{r} e).obj M).IsLocallyGeneratedBySectionsOnSite := by
  let _ : ∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{r} :=
    fun _ ↦ AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  intro U
  obtain ⟨I, V, hcov, hV⟩ := hM U
  refine ⟨I, V, hcov, fun i ↦ ?_⟩
  obtain ⟨σ⟩ := hV i
  exact ⟨σ.map (SheafOfModules.restrictScalars.{r} (overRingHom e (V i).left))
    (restrictScalarsUnitIsoOfHom (overRingHom e (V i).left)).symm⟩

end Stacks.SheafOfModules

end
