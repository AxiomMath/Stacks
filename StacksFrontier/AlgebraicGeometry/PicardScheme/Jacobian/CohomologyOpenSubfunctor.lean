module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.OpenSubfunctor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree

/-!
# The open subfunctor of Stacks 0B9V, on the degree-zero rigidified Picard functor

Let `f : X ⟶ S` be flat, proper and locally of finite presentation with a section `σ`, and fix a
Picard class `θ` of `X`. For an `S`-scheme `T` and a rigidified class `x` of `X_T`, consider the
class `x + pr_X^* θ` of `X_T`. The classes `x` for which `Rf_{T,*}` of (a representative of)
`x + pr_X^* θ` is an invertible module placed in degree `0` form an *open* subfunctor of the
rigidified Picard functor and of its degree-zero part.

With `θ = 0` this is [Stacks, Tag 0B9V]. With `θ` of degree `g` it is the translate of the
`0B9V` locus into `Pic⁰`, which is the chart to which the group-scheme criterion
([Stacks, Tag 0B9Q]) is applied: on a curve of genus `g`, a rigidified class of degree zero lies
in it exactly when its translate by `θ` is the class of a degree-`g` divisor `D` with
`h⁰(𝒪(D)) = 1`, `h¹(𝒪(D)) = 0` on every fibre.

Openness is [Stacks, Tag 0B9S] in degree `0` and rank `1`
(`exists_opens_factorsThrough_iff_invertible_of_baseChange`), which is stated given the two halves
of [Stacks, Tag 0B91]; so are the results here.

## Main definitions

* `Stacks.RigidifiedPicard.IsCohomologyClass` — the condition on a class.
* `Stacks.RigidifiedPicard.cohomologySubfunctorZero` — the subfunctor of `Pic⁰_{X/S,σ}`.

## Main results

* `Stacks.RigidifiedPicard.exists_opens_isCohomologyClass_iff` — openness.
* `Stacks.RigidifiedPicard.isOpenSubfunctor_cohomologySubfunctorZero` and
  `Stacks.RigidifiedPicard.isOpenImmersion_presheaf_cohomologySubfunctorZero` — the subfunctor is
  open, hence representable by open immersions.

## References

* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 0B9S](https://stacks.math.columbia.edu/tag/0B9S)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The pullback of the chosen representative of a Picard class is isomorphic to the chosen
representative of the pulled-back class. -/
theorem nonempty_iso_pullback_picardRepresentative {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    (c : Stacks.Picard.ofScheme Z) :
    Nonempty ((Scheme.Modules.pullback h).obj (Stacks.Picard.picardRepresentative _ c).obj ≅
      (Stacks.Picard.picardRepresentative _ (Stacks.Picard.schemePullbackClass h c)).obj) := by
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _
    (Stacks.RingedSpace.modulePullback_isInvertible_of h.toLRSHom.toShHom _
      (Stacks.Picard.picardRepresentative Z.toRingedSpace c).property)
    (Stacks.Picard.picardRepresentative _ _).property).1 ?_
  rw [← Stacks.Picard.pullbackClass_classOf h.toLRSHom.toShHom _
    (Stacks.Picard.picardRepresentative Z.toRingedSpace c).property,
    Stacks.Picard.classOf_picardRepresentative, Stacks.Picard.classOf_picardRepresentative]

/-- **The condition of [Stacks, Tag 0B9V], translated by `θ`**: `Rf_{T,*}` of the representative
of `c + pr_X^* θ` is an invertible module placed in degree `0`. -/
def IsCohomologyClass (θ : Stacks.Picard.ofScheme X) (T : Over S)
    (c : Stacks.Picard.ofScheme (bc f T)) : Prop :=
  HasDerivedPushforwardRank (bcProj f T) (Stacks.Picard.picardRepresentative _
    (c + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ)).obj 0 1

/-- The pullback along `bcMap f g` of a class `c` of `X_T` satisfies the condition on `X_{T'}`
exactly when `Rf_{T',*}` of the pullback of the representative of `c + pr_X^* θ` is an invertible
module placed in degree `0`. -/
theorem isCohomologyClass_bcMap_iff (θ : Stacks.Picard.ofScheme X) {T T' : Over S}
    (g : T' ⟶ T) (c : Stacks.Picard.ofScheme (bc f T)) :
    IsCohomologyClass f θ T' (Stacks.Picard.schemePullbackClass (bcMap f g) c) ↔
      HasDerivedPushforwardRank (bcProj f T') ((Scheme.Modules.pullback (bcMap f g)).obj
        (Stacks.Picard.picardRepresentative _
          (c + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ)).obj) 0 1 := by
  obtain ⟨e⟩ := nonempty_iso_pullback_picardRepresentative (bcMap f g)
    (c + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ)
  have hcl : Stacks.Picard.schemePullbackClass (bcMap f g)
      (c + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ) =
      Stacks.Picard.schemePullbackClass (bcMap f g) c +
        Stacks.Picard.schemePullbackClass (pullback.fst f T'.hom) θ := by
    rw [Stacks.Picard.schemePullbackClass_add, Stacks.Picard.schemePullbackClass_comp, bcMap_fst]
  rw [hasDerivedPushforwardRank_congr e, IsCohomologyClass, hcl]

variable [Flat f] [LocallyOfFinitePresentation f] [IsProper f]

/-- The base change `X_T ⟶ T` of a flat morphism `f` is flat. -/
instance flat_bcProj (T : Over S) : Flat (bcProj f T) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback f T.hom) inferInstance

omit [Flat f] in
/-- The base change `X_T ⟶ T` of `f` is of finite presentation. -/
theorem finitePresentation_bcProj (T : Over S) : FinitePresentation (bcProj f T) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Openness of the condition of [Stacks, Tag 0B9V]**, given [Stacks, Tag 0B91]: for every
class `c` of `X_T` there is an open `U ⊆ T` such that for every morphism of `S`-schemes
`g : T' ⟶ T` the pulled-back class satisfies the condition exactly when `g` maps into `U`. -/
theorem exists_opens_isCohomologyClass_iff (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X) (T : Over S)
    (c : Stacks.Picard.ofScheme (bc f T)) :
    ∃ U : T.left.Opens, ∀ (T' : Over S) (g : T' ⟶ T),
      IsCohomologyClass f θ T' (Stacks.Picard.schemePullbackClass (bcMap f g) c) ↔
        Set.range g.left ⊆ (U : Set T.left) := by
  obtain ⟨U, hU⟩ := exists_opens_factorsThrough_iff_invertible_of_baseChange h0B91 hbc
    (bcProj f T) (finitePresentation_bcProj f T) _ (Stacks.Picard.picardRepresentative _
      (c + Stacks.Picard.schemePullbackClass (pullback.fst f T.hom) θ)).property
  refine ⟨U, fun T' g => ?_⟩
  rw [isCohomologyClass_bcMap_iff, ← hU g.left (bcProj f T') (bcMap f g)
    (bcMap_isPullback_proj f g)]
  constructor
  · rintro ⟨h, hh⟩
    rw [← hh, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (Set.image_subset_range _ _).trans (by simp)
  · intro hr
    exact ⟨IsOpenImmersion.lift U.ι g.left (by simpa using hr), IsOpenImmersion.lift_fac _ _ _⟩

/-- A subfunctor cut out by the condition on a class `cls T x` of `X_T`, compatible with pullback
of classes, is open. -/
private theorem isOpenSubfunctor_of_isCohomologyClass (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X)
    {P : (Over S)ᵒᵖ ⥤ Type u} (F : Subfunctor P)
    (cls : ∀ T : Over S, P.obj (op T) → Stacks.Picard.ofScheme (bc f T))
    (hF : ∀ (T : Over S) (x : P.obj (op T)), x ∈ F.obj (op T) ↔ IsCohomologyClass f θ T (cls T x))
    (hcls : ∀ (T T' : Over S) (g : T' ⟶ T) (x : P.obj (op T)),
      cls T' (P.map g.op x) = Stacks.Picard.schemePullbackClass (bcMap f g) (cls T x)) :
    IsOpenSubfunctor F := by
  intro T x
  obtain ⟨U, hU⟩ := exists_opens_isCohomologyClass_iff f h0B91 hbc θ T (cls T x)
  exact ⟨U, fun T' g => by rw [hF, hcls, hU]⟩

section Full

variable (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

omit [Flat f] [LocallyOfFinitePresentation f] [IsProper f] in
/-- The image of a rigidified class under the map of `Pic_{X/S,σ}` induced by `g : T' ⟶ T` is
the pullback of the underlying Picard class along `bcMap f g`. -/
theorem functor_map_val {T T' : Over S} (g : T' ⟶ T)
    (x : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    smallEquiv _ (((Multiplicative.toAdd ((functor f σ hσ ⋙ forget GrpCat).map g.op x) :
        group f σ hσ T') : Stacks.Picard.smallOfScheme (bc f T'))) =
      Stacks.Picard.schemePullbackClass (bcMap f g)
        (smallEquiv _ ((Multiplicative.toAdd x : group f σ hσ T) :
          Stacks.Picard.smallOfScheme (bc f T))) :=
  smallEquiv_smallSchemePullbackClassHom _ _

/-- **The subfunctor `F ⊆ Pic_{X/S,σ}` of [Stacks, Tag 0B9V]**, translated by `θ` (the source's
`F` is `θ = 0`): the rigidified classes `ℒ` with `Rf_{T,*}(ℒ ⊗ pr_X^*θ)` an invertible module
in degree `0`. It is a subfunctor given [Stacks, Tag 0B91]. -/
def cohomologySubfunctor (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X) :
    Subfunctor (functor f σ hσ ⋙ forget GrpCat) where
  obj T := {x | IsCohomologyClass f θ T.unop (smallEquiv _ ((Multiplicative.toAdd x :
    group f σ hσ T.unop) : Stacks.Picard.smallOfScheme (bc f T.unop)))}
  map {T T'} g x hx := by
    obtain ⟨U, hU⟩ := exists_opens_isCohomologyClass_iff f h0B91 hbc θ T.unop
      (smallEquiv _ ((Multiplicative.toAdd x : group f σ hσ T.unop) :
        Stacks.Picard.smallOfScheme (bc f T.unop)))
    have hall : Set.range (Over.Hom.left (𝟙 T.unop)) ⊆ (U : Set T.unop.left) := by
      have h := hU T.unop (𝟙 _)
      rw [bcMap_id, Stacks.Picard.schemePullbackClass_id] at h
      exact h.1 hx
    change IsCohomologyClass f θ T'.unop _
    rw [show g = g.unop.op from rfl, functor_map_val, hU]
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact hall ⟨g.unop.left z, rfl⟩

/-- **[Stacks, Tag 0B9V], the openness half, translated by `θ`**: the subfunctor is open. -/
theorem isOpenSubfunctor_cohomologySubfunctor (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X) :
    IsOpenSubfunctor (cohomologySubfunctor f σ hσ h0B91 hbc θ) := by
  exact isOpenSubfunctor_of_isCohomologyClass f h0B91 hbc θ _ _ (fun _ _ => Iff.rfl)
    fun _ _ g x => functor_map_val f σ hσ g x

end Full

variable [LocallyOfFiniteType f] (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The condition read on an element of `Pic⁰_{X/S,σ}(T)`. -/
abbrev IsCohomologyClassZero (θ : Stacks.Picard.ofScheme X) (T : Over S)
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) : Prop :=
  IsCohomologyClass f θ T
    (smallEquiv _ (((Multiplicative.toAdd x : groupZero f hdim σ hσ T) : group f σ hσ T) :
      Stacks.Picard.smallOfScheme (bc f T)))

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The image of a class under the map of `Pic⁰_{X/S,σ}` induced by `g : T' ⟶ T` is the
pullback of the underlying Picard class along `bcMap f g`. -/
theorem functorZero_map_val {T T' : Over S} (g : T' ⟶ T)
    (x : (functorZero f hdim σ hσ ⋙ forget GrpCat).obj (op T)) :
    smallEquiv _ (((Multiplicative.toAdd ((functorZero f hdim σ hσ ⋙ forget GrpCat).map g.op x) :
        groupZero f hdim σ hσ T') : group f σ hσ T') : Stacks.Picard.smallOfScheme (bc f T')) =
      Stacks.Picard.schemePullbackClass (bcMap f g)
        (smallEquiv _ (((Multiplicative.toAdd x : groupZero f hdim σ hσ T) : group f σ hσ T) :
          Stacks.Picard.smallOfScheme (bc f T))) :=
  smallEquiv_smallSchemePullbackClassHom _ _

/-- **The subfunctor of `Pic⁰_{X/S,σ}` of classes satisfying the translated condition of
[Stacks, Tag 0B9V]**, given [Stacks, Tag 0B91]. -/
def cohomologySubfunctorZero (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X) :
    Subfunctor (functorZero f hdim σ hσ ⋙ forget GrpCat) where
  obj T := {x | IsCohomologyClassZero f hdim σ hσ θ T.unop x}
  map {T T'} g x hx := by
    obtain ⟨U, hU⟩ := exists_opens_isCohomologyClass_iff f h0B91 hbc θ T.unop
      (smallEquiv _ (((Multiplicative.toAdd x : groupZero f hdim σ hσ T.unop) :
        group f σ hσ T.unop) : Stacks.Picard.smallOfScheme (bc f T.unop)))
    have hall : Set.range (Over.Hom.left (𝟙 T.unop)) ⊆ (U : Set T.unop.left) := by
      have h := hU T.unop (𝟙 _)
      rw [bcMap_id, Stacks.Picard.schemePullbackClass_id] at h
      exact h.1 hx
    change IsCohomologyClass f θ T'.unop _
    rw [show g = g.unop.op from rfl, functorZero_map_val, hU]
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact hall ⟨g.unop.left z, rfl⟩

/-- **[Stacks, Tag 0B9V], translated into `Pic⁰`**: the subfunctor is open. -/
theorem isOpenSubfunctor_cohomologySubfunctorZero (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X) :
    IsOpenSubfunctor (cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ) := by
  exact isOpenSubfunctor_of_isCohomologyClass f h0B91 hbc θ _ _ (fun _ _ => Iff.rfl)
    fun _ _ g x => functorZero_map_val f hdim σ hσ g x

/-- The inclusion of the subfunctor into `Pic⁰_{X/S,σ}` is representable by open immersions,
in the form of the hypothesis `hopen` of [Stacks, Tag 0B9Q]. -/
theorem isOpenImmersion_presheaf_cohomologySubfunctorZero (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) (θ : Stacks.Picard.ofScheme X) :
    (IsOpenImmersion.over (X := S)).presheaf (cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ).ι :=
  (isOpenSubfunctor_cohomologySubfunctorZero f hdim σ hσ h0B91 hbc θ).isOpenImmersion_presheaf_ι

end Stacks.RigidifiedPicard

end
