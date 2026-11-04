module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Change of residue field

Changing the residue field `k` of the base category along a field extension.
This file constructs the comparison functor, and shows it carries predeformation categories and
their isomorphism classes across.

## Main definitions

* `ChangeOfFieldsSituation` packages the finite tower `Λ → k → l`.
* `ComparisonFunctor` specifies the functor `B ↦ B ×_l k`.
* `comparisonFunctor` constructs this canonical functor.
* `changeOfFieldsProjection` is the associated projection over
  `𝒞_{Λ,l}`.
* `changeOfFieldsFiberInclusion` sends an object of the original fiber
  over `B ×_l k` to the canonical object in the changed fiber over `B`.
* `comparisonFunctor` is the comparison functor `B ↦ B ×_l k`, together
  with its canonical algebra and residue-field structures and its action on morphisms.
* `changeOfFieldsIsoClassMap` is the map induced
  by the canonical inclusion of fibers.
* `changeOfFieldsIsoClassEquiv` is the resulting
  canonical equivalence of sets of isomorphism classes.

## Main results

* `changeOfFieldsProjection_isCofiberedInGroupoids` says that base change
  preserves categories cofibered in groupoids.
* `changeOfFieldsFiberEquivalence` identifies its fiber over `B` with the
  original fiber over `B ×_l k`.
* `changeOfFieldsIsoClassMap_bijective` identifies
  the isomorphism classes in each changed fiber with those in the old fiber.
* `changeOfFieldsIsoClassMap_naturality` states
  that this identification is natural in the Artinian algebra.
* `changeOfFieldsProjection_isPredeformationCategory`
  states that the projection of the changed category is a predeformation category.

## Implementation notes

### Change of residue field

The pullback ring is Mathlib's `RingHom.pullback`. The object and morphism formulas for
the comparison functor are recorded in `ComparisonFunctor`. The source's situation
itself constructs this functor; Tag 07W9 separately labels its displayed equation.
The associated category is modeled by the categorical pullback of the original
projection and the comparison functor. The displayed equality of fiber categories
is represented by an equivalence whose inverse functor is the specified canonical
inclusion.

### Comparison functor for change of residue field

Tag 07W8 already states the comparison construction as part of its standing situation.
This statement registers that same construction for the displayed equation, rather than
introducing a second, independently chosen functor.

### Isomorphism classes after change of residue field

The fiberwise identification is induced by the canonical fiber inclusion of
07W8, rather than an unspecified bijection. It is stated for an arbitrary
universe of objects of the total category. Naturality is stated on classes of
representatives, which generate the quotient. This avoids imposing a common
universe on the two set-valued functors. A cofibered category is viewed as
fibered on opposite categories to formulate its functorial class maps.

### Predeformation categories under change of residue field

The source writes the changed category as `𝓕_{l/k}`. Here it is the categorical
pullback projection of Tag 07W8. The carrier universe of its Artinian algebra
category is chosen to contain the universe of `l`, so that the residue-field
object used in Tag 06GS exists in that category.

## References

* [Stacks Project, Tag 07W8](https://stacks.math.columbia.edu/tag/07W8)
* [Stacks Project, Tag 07W9](https://stacks.math.columbia.edu/tag/07W9)
* [Stacks Project, Tag 07WA](https://stacks.math.columbia.edu/tag/07WA)
-/

@[expose] public section

namespace Deformation

/-! ### Change of residue field -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open IsLocalRing
universe u v w x y z

/-- **Stacks Project, Tag 07W8.** The standing finite tower of fields over the
Noetherian base ring `Λ`. -/
@[stacks 07W8 "the standing situation"]
public structure ChangeOfFieldsSituation where
  /-- The Noetherian base ring. -/
  Λ : Type u
  /-- The original residue field. -/
  k : Type v
  /-- The extended residue field. -/
  l : Type w
  [commRingΛ : CommRing Λ]
  [fieldK : Field k]
  [fieldL : Field l]
  [algebraΛK : Algebra Λ k]
  [algebraKL : Algebra k l]
  [algebraΛL : Algebra Λ l]
  [scalarTower : IsScalarTower Λ k l]
  [noetherianΛ : IsNoetherianRing Λ]
  [finiteΛK : Module.Finite Λ k]
  [finiteKL : Module.Finite k l]

attribute [instance] ChangeOfFieldsSituation.commRingΛ ChangeOfFieldsSituation.fieldK
  ChangeOfFieldsSituation.fieldL ChangeOfFieldsSituation.algebraΛK
  ChangeOfFieldsSituation.algebraKL ChangeOfFieldsSituation.algebraΛL
  ChangeOfFieldsSituation.scalarTower ChangeOfFieldsSituation.noetherianΛ
  ChangeOfFieldsSituation.finiteΛK ChangeOfFieldsSituation.finiteKL

/-- The residue homomorphism from an object with residue field `l` to `l`. -/
public def residueMap (S : ChangeOfFieldsSituation.{u, v, w})
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) : B →+* S.l :=
  B.residueEquiv.toAlgHom.toRingHom.comp (residue B)

public lemma finiteLength_base_of_artinianObj
    (S : ChangeOfFieldsSituation.{u, v, w})
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    IsFiniteLength S.Λ B := by
  let : Module.Finite S.Λ S.l := Module.Finite.trans S.k S.l
  let old : Module S.Λ B := inferInstance
  let comp : Module S.Λ B := Module.compHom B (algebraMap S.Λ B)
  have hcomp : @IsFiniteLength S.Λ _ B _ comp := by
    rw [← Module.length_ne_top_iff,
      ← finrank_residueImageField_mul_length_eq_length S.Λ S.l B B B.residueEquiv]
    have hB : Module.length B B ≠ ⊤ :=
      (@Module.length_ne_top_iff B B _ _ _).mpr
        ((isArtinianRing_iff_isFiniteLength B).mp inferInstance)
    rw [← ENat.natCast_toNat hB, ← ENat.natCast_mul]
    exact ENat.natCast_ne_top _
  let f : @LinearMap S.Λ S.Λ _ _ (RingHom.id S.Λ) B B _ _ old comp :=
    @LinearMap.mk S.Λ S.Λ _ _ (RingHom.id S.Λ) B B _ _ old comp (AddHom.id B) (by
      intro r x
      change old.toSMul.smul r x = comp.toSMul.smul r x
      exact Algebra.smul_def r x)
  exact @IsFiniteLength.of_injective S.Λ _ B B _ old _ comp f hcomp fun _ _ h ↦ by
    simpa [f] using h

public abbrev ChangeOfFieldsPullbackData
    (S : ChangeOfFieldsSituation.{u, v, w})
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :=
  Σ object : ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k,
    { pullbackEquiv : object ≃+* RingHom.pullback (residueMap S B) (algebraMap S.k S.l) //
      ∀ a : object, object.residueEquiv (residue object a) = (pullbackEquiv a).val.2 }

public abbrev ChangeOfFieldsPullbackData.object
    {S : ChangeOfFieldsSituation.{u, v, w}}
    {B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (d : ChangeOfFieldsPullbackData S B) := d.1

public abbrev ChangeOfFieldsPullbackData.pullbackEquiv
    {S : ChangeOfFieldsSituation.{u, v, w}}
    {B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (d : ChangeOfFieldsPullbackData S B) := d.2.1

public noncomputable def changeOfFieldsPullbackData
    (S : ChangeOfFieldsSituation.{u, v, w})
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    ChangeOfFieldsPullbackData S B := by
  classical
  let f : B →ₐ[S.Λ] S.l :=
    { toRingHom := residueMap S B
      commutes' := by
        intro a
        calc
          B.residueEquiv (residue B (algebraMap S.Λ B a)) =
              B.residueEquiv (algebraMap B (ResidueField B) (algebraMap S.Λ B a)) := by
                rw [ResidueField.algebraMap_eq]
          _ = B.residueEquiv (algebraMap S.Λ (ResidueField B) a) := by
                rw [IsScalarTower.algebraMap_apply S.Λ B (ResidueField B) a]
          _ = algebraMap S.Λ S.l a := B.residueEquiv.commutes a }
  let g : S.k →ₐ[S.Λ] S.l :=
    { toRingHom := algebraMap S.k S.l
      commutes' := fun a ↦ (IsScalarTower.algebraMap_apply S.Λ S.k S.l a).symm }
  let R := AlgHom.pullback f g
  letI : IsLocalHom g.toRingHom := ⟨fun a ha ↦
    isUnit_iff_ne_zero.mpr fun ha0 ↦ (isUnit_iff_ne_zero.mp ha) (by simp [ha0])⟩
  letI : IsLocalRing R := AlgHom.isLocalRing_pullback f g
  letI : IsLocalHom B.residueEquiv.toAlgHom.toRingHom := ⟨fun a ha ↦
    isUnit_iff_ne_zero.mpr fun ha0 ↦ (isUnit_iff_ne_zero.mp ha) (by simp [ha0])⟩
  letI : IsLocalHom f.toRingHom := by
    change IsLocalHom (B.residueEquiv.toAlgHom.toRingHom.comp (residue B))
    exact RingHom.isLocalHom_comp _ _
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (R := B) (B.residueEquiv.symm y)
    exact ⟨b, by simp [f, residueMap, hb]⟩
  letI : IsLocalHom (AlgHom.pullbackSnd f g).toRingHom := by
    change IsLocalHom (RingHom.pullbackSnd f.toRingHom g.toRingHom)
    infer_instance
  let qbar : IsLocalRing.ResidueField R →+* S.k :=
    IsLocalRing.ResidueField.lift (AlgHom.pullbackSnd f g).toRingHom
  have hqbar_surj : Function.Surjective qbar := by
    intro y
    obtain ⟨r, hr⟩ := AlgHom.surjective_pullbackSnd_of_surjective f g hf y
    exact ⟨residue R r, by
      change IsLocalRing.ResidueField.lift (AlgHom.pullbackSnd f g).toRingHom
        (residue R r) = y
      rw [IsLocalRing.ResidueField.lift_residue_apply]
      exact hr⟩
  let eRing : IsLocalRing.ResidueField R ≃+* S.k := RingEquiv.ofBijective qbar
    ⟨qbar.injective, hqbar_surj⟩
  let e : IsLocalRing.ResidueField R ≃ₐ[S.Λ] S.k :=
    { eRing with
      commutes' := by
        intro a
        change IsLocalRing.ResidueField.lift (AlgHom.pullbackSnd f g).toRingHom
          (residue R (algebraMap S.Λ R a)) = algebraMap S.Λ S.k a
        rw [IsLocalRing.ResidueField.lift_residue_apply]
        exact (AlgHom.pullbackSnd f g).commutes a }
  have hRlen : IsFiniteLength S.Λ R := by
    let fst : R →ₐ[S.Λ] B := AlgHom.pullbackFst f g
    have hfst : Function.Injective fst := fun a b hab ↦ Subtype.ext <| Prod.ext hab <|
      g.toRingHom.injective <| a.property.symm.trans <| (congrArg f hab).trans b.property
    exact IsFiniteLength.of_injective (finiteLength_base_of_artinianObj S B)
      (f := fst.toLinearMap) hfst
  haveI : IsArtinianRing R :=
    isArtinian_of_tower S.Λ (isFiniteLength_iff_isNoetherian_isArtinian.mp hRlen).2
  refine ⟨{ carrier := R, residueEquiv := e }, ⟨RingEquiv.refl _, ?_⟩⟩
  intro a
  change IsLocalRing.ResidueField.lift (AlgHom.pullbackSnd f g).toRingHom
    (residue R a) = (RingEquiv.refl R a).val.2
  rw [IsLocalRing.ResidueField.lift_residue_apply]
  rfl

public def comparisonPullbackAlgHom
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B C : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B ⟶ C) :
    (changeOfFieldsPullbackData S B).object →ₐ[S.Λ]
      (changeOfFieldsPullbackData S C).object := by
  let fB : B →ₐ[S.Λ] S.l :=
    { toRingHom := residueMap S B
      commutes' := by
        intro a
        calc
          B.residueEquiv (residue B (algebraMap S.Λ B a)) =
              B.residueEquiv (algebraMap B (ResidueField B) (algebraMap S.Λ B a)) := by
                rw [ResidueField.algebraMap_eq]
          _ = B.residueEquiv (algebraMap S.Λ (ResidueField B) a) := by
                rw [IsScalarTower.algebraMap_apply S.Λ B (ResidueField B) a]
          _ = algebraMap S.Λ S.l a := B.residueEquiv.commutes a }
  let g : S.k →ₐ[S.Λ] S.l :=
    { toRingHom := algebraMap S.k S.l
      commutes' := fun a ↦ (IsScalarTower.algebraMap_apply S.Λ S.k S.l a).symm }
  let fC : C →ₐ[S.Λ] S.l :=
    { toRingHom := residueMap S C
      commutes' := by
        intro a
        calc
          C.residueEquiv (residue C (algebraMap S.Λ C a)) =
              C.residueEquiv (algebraMap C (ResidueField C) (algebraMap S.Λ C a)) := by
                rw [ResidueField.algebraMap_eq]
          _ = C.residueEquiv (algebraMap S.Λ (ResidueField C) a) := by
                rw [IsScalarTower.algebraMap_apply S.Λ C (ResidueField C) a]
          _ = algebraMap S.Λ S.l a := C.residueEquiv.commutes a }
  let h₁ := f.hom.comp (AlgHom.pullbackFst fB g)
  let h₂ := AlgHom.pullbackSnd fB g
  exact AlgHom.codRestrict (AlgHom.prod h₁ h₂) (fC.pullback g) (by
    intro a
    change residueMap S C (f.hom a.val.1) = algebraMap S.k S.l a.val.2
    calc
      residueMap S C (f.hom a.val.1) =
          C.residueEquiv (residue C (f.hom a.val.1)) := rfl
      _ = B.residueEquiv (residue B a.val.1) := f.residue_comm _
      _ = residueMap S B a.val.1 := rfl
      _ = algebraMap S.k S.l a.val.2 := a.property)

public lemma comparisonPullbackAlgHom_fst
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B C : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B ⟶ C) (a : (changeOfFieldsPullbackData S B).object) :
    ((changeOfFieldsPullbackData S C).pullbackEquiv
      (comparisonPullbackAlgHom S f a)).val.1 =
        f.hom (((changeOfFieldsPullbackData S B).pullbackEquiv a).val.1) := rfl

public lemma comparisonPullbackAlgHom_snd
    (S : ChangeOfFieldsSituation.{u, v, w})
    {B C : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B ⟶ C) (a : (changeOfFieldsPullbackData S B).object) :
    ((changeOfFieldsPullbackData S C).pullbackEquiv
      (comparisonPullbackAlgHom S f a)).val.2 =
        ((changeOfFieldsPullbackData S B).pullbackEquiv a).val.2 := rfl
/-- The complete specification of the comparison functor `B ↦ B ×_l k`.

The ring equivalences specify its action on objects.  The last two fields specify its
action on morphisms, while `algebraMap_fst`, `algebraMap_snd`, and `residue_snd` ensure
that the `Λ`-algebra and chosen-residue-field structures are the canonical ones. -/
public structure ComparisonFunctor (S : ChangeOfFieldsSituation.{u, v, w}) where
  /-- The functor from Artinian local algebras with residue field `l` to those with
  residue field `k`. -/
  functor :
    ArtinianLocalAlgCat.{u, x, w} S.Λ S.l ⥤
      ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k
  /-- On underlying rings, the value at `B` is `B ×_l k`. -/
  pullbackEquiv (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    functor.obj B ≃+* RingHom.pullback (residueMap S B) (algebraMap S.k S.l)
  /-- The first component of the algebra map is the algebra map to `B`. -/
  algebraMap_fst (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) (a : S.Λ) :
    ((pullbackEquiv B) (algebraMap S.Λ (functor.obj B) a)).val.1 = algebraMap S.Λ B a
  /-- The second component of the algebra map is the algebra map to `k`. -/
  algebraMap_snd (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) (a : S.Λ) :
    ((pullbackEquiv B) (algebraMap S.Λ (functor.obj B) a)).val.2 = algebraMap S.Λ S.k a
  /-- The chosen residue map of the pullback is its second projection to `k`. -/
  residue_snd (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l)
      (a : functor.obj B) :
    (functor.obj B).residueEquiv (residue (functor.obj B) a) =
      ((pullbackEquiv B) a).val.2
  /-- On a morphism, the first pullback coordinate is the given morphism. -/
  map_fst {B C : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l} (f : B ⟶ C)
      (a : functor.obj B) :
    ((pullbackEquiv C) ((functor.map f).hom a)).val.1 =
      f.hom (((pullbackEquiv B) a).val.1)
  /-- On a morphism, the second pullback coordinate is unchanged. -/
  map_snd {B C : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l} (f : B ⟶ C)
      (a : functor.obj B) :
    ((pullbackEquiv C) ((functor.map f).hom a)).val.2 =
      ((pullbackEquiv B) a).val.2

/-- **Stacks Project, Tag 07W8.** The canonical comparison functor sending
`B` to `B ×_l k`, with its prescribed algebra, residue and morphism maps. -/
@[stacks 07W8 "the comparison functor"]
public noncomputable def comparisonFunctor
    (S : ChangeOfFieldsSituation.{u, v, w}) :
    ComparisonFunctor.{u, v, w, x} S := by
  classical
  let F :
      ArtinianLocalAlgCat.{u, x, w} S.Λ S.l ⥤
        ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k := by
    refine
      { obj := fun B ↦ (changeOfFieldsPullbackData S B).object
        map := fun {B C} f ↦ ?_
        map_id := ?_
        map_comp := ?_ }
    · let DB := changeOfFieldsPullbackData S B
      let DC := changeOfFieldsPullbackData S C
      let m := comparisonPullbackAlgHom S f
      refine
        { hom := m
          isLocal := ⟨fun a ha ↦ ?_⟩
          residue_comm := ?_ }
      · have htarget : IsUnit (DC.pullbackEquiv (m a)) := by
          simpa [m] using ha
        have hpair :=
          (RingHom.isUnit_pullback_mk_iff (residueMap S C) (algebraMap S.k S.l)
            (DC.pullbackEquiv (m a)).property).mp htarget
        have hfirst : IsUnit (f.hom ((DB.pullbackEquiv a).val.1)) := by
          have hfirst' := hpair.1
          change IsUnit ((DC.pullbackEquiv (m a)).val.1) at hfirst'
          have hcoord := comparisonPullbackAlgHom_fst S f a
          rw [hcoord] at hfirst'
          exact hfirst'
        have hsecond : IsUnit ((DB.pullbackEquiv a).val.2) := by
          have hsecond' := hpair.2
          change IsUnit ((DC.pullbackEquiv (m a)).val.2) at hsecond'
          have hcoord := comparisonPullbackAlgHom_snd S f a
          rw [hcoord] at hsecond'
          exact hsecond'
        have hsource :=
          (RingHom.isUnit_pullback_mk_iff (residueMap S B) (algebraMap S.k S.l)
            (DB.pullbackEquiv a).property).mpr
            ⟨f.isLocal.map_nonunit _ hfirst, hsecond⟩
        simpa [DB] using hsource
      · intro a
        calc
          DC.object.residueEquiv (residue DC.object (m a)) =
              (DC.pullbackEquiv (m a)).val.2 :=
            DC.2.2 (m a)
          _ = (DB.pullbackEquiv a).val.2 := comparisonPullbackAlgHom_snd S f a
          _ = DB.object.residueEquiv (residue DB.object a) := (DB.2.2 a).symm
    · intro B
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      apply Subtype.ext
      apply Prod.ext
      · change ((changeOfFieldsPullbackData S B).pullbackEquiv
          (comparisonPullbackAlgHom S (𝟙 B) a)).val.1 =
          ((changeOfFieldsPullbackData S B).pullbackEquiv
            (AlgHom.id S.Λ ((changeOfFieldsPullbackData S B).object) a)).val.1
        rw [comparisonPullbackAlgHom_fst]
        simp [ArtinianLocalAlgCat.id_hom]
      · change ((changeOfFieldsPullbackData S B).pullbackEquiv
          (comparisonPullbackAlgHom S (𝟙 B) a)).val.2 =
          ((changeOfFieldsPullbackData S B).pullbackEquiv
            (AlgHom.id S.Λ ((changeOfFieldsPullbackData S B).object) a)).val.2
        rw [comparisonPullbackAlgHom_snd]
        simp
    · intro B C D f g
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro a
      apply Subtype.ext
      apply Prod.ext
      · change ((changeOfFieldsPullbackData S D).pullbackEquiv
          (comparisonPullbackAlgHom S (f ≫ g) a)).val.1 =
          ((changeOfFieldsPullbackData S D).pullbackEquiv
            (comparisonPullbackAlgHom S g (comparisonPullbackAlgHom S f a))).val.1
        rw [comparisonPullbackAlgHom_fst, comparisonPullbackAlgHom_fst,
          comparisonPullbackAlgHom_fst]
        simp [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply]
      · change ((changeOfFieldsPullbackData S D).pullbackEquiv
          (comparisonPullbackAlgHom S (f ≫ g) a)).val.2 =
          ((changeOfFieldsPullbackData S D).pullbackEquiv
            (comparisonPullbackAlgHom S g (comparisonPullbackAlgHom S f a))).val.2
        rw [comparisonPullbackAlgHom_snd, comparisonPullbackAlgHom_snd,
          comparisonPullbackAlgHom_snd]
  refine
    { functor := F
      pullbackEquiv := fun B ↦ (changeOfFieldsPullbackData S B).pullbackEquiv
      algebraMap_fst := ?_
      algebraMap_snd := ?_
      residue_snd := ?_
      map_fst := ?_
      map_snd := ?_ }
  · intro B a
    rfl
  · intro B a
    rfl
  · intro B a
    exact (changeOfFieldsPullbackData S B).2.2 a
  · intro B C f a
    exact comparisonPullbackAlgHom_fst S f a
  · intro B C f a
    exact comparisonPullbackAlgHom_snd S f a

/-- The category obtained from `p : F ⟶ 𝒞_{Λ,k}` by change of residue field.
It is the categorical pullback of `p` along `B ↦ B ×_l k`. -/
public abbrev ChangeOfFieldsCategory (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k) :=
  CategoricalPullback p (comparisonFunctor S).functor

/-- **Stacks Project, Tag 07W8.** The projection
`p_{l/k} : F_{l/k} ⟶ 𝒞_{Λ,l}` associated to `p : F ⟶ 𝒞_{Λ,k}`. -/
@[stacks 07W8 "the associated projection"]
public def changeOfFieldsProjection (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k) :
    ChangeOfFieldsCategory S p ⥤
      ArtinianLocalAlgCat.{u, x, w} S.Λ S.l :=
  CategoricalPullback.π₂ p (comparisonFunctor S).functor

/-- The canonical functor from the old fiber over `B ×_l k` to the changed fiber
over `B`. It sends `a` to `(a.val, B, eqToIso a.property)` and acts on a fiber
morphism by its underlying morphism and the identity of `B`. -/
public def changeOfFieldsFiberInclusion
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    p.Fiber ((comparisonFunctor S).functor.obj B) ⥤
      (changeOfFieldsProjection S p).Fiber B where
  obj a := ⟨⟨a.val, B, eqToIso a.property⟩, rfl⟩
  map {a b} f := by
    let m :
        (⟨a.val, B, eqToIso a.property⟩ :
          CategoricalPullback p (comparisonFunctor S).functor) ⟶
        (⟨b.val, B, eqToIso b.property⟩ :
          CategoricalPullback p (comparisonFunctor S).functor) :=
      ⟨f.val, 𝟙 B, by
      have := f.property
      simpa using (IsHomLift.commSq p (𝟙 _) f.val).w⟩
    have h : (changeOfFieldsProjection S p).map m = 𝟙 B := rfl
    exact ⟨m, h ▸ IsHomLift.map (changeOfFieldsProjection S p) m⟩
  map_id a := by
    apply Subtype.ext
    apply CategoricalPullback.hom_ext <;> rfl
  map_comp f g := by
    apply Subtype.ext
    apply CategoricalPullback.hom_ext <;> rfl

/-- **Stacks Project, Tag 07W8.** The canonical fiber inclusion is an equivalence.
This fixes the identification of the changed fiber with the original fiber over
`B ×_l k`, rather than merely asserting existence of an unspecified equivalence. -/
@[stacks 07W8 "the fibers"]
public theorem changeOfFieldsFiberInclusion_isEquivalence
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    (changeOfFieldsFiberInclusion S p B).IsEquivalence := by
  classical
  let I := changeOfFieldsFiberInclusion S p B
  let G := (comparisonFunctor S).functor
  let Q := changeOfFieldsProjection S p
  let : I.Faithful :=
    ⟨fun h ↦ Subtype.ext (congrArg CategoricalPullback.Hom.fst (congrArg Subtype.val h))⟩
  let : I.Full := by
    constructor
    intro a b f
    let f₁ := f.val.fst
    let : Q.IsHomLift (𝟙 B) f.val := f.property
    have hsnd : f.val.snd = 𝟙 B := by
      have h := IsHomLift.fac' Q (𝟙 B) f.val
      have hdom := IsHomLift.domain_eq Q (𝟙 B) f.val
      have hcod := IsHomLift.codomain_eq Q (𝟙 B) f.val
      cases hdom
      cases hcod
      change f.val.snd = 𝟙 B at h
      simpa using h
    have h₁ : p.IsHomLift (𝟙 (G.obj B)) f₁ := by
      have h := f.val.w
      rw [hsnd] at h
      change p.map f₁ ≫ eqToHom b.property =
        eqToHom a.property ≫ G.map (𝟙 B) at h
      rw [G.map_id] at h
      exact IsHomLift.of_commsq p (𝟙 (G.obj B)) f₁ a.property b.property h
    let g : a ⟶ b := ⟨f₁, h₁⟩
    exact ⟨g, Functor.Fiber.hom_ext (CategoricalPullback.hom_ext rfl hsnd.symm)⟩
  let : I.EssSurj := by
    constructor
    intro t
    rcases t with ⟨P, hPB⟩
    rcases P with ⟨a, b, i⟩
    change b = B at hPB
    subst b
    let c : p.obj a ≅ (comparisonFunctor S).functor.obj B := i
    obtain ⟨a', ha', β, hβ⟩ :=
      hp.exists_iso_lift (z := Opposite.op a) (U := Opposite.op (G.obj B)) c.symm.op
    let α : a'.unop ≅ a := β.unop
    have hbase : p.obj a'.unop = G.obj B := by
      simpa using congrArg Opposite.unop ha'
    have hmap : p.map α.hom = eqToHom hbase ≫ c.inv := by
      have hfac := IsHomLift.fac' p.op c.symm.op.hom β.hom
      have hfac' : (p.map α.hom).op =
          c.symm.op.hom ≫ eqToHom (congrArg Opposite.op hbase).symm := by
        simpa [α, Functor.op_map] using hfac
      simpa using congrArg (fun f => f.unop) hfac'
    let a₀ : p.Fiber (G.obj B) := ⟨a'.unop, hbase⟩
    let eCP : ((I.obj a₀).val) ≅ ⟨a, B, i⟩ :=
      CategoricalPullback.mkIso α (Iso.refl B) (by
        change p.map α.hom ≫ i.hom =
          (eqToIso hbase).hom ≫ (comparisonFunctor S).functor.map (𝟙 B)
        rw [hmap]
        change (eqToHom hbase ≫ c.inv) ≫ c.hom =
          eqToHom hbase ≫ (comparisonFunctor S).functor.map (𝟙 B)
        rw [G.map_id, Category.assoc, c.inv_hom_id, Category.comp_id])
    let t' : (changeOfFieldsProjection S p).Fiber B := ⟨⟨a, B, i⟩, rfl⟩
    let e : I.obj a₀ ≅ t' :=
      { hom := ⟨eCP.hom, IsHomLift.of_fac' Q (𝟙 B) _ rfl rfl rfl⟩
        inv := ⟨eCP.inv, IsHomLift.of_fac' Q (𝟙 B) _ rfl rfl rfl⟩
        hom_inv_id := Subtype.ext eCP.hom_inv_id
        inv_hom_id := Subtype.ext eCP.inv_hom_id }
    exact ⟨a₀, ⟨e⟩⟩
  exact Functor.IsEquivalence.mk

/-- The canonical equivalence of changed and original fibers, with inverse functor
`changeOfFieldsFiberInclusion S p B`. -/
public noncomputable def changeOfFieldsFiberEquivalence
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    (changeOfFieldsProjection S p).Fiber B ≌
      p.Fiber ((comparisonFunctor S).functor.obj B) := by
  letI := changeOfFieldsFiberInclusion_isEquivalence S p hp B
  exact (changeOfFieldsFiberInclusion S p B).asEquivalence.symm

/-- **Stacks Project, Tag 07W8.** The projection obtained by change of residue field is
cofibered in groupoids whenever the original projection is. -/
@[stacks 07W8 "cofibered in groupoids"]
public theorem changeOfFieldsProjection_isCofiberedInGroupoids
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p) :
    IsCofiberedInGroupoids (changeOfFieldsProjection S p) := by
  classical
  let G := (comparisonFunctor S).functor
  let CP := CategoricalPullback p G
  let q : CP ⥤ ArtinianLocalAlgCat.{u, x, w} S.Λ S.l :=
    CategoricalPullback.π₂ p G
  change q.op.IsFiberedInGroupoids
  refine ⟨?_, ?_⟩
  · intro V U f X hX
    let P := X.unop
    cases hX
    let v : P.snd ⟶ V.unop := f.unop
    let gbase : p.obj P.fst ⟶ G.obj V.unop := P.iso.hom ≫ G.map v
    obtain ⟨Y, β, hβ⟩ := hp.exists_lift gbase.op (Opposite.op P.fst) rfl
    have hY : p.obj Y.unop = G.obj V.unop := by
      simpa using congrArg Opposite.unop (IsHomLift.domain_eq p.op gbase.op β)
    let T : CP := ⟨Y.unop, V.unop, eqToIso hY⟩
    let u : P.fst ⟶ Y.unop := β.unop
    have hmap : p.map u = gbase ≫ eqToHom hY.symm := by
      have hfac := IsHomLift.fac' p.op gbase.op β
      simpa [u, Functor.op_map, eqToHom_unop] using congrArg (fun m => m.unop) hfac
    let m : P ⟶ T :=
      { fst := u
        snd := v
        w := by
          change p.map u ≫ (eqToIso hY).hom = P.iso.hom ≫ G.map v
          rw [hmap]
          simp [gbase, Category.assoc] }
    refine ⟨Opposite.op T, m.op, ?_⟩
    have hdom : q.op.obj (Opposite.op T) = V := by
      cases V
      rfl
    apply IsHomLift.of_fac' q.op f m.op hdom rfl
    cases hdom
    change f.unop.op = f
    exact Quiver.Hom.op_unop f
  · intro X Y Z φ ψ f hf
    let X₀ := X.unop
    let Y₀ := Y.unop
    let Z₀ := Z.unop
    let φ₀ : X₀ ⟶ Y₀ := φ.unop
    let ψ₀ : X₀ ⟶ Z₀ := ψ.unop
    let f₀ : Y₀.snd ⟶ Z₀.snd := f.unop
    have hbase : φ₀.snd ≫ f₀ = ψ₀.snd := (congrArg (fun m => m.unop) hf :)
    let gbase : p.obj Y₀.fst ⟶ p.obj Z₀.fst :=
      Y₀.iso.hom ≫ G.map f₀ ≫ Z₀.iso.inv
    have hcomm : p.map φ₀.fst ≫ gbase = p.map ψ₀.fst := by
      calc
        p.map φ₀.fst ≫ gbase =
            (p.map φ₀.fst ≫ Y₀.iso.hom) ≫ G.map f₀ ≫ Z₀.iso.inv := by
              simp [gbase, Category.assoc]
        _ = (X₀.iso.hom ≫ G.map φ₀.snd) ≫ G.map f₀ ≫ Z₀.iso.inv := by rw [φ₀.w]
        _ = X₀.iso.hom ≫ G.map (φ₀.snd ≫ f₀) ≫ Z₀.iso.inv := by
              simp [Category.assoc]
        _ = X₀.iso.hom ≫ G.map ψ₀.snd ≫ Z₀.iso.inv := by rw [hbase]
        _ = (p.map ψ₀.fst ≫ Z₀.iso.hom) ≫ Z₀.iso.inv := by
              simp [Category.assoc]
        _ = p.map ψ₀.fst := by simp
    obtain ⟨χ, ⟨hχmap, hχcomp⟩, hχuniq⟩ :=
      hp.unique_lift (φ₀.fst.op) (ψ₀.fst.op) gbase.op (by
        simpa [Functor.op_map] using congrArg (fun m => m.op) hcomm)
    let m₁ : Y₀.fst ⟶ Z₀.fst := χ.unop
    have hm₁ : p.map m₁ = gbase := by
      simpa [m₁, Functor.op_map] using congrArg (fun m => m.unop) hχmap
    have hm₁comp : φ₀.fst ≫ m₁ = ψ₀.fst := by
      simpa [m₁] using congrArg (fun m => m.unop) hχcomp
    let m : Y₀ ⟶ Z₀ :=
      { fst := m₁
        snd := f₀
        w := by
          change p.map m₁ ≫ Z₀.iso.hom = Y₀.iso.hom ≫ G.map f₀
          rw [hm₁]
          simp [gbase, Category.assoc] }
    have hmcomp : φ₀ ≫ m = ψ₀ := CategoricalPullback.hom_ext hm₁comp hbase
    refine ⟨m.op, ?_, ?_⟩
    · constructor
      · change (q.map m).op = f
        simp [q, m, f₀]
      · apply Quiver.Hom.unop_inj
        exact hmcomp
    · intro n hn
      apply Quiver.Hom.unop_inj
      let hn₀ : Y₀ ⟶ Z₀ := n.unop
      have hnsnd : hn₀.snd = f₀ := (congrArg (fun g => g.unop) hn.1 :)
      have hncomp : φ₀ ≫ hn₀ = ψ₀ := (congrArg (fun g => g.unop) hn.2 :)
      have hnmap : p.map hn₀.fst = gbase := by
        calc
          p.map hn₀.fst = (p.map hn₀.fst ≫ Z₀.iso.hom) ≫ Z₀.iso.inv := by simp
          _ = (Y₀.iso.hom ≫ G.map hn₀.snd) ≫ Z₀.iso.inv := by rw [hn₀.w]
          _ = Y₀.iso.hom ≫ G.map hn₀.snd ≫ Z₀.iso.inv := by simp [Category.assoc]
          _ = gbase := by rw [hnsnd]
      have hn₁ : hn₀.fst.op ≫ φ₀.fst.op = ψ₀.fst.op := by
        have hh := congrArg (fun g => g.fst) hncomp
        change φ₀.fst ≫ hn₀.fst = ψ₀.fst at hh
        simpa using congrArg (fun g => g.op) hh
      have huniq := hχuniq hn₀.fst.op ⟨by
        simpa [Functor.op_map] using congrArg (fun g => g.op) hnmap, hn₁⟩
      have hfst : hn₀.fst = m₁ := by
        simpa [m₁] using congrArg (fun g => g.unop) huniq
      change hn₀ = m
      exact CategoricalPullback.hom_ext hfst (by simpa [m] using hnsnd)

end

/-! ### Comparison functor for change of residue field -/

section

add_to_stacks 07W9 comparisonFunctor

end

/-! ### Isomorphism classes after change of residue field -/

noncomputable section
open CategoryTheory
universe u v w x y z

/-- The canonical map on isomorphism classes is induced by the fiber inclusion
from the original fiber over `B ×_l k` to the changed fiber over `B`. -/
public def changeOfFieldsIsoClassMap
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    Quotient (isIsomorphicSetoid (p.Fiber ((comparisonFunctor S).functor.obj B))) →
      Quotient (isIsomorphicSetoid ((changeOfFieldsProjection S p).Fiber B)) :=
  Quotient.map (changeOfFieldsFiberInclusion S p B).obj
    (fun _ _ h => ⟨(changeOfFieldsFiberInclusion S p B).mapIso h.some⟩)

/-- The canonical fiber inclusion induces a bijection on isomorphism classes,
without restricting the universe of the total category. -/
@[stacks 07WA "isomorphism_classes"]
public theorem changeOfFieldsIsoClassMap_bijective
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    Function.Bijective (changeOfFieldsIsoClassMap S p B) := by
  classical
  let I := changeOfFieldsFiberInclusion S p B
  let : I.IsEquivalence :=
    changeOfFieldsFiberInclusion_isEquivalence S p hp B
  let E := I.asEquivalence
  constructor
  · rintro ⟨a⟩ ⟨b⟩ hab
    obtain ⟨e⟩ := Quotient.exact hab
    exact Quotient.sound ⟨E.unitIso.app a ≪≫ E.inverse.mapIso e ≪≫ (E.unitIso.app b).symm⟩
  · rintro ⟨b⟩
    exact ⟨Quotient.mk _ (E.inverse.obj b), Quotient.sound ⟨E.counitIso.app b⟩⟩

/-- The canonical equivalence of sets of isomorphism classes after change of
residue field. Its forward map is the map induced by fiber inclusion. -/
public noncomputable def changeOfFieldsIsoClassEquiv
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) :
    Quotient (isIsomorphicSetoid (p.Fiber ((comparisonFunctor S).functor.obj B))) ≃
      Quotient (isIsomorphicSetoid ((changeOfFieldsProjection S p).Fiber B)) :=
  Equiv.ofBijective (changeOfFieldsIsoClassMap S p B)
    (changeOfFieldsIsoClassMap_bijective S p hp B)

/-- Naturality of the canonical identification on representative classes: a
coCartesian pushforward and the change-of-fields fiber inclusion commute on
isomorphism classes. This formulation allows the total category to live in
an arbitrary universe. -/
@[stacks 07WA "isomorphism_classes"]
public theorem changeOfFieldsIsoClassMap_naturality
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    {B C : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l}
    (f : B ⟶ C)
    (a : p.Fiber ((comparisonFunctor S).functor.obj B)) :
    letI : p.op.IsFibered := hp.isFibered
    letI : (changeOfFieldsProjection S p).op.IsFibered :=
      (changeOfFieldsProjection_isCofiberedInGroupoids S p hp).isFibered
    let a' : p.Fiber ((comparisonFunctor S).functor.obj C) :=
      ⟨(CategoryTheory.Functor.pullbackFiber p.op
        (⟨Opposite.op a.1, congrArg Opposite.op a.2⟩ :
          p.op.Fiber (Opposite.op ((comparisonFunctor S).functor.obj B)))
        ((comparisonFunctor S).functor.map f).op).1.unop,
        congrArg Opposite.unop (CategoryTheory.Functor.pullbackFiber p.op
          (⟨Opposite.op a.1, congrArg Opposite.op a.2⟩ :
            p.op.Fiber (Opposite.op ((comparisonFunctor S).functor.obj B)))
          ((comparisonFunctor S).functor.map f).op).2⟩
    (changeOfFieldsProjection S p).op.isoClassPresheaf.map f.op.op
      (CategoryTheory.Functor.isoClassMk (changeOfFieldsProjection S p).op
        (⟨Opposite.op ((changeOfFieldsFiberInclusion S p B).obj a).1,
          congrArg Opposite.op ((changeOfFieldsFiberInclusion S p B).obj a).2⟩ :
          (changeOfFieldsProjection S p).op.Fiber (Opposite.op B))) =
      CategoryTheory.Functor.isoClassMk (changeOfFieldsProjection S p).op
        (⟨Opposite.op ((changeOfFieldsFiberInclusion S p C).obj a').1,
          congrArg Opposite.op ((changeOfFieldsFiberInclusion S p C).obj a').2⟩ :
          (changeOfFieldsProjection S p).op.Fiber (Opposite.op C)) := by
  classical
  let : p.op.IsFibered := hp.isFibered
  let : (changeOfFieldsProjection S p).op.IsFibered :=
    (changeOfFieldsProjection_isCofiberedInGroupoids S p hp).isFibered
  intro a'
  let q := changeOfFieldsProjection S p
  let x : q.op.Fiber (Opposite.op B) :=
    ⟨Opposite.op ((changeOfFieldsFiberInclusion S p B).obj a).1,
      congrArg Opposite.op ((changeOfFieldsFiberInclusion S p B).obj a).2⟩
  let y : q.op.Fiber (Opposite.op C) :=
    ⟨Opposite.op ((changeOfFieldsFiberInclusion S p C).obj a').1,
      congrArg Opposite.op ((changeOfFieldsFiberInclusion S p C).obj a').2⟩
  change q.op.isoClassPresheaf.map f.op.op (q.op.isoClassMk x) = q.op.isoClassMk y
  rw [Functor.isoClassPresheaf_map_isoClassMk]
  apply Functor.isoClassMk_eq_of_iso
  let g := (comparisonFunctor S).functor
  let α : Opposite.op a'.1 ⟶ Opposite.op a.1 :=
    Functor.IsPreFibered.pullbackMap (congrArg Opposite.op a.2) (g.map f).op
  let m : Opposite.unop x.1 ⟶ Opposite.unop y.1 :=
    { fst := α.unop
      snd := f
      w := by
        change p.map α.unop ≫ (eqToIso a'.2).hom =
          (eqToIso a.2).hom ≫ g.map f
        have hα := IsHomLift.fac' p.op (g.map f).op α
        have hα' : (eqToHom a'.2).op ≫ p.op.map α =
            (g.map f).op ≫ (eqToHom a.2).op := by
          rw [hα]
          simp
        simpa using congrArg Quiver.Hom.unop hα' }
  let γ : y.1 ⟶ x.1 := m.op
  have hm : q.op.map γ = f.op := rfl
  have : q.op.IsHomLift f.op γ := hm ▸ IsHomLift.map q.op γ
  let δ := Functor.IsPreFibered.pullbackMap x.2 f.op
  have : q.op.IsCartesian f.op δ := Functor.IsPreFibered.pullbackMap.IsCartesian x.2 f.op
  have hβexist :=
    (Functor.IsCartesian.universal_property (p := q.op) (f := f.op) (φ := δ) γ).exists
  let β := Classical.choose hβexist
  have hβ := (Classical.choose_spec hβexist).1
  have : IsGroupoid (q.op.Fiber (Opposite.op C)) :=
    (changeOfFieldsProjection_isCofiberedInGroupoids S p hp).fiber_isGroupoid
      (Opposite.op C)
  let e : y ⟶ q.op.pullbackFiber x f.op := ⟨β, hβ⟩
  exact (asIso e).symm

end

/-! ### Predeformation categories under change of residue field -/

section
open CategoryTheory
open CategoryTheory.Functor Category IsHomLift
universe u v w x y z a b c d

/-- The comparison functor `B ↦ B ×_l k` sends the residue-field object `l` of `𝒞_{Λ,l}` to an
algebra canonically isomorphic to `k`, the residue map of `l` being injective. -/
public noncomputable def comparisonResidueFieldEquiv
    (S : ChangeOfFieldsSituation.{u, v, w}) :
    (comparisonFunctor.{u, v, w, max x w} S).functor.obj
        (residueFieldObject.{u, x, w} S.Λ S.l) ≃ₐ[S.Λ]
      ULift.{max x w} S.k := by
  let B : ArtinianLocalAlgCat.{u, max x w, w} S.Λ S.l :=
    residueFieldObject.{u, x, w} S.Λ S.l
  let C := (comparisonFunctor.{u, v, w, max x w} S).functor.obj B
  let f : (↑B) →+* S.l := residueMap S B
  let g : S.k →+* S.l := algebraMap S.k S.l
  let q : RingHom.pullback f g →+* S.k := RingHom.pullbackSnd f g
  have hq : Function.Bijective q := by
    have hf : Function.Injective f := by
      intro a b hab
      have ha : f a = a.down := residueFieldObject_residue S.Λ S.l a
      have hb : f b = b.down := residueFieldObject_residue S.Λ S.l b
      apply ULift.ext
      rw [← ha, ← hb, hab]
    constructor
    · intro a b hab
      have hs : a.val.2 = b.val.2 := by simpa [q] using hab
      exact Subtype.ext <| Prod.ext
        (hf <| a.property.trans <| (congrArg g hs).trans b.property.symm) hs
    · intro y
      obtain ⟨r, hr⟩ := B.residueEquiv.surjective (g y)
      obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective r
      refine ⟨⟨(a, y), ?_⟩, rfl⟩
      change B.residueEquiv (IsLocalRing.residue (↑B) a) = g y
      rw [ha, hr]
  let e : C ≃+* ULift.{max x w} S.k :=
    ((comparisonFunctor.{u, v, w, max x w} S).pullbackEquiv B).trans
      ((RingEquiv.ofBijective q hq).trans ULift.ringEquiv.{v, max x w}.symm)
  apply AlgEquiv.ofRingEquiv (f := e)
  intro a
  apply ULift.ext
  change (ULift.ringEquiv.{v, max x w}.symm
      ((RingEquiv.ofBijective q hq)
        ((comparisonFunctor.{u, v, w, max x w} S).pullbackEquiv B
          (algebraMap S.Λ C a)))).down = algebraMap S.Λ S.k a
  rw [RingEquiv.ofBijective_apply q hq]
  rw [show ∀ t : S.k, (ULift.ringEquiv.{v, max x w}).symm t = ULift.up t from fun _ ↦ rfl]
  simpa [q] using
    (comparisonFunctor.{u, v, w, max x w} S).algebraMap_snd B a

/-- The comparison equivalence at the residue-field object is the second projection of the
pullback `l ×_l k`. -/
public lemma comparisonResidueFieldEquiv_snd
    (S : ChangeOfFieldsSituation.{u, v, w})
    (a : (comparisonFunctor.{u, v, w, max x w} S).functor.obj
      (residueFieldObject.{u, x, w} S.Λ S.l)) :
    (comparisonResidueFieldEquiv S a).down =
      ((comparisonFunctor.{u, v, w, max x w} S).pullbackEquiv
        (residueFieldObject.{u, x, w} S.Λ S.l) a).val.2 := by
  simp only [comparisonResidueFieldEquiv, AlgEquiv.ofRingEquiv_apply,
    RingEquiv.trans_apply]
  rfl

/-- The isomorphism of Artinian local `Λ`-algebras carrying the value of the comparison functor
`B ↦ B ×_l k` at the residue-field object `l` to the residue-field object `k`. -/
public noncomputable def comparisonResidueFieldIso
    (S : ChangeOfFieldsSituation.{u, v, w}) :
    (comparisonFunctor.{u, v, w, max x w} S).functor.obj
        (residueFieldObject.{u, x, w} S.Λ S.l) ≅
      residueFieldObject.{u, max x w, v} S.Λ S.k := by
  let B : ArtinianLocalAlgCat.{u, max x w, w} S.Λ S.l :=
    residueFieldObject.{u, x, w} S.Λ S.l
  let C := (comparisonFunctor.{u, v, w, max x w} S).functor.obj B
  let K : ArtinianLocalAlgCat.{u, max (max x w) v, v} S.Λ S.k :=
    residueFieldObject.{u, max x w, v} S.Λ S.k
  let e := comparisonResidueFieldEquiv S
  let f : C ⟶ K :=
    { hom := e.toAlgHom
      isLocal := IsLocalHom.of_surjective e.toAlgHom.toRingHom e.surjective
      residue_comm := by
        intro a
        calc
          K.residueEquiv (IsLocalRing.residue (↑K) (e a)) = ULift.down (e a) :=
            residueFieldObject_residue S.Λ S.k (e a)
          _ = ((comparisonFunctor.{u, v, w, max x w} S).pullbackEquiv B a).val.2 :=
            (comparisonResidueFieldEquiv_snd S a).symm
          _ = C.residueEquiv (IsLocalRing.residue (↑C) a) :=
            ((comparisonFunctor.{u, v, w, max x w} S).residue_snd B a).symm }
  let g : K ⟶ C :=
    { hom := e.symm.toAlgHom
      isLocal := IsLocalHom.of_surjective e.symm.toAlgHom.toRingHom e.symm.surjective
      residue_comm := by
        intro a
        calc
          C.residueEquiv (IsLocalRing.residue (↑C) (e.symm a)) =
              ((comparisonFunctor.{u, v, w, max x w} S).pullbackEquiv
                B (e.symm a)).val.2 :=
            (comparisonFunctor.{u, v, w, max x w} S).residue_snd B (e.symm a)
          _ = ULift.down a := (comparisonResidueFieldEquiv_snd S (e.symm a)).symm.trans
            (congrArg ULift.down (e.apply_symm_apply a))
          _ = K.residueEquiv (IsLocalRing.residue (↑K) a) :=
            (residueFieldObject_residue S.Λ S.k a).symm }
  exact
    { hom := f
      inv := g
      hom_inv_id := by
        ext a
        exact e.symm_apply_apply a
      inv_hom_id := by
        ext a
        exact e.apply_symm_apply a }


/-- A chosen cocartesian lift in a category cofibered in groupoids: a morphism `f : R ⟶ T` of
the base and an object of the fiber over `R` determine an object of the fiber over `T` together
with a morphism to it lifting `f`. -/
public noncomputable def cofiberedFiberLift
    {E : Type a} {D : Type b} [Category.{c} E] [Category.{d} D]
    (p : E ⥤ D) (hp : p.op.IsFiberedInGroupoids)
    {R T : D} (f : R ⟶ T) (X : p.Fiber R) :
    Σ Y : p.Fiber T, {φ : X.val ⟶ Y.val // p.IsHomLift f φ} := by
  rcases X with ⟨X, hX⟩
  subst R
  let h := hp.exists_lift f.op (Opposite.op X) (by simp)
  let Yop := Classical.choose h
  let φop := Classical.choose (Classical.choose_spec h)
  have hφop : p.op.IsHomLift f.op φop := Classical.choose_spec (Classical.choose_spec h)
  let φ := φop.unop
  have hY : p.obj Yop.unop = T := by
    let := hφop
    simpa using congrArg Opposite.unop (IsHomLift.domain_eq p.op f.op φop)
  have hφ : p.IsHomLift f φ := by
    apply IsHomLift.of_fac' p f φ rfl hY
    apply Quiver.Hom.op_inj
    let := hφop
    simpa [Functor.op_map] using IsHomLift.fac' p.op f.op φop
  letI : p.IsHomLift f φ := hφ
  refine ⟨⟨Yop.unop, IsHomLift.codomain_eq p f φ⟩, ⟨φ, inferInstance⟩⟩

/-- For a category cofibered in groupoids, the property that the fiber is nonempty with a
unique morphism between any two of its objects transports along an isomorphism of the base
objects. -/
public theorem cofibered_fiber_unique_of_iso
    {E : Type a} {D : Type b} [Category.{c} E] [Category.{d} D]
    (p : E ⥤ D) (hp : p.op.IsFiberedInGroupoids)
    {R T : D} (e : R ≅ T)
    (hR : Nonempty (p.Fiber R) ∧
      ∀ X Y : p.Fiber R, Nonempty (Unique (X ⟶ Y))) :
    Nonempty (p.Fiber T) ∧ ∀ X Y : p.Fiber T, Nonempty (Unique (X ⟶ Y)) := by
  classical
  obtain ⟨X⟩ := hR.1
  refine ⟨⟨(cofiberedFiberLift p hp e.hom X).1⟩, ?_⟩
  intro X Y
  let LX := cofiberedFiberLift p hp e.inv X
  let LY := cofiberedFiberLift p hp e.inv Y
  let ψX := LX.2.val
  let ψY := LY.2.val
  let : p.IsHomLift e.inv ψX := LX.2.property
  let : p.IsHomLift e.inv ψY := LY.2.property
  let : Functor.IsStronglyCocartesian p e.inv ψX :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp e.inv ψX inferInstance
  let : Functor.IsStronglyCocartesian p e.inv ψY :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp e.inv ψY inferInstance
  let : IsIso ψX := Functor.IsStronglyCocartesian.isIso_of_base_isIso p e.inv ψX
  let : IsIso ψY := Functor.IsStronglyCocartesian.isIso_of_base_isIso p e.inv ψY
  let sourceHom := (hR.2 LX.1 LY.1).some.default
  let φ : X.val ⟶ Y.val := ψX ≫ sourceHom.val ≫ inv ψY
  have hφ : p.IsHomLift (𝟙 T) φ := by
    let : p.IsHomLift (𝟙 R) sourceHom.val := sourceHom.property
    let : p.IsHomLift e.hom (inv ψY) := by simpa using IsHomLift.inv p e.inv ψY
    simpa using (show p.IsHomLift (e.inv ≫ 𝟙 R ≫ e.hom) φ from inferInstance)
  let m : X ⟶ Y := ⟨φ, hφ⟩
  refine ⟨{ default := m, uniq := ?_ }⟩
  intro n
  let ψXinv : LX.1.val ⟶ X.val := inv ψX
  let back (k : X ⟶ Y) : LX.1 ⟶ LY.1 := by
    let : p.IsHomLift e.hom ψXinv := by simpa using IsHomLift.inv p e.inv ψX
    let : p.IsHomLift (𝟙 T) k.val := k.property
    let : p.IsHomLift e.inv ψY := LY.2.property
    refine ⟨ψXinv ≫ k.val ≫ ψY, ?_⟩
    simpa using (show p.IsHomLift (e.hom ≫ 𝟙 T ≫ e.inv)
      (ψXinv ≫ k.val ≫ ψY) from inferInstance)
  let sourceUnique := (hR.2 LX.1 LY.1).some
  have hb : back n = back m := (sourceUnique.uniq (back n)).trans (sourceUnique.uniq (back m)).symm
  exact Subtype.ext ((cancel_mono ψY).mp ((cancel_epi ψXinv).mp (congrArg Subtype.val hb)))

/-- Changing the residue field of a predeformation category along `k → l`
again gives a predeformation category. -/
@[stacks 07WA "predeformation"]
public theorem changeOfFieldsProjection_isPredeformationCategory
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max (max x w) v, v} S.Λ S.k)
    (hp : IsPredeformationCategory.{u, max x w, v, z, y} p) :
    IsPredeformationCategory
      (changeOfFieldsProjection.{u, v, w, max x w, y, z} S p) := by
  refine ⟨?_, ?_⟩
  · exact changeOfFieldsProjection_isCofiberedInGroupoids S p hp.cofibered
  · let B : ArtinianLocalAlgCat.{u, max x w, w} S.Λ S.l :=
      residueFieldObject.{u, x, w} S.Λ S.l
    let K : ArtinianLocalAlgCat.{u, max (max x w) v, v} S.Λ S.k :=
      residueFieldObject.{u, max x w, v} S.Λ S.k
    let C := (comparisonFunctor.{u, v, w, max x w} S).functor.obj B
    have hK : Nonempty (p.Fiber K) ∧
        ∀ X Y : p.Fiber K, Nonempty (Unique (X ⟶ Y)) :=
      (CategoryTheory.equiv_punit_iff_unique (C := p.Fiber K)).mp hp.specialFiber
    have hC := cofibered_fiber_unique_of_iso p hp.cofibered
      (comparisonResidueFieldIso S).symm hK
    have hCEquiv : Nonempty (p.Fiber C ≌ Discrete PUnit.{
        max (max (max (max u v) (w + 1)) (x + 1)) y + 1}) :=
      (CategoryTheory.equiv_punit_iff_unique (C := p.Fiber C)).2 hC
    rcases hCEquiv with ⟨eC⟩
    exact ⟨(changeOfFieldsFiberEquivalence S p hp.cofibered B).trans eC⟩

end

end Deformation
