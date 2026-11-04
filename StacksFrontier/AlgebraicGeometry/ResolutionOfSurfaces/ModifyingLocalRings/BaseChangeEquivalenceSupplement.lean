module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeEquivalence
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.Full.Basic
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Modifications
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.FibreProduct

/-!
# Base change near finitely many closed points is an equivalence

Let `D` be a `FinitePresentationAwayPointsSituation`: a scheme `S` with finitely many pairwise
distinct closed points `s i` whose open complement `U` is quasi-compact. This file proves
[Stacks, Tag 0BFV]: base change to the spectra of the local rings `Spec 𝒪_{S, s i}`, the functor
of [Stacks, Tag 0BFU], is an equivalence of categories. Full faithfulness comes from the canonical
restriction functor of [Stacks, Tag 0E8Q]; essential surjectivity from the one-point equivalence
of [Stacks, Tag 0B3X] at each distinguished point, followed by the fibre product over `S` of the
resulting modifications.

## Main results

* `AlgebraicGeometry.isIso_pullback_hom_of_range_le`: base change along a morphism whose image
  lies in an open `V` inverts the structure morphism of an object which is an isomorphism over
  `V`.
* `AlgebraicGeometry.BaseChangeFunctor.isEquivalence_unconditional`: every functor carrying the
  canonical identifications with base change to the local rings is an equivalence.
* `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_isEquivalence_unconditional`: the
  base-change functor of Tag 0BFU is an equivalence of categories.

## References

* [Stacks Project, Tag 0BFV](https://stacks.math.columbia.edu/tag/0BFV)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Tag 0B3X](https://stacks.math.columbia.edu/tag/0B3X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe w v u

namespace AlgebraicGeometry

open CategoryTheory.Over CategoryTheory.ObjectProperty

/-- Base change along a morphism whose image lies in an open `V` inverts the structure morphism
of any object of `Over S` whose restriction to `V` is an isomorphism. -/
theorem isIso_pullback_hom_of_range_le {S T : Scheme.{u}} (g : T ⟶ S) (V : S.Opens)
    (hle : Set.range g ⊆ (V : Set S)) {X : Over S}
    (hX : IsIso ((Over.pullback V.ι).obj X).hom) :
    IsIso ((Over.pullback g).obj X).hom := by
  have hrange : Set.range g ⊆ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  have hiso : IsIso ((Over.pullback
      (IsOpenImmersion.lift V.ι g hrange ≫ V.ι)).obj X).hom := by
    refine (isIso_hom_iff_of_iso ((Over.pullbackComp
      (IsOpenImmersion.lift V.ι g hrange) V.ι).app X)).mpr ?_
    change IsIso (pullback.snd ((Over.pullback V.ι).obj X).hom
      (IsOpenImmersion.lift V.ι g hrange))
    infer_instance
  rwa [IsOpenImmersion.lift_fac] at hiso

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- The property of a finitely presented scheme over `S` that its glueing datum has trivial
component over the open complement. -/
private def pglueProperty : ObjectProperty (FinitePresentationOver D.S) :=
  D.trivialOpenProperty.inverseImage
    (canonicalRestrictionFunctor D.liftedPoints D.liftedPoints_mem_closedPoints)

private theorem openAwayProperty_eq_pglueProperty :
    D.openAwayProperty.inverseImage (isFinitePresentationOver D.S).ι = D.pglueProperty := by
  apply funext
  intro X
  apply propext
  let eOpen := D.S.isoOfEq D.complementOfClosedPoints_liftedPoints
  have hincl : eOpen.hom ≫ D.complement.ι =
      (complementOfClosedPoints D.liftedPoints D.liftedPoints_mem_closedPoints).ι :=
    Scheme.isoOfEq_hom_ι D.S D.complementOfClosedPoints_liftedPoints
  change IsIso ((Over.pullback D.complement.ι).obj X.obj).hom ↔
    IsIso ((Over.pullback
      ((complementOfClosedPoints D.liftedPoints
        D.liftedPoints_mem_closedPoints).ι)).obj X.obj).hom
  rw [← hincl]
  exact (isIso_pullback_obj_hom_iff_of_isoComp D.complement.ι eOpen X.obj).symm

private theorem inf_openAwayProperty_eq :
    (isFinitePresentationOver D.S ⊓ D.openAwayProperty) =
      IsFinitePresentationAway D.complement := by
  ext X
  rfl

/-- The global category of the situation is the full subcategory of finitely presented schemes
over `S` whose glueing datum has trivial open component. -/
private noncomputable def globalToPglue : D.globalCategory ≌ D.pglueProperty.FullSubcategory :=
  ((nestedFullSubcategoryEquivalence (isFinitePresentationOver D.S) D.openAwayProperty).trans
      (ObjectProperty.fullSubcategoryCongr D.inf_openAwayProperty_eq)).symm.trans
    (ObjectProperty.fullSubcategoryCongr D.openAwayProperty_eq_pglueProperty)

/-- The canonical restriction functor of Stacks Tag 0E8Q, cut down to the objects whose glueing
datum has trivial open component. -/
private noncomputable def glueingLift :
    D.pglueProperty.FullSubcategory ⥤ D.trivialOpenProperty.FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι D.pglueProperty ⋙
    canonicalRestrictionFunctor D.liftedPoints D.liftedPoints_mem_closedPoints)
    fun X ↦ X.property

private theorem glueingLift_faithful : D.glueingLift.Faithful := by
  have := faithful_canonicalRestrictionFunctor D.liftedPoints D.liftedPoints_mem_closedPoints
    D.quasiCompact_complementOfClosedPoints_liftedPoints
  exact Functor.Faithful.of_comp_iso (ObjectProperty.liftCompιIso _ _ _)

private theorem glueingLift_full : D.glueingLift.Full := by
  have := faithful_canonicalRestrictionFunctor D.liftedPoints D.liftedPoints_mem_closedPoints
    D.quasiCompact_complementOfClosedPoints_liftedPoints
  have := full_canonicalRestrictionFunctor D.liftedPoints D.liftedPoints_mem_closedPoints
    D.liftedPoints_injective D.quasiCompact_complementOfClosedPoints_liftedPoints
  exact Functor.Full.of_comp_faithful_iso (ObjectProperty.liftCompιIso _ _ _)

/-- Base change to the spectra of the local rings, read through the glueing theorem of Stacks
Tag 0E8Q and the projection to the local components. -/
private noncomputable def baseChangeComparison :
    D.globalCategory ⥤ (∀ i, D.localCategory i) :=
  D.globalToPglue.functor ⋙ D.glueingLift ⋙ D.localAwayProjection ⋙
    D.localAwayToLocalCategoryEquivalence.functor

private noncomputable def baseChangeComparisonFullyFaithful :
    D.baseChangeComparison.FullyFaithful := by
  haveI := D.glueingLift_full
  haveI := D.glueingLift_faithful
  haveI := D.localAwayProjection_full
  haveI := D.localAwayProjection_faithful
  exact (Functor.FullyFaithful.ofFullyFaithful D.globalToPglue.functor).comp
    ((Functor.FullyFaithful.ofFullyFaithful D.glueingLift).comp
      ((Functor.FullyFaithful.ofFullyFaithful D.localAwayProjection).comp
        (Functor.FullyFaithful.ofFullyFaithful
          D.localAwayToLocalCategoryEquivalence.functor)))

/-- Every component of the comparison functor is base change along the canonical morphism from
the spectrum of the corresponding local ring. -/
private noncomputable def baseChangeComparisonComponentIso (i : Fin D.n) :
    D.baseChangeComparison ⋙ Pi.eval (fun i ↦ D.localCategory i) i ⋙
        ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i)) ≅
      ObjectProperty.ι (IsFinitePresentationAway D.complement) ⋙
        Over.pullback (D.S.fromSpecStalk (D.points i)) := by
  refine NatIso.ofComponents (fun X ↦ Iso.refl _) ?_
  intro X Y f
  simp only [Iso.refl_hom]
  exact rfl

/-- Any functor carrying the canonical identifications with base change to the spectra of the
local rings is isomorphic to the comparison functor. -/
private noncomputable def baseChangeComparisonIso (B : BaseChangeFunctor D) :
    D.baseChangeComparison ≅ B.functor := by
  let γ (i : Fin D.n) :
      (D.baseChangeComparison ⋙ Pi.eval (fun i ↦ D.localCategory i) i ⋙
        ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))) ≅
      (B.functor ⋙ Pi.eval (fun i ↦ D.localCategory i) i ⋙
        ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))) :=
    D.baseChangeComparisonComponentIso i ≪≫ (B.pullbackIso i).symm
  apply NatIso.ofComponents (fun X ↦ by
    let f : D.baseChangeComparison.obj X ⟶ B.functor.obj X := fun i ↦
      (ObjectProperty.isoMk (IsFinitePresentationAway (D.puncturedLocalScheme i))
        ((γ i).app X)).hom
    have hf : ∀ i, IsIso (f i) := fun i ↦
      (ObjectProperty.isoMk (IsFinitePresentationAway (D.puncturedLocalScheme i))
        ((γ i).app X)).isIso_hom
    have : IsIso f := (isIso_pi_iff f).2 hf
    exact asIso f) (by
      intro X Y f
      funext i
      apply ObjectProperty.hom_ext
      change ((D.baseChangeComparison ⋙ Pi.eval (fun i ↦ D.localCategory i) i ⋙
          ObjectProperty.ι (IsFinitePresentationAway
            (D.puncturedLocalScheme i))).map f ≫ (γ i).hom.app Y) =
        ((γ i).hom.app X ≫
          (B.functor ⋙ Pi.eval (fun i ↦ D.localCategory i) i ⋙
            ObjectProperty.ι (IsFinitePresentationAway
              (D.puncturedLocalScheme i))).map f)
      exact (γ i).hom.naturality f)

/-! ### Essential surjectivity from the one-point case -/

/-- The open complement of one distinguished point has quasi-compact inclusion. It differs from
the open complement of the whole family by the finitely many other distinguished points, and
adjoining finitely many points to a quasi-compact set leaves it quasi-compact. -/
private theorem quasiCompact_puncturedOpen (i : Fin D.n) :
    QuasiCompact (GlueingNearPoint.puncturedOpen (D.points_closed i)).ι := by
  have hbase : IsRetrocompact (D.complement : Set D.S) :=
    GlueingNearPoint.isRetrocompact_of_quasiCompact_ι _ D.complement_quasiCompact
  have hretro :
      IsRetrocompact (GlueingNearPoint.puncturedOpen (D.points_closed i) : Set D.S) := by
    intro U hUcomp hUopen
    have hset : (GlueingNearPoint.puncturedOpen (D.points_closed i) : Set D.S) ∩ U =
        ((D.complement : Set D.S) ∩ U) ∪ ((Set.range D.points \ {D.points i}) ∩ U) := by
      ext x
      constructor
      · rintro ⟨hx, hxU⟩
        by_cases hr : x ∈ Set.range D.points
        · exact Or.inr ⟨⟨hr, hx⟩, hxU⟩
        · exact Or.inl ⟨hr, hxU⟩
      · rintro (⟨hx, hxU⟩ | ⟨⟨_, hxi⟩, hxU⟩)
        · exact ⟨fun hcon ↦ hx ⟨i, hcon.symm⟩, hxU⟩
        · exact ⟨hxi, hxU⟩
    rw [hset]
    exact (hbase hUcomp hUopen).union
      ((Set.Finite.sdiff (Set.finite_range D.points)).inter_of_left U).isCompact
  exact quasiCompact_iff_isSpectralMap.mpr
    (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hretro)

/-- The open complement of the distinguished points lies in the open complement of any one of
them. -/
private theorem range_complement_le_puncturedOpen (j : Fin D.n) :
    Set.range D.complement.ι ⊆
      (GlueingNearPoint.puncturedOpen (D.points_closed j) : Set D.S) := by
  rw [Scheme.Opens.range_ι]
  intro x hx
  exact fun hcon ↦ hx ⟨j, hcon.symm⟩

/-- The image of `Spec 𝒪_{S, s i}` in `S` avoids every other distinguished point: a point
specializing to `s i` that equals the closed point `s j` forces `i = j`. -/
private theorem range_fromSpecStalk_le_puncturedOpen {i j : Fin D.n} (hij : j ≠ i) :
    Set.range (D.S.fromSpecStalk (D.points i)) ⊆
      (GlueingNearPoint.puncturedOpen (D.points_closed j) : Set D.S) := by
  rw [Scheme.range_fromSpecStalk]
  intro x hx hcon
  have hspec : D.points j ⤳ D.points i := by
    have hx' : x ⤳ D.points i := hx
    rwa [Set.mem_singleton_iff.mp hcon] at hx'
  have hmem : D.points i ∈ ({D.points j} : Set D.S) :=
    specializes_iff_forall_closed.mp hspec _ (D.points_closed j) (by simp)
  exact hij (D.points_injective (by simpa using hmem.symm))

/-- **Essential surjectivity**, as in Stacks Tag 0BFV. Each local object is, by the one-point
equivalence of [Stacks, Tag 0B3X], the base change of a modification at `s i`, which restricts to
an isomorphism over `S ∖ {s i}`, hence over the open complement of the whole family and over
every `Spec 𝒪_{S, s j}` with `j ≠ i`; so the fibre product over `S` of these modifications is a
modification supported at the distinguished points with the given base change over each
`Spec 𝒪_{S, s i}`. -/
private theorem essSurj (B : BaseChangeFunctor D) : B.functor.EssSurj := by
  constructor
  intro Y
  have key : ∀ i : Fin D.n, ∃ W : Over D.S, FinitePresentation W.hom ∧
      IsIso ((Over.pullback
        (GlueingNearPoint.puncturedOpen (D.points_closed i)).ι).obj W).hom ∧
      Nonempty ((Over.pullback (D.S.fromSpecStalk (D.points i))).obj W ≅ (Y i).obj) := by
    intro i
    have : (GlueingNearPoint.finitePresentationAwayBaseChange D.S (D.points i)
        (D.points_closed i)).IsEquivalence :=
      GlueingNearPoint.finitePresentationAwayBaseChange_isEquivalence D.S (D.points i)
        (D.points_closed i) (D.quasiCompact_puncturedOpen i)
    have hV : (D.S.fromSpecStalk (D.points i)) ⁻¹ᵁ
        (GlueingNearPoint.puncturedOpen (D.points_closed i)) = D.puncturedLocalScheme i :=
      GlueingNearPoint.preimage_puncturedOpen (D.points_closed i)
    let Y' : FinitePresentationAway ((D.S.fromSpecStalk (D.points i)) ⁻¹ᵁ
        (GlueingNearPoint.puncturedOpen (D.points_closed i))) :=
      ⟨(Y i).obj, by rw [hV]; exact (Y i).property⟩
    let X₀ := (GlueingNearPoint.finitePresentationAwayBaseChange D.S (D.points i)
      (D.points_closed i)).objPreimage Y'
    refine ⟨X₀.obj, X₀.property.1, X₀.property.2, ⟨?_⟩⟩
    exact (ObjectProperty.ι _).mapIso
      ((GlueingNearPoint.finitePresentationAwayBaseChange D.S (D.points i)
        (D.points_closed i)).objObjPreimageIso Y')
  choose W hWfp hWaway hWiso using key
  have hfp : FinitePresentation (finFibreProduct W).hom :=
    finitePresentation_finFibreProduct_hom W hWfp
  have hcompl : IsIso ((Over.pullback D.complement.ι).obj (finFibreProduct W)).hom :=
    isIso_pullback_finFibreProduct_hom D.complement.ι W fun j ↦
      isIso_pullback_hom_of_range_le D.complement.ι
        (GlueingNearPoint.puncturedOpen (D.points_closed j))
        (D.range_complement_le_puncturedOpen j) (hWaway j)
  let X : D.globalCategory := ⟨finFibreProduct W, hfp, hcompl⟩
  have hcomp : ∀ i : Fin D.n, Nonempty (B.functor.obj X i ≅ Y i) := by
    intro i
    obtain ⟨e₁⟩ := nonempty_pullback_finFibreProduct_iso
      (D.S.fromSpecStalk (D.points i)) W i fun j hj ↦
        isIso_pullback_hom_of_range_le (D.S.fromSpecStalk (D.points i))
          (GlueingNearPoint.puncturedOpen (D.points_closed j))
          (D.range_fromSpecStalk_le_puncturedOpen hj) (hWaway j)
    obtain ⟨e₂⟩ := hWiso i
    exact ⟨ObjectProperty.isoMk _ ((B.pullbackIso i).app X ≪≫ e₁ ≪≫ e₂)⟩
  exact ⟨X, ⟨{ hom := fun i ↦ (hcomp i).some.hom
               inv := fun i ↦ (hcomp i).some.inv
               hom_inv_id := funext fun i ↦ (hcomp i).some.hom_inv_id
               inv_hom_id := funext fun i ↦ (hcomp i).some.inv_hom_id }⟩⟩

end FinitePresentationAwayPointsSituation

/-- **Stacks Project, Tag 0BFV.** Any functor carrying the canonical identifications with base
change to the spectra of the local rings — in particular the one of [Stacks, Tag 0BFU] — is an
equivalence of categories.

Full faithfulness comes from the full faithfulness of the canonical restriction functor of
[Stacks, Tag 0E8Q]; essential surjectivity is the one-point equivalence of
[Stacks, Tag 0B3X] applied at each distinguished point, followed by the fibre product over `S`
of the resulting modifications.

The tag is carried by
`AlgebraicGeometry.finitePresentationAwayPointsBaseChange_isEquivalence_unconditional`, the
specialization of this statement to the functor Tag 0BFU displays. -/
theorem BaseChangeFunctor.isEquivalence_unconditional
    {D : FinitePresentationAwayPointsSituation.{u}} (B : BaseChangeFunctor D) :
    B.functor.IsEquivalence :=
  have hff := D.baseChangeComparisonFullyFaithful.ofIso (D.baseChangeComparisonIso B)
  Functor.IsEquivalence.mk hff.faithful hff.full (D.essSurj B)

/-- **Stacks Project, Tag 0BFV.** Base change from finitely presented modifications supported
at finitely many closed points to the corresponding local modifications is an equivalence of
categories. -/
@[stacks 0BFV]
theorem finitePresentationAwayPointsBaseChange_isEquivalence_unconditional
    (D : FinitePresentationAwayPointsSituation.{u}) :
    (finitePresentationAwayPointsBaseChange D).functor.IsEquivalence :=
  (finitePresentationAwayPointsBaseChange D).isEquivalence_unconditional

end AlgebraicGeometry

end
