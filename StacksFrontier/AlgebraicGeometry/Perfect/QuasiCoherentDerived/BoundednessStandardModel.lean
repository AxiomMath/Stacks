module

public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.BoundednessByCompactObjects
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite

/-!
# Boundedness detected by a perfect generator, at the standard model of `D(𝒪_X)`

The statements of [Stacks, Tags 0GEN and 0GEQ] in this library are made at the derived category
`CategoryTheory.HasDerivedCategory.standard` of `𝒪_X`-modules, with perfectness read at the
ringed site of opens of `X`. The induction proving them,
`StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.BoundednessByCompactObjects`, runs at
the locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` with compact
objects of `D_QCoh(𝒪_X)`. This module carries it across.

The comparison equivalence of the two models,
`StacksDraft.DerivedModel.modelEquiv`, commutes with the shifts and with the cohomology
sheaves; a perfect object becomes compact in `D_QCoh(𝒪_X)` by
`Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect`, and a generator of `D_QCoh(𝒪_X)` stays
one.

## Main results

* `Stacks.Duality.CompactBoundedness.eventuallyOrthogonal_of_isPerfect_of_bdd`: a perfect `P`
  is eventually orthogonal to every bounded object with quasi-coherent cohomology.
* `Stacks.Duality.CompactBoundedness.bdd_of_eventuallyOrthogonal_of_isPerfect_generator`: an
  object with quasi-coherent cohomology eventually orthogonal to a perfect generator is bounded.

## References

* [Stacks Project, Tag 0GEN](https://stacks.math.columbia.edu/tag/0GEN)
* [Stacks Project, Tag 0GEQ](https://stacks.math.columbia.edu/tag/0GEQ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Filter

universe w z u₁ v₁ u

/-! ### The comparison of two models commutes with cohomology and with the shifts -/

namespace StacksDraft.DerivedModel

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w} C) (h₂ : HasDerivedCategory.{z} C)

/-- The comparison equivalence of two models of `D(C)` commutes with the cohomology objects. -/
def homologyModelIso (K : @DerivedCategory C _ _ h₁) (q : ℤ) :
    (@DerivedCategory.homologyFunctor C _ _ h₂ q).obj ((modelEquiv h₁ h₂).functor.obj K) ≅
      (@DerivedCategory.homologyFunctor C _ _ h₁ q).obj K :=
  let X := (@DerivedCategory.Q C _ _ h₁).objPreimage K
  let e : (@DerivedCategory.Q C _ _ h₁).obj X ≅ K :=
    (@DerivedCategory.Q C _ _ h₁).objObjPreimageIso K
  (@DerivedCategory.homologyFunctor C _ _ h₂ q).mapIso
      ((modelEquiv h₁ h₂).functor.mapIso e.symm ≪≫ (modelCompQIso h₁ h₂).app X) ≪≫
    (@DerivedCategory.homologyFunctorFactors C _ _ h₂ q).app X ≪≫
    ((@DerivedCategory.homologyFunctorFactors C _ _ h₁ q).app X).symm ≪≫
    (@DerivedCategory.homologyFunctor C _ _ h₁ q).mapIso e

/-- Boundedness does not depend on the model. -/
theorem bdd_model_iff (l : Filter ℤ) (K : @DerivedCategory C _ _ h₁) :
    @Stacks.Duality.CompactBoundedness.Bdd C _ _ h₂ l ((modelEquiv h₁ h₂).functor.obj K) ↔
      @Stacks.Duality.CompactBoundedness.Bdd C _ _ h₁ l K :=
  ⟨fun h => h.mono fun q hq => hq.of_iso (homologyModelIso h₁ h₂ K q).symm,
    fun h => h.mono fun q hq => hq.of_iso (homologyModelIso h₁ h₂ K q)⟩

/-- Morphism groups out of shifts do not depend on the model. -/
theorem subsingleton_shift_model_iff (P E : @DerivedCategory C _ _ h₁) (n : ℤ) :
    Subsingleton (((modelEquiv h₁ h₂).functor.obj P)⟦n⟧ ⟶ (modelEquiv h₁ h₂).functor.obj E) ↔
      Subsingleton (P⟦n⟧ ⟶ E) := by
  let := StacksDraft.Perfect.derivedEquivalenceCommShift h₁ h₂
  refine Iff.trans ?_ ((modelEquiv h₁ h₂).fullyFaithfulFunctor.homEquiv
    (X := P⟦n⟧) (Y := E)).subsingleton_congr.symm
  exact ((((modelEquiv h₁ h₂).functor.commShiftIso n).app P).homFromEquiv
    (Z := (modelEquiv h₁ h₂).functor.obj E)).subsingleton_congr.symm

/-- Eventual orthogonality does not depend on the model. -/
theorem eventuallyOrthogonal_model_iff (l : Filter ℤ) (P E : @DerivedCategory C _ _ h₁) :
    EventuallyOrthogonal l ((modelEquiv h₁ h₂).functor.obj P) ((modelEquiv h₁ h₂).functor.obj E) ↔
      EventuallyOrthogonal l P E :=
  ⟨fun h => h.mono fun i hi => (subsingleton_shift_model_iff h₁ h₂ P E (-i)).1 hi,
    fun h => h.mono fun i hi => (subsingleton_shift_model_iff h₁ h₂ P E (-i)).2 hi⟩

end StacksDraft.DerivedModel

/-! ### Transport to the standard model -/

namespace Stacks.Duality.CompactBoundedness

open StacksDraft.DerivedModel TopologicalSpace

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- The derived category of `𝒪_X`-modules at the standard model
`CategoryTheory.HasDerivedCategory.standard`. -/
abbrev Dstd (X : Scheme.{u}) : Type (u + 1) :=
  @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard X.Modules)

/-- The cohomology sheaves at the standard model. -/
abbrev Hstd (X : Scheme.{u}) (i : ℤ) : Dstd X ⥤ X.Modules :=
  @DerivedCategory.homologyFunctor X.Modules _ _ (HasDerivedCategory.standard X.Modules) i

/-- Perfectness at the standard model, in the ringed-space reading of [Stacks, Tag 08CM]. -/
abbrev IsPerfectStd (P : Dstd X) : Prop :=
  @Stacks.Cohomology.PerfectComplexes.IsPerfect X.toRingedSpace
    (HasDerivedCategory.standard X.Modules) P

/-- The comparison of the standard model of `D(𝒪_X)` with the locally small one. -/
abbrev toLocallySmall (X : Scheme.{u}) : Dstd X ⥤ DerivedCategory X.Modules :=
  (modelEquiv (HasDerivedCategory.standard X.Modules) (Scheme.Modules.hasDerivedCategory X)).functor

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- An object with quasi-coherent cohomology, as an object of `D_QCoh(𝒪_X)` at the locally small
model. -/
theorem isQuasicoherent_toLocallySmall (E : Dstd X)
    (hE : ∀ i : ℤ, ((Hstd X i).obj E).IsQuasicoherent) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) ((toLocallySmall X).obj E) := fun i =>
  (AlgebraicGeometry.isQuasicoherentModules X).prop_of_iso
    (homologyModelIso (HasDerivedCategory.standard X.Modules)
      (Scheme.Modules.hasDerivedCategory X) E i).symm (hE i)

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- A perfect object at the standard model is perfect at the locally small model. -/
theorem isPerfect_toLocallySmall (P : Dstd X) (hP : IsPerfectStd P) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((toLocallySmall X).obj P) := by
  let h₁ := HasDerivedCategory.standard X.Modules
  let h₂ := Scheme.Modules.hasDerivedCategory X
  let K := (@DerivedCategory.Q X.Modules _ _ h₁).objPreimage P
  let e₁ : (@DerivedCategory.Q X.Modules _ _ h₁).obj K ≅ P :=
    (@DerivedCategory.Q X.Modules _ _ h₁).objObjPreimageIso P
  let e₂ : (@DerivedCategory.Q X.Modules _ _ h₂).obj K ≅ (toLocallySmall X).obj P :=
    ((modelCompQIso h₁ h₂).app K).symm ≪≫ (toLocallySmall X).mapIso e₁
  exact (Stacks.Cohomology.PerfectComplexes.isPerfect_iff_of_model h₁ h₂ e₁ e₂).1 hP

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- A perfect object of `D(𝒪_X)` has quasi-coherent cohomology. -/
theorem isQuasicoherent_of_isPerfectStd (P : Dstd X) (hP : IsPerfectStd P) (i : ℤ) :
    ((Hstd X i).obj P).IsQuasicoherent :=
  AlgebraicGeometry.PerfectApproximation.isQuasicoherent_homology_of_isPerfect X P hP i

/-- An object of `D(𝒪_X)` with quasi-coherent cohomology, as an object of `D_QCoh(𝒪_X)`. -/
private abbrev toQCoh (E : Dstd X) (hE : ∀ i : ℤ, ((Hstd X i).obj E).IsQuasicoherent) :
    Stacks.Duality.quasiCoherentDerivedCategory X :=
  ⟨(toLocallySmall X).obj E, isQuasicoherent_toLocallySmall E hE⟩

/-- A perfect object of `D(𝒪_X)` becomes a compact object of `D_QCoh(𝒪_X)`. -/
private theorem isCompactObject_toQCoh (P : Dstd X) (hP : IsPerfectStd P) :
    IsCompactObject.{u} (toQCoh P (isQuasicoherent_of_isPerfectStd P hP)) :=
  Stacks.Duality.QcqsPerfect.isCompactObject_of_isPerfect X _ (isPerfect_toLocallySmall P hP)

/-- Eventual orthogonality in `D(𝒪_X)` is the same as in `D_QCoh(𝒪_X)`. -/
private theorem eventuallyOrthogonal_toQCoh_iff {Y : Scheme.{u}} (l : Filter ℤ) (P E : Dstd Y)
    (hP : ∀ i : ℤ, ((Hstd Y i).obj P).IsQuasicoherent)
    (hE : ∀ i : ℤ, ((Hstd Y i).obj E).IsQuasicoherent) :
    EventuallyOrthogonal l P E ↔ EventuallyOrthogonal l (toQCoh P hP) (toQCoh E hE) :=
  (eventuallyOrthogonal_model_iff (HasDerivedCategory.standard Y.Modules)
    (Scheme.Modules.hasDerivedCategory Y) l P E).symm.trans
    ⟨fun h => h.mono fun i hi => (subsingleton_shift_hom_iff _ _ (-i)).2 hi,
      fun h => h.mono fun i hi => (subsingleton_shift_hom_iff _ _ (-i)).1 hi⟩

/-- **The window of a perfect object.** On a quasi-compact quasi-separated scheme `X`, a perfect
object `P` of `D(𝒪_X)` is eventually orthogonal along `l` to every object with quasi-coherent
cohomology which is bounded along `l`: if `E ∈ D^-_QCoh(𝒪_X)` then `Hom(P⟦-i⟧, E) = 0` for
`i ≫ 0`, and if `E ∈ D^+_QCoh(𝒪_X)` then `Hom(P⟦-i⟧, E) = 0` for `i ≪ 0`. -/
theorem eventuallyOrthogonal_of_isPerfect_of_bdd {l : Filter ℤ} (hl : l = atTop ∨ l = atBot)
    (P E : Dstd X) (hP : IsPerfectStd P) (hE : ∀ i : ℤ, ((Hstd X i).obj E).IsQuasicoherent)
    (hb : @Bdd X.Modules _ _ (HasDerivedCategory.standard X.Modules) l E) :
    EventuallyOrthogonal l P E :=
  (eventuallyOrthogonal_toQCoh_iff l P E (isQuasicoherent_of_isPerfectStd P hP) hE).2
    (window hl X _ (isCompactObject_toQCoh P hP) _
      ((bdd_model_iff (HasDerivedCategory.standard X.Modules)
        (Scheme.Modules.hasDerivedCategory X) l E).2 hb))

/-- **Boundedness is detected by a perfect generator.** On a quasi-compact quasi-separated scheme
`X`, let `G` be a perfect object of `D(𝒪_X)` generating `D_QCoh(𝒪_X)` and let `E` be an object
with quasi-coherent cohomology. If `G` is eventually orthogonal to `E` along `l`, then `E` is
bounded along `l`: if `Hom(G⟦-i⟧, E) = 0` for `i ≫ 0` then `E ∈ D^-`, and if it vanishes for
`i ≪ 0` then `E ∈ D^+`. -/
theorem bdd_of_eventuallyOrthogonal_of_isPerfect_generator {l : Filter ℤ}
    (hl : l = atTop ∨ l = atBot) (G E : Dstd X) (hG : IsPerfectStd G)
    (hgen : ∀ K : Dstd X, (∀ i : ℤ, ((Hstd X i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (hE : ∀ i : ℤ, ((Hstd X i).obj E).IsQuasicoherent)
    (h : EventuallyOrthogonal l G E) :
    @Bdd X.Modules _ _ (HasDerivedCategory.standard X.Modules) l E := by
  let h₁ := HasDerivedCategory.standard X.Modules
  let h₂ := Scheme.Modules.hasDerivedCategory X
  let G' := toQCoh G (isQuasicoherent_of_isPerfectStd G hG)
  let E' := toQCoh E hE
  have hGc := isCompactObject_toQCoh G hG
  have hgen' : (ObjectProperty.singleton G').IsWeakTriangulatedGenerator := by
    intro K hK
    rw [rightOrthogonal_shiftClosure_ofObj_iff] at hK
    let K₁ : Dstd X := (modelEquiv h₁ h₂).inverse.obj K.obj
    let e : (toLocallySmall X).obj K₁ ≅ K.obj := (modelEquiv h₁ h₂).counitIso.app K.obj
    have hK₁ : ∀ i : ℤ, ((Hstd X i).obj K₁).IsQuasicoherent := fun i =>
      (AlgebraicGeometry.isQuasicoherentModules X).prop_of_iso
        ((@DerivedCategory.homologyFunctor X.Modules _ _ h₂ i).mapIso e.symm ≪≫
          homologyModelIso h₁ h₂ K₁ i) (K.2 i)
    have hz : IsZero K₁ := hgen K₁ hK₁ fun n f => by
      have hs : Subsingleton (G⟦n⟧ ⟶ K₁) := by
        refine (subsingleton_shift_model_iff h₁ h₂ G K₁ n).1 ?_
        have : Subsingleton (G'.obj⟦n⟧ ⟶ K.obj) :=
          (subsingleton_shift_hom_iff G' K n).1 ⟨fun a b => (hK PUnit.unit n a).trans
            (hK PUnit.unit n b).symm⟩
        exact ⟨fun a b => (cancel_mono e.hom).1 (Subsingleton.elim _ _)⟩
      exact Subsingleton.elim _ _
    exact isZero_of_isZero_obj (((toLocallySmall X).map_isZero hz).of_iso e.symm)
  have hE' : EventuallyOrthogonal l G' E' :=
    (eventuallyOrthogonal_toQCoh_iff l G E _ hE).1 h
  exact (bdd_model_iff h₁ h₂ l E).1 (detection hl X E'
    fun P hP => eventuallyOrthogonal_of_isCompactObject hl G' hgen' E' hE' P hP)

end Stacks.Duality.CompactBoundedness

end
