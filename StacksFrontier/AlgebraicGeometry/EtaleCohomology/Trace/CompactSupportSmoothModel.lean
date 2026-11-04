module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralExtensionByZeroRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekCompactification

/-!
# `H^i_c(X_k̄, -)` of a curve through its smooth projective model

Let `k` be a field, `X` a geometrically connected smooth curve over `k`, `j : X ⟶ X̄` a
compactification of `X` over `k` (an open immersion into a proper `k`-scheme, arbitrary
otherwise), and `k̄` an algebraically closed extension of `k`.  Remark 03UI (2) of the Trace
Formula chapter defines `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`.  This file computes the
cohomology modules of that complex, for a sheaf `F` of `Λ`-modules on `X`, on the smooth
projective model `C` of the geometric curve `X_k̄`:

`H^i_c(X_k̄, F) ≅ H^i(C, j_{C!}(F|_{X_k̄}))`,

where `j_C : X_k̄ ⟶ C` is the open immersion.  Three identifications go into it.

1. `(j_! F)|_{X̄_k̄} ≅ j'_!(F|_{X_k̄})` for the base change `j' : X_k̄ ⟶ X̄_k̄` of `j`: extension
   by zero commutes with base change ([Stacks, Tag 03S6]), the square of `j`, `j'` and the two
   projections being cartesian.
2. `X_k̄` is a smooth curve over the perfect field `k̄` and `C` is its smooth projective
   compactification over `X̄_k̄` ([Stacks, Tag 0H1F]; `AlgebraicGeometry.CoverCompactification`),
   with a finite morphism `f̄ : C ⟶ X̄_k̄` such that `X_k̄ = f̄^{-1}(X_k̄)`.  Extension by zero
   commutes with that finite direct image: `j'_! G ≅ f̄_* j_{C!} G`.
3. A finite direct image is exact and preserves injectives, so `H^i(X̄_k̄, f̄_* -) = H^i(C, -)`.

No condition is put on the compactification `X̄`: it may be singular, reducible, or of any
dimension.

## Main definitions

* item 1 is `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso` applied to the
  cartesian square `Stacks.EtaleCohomology.isPullback_compactificationFieldBaseChange`.
* `AlgebraicGeometry.isCurve_pullback_snd_specAlgebraMap` — `X_K` is a curve over `K`.
* `Stacks.EtaleCohomology.geometricSmoothModel` — the smooth projective model `C` of `X_k̄`.
* `Stacks.EtaleCohomology.extensionByZeroGeometricSmoothModelIso` — item 2.
* `Stacks.EtaleCohomology.integralDirectImageCohomologyIso` — item 3.
* `Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso` — the composite.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (2).
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6).
* [Stacks Project, Tag 0H1F](https://stacks.math.columbia.edu/tag/0H1F).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

/-! ### The base change of a curve to an extension field -/

namespace AlgebraicGeometry

/-- **The base change of a geometrically connected smooth curve to an extension field is a
curve.** -/
public theorem isCurve_pullback_snd_specAlgebraMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u)
    [Field K] [Algebra k K] :
    IsCurve K (pullback.snd f (specAlgebraMap k K)) := by
  have : ConnectedSpace (pullback f (specAlgebraMap k K) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := pullback.snd f (specAlgebraMap k K))
  have : IsIntegral (pullback f (specAlgebraMap k K)) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (pullback.snd f (specAlgebraMap k K))
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
  have : SmoothOfRelativeDimension 1 (pullback.snd f (specAlgebraMap k K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f (specAlgebraMap k K)) inferInstance
  exact
    { toIsIntegral := inferInstance
      topologicalKrullDim_eq_one := by
        simpa using topologicalKrullDim_eq_of_smoothOfRelativeDimension
          (pullback.snd f (specAlgebraMap k K)) 1 }

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Extension by zero and the base change of a compactification -/

section Square

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

variable (Λ : Type r) [Ring Λ]

/-- **`H^i_c(X_k̄, F) ≅ H^i(X̄_k̄, (j_! F)|_{X̄_k̄})`** for a sheaf of `Λ`-modules placed in degree
zero: the complex `(j_! F[0])|_{X̄_k̄}` is `((j_! F)|_{X̄_k̄})[0]`. -/
public def galoisCompactSupportSingleIso (F : EtaleModules.{u, r} Λ X) (i : ℤ) :
    galoisCompactSupportCohomologyGroup.{u, r} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i ≅
      ((etaleModuleGlobalSections.{u, r} Λ
          (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus i).obj
        ((etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F)) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).mapIso
    ((etaleModuleDerivedGlobalSections.{u, r} Λ
        (pullback j.toBase (specAlgebraMap k kbar))).mapIso
      (DerivedCategory.Plus.Q.mapIso
        ((etaleModuleInverseImage.{u, r} Λ
            (pullback.fst j.toBase (specAlgebraMap k kbar))).mapCochainComplexPlus.mapIso
            (mapCochainComplexPlusSinglePlusIso
              (etaleModuleExtensionByZero.{u, r} Λ j.immersion) F) ≪≫
          mapCochainComplexPlusSinglePlusIso
            (etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase (specAlgebraMap k kbar)))
            ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).obj F))))

end Square

/-! ### Cohomology along a finite morphism -/

section Integral

variable (Λ : Type r) [Ring Λ] {A B : Scheme.{u}} (g : A ⟶ B) [IsIntegralHom g]

/-- **`H^i(B, g_* H) ≅ H^i(A, H)`** for an integral morphism `g : A ⟶ B`, a finite morphism for
instance: `g_*` is exact (Tag 04C2), so `R g_*(H[0]) = (g_* H)[0]`, and
`RΓ(A, -) = RΓ(B, -) ∘ R g_*`. -/
public def integralDirectImageCohomologyIso (H : EtaleModules.{u, r} Λ A) (i : ℤ) :
    ((etaleModuleGlobalSections.{u, r} Λ B).rightDerivedPlus i).obj
        ((etaleModuleDirectImage.{u, r} Λ g).obj H) ≅
      ((etaleModuleGlobalSections.{u, r} Λ A).rightDerivedPlus i).obj H :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).mapIso
    ((etaleModuleDerivedGlobalSections.{u, r} Λ B).mapIso
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (etaleModuleDirectImage.{u, r} Λ g) 0).app H) ≪≫
      (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ g).symm.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj H))

end Integral

/-! ### The open complement of an open immersion -/

section Complement

variable {A B : Scheme.{u}} (o : A ⟶ B) [IsOpenImmersion o]

/-- The complement of the image of an open immersion, as a closed subset. -/
public def openImmersionReducedComplementCloseds : Closeds B :=
  ⟨(Set.range o.base)ᶜ, o.isOpenEmbedding.isOpen_range.isClosed_compl⟩

/-- The closed immersion of the complement of an open immersion, with its reduced induced
structure. -/
public abbrev openImmersionReducedComplementι :
    (Scheme.IdealSheafData.vanishingIdeal (openImmersionReducedComplementCloseds o)).subscheme ⟶
      B :=
  (Scheme.IdealSheafData.vanishingIdeal (openImmersionReducedComplementCloseds o)).subschemeι

/-- The image of `openImmersionReducedComplementι o` is the complement of the image of `o`. -/
public lemma range_openImmersionReducedComplementι :
    Set.range (openImmersionReducedComplementι o).base = (Set.range o.base)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

end Complement

/-! ### Base change along a tower of fields -/

section Tower

variable {k : Type u} [Field k] (K L : Type u) [Field K] [Field L] [Algebra k K] [Algebra K L]
  [Algebra k L] [IsScalarTower k K L]

variable {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))

/-- **The comparison `Y_L ⟶ Y_K`** for a tower of fields `k ⊆ K ⊆ L` and a scheme `Y` over `k`:
the identity of `Y` times `Spec L ⟶ Spec K`. -/
public def fieldTowerBaseChangeMap :
    pullback g (specAlgebraMap k L) ⟶ pullback g (specAlgebraMap k K) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ specAlgebraMap K L)
    (by rw [pullback.condition, Category.assoc, specAlgebraMap_comp_specAlgebraMap])

/-- The comparison `Y_L ⟶ Y_K` commutes with the projections to `Y`. -/
@[reassoc (attr := simp)]
public lemma fieldTowerBaseChangeMap_fst :
    fieldTowerBaseChangeMap K L g ≫ pullback.fst g (specAlgebraMap k K) =
      pullback.fst g (specAlgebraMap k L) :=
  pullback.lift_fst _ _ _

/-- The comparison `Y_L ⟶ Y_K` lies over `Spec L ⟶ Spec K`. -/
@[reassoc (attr := simp)]
public lemma fieldTowerBaseChangeMap_snd :
    fieldTowerBaseChangeMap K L g ≫ pullback.snd g (specAlgebraMap k K) =
      pullback.snd g (specAlgebraMap k L) ≫ specAlgebraMap K L :=
  pullback.lift_snd _ _ _

/-- **`Y_L = Y_K ×_{Spec K} Spec L`**: the square of the comparison `Y_L ⟶ Y_K` and the two
structure morphisms is cartesian. -/
public theorem isPullback_fieldTowerBaseChangeMap :
    IsPullback (fieldTowerBaseChangeMap K L g) (pullback.snd g (specAlgebraMap k L))
      (pullback.snd g (specAlgebraMap k K)) (specAlgebraMap K L) := by
  refine IsPullback.of_right ?_ (fieldTowerBaseChangeMap_snd K L g)
    (IsPullback.of_hasPullback g (specAlgebraMap k K))
  rw [fieldTowerBaseChangeMap_fst, specAlgebraMap_comp_specAlgebraMap]
  exact IsPullback.of_hasPullback g _

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))

/-- The base changes `X_L ⟶ X̄_L` and `X_K ⟶ X̄_K` of the compactification commute with the
comparison maps along `Spec L ⟶ Spec K`. -/
@[reassoc]
public lemma compactificationFieldBaseChangeImmersion_comp_fieldTowerBaseChangeMap :
    compactificationFieldBaseChangeImmersion f j L ≫ fieldTowerBaseChangeMap K L j.toBase =
      fieldTowerBaseChangeMap K L f ≫ compactificationFieldBaseChangeImmersion f j K := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- **`X_L = X_K ×_{X̄_K} X̄_L`**: the base change of a compactification along a tower of fields is
cartesian over the comparison maps. -/
public theorem isPullback_fieldTowerBaseChangeMap_compactification :
    IsPullback (fieldTowerBaseChangeMap K L f) (compactificationFieldBaseChangeImmersion f j L)
      (compactificationFieldBaseChangeImmersion f j K) (fieldTowerBaseChangeMap K L j.toBase) := by
  refine IsPullback.of_right ?_
    (compactificationFieldBaseChangeImmersion_comp_fieldTowerBaseChangeMap K L f j).symm
    (isPullback_compactificationFieldBaseChange f j K)
  simpa only [fieldTowerBaseChangeMap_fst] using
    isPullback_compactificationFieldBaseChange f j L

end Tower

/-! ### The smooth projective model of the geometric curve -/

section SmoothModel

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar]

/-- The base change `X_k̄` is a curve over `k̄`. -/
instance : IsCurve kbar (pullback.snd f (specAlgebraMap k kbar)) :=
  isCurve_pullback_snd_specAlgebraMap f kbar

/-- The base change `X_k̄` is connected. -/
instance : ConnectedSpace (pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton
    (f := pullback.snd f (specAlgebraMap k kbar))

/-- **The smooth projective model `C'` of `X_{k'}` over the perfect closure `k'` of `k` in `k̄`**:
`AlgebraicGeometry.CoverCompactification` over the perfect field `k'` for the identity cover of the
smooth curve `X_{k'}`, over the base change `X̄_{k'}` of the compactification.  Every
`k`-automorphism of `k̄` fixes `k'`, so its base change `C' ×_{k'} k̄` carries the Galois
action. -/
public def perfectClosureSmoothModel :
    CoverCompactification (perfectClosure k kbar)
      (pullback.snd j.toBase (specAlgebraMap k (perfectClosure k kbar)))
      (compactificationFieldBaseChangeImmersion f j (perfectClosure k kbar))
      (𝟙 (pullback f (specAlgebraMap k (perfectClosure k kbar)))) :=
  haveI := isCurve_pullback_snd_specAlgebraMap f (perfectClosure k kbar)
  haveI : ConnectedSpace (pullback f (specAlgebraMap k (perfectClosure k kbar)) : Scheme.{u}) :=
    GeometricallyConnected.connectedSpace_of_subsingleton
      (f := pullback.snd f (specAlgebraMap k (perfectClosure k kbar)))
  (nonempty_coverCompactification (perfectClosure k kbar)
    (pullback.snd f (specAlgebraMap k (perfectClosure k kbar)))
    (pullback.snd j.toBase (specAlgebraMap k (perfectClosure k kbar)))
    (compactificationFieldBaseChangeImmersion f j (perfectClosure k kbar))
    (compactificationFieldBaseChange_immersion_comp_snd f j (perfectClosure k kbar))
    (𝟙 (pullback f (specAlgebraMap k (perfectClosure k kbar))))).some

/-- The open immersion `X_k̄ ⟶ C' ×_{X̄_{k'}} X̄_k̄`, with components `X_k̄ ⟶ X_{k'} ⟶ C'` and
`X_k̄ ⟶ X̄_k̄`. -/
public def geometricSmoothModelImmersion :
    pullback f (specAlgebraMap k kbar) ⟶
      pullback (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) :=
  pullback.lift
    (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar f ≫
      (perfectClosureSmoothModel f j kbar).j)
    (compactificationFieldBaseChangeImmersion f j kbar) (by
      rw [Category.assoc, (perfectClosureSmoothModel f j kbar).w, Category.id_comp,
        compactificationFieldBaseChangeImmersion_comp_fieldTowerBaseChangeMap])

/-- The first component of `X_k̄ ⟶ C' ×_{X̄_{k'}} X̄_k̄` is `X_k̄ ⟶ X_{k'} ⟶ C'`. -/
@[reassoc (attr := simp)]
public lemma geometricSmoothModelImmersion_fst :
    geometricSmoothModelImmersion f j kbar ≫ pullback.fst _ _ =
      fieldTowerBaseChangeMap (perfectClosure k kbar) kbar f ≫
        (perfectClosureSmoothModel f j kbar).j :=
  pullback.lift_fst _ _ _

/-- The second component of `X_k̄ ⟶ C' ×_{X̄_{k'}} X̄_k̄` is `X_k̄ ⟶ X̄_k̄`. -/
@[reassoc (attr := simp)]
public lemma geometricSmoothModelImmersion_snd :
    geometricSmoothModelImmersion f j kbar ≫ pullback.snd _ _ =
      compactificationFieldBaseChangeImmersion f j kbar :=
  pullback.lift_snd _ _ _

/-- **`X_k̄ = X_{k'} ×_{C'} (C' ×_{X̄_{k'}} X̄_k̄)`**. -/
public theorem isPullback_geometricSmoothModelImmersion_fst :
    IsPullback (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar f)
      (geometricSmoothModelImmersion f j kbar) (perfectClosureSmoothModel f j kbar).j
      (pullback.fst (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)) := by
  refine IsPullback.of_bot ?_ (geometricSmoothModelImmersion_fst f j kbar).symm
    (IsPullback.of_hasPullback _ _)
  rw [geometricSmoothModelImmersion_snd, (perfectClosureSmoothModel f j kbar).w,
    Category.id_comp]
  exact isPullback_fieldTowerBaseChangeMap_compactification (perfectClosure k kbar) kbar f j

/-- `X_k̄ ⟶ C' ×_{X̄_{k'}} X̄_k̄` is an open immersion. -/
instance : IsOpenImmersion (geometricSmoothModelImmersion f j kbar) :=
  MorphismProperty.of_isPullback (isPullback_geometricSmoothModelImmersion_fst f j kbar)
    inferInstance

/-- **`X_k̄ = (C' ×_{X̄_{k'}} X̄_k̄) ×_{X̄_k̄} X_k̄`**. -/
public theorem isPullback_geometricSmoothModelImmersion :
    IsPullback (geometricSmoothModelImmersion f j kbar) (𝟙 _)
      (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase))
      (compactificationFieldBaseChangeImmersion f j kbar) := by
  refine IsPullback.of_right ?_ (by rw [geometricSmoothModelImmersion_snd, Category.id_comp])
    (IsPullback.of_hasPullback _ _)
  rw [geometricSmoothModelImmersion_fst,
    compactificationFieldBaseChangeImmersion_comp_fieldTowerBaseChangeMap]
  exact (IsPullback.id_vert _).paste_horiz (perfectClosureSmoothModel f j kbar).isPullback

/-- **`C' ×_{X̄_{k'}} X̄_k̄ = C' ×_{k'} k̄`**: the model over `k̄` is the base change of `C'`
along `Spec k̄ ⟶ Spec k'`. -/
public theorem isPullback_geometricSmoothModel_q :
    IsPullback
      (pullback.fst (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase))
      (pullback.snd (perfectClosureSmoothModel f j kbar).fb
          (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
        pullback.snd j.toBase (specAlgebraMap k kbar))
      (perfectClosureSmoothModel f j kbar).q (specAlgebraMap (perfectClosure k kbar) kbar) := by
  rw [← (perfectClosureSmoothModel f j kbar).hq]
  exact (IsPullback.of_hasPullback _ _).paste_vert
    (isPullback_fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)

/-- `C' ×_{X̄_{k'}} X̄_k̄` is smooth over `k̄`. -/
instance smooth_geometricSmoothModel_q :
    Smooth (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) :=
  MorphismProperty.of_isPullback (isPullback_geometricSmoothModel_q f j kbar) inferInstance

/-- `C' ×_{X̄_{k'}} X̄_k̄` is proper over `k̄`. -/
instance isProper_geometricSmoothModel_q :
    IsProper (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) :=
  MorphismProperty.of_isPullback (isPullback_geometricSmoothModel_q f j kbar) inferInstance

/-- `C' ×_{X̄_{k'}} X̄_k̄` is smooth of relative dimension `1` over `k̄`. -/
instance smoothOfRelativeDimension_geometricSmoothModel_q :
    SmoothOfRelativeDimension 1 (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (isPullback_geometricSmoothModel_q f j kbar) inferInstance

/-- The image of the first projection of a cartesian square is the preimage of the image of the
opposite side. -/
private theorem range_base_fst_of_isPullback {P A B C : Scheme.{u}} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) :
    Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.2 h.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst]

/-- The open `X_k̄` is dense in `C' ×_{X̄_{k'}} X̄_k̄`. -/
public lemma dense_range_geometricSmoothModelImmersion :
    Dense (Set.range (geometricSmoothModelImmersion f j kbar).base) := by
  have : UniversallyOpen (pullback.fst (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)) :=
    MorphismProperty.of_isPullback (isPullback_geometricSmoothModel_q f j kbar).flip
      inferInstance
  have h := isPullback_geometricSmoothModelImmersion_fst f j kbar
  rw [range_base_fst_of_isPullback h.flip]
  exact (perfectClosureSmoothModel f j kbar).j.denseRange.preimage
    (pullback.fst (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)).isOpenMap

/-- `C' ×_{X̄_{k'}} X̄_k̄` is connected. -/
instance connectedSpace_geometricSmoothModel :
    ConnectedSpace (pullback (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) : Scheme.{u}) := by
  rw [connectedSpace_iff_univ, ← (dense_range_geometricSmoothModelImmersion f j kbar).closure_eq]
  exact (isConnected_range (geometricSmoothModelImmersion f j kbar).continuous).closure

/-- `C' ×_{X̄_{k'}} X̄_k̄` is integral. -/
instance isIntegral_geometricSmoothModel :
    IsIntegral (pullback (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)) :=
  Stacks.Chow.isIntegral_of_connectedSpace_of_smooth
    (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar))

/-- **The smooth projective model `C` of the geometric curve `X_k̄`**, over the base change
`X̄_k̄` of the compactification: a smooth proper curve over `k̄` with an open immersion
`j_C : X_k̄ ⟶ C` whose complement is a finite set of closed points, and a finite morphism
`f̄ : C ⟶ X̄_k̄` extending `j'`, with `X_k̄ = C ×_{X̄_k̄} X_k̄`.  It is the base change
`C = C' ×_{k'} k̄ = C' ×_{X̄_{k'}} X̄_k̄` of the smooth projective model `C'` of `X_{k'}` over the
perfect closure `k'` of `k` in `k̄` (`Stacks.EtaleCohomology.perfectClosureSmoothModel`), so that
`id_{C'} × Spec σ` acts on it for every `σ ∈ Aut_k(k̄)`. -/
public def geometricSmoothModel :
    CoverCompactification kbar (pullback.snd j.toBase (specAlgebraMap k kbar))
      (compactificationFieldBaseChangeImmersion f j kbar)
      (𝟙 (pullback f (specAlgebraMap k kbar))) :=
  haveI hcurve : IsCurve kbar (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) :=
    { toIsIntegral := inferInstance
      topologicalKrullDim_eq_one := by
        simpa using topologicalKrullDim_eq_of_smoothOfRelativeDimension
          (pullback.snd (perfectClosureSmoothModel f j kbar).fb
            (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
          pullback.snd j.toBase (specAlgebraMap k kbar)) 1 }
  haveI : IsLocallyNoetherian (pullback (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar))
  haveI : CompactSpace (pullback (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar))
  haveI : IsNoetherian (pullback (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)) := ⟨⟩
  have hcompl := Stacks.CurveProjectiveCompletion.finite_compl_of_genericPoints_subset
    (geometricSmoothModelImmersion f j kbar).isOpenEmbedding.isOpen_range
    (IsCurve.topologicalKrullDim_eq_one (k := kbar)
      (pullback.snd (perfectClosureSmoothModel f j kbar).fb
          (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
        pullback.snd j.toBase (specAlgebraMap k kbar))).le
    (fun _ hx => TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense
      (geometricSmoothModelImmersion f j kbar).isOpenEmbedding.isOpen_range
      (dense_range_geometricSmoothModelImmersion f j kbar) hx)
  { Vb := pullback (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)
    q := pullback.snd (perfectClosureSmoothModel f j kbar).fb
        (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)
    j := geometricSmoothModelImmersion f j kbar
    isOpenImmersion := inferInstance
    fb := pullback.snd _ _
    w := by rw [geometricSmoothModelImmersion_snd, Category.id_comp]
    hq := rfl
    isCurve := hcurve
    smooth := inferInstance
    isProper := inferInstance
    isFinite := MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) inferInstance
    isPullback := isPullback_geometricSmoothModelImmersion f j kbar
    finite_compl := hcompl.1
    isClosed_compl := hcompl.2 }

/-- The finite morphism `f̄ : C ⟶ X̄_k̄` is the second projection of `C' ×_{X̄_{k'}} X̄_k̄`. -/
public lemma geometricSmoothModel_fb :
    (geometricSmoothModel f j kbar).fb = pullback.snd (perfectClosureSmoothModel f j kbar).fb
      (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase) :=
  rfl

/-- The open immersion `j_C : X_k̄ ⟶ C`. -/
public lemma geometricSmoothModel_j :
    (geometricSmoothModel f j kbar).j = geometricSmoothModelImmersion f j kbar :=
  rfl

/-- The structure morphism of `C` is `f̄` followed by the structure morphism of `X̄_k̄`. -/
public lemma geometricSmoothModel_q :
    (geometricSmoothModel f j kbar).q = (geometricSmoothModel f j kbar).fb ≫
      pullback.snd j.toBase (specAlgebraMap k kbar) :=
  rfl

/-- The projection `C = C' ×_{X̄_{k'}} X̄_k̄ ⟶ C'`. -/
public def geometricSmoothModelFst :
    (geometricSmoothModel f j kbar).Vb ⟶ (perfectClosureSmoothModel f j kbar).Vb :=
  pullback.fst (perfectClosureSmoothModel f j kbar).fb
    (fieldTowerBaseChangeMap (perfectClosure k kbar) kbar j.toBase)

/-- Morphisms into `C = C' ×_{X̄_{k'}} X̄_k̄` agree when they agree after the two projections. -/
public lemma geometricSmoothModel_hom_ext {Z : Scheme.{u}}
    {a b : Z ⟶ (geometricSmoothModel f j kbar).Vb}
    (h₁ : a ≫ geometricSmoothModelFst f j kbar = b ≫ geometricSmoothModelFst f j kbar)
    (h₂ : a ≫ (geometricSmoothModel f j kbar).fb = b ≫ (geometricSmoothModel f j kbar).fb) :
    a = b :=
  pullback.hom_ext h₁ h₂

/-- `j_C : X_k̄ ⟶ C` followed by `C ⟶ C'` is `X_k̄ ⟶ X_{k'} ⟶ C'`. -/
@[reassoc]
public lemma geometricSmoothModel_j_fst :
    (geometricSmoothModel f j kbar).j ≫ geometricSmoothModelFst f j kbar =
      fieldTowerBaseChangeMap (perfectClosure k kbar) kbar f ≫
        (perfectClosureSmoothModel f j kbar).j :=
  pullback.lift_fst _ _ _

/-- `f̄ ∘ j_C` is the base change `X_k̄ ⟶ X̄_k̄` of the compactification. -/
@[reassoc]
public lemma geometricSmoothModel_j_fb :
    (geometricSmoothModel f j kbar).j ≫ (geometricSmoothModel f j kbar).fb =
      compactificationFieldBaseChangeImmersion f j kbar :=
  pullback.lift_snd _ _ _

/-- The image of `j_C : X_k̄ ⟶ C` is the preimage of `X_k̄` under `f̄ : C ⟶ X̄_k̄`. -/
public lemma range_geometricSmoothModel_j :
    Set.range (geometricSmoothModel f j kbar).j.base =
      (geometricSmoothModel f j kbar).fb.base ⁻¹'
        Set.range (compactificationFieldBaseChangeImmersion f j kbar).base :=
  range_base_fst_of_isPullback (geometricSmoothModel f j kbar).isPullback

variable (Λ : Type) [Ring Λ]

/-- **`j'_! G ≅ f̄_* j_{C!} G`** for a sheaf `G` of `Λ`-modules on `X_k̄`: extension by zero along
`j' : X_k̄ ⟶ X̄_k̄` is the direct image along the finite `f̄ : C ⟶ X̄_k̄` of the extension by zero
along `j_C : X_k̄ ⟶ C`. -/
public def extensionByZeroGeometricSmoothModelIso
    (G : EtaleModules.{u, 0} Λ (pullback f (specAlgebraMap k kbar))) :
    (etaleModuleExtensionByZero.{u, 0} Λ
        (compactificationFieldBaseChangeImmersion f j kbar)).obj G ≅
      (etaleModuleDirectImage.{u, 0} Λ (geometricSmoothModel f j kbar).fb).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj G) :=
  let C := geometricSmoothModel f j kbar
  let ι := openImmersionReducedComplementι (compactificationFieldBaseChangeImmersion f j kbar)
  haveI : IsIso (extensionByZeroIntegralDirectImageMap Λ
      (compactificationFieldBaseChangeImmersion f j kbar) C.j (𝟙 _) C.fb C.isPullback.flip G) := by
    refine isIso_extensionByZeroIntegralDirectImageMap Λ _ C.j (𝟙 _) C.fb C.isPullback.flip ι
      (by rw [range_openImmersionReducedComplementι, compl_compl]) (pullback.snd ι C.fb) ?_
      (pullback.fst ι C.fb)
      (IsPullback.of_hasPullback ι C.fb) G
    rw [Scheme.Pullback.range_snd, range_openImmersionReducedComplementι, Set.preimage_compl,
      compl_compl]
    exact range_geometricSmoothModel_j f j kbar
  (etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)).mapIso
      ((etaleModuleDirectImageIdIso Λ _).app G).symm ≪≫
    asIso (extensionByZeroIntegralDirectImageMap Λ
      (compactificationFieldBaseChangeImmersion f j kbar) C.j (𝟙 _) C.fb C.isPullback.flip G)

/-- **`H^i_c(X_k̄, F) ≅ H^i(C, j_{C!}(F|_{X_k̄}))`** for a sheaf `F` of `Λ`-modules on `X`: the
cohomology of Remark 03UI (2), through an arbitrary compactification of `X` over `k`, computed on
the smooth projective model `C` of `X_k̄`. -/
public def galoisCompactSupportSmoothModelIso (F : EtaleModules.{u, 0} Λ X) (i : ℤ) :
    galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) i ≅
      ((etaleModuleGlobalSections.{u, 0} Λ (geometricSmoothModel f j kbar).Vb).rightDerivedPlus
          i).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ (geometricSmoothModel f j kbar).j).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f (specAlgebraMap k kbar))).obj F)) :=
  galoisCompactSupportSingleIso f j kbar Λ F i ≪≫
    ((etaleModuleGlobalSections.{u, 0} Λ
        (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus i).mapIso
      ((etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ
        (isPullback_compactificationFieldBaseChange f j kbar)).app F).symm ≪≫
    ((etaleModuleGlobalSections.{u, 0} Λ
        (pullback j.toBase (specAlgebraMap k kbar))).rightDerivedPlus i).mapIso
      (extensionByZeroGeometricSmoothModelIso f j kbar Λ _) ≪≫
    integralDirectImageCohomologyIso Λ (geometricSmoothModel f j kbar).fb _ i

end SmoothModel

end Stacks.EtaleCohomology

end
