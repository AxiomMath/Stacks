module

public import StacksFrontier.RingTheory.AbsolutelyIntegrallyClosed.IntegralCover
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.ConstructiblePieces
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.CoverCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.Gabber.FourLemma
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveInverseImageFaithful
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.TorsionConstructibleSubsheaves
import StacksCore.Tactic.StacksAttribute

/-!
# Gabber's theorem for a henselian pair

Let `(A, I)` be a henselian pair, `X = Spec A` and `Z = Spec (A ⧸ I)`. For every torsion abelian
sheaf `F` on `X_étale` and every `q` the restriction map `H^q(X, F) → H^q(Z, F|_Z)` is bijective
([Stacks, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)).

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_henselianPair` — for a
  henselian pair `(A, I)` and a torsion sheaf `F` on `(Spec A)_étale`, restriction to
  `Spec (A ⧸ I)` is bijective on étale cohomology in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasExt_sheaf_smallEtale_succ

/-- For a surjective morphism of schemes the unit `F ⟶ f_* f^{-1} F` of abelian sheaves on the
small étale sites is a monomorphism. -/
theorem mono_etaleAbelianInverseImageDirectImageAdj_unit_of_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Surjective f] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app F) := by
  let U := forget AddCommGrpCat.{u + 1}
  have : U.PreservesLeftKanExtensions (smallEtaleBaseChange f).op :=
    preservesLeftKanExtensions_forget_smallEtaleBaseChange f
  have hcmp : IsIso (coefficientPullbackComparison (smallEtaleBaseChange f)
      Y.smallEtaleTopology X.smallEtaleTopology U F) := by
    rw [← coefficientPullbackTwoSquare_app]
    infer_instance
  have hcomp : Mono ((sheafCompose Y.smallEtaleTopology U).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange f)
        AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).unit.app F) ≫
        (coefficientPushforwardTwoSquare (smallEtaleBaseChange f)
          Y.smallEtaleTopology X.smallEtaleTopology U).natTrans.app
          ((Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange f)
            AddCommGrpCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj F)) := by
    rw [← coefficientPullbackComparison_unit (smallEtaleBaseChange f)
      Y.smallEtaleTopology X.smallEtaleTopology U F]
    have : Mono ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange f) (Type (u + 1)) Y.smallEtaleTopology
        X.smallEtaleTopology).unit.app ((sheafCompose Y.smallEtaleTopology U).obj F)) :=
      mono_smallEtaleUnit_of_surjective.{0, u} f ((sheafCompose Y.smallEtaleTopology U).obj F)
    exact mono_comp' this (@IsIso.mono_of_iso _ _ _ _ _ (Functor.map_isIso _ _))
  exact (sheafCompose Y.smallEtaleTopology U).mono_of_mono_map (@mono_of_mono _ _ _ _ _ _ _ hcomp)

/-- **A torsion sheaf on a quasi-compact quasi-separated scheme is a filtered colimit of
constructible sheaves** (Stacks 03SA (2)), read on Mathlib's small étale site. -/
@[sga "4½ Arcata 4.3.3" "more general"]
theorem exists_isColimit_isConstructibleOnEveryBigSite {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
      (D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ι : D ⟶ (Functor.const I).obj F), Nonempty (IsColimit (Cocone.mk F ι)) ∧
        ∀ j, IsConstructibleOnEveryBigSite (D.obj j) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  let e := SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}
  have : CompactSpace (B.obj X hX).obj := inferInstanceAs (CompactSpace X)
  have : QuasiSeparatedSpace (B.obj X hX).obj := inferInstanceAs (QuasiSeparatedSpace X)
  obtain ⟨I, hI, hfilt, D', ι', ⟨hc'⟩, hD'⟩ :=
    exists_isFilteredColimit_isConstructibleAbelianSheaf_of_qcqs B (B.obj X hX) (e.inverse.obj F)
      (torsionSheafProperty_sheafEquiv_inverse B X hX F hF)
  let c₂ : Cocone (D' ⋙ e.functor) :=
    { pt := F
      ι := (e.functor.mapCocone (Cocone.mk _ ι')).ι ≫ (Functor.const I).map (e.counit.app F) }
  have hc₂ : IsColimit c₂ := (isColimitOfPreserves e.functor hc').ofIsoColimit
    (Cocone.ext (e.counitIso.app F) (fun _ ↦ rfl))
  exact ⟨I, hI, hfilt, D' ⋙ e.functor, c₂.ι, ⟨hc₂⟩, fun j ↦
    IsConstructibleOnEveryBigSite.of_contains hX
      (isConstructibleAbelianSheaf_congr B (B.obj X hX) (e.unitIso.app (D'.obj j)) (hD' j))⟩

section Gabber

variable (A : Type u) [CommRing A]

open Stacks.AbsolutelyIntegrallyClosed in
/-- The absolutely integrally closed integral cover `Spec (IntegralCover A) ⟶ Spec A` is
surjective. -/
instance surjective_specMap_integralCoverMap :
    Surjective (Spec.map (CommRingCat.ofHom (integralCoverMap A))) := by
  refine ⟨fun x => ?_⟩
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime (x : PrimeSpectrum A)
  obtain ⟨Q, hQ, hQc⟩ := exists_comap_integralCoverMap_eq A x.asIdeal
  let z : Spec (.of (IntegralCover A)) := (⟨Q, hQ⟩ : PrimeSpectrum (IntegralCover A))
  exact ⟨z, PrimeSpectrum.ext (R := A) ((specMap_base_asIdeal (integralCoverMap A) z).trans hQc)⟩

variable (I : Ideal A) (hI : HenselianPair A I)
include hI

open Stacks.AbsolutelyIntegrallyClosed in
/-- **Gabber's theorem for `f_* f^{-1} F` with `F` constructible**, `f` the absolutely integrally
closed integral cover of `Spec A`. -/
theorem bijective_etaleCohomologyRestrictionMap_directImage_inverseImage_integralCover
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleOnEveryBigSite F) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      ((etaleAbelianDirectImage.{u, 0} (Spec.map (CommRingCat.ofHom (integralCoverMap A)))).obj
        ((etaleAbelianInverseImage.{u, 0} (Spec.map (CommRingCat.ofHom (integralCoverMap A)))).obj
          F)) q) := by
  let : Algebra A (IntegralCover A) := (integralCoverMap A).toAlgebra
  have : Algebra.IsIntegral A (IntegralCover A) := ⟨integralCoverMap_isIntegral A⟩
  have hC := isAbsolutelyIntegrallyClosed_integralCover A
  obtain ⟨pieces, hgood, hcover⟩ := exists_goodPieces_of_isConstructibleOnEveryBigSite _ hC
    (hF.etaleAbelianInverseImage (Spec.map (CommRingCat.ofHom (integralCoverMap A))))
  exact bijective_etaleCohomologyRestrictionMap_directImage_of_cover A I hI (IntegralCover A) hC _
    pieces hcover hgood q

omit hI in
open Stacks.AbsolutelyIntegrallyClosed in
/-- The quotient of the unit `F ⟶ f_* f^{-1} F` of a constructible sheaf, `f` the absolutely
integrally closed cover, is torsion. -/
theorem torsionSheafProperty_cokernel_unit_integralCover
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleOnEveryBigSite F) :
    Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology
      (cokernel ((etaleAbelianInverseImageDirectImageAdj.{u, 0}
        (Spec.map (CommRingCat.ofHom (integralCoverMap A)))).unit.app F)) := by
  let f := Spec.map (CommRingCat.ofHom (integralCoverMap A))
  obtain ⟨n, hn, h⟩ := hF.exists_nsmul_id_eq_zero
  have : (etaleAbelianDirectImage.{u, 0} f).IsRightAdjoint :=
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).isRightAdjoint
  have : (etaleAbelianDirectImage.{u, 0} f).Additive :=
    Functor.additive_of_preserves_binary_products _
  let η := (etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app F
  refine torsionSheafProperty_of_nsmul_id_eq_zero _ n hn ?_
  rw [← cancel_epi (cokernel.π η), Preadditive.comp_nsmul, Category.comp_id, comp_zero,
    ← Category.id_comp (cokernel.π η), ← Preadditive.nsmul_comp]
  change (n • 𝟙 ((etaleAbelianInverseImage.{u, 0} f ⋙ etaleAbelianDirectImage.{u, 0} f).obj F)) ≫
    cokernel.π η = 0
  rw [nsmul_id_eq_zero_map (etaleAbelianInverseImage.{u, 0} f ⋙
    etaleAbelianDirectImage.{u, 0} f) h, zero_comp]

open Stacks.AbsolutelyIntegrallyClosed in
/-- A constructible sheaf `F` sits in a short exact sequence `0 → F → f_* f^{-1} F → Q → 0`, `f`
the absolutely integrally closed integral cover, whose middle term has bijective restriction maps
in every degree and whose quotient is torsion. -/
theorem exists_shortExact_unit_integralCover
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleOnEveryBigSite F) :
    ∃ S : ShortComplex (Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      S.ShortExact ∧ S.X₁ = F ∧ (∀ q, Function.Bijective
        (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) S.X₂ q)) ∧
      Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology S.X₃ := by
  let η := (etaleAbelianInverseImageDirectImageAdj.{u, 0}
    (Spec.map (CommRingCat.ofHom (integralCoverMap A)))).unit.app F
  have : Mono η := mono_etaleAbelianInverseImageDirectImageAdj_unit_of_surjective _ F
  exact ⟨ShortComplex.mk η (cokernel.π η) (cokernel.condition η),
    { exact := ShortComplex.exact_cokernel η }, rfl,
    bijective_etaleCohomologyRestrictionMap_directImage_inverseImage_integralCover A I hI F hF,
    torsionSheafProperty_cokernel_unit_integralCover A F hF⟩

open Stacks.AbsolutelyIntegrallyClosed in
/-- **Gabber's theorem.** Let `(A, I)` be a henselian pair, `X = Spec A` and
`Z = Spec (A ⧸ I)`. For every torsion abelian sheaf `F` on `X_étale` and every `q ≥ 0` the
restriction map `H^q_étale(X, F) → H^q_étale(Z, F|_Z)` is bijective.

Torsion is the local condition of Stacks 0DD7, `Stacks.Torsion.torsionSheafProperty`: every
section is annihilated by a positive integer after restriction along a covering. Cohomology is
Mathlib's `CategoryTheory.Sheaf.H`, the restricted sheaf is the étale inverse image along
`Spec (A ⧸ I) ⟶ Spec A`, and the map is
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`. -/
@[stacks 09ZI "Gabber's theorem: for a henselian pair (A, I), every torsion abelian sheaf F on
the small étale site of X = Spec A and every q, restriction H^q(X, F) → H^q(Z, F|_Z) to
Z = Spec (A/I) is bijective", sga "4 XII 6.13" "more general"]
theorem etaleCohomologyRestrictionMap_bijective_of_henselianPair
    (F : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology F) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1}
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q) := by
  let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  induction q generalizing F with
  | zero => exact bijective_etaleCohomologyRestrictionMap_zero_of_henselianPair A I hI F
  | succ q ih =>
    have hinjC : ∀ F, IsConstructibleOnEveryBigSite F →
        Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F (q + 1)) := by
      intro F hFc
      obtain ⟨S, hS, rfl, hgood, hQ⟩ := exists_shortExact_unit_integralCover A I hI F hFc
      exact injective_etaleCohomologyRestrictionMap_X₁_of_shortExact i hS q (hgood (q + 1)).1
        (hgood q).2 (ih _ hQ).1
    have hinj : ∀ F, Stacks.Torsion.torsionSheafProperty (Spec (.of A)).smallEtaleTopology F →
        Function.Injective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F (q + 1)) := by
      intro F hF
      obtain ⟨J, _, _, _, _, ⟨hc⟩, hD⟩ := exists_isColimit_isConstructibleOnEveryBigSite F hF
      exact injective_etaleCohomologyRestrictionMap_of_isColimit hc i (q + 1)
        fun j => hinjC _ (hD j)
    have hsurjC : ∀ F, IsConstructibleOnEveryBigSite F →
        Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F (q + 1)) := by
      intro F hFc
      obtain ⟨S, hS, rfl, hgood, hQ⟩ := exists_shortExact_unit_integralCover A I hI F hFc
      exact surjective_etaleCohomologyRestrictionMap_X₁_of_injective_X₃ i hS q (hgood (q + 1)).2
        (hinj _ hQ) (ih _ hQ).2
    obtain ⟨J, _, _, _, _, ⟨hc⟩, hD⟩ := exists_isColimit_isConstructibleOnEveryBigSite F hF
    exact bijective_etaleCohomologyRestrictionMap_of_isColimit hc i (q + 1)
      fun j => ⟨hinjC _ (hD j), hsurjC _ (hD j)⟩

end Gabber

end Stacks.EtaleCohomology
