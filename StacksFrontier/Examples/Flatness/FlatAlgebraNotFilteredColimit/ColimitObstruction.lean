module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Basic.Countable.Defs
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Set.Countable
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.OfPrime
public import Mathlib.RingTheory.Trace.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.FiniteType.Basic

/-!
# Obstructions to writing an algebra as a filtered colimit

General facts used in `StacksFrontier.Examples.Flatness.FlatAlgebraNotFilteredColimit`: forgetful
functors from commutative algebras preserve the relevant colimits; a filtered colimit of
algebras each mapping to a nonzero finite free algebra of invertible rank is reduced, so a
nonreduced adic completion over a local ring with residue field of characteristic zero is the
colimit of no such diagram; and over a Henselian local ring, faithful flatness of a filtered
colimit passes to its finitely presented flat stages, which then map to nonzero finite free
algebras.

## References

* [Stacks Project, Tag 0ATF](https://stacks.math.columbia.edu/tag/0ATF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Examples.FlatAlgebraNotFilteredColimit

open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
open scoped RatFunc LaurentSeries

/-- An algebra-linear functional sends an extended ideal into the original ideal. -/
private lemma linearMap_mem_ideal_of_mem_map
    {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (f : S →ₗ[R] R) (I : Ideal R) {x : S}
    (hx : x ∈ I.map (algebraMap R S)) : f x ∈ I := by
  have hx' : x ∈ I • (⊤ : Submodule R S) := by simpa using hx
  have hf := Submodule.smul_top_le_comap_smul_top I f hx'
  simpa only [Submodule.mem_comap, Ideal.smul_eq_mul, Ideal.mul_top] using hf

/-- Trace contracts the scalar part of a nilpotent modulo an extended ideal. -/
private lemma mem_ideal_of_nilpotent_sub_algebraMap_mem
    {R S T : Type*} [CommRing R] [IsReduced R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Free R T]
    (g : S →ₐ[R] T) (hrank : IsUnit (Module.finrank R T : R))
    (I : Ideal R) {x : S} {a : R} (hx : IsNilpotent x)
    (hxa : x - algebraMap R S a ∈ I.map (algebraMap R S)) : a ∈ I := by
  nontriviality R
  have ht := linearMap_mem_ideal_of_mem_map
    ((Algebra.trace R T).comp g.toLinearMap) I hxa
  have hxtrace : Algebra.trace R T (g x) = 0 :=
    (Algebra.isNilpotent_trace_of_isNilpotent (hx.map g)).eq_zero
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_sub, g.commutes,
    hxtrace, Algebra.trace_algebraMap, nsmul_eq_mul, zero_sub] at ht
  have hmul : (Module.finrank R T : R) * a ∈ I := by simpa using I.neg_mem ht
  obtain ⟨d, hd⟩ := hrank
  rw [← hd] at hmul
  simpa using I.mul_mem_left (↑d⁻¹) hmul

/-- Forgetting the algebra structure preserves connected colimits. -/
lemma preservesColimitsOfShape_forget₂_commAlgCat
    (R : Type u) [CommRing R] (J : Type v) [Category J] [IsConnected J] :
    PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) := by
  change PreservesColimitsOfShape J
    ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R))
  infer_instance

/-- The ring forgetful functor preserves filtered colimits indexed in a smaller universe. -/
lemma preservesColimitsOfShape_forget_commRingCat
    (J : Type v) [SmallCategory J] [IsFiltered J] [UnivLE.{v, u}] :
    PreservesColimitsOfShape J (forget CommRingCat.{u}) := by
  have : PreservesFilteredColimitsOfSize.{v, v} (forget CommRingCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE (forget CommRingCat.{u})
  infer_instance

/-- The legs of a cocone are compatible with the maps of the diagram. -/
private lemma cocone_app_map {R : Type*} [CommRing R]
    {J : Type v} [Category J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) {i j : J} (f : i ⟶ j) (x : F.obj i) :
    (c.ι.app j).hom ((F.map f).hom x) = (c.ι.app i).hom x :=
  congrArg (fun h => CommAlgCat.Hom.hom h x) (c.w f)

/-- Nilpotency and a polynomial congruence in a filtered colimit hold at a common stage. -/
private lemma exists_nilpotent_approximation
    {R : Type*} [CommRing R] {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [PreservesColimit F (forget (CommAlgCat.{u} R))]
    {c : Cocone F} (hc : IsColimit c) {x y : c.pt} (hx : IsNilpotent x)
    (a t : R) (n : ℕ)
    (hxy : x = algebraMap R c.pt a + algebraMap R c.pt t ^ n * y) :
    ∃ (i : J) (z w : F.obj i), IsNilpotent z ∧ (c.ι.app i).hom z = x ∧
      z = algebraMap R (F.obj i) a + algebraMap R (F.obj i) t ^ n * w := by
  have hc' := isColimitOfPreserves (forget (CommAlgCat.{u} R)) hc
  obtain ⟨i, z, w, hz, hw⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc' x y
  change F.obj i at z w
  change (c.ι.app i).hom z = x at hz
  change (c.ι.app i).hom w = y at hw
  obtain ⟨m, hm⟩ := hx
  have hm' : (c.ι.app i).hom (z ^ m) = (c.ι.app i).hom 0 := by
    simpa only [map_pow, map_zero, hz] using hm
  obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' (z ^ m) (0 : F.obj i)).mp hm'
  change (F.map f).hom (z ^ m) = (F.map f).hom 0 at hf
  have hnil : IsNilpotent ((F.map f).hom z) := by
    refine ⟨m, ?_⟩
    simpa only [map_pow, map_zero] using hf
  have heq : (c.ι.app j).hom ((F.map f).hom z) =
      (c.ι.app j).hom (algebraMap R (F.obj j) a +
        algebraMap R (F.obj j) t ^ n * (F.map f).hom w) := by
    simp only [map_add, map_mul, map_pow, AlgHom.commutes, cocone_app_map, hz, hw]
    exact hxy
  obtain ⟨k, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc'
    ((F.map f).hom z) (algebraMap R (F.obj j) a +
        algebraMap R (F.obj j) t ^ n * (F.map f).hom w)).mp heq
  change (F.map g).hom ((F.map f).hom z) = (F.map g).hom
    (algebraMap R (F.obj j) a + algebraMap R (F.obj j) t ^ n * (F.map f).hom w) at hg
  refine ⟨k, (F.map g).hom ((F.map f).hom z),
    (F.map g).hom ((F.map f).hom w), hnil.map (F.map g).hom, ?_, ?_⟩
  · rw [cocone_app_map, cocone_app_map]
    exact hz
  · simpa only [map_add, map_mul, map_pow, AlgHom.commutes] using hg

/-- Trace and adic separatedness force nilpotents in the colimit to vanish. -/
private lemma isReduced_of_filtered_colimit_of_free_factorizations
    {R : Type*} [CommRing R] [IsReduced R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [PreservesColimit F (forget (CommAlgCat.{u} R))]
    {c : Cocone F} (hc : IsColimit c) (t : R)
    [IsHausdorff (Ideal.span {t}) c.pt]
    (happrox : ∀ (x : c.pt) (n : ℕ), ∃ (a : R) (y : c.pt),
      x = algebraMap R c.pt a + algebraMap R c.pt t ^ n * y)
    (hfree : ∀ i, ∃ T : CommAlgCat.{u} R, Module.Free R T ∧
      IsUnit (Module.finrank R T : R) ∧ Nonempty (F.obj i ⟶ T)) :
    IsReduced c.pt := by
  refine ⟨fun x hx => IsHausdorff.haus' (I := Ideal.span {t}) x fun n => ?_⟩
  obtain ⟨a, y, hxy⟩ := happrox x n
  obtain ⟨i, z, w, hz, hzx, hzw⟩ := exists_nilpotent_approximation F hc hx a t n hxy
  obtain ⟨T, hT, hrank, ⟨g⟩⟩ := hfree i
  let I : Ideal R := Ideal.span {t ^ n}
  have hzw' : z - algebraMap R (F.obj i) a ∈ I.map (algebraMap R (F.obj i)) := by
    rw [hzw, add_sub_cancel_left]
    change _ ∈ (Ideal.span {t ^ n}).map (algebraMap R (F.obj i))
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    exact Ideal.mem_span_singleton.mpr ⟨w, rfl⟩
  have ha : a ∈ I := mem_ideal_of_nilpotent_sub_algebraMap_mem g.hom hrank I hz hzw'
  have hzI : z ∈ I.map (algebraMap R (F.obj i)) := by
    simpa only [sub_add_cancel] using
      (I.map (algebraMap R (F.obj i))).add_mem hzw' (Ideal.mem_map_of_mem _ ha)
  have hxI := Ideal.mem_map_of_mem (c.ι.app i).hom.toRingHom hzI
  rw [Ideal.map_map] at hxI
  change (c.ι.app i).hom z ∈ I.map
    ((c.ι.app i).hom.toRingHom.comp (algebraMap R (F.obj i))) at hxI
  have hcomp : (c.ι.app i).hom.toRingHom.comp (algebraMap R (F.obj i)) =
      algebraMap R c.pt := by
    ext a
    exact (c.ι.app i).hom.commutes a
  rw [hcomp, hzx] at hxI
  change x ∈ (Ideal.span {t ^ n}).map (algebraMap R c.pt) at hxI
  simpa only [SModEq.zero, Ideal.smul_top_eq_map, Ideal.span_singleton_pow,
    Submodule.restrictScalars_mem] using hxI

/-- An element of a principal-ideal completion is a scalar modulo each power of the ideal. -/
private lemma adicCompletion_exists_eq_algebraMap_add_pow_mul
    {R : Type*} [CommRing R] (t : R)
    (x : AdicCompletion (Ideal.span {t}) R) (n : ℕ) :
    ∃ (a : R) (y : AdicCompletion (Ideal.span {t}) R),
      x = algebraMap R _ a + algebraMap R _ t ^ n * y := by
  let I : Ideal R := Ideal.span {t}
  obtain ⟨a, ha⟩ := (I ^ n • (⊤ : Submodule R R)).mkQ_surjective
    (AdicCompletion.eval I R n x)
  have hx : x - algebraMap R (AdicCompletion I R) a ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton t),
      LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply,
      AdicCompletion.eval_of, Algebra.algebraMap_self_apply, ha, sub_self]
  change x - algebraMap R _ a ∈
    Ideal.span {t} ^ n • (⊤ : Submodule R (AdicCompletion I R)) at hx
  rw [Ideal.smul_top_eq_map, Ideal.span_singleton_pow, Ideal.map_span,
    Set.image_singleton, map_pow] at hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  exact ⟨a, y, by simpa only [add_comm] using (sub_eq_iff_eq_add.mp hy)⟩

/-- A principal-ideal completion obtained by such approximation is reduced. -/
private lemma isReduced_adicCompletion_of_isColimit_of_free_factorizations
    {R : Type u} [CommRing R] [IsReduced R] (t : R)
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [PreservesColimit F (forget (CommAlgCat.{u} R))]
    {c : Cocone F} (hc : IsColimit c)
    (hpt : c.pt = CommAlgCat.of R (AdicCompletion (Ideal.span {t}) R))
    (hfree : ∀ i, ∃ T : CommAlgCat.{u} R, Module.Free R T ∧
      IsUnit (Module.finrank R T : R) ∧ Nonempty (F.obj i ⟶ T)) :
    IsReduced (AdicCompletion (Ideal.span {t}) R) := by
  rcases c with ⟨B, ι⟩
  change B = CommAlgCat.of R (AdicCompletion (Ideal.span {t}) R) at hpt
  subst B
  have := (AdicCompletion.isAdicComplete (M := R)
    (Submodule.fg_span_singleton t)).toIsHausdorff
  exact isReduced_of_filtered_colimit_of_free_factorizations F hc t
    (adicCompletion_exists_eq_algebraMap_add_pow_mul t) hfree

/-- Nonzero finite free algebras have invertible rank in residue characteristic zero. -/
private lemma isUnit_finrank_of_residue_charZero
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CharZero (IsLocalRing.ResidueField R)]
    [CommRing S] [Algebra R S] [Nontrivial S] [Module.Free R S] [Module.Finite R S] :
    IsUnit (Module.finrank R S : R) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  exact Nat.cast_ne_zero.mpr ((Module.finrank_pos_iff_of_free R S).mpr inferInstance).ne'

/-- A nonreduced completion obstructs approximation through nonzero finite free algebras. -/
lemma isEmpty_isColimit_of_not_isReduced_adicCompletion
    {R : Type u} [CommRing R] [IsLocalRing R] [IsReduced R]
    [CharZero (IsLocalRing.ResidueField R)] (t : R)
    (hnot : ¬ IsReduced (AdicCompletion (Ideal.span {t}) R))
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) [PreservesColimit F (forget (CommAlgCat.{u} R))]
    (c : Cocone F) (hpt : c.pt = CommAlgCat.of R (AdicCompletion (Ideal.span {t}) R))
    (hfree : ∀ i, ∃ T : CommAlgCat.{u} R, Module.Free R T ∧ Module.Finite R T ∧
      Nontrivial T ∧ Nonempty (F.obj i ⟶ T)) : IsEmpty (IsColimit c) := by
  refine ⟨fun hc => hnot
    (isReduced_adicCompletion_of_isColimit_of_free_factorizations t F hc hpt ?_)⟩
  intro i
  obtain ⟨T, hT, hfin, hne, hg⟩ := hfree i
  exact ⟨T, hT, isUnit_finrank_of_residue_charZero, hg⟩

/-- A flat algebra admitting an algebra map to a faithfully flat algebra is faithfully flat. -/
lemma faithfullyFlat_of_algHom_to_faithfullyFlat
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Module.Flat R S]
    [Module.FaithfullyFlat R T] (f : S →ₐ[R] T) :
    Module.FaithfullyFlat R S := by
  apply Module.FaithfullyFlat.of_comap_surjective
  intro P
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := T) P
  refine ⟨PrimeSpectrum.comap f.toRingHom Q, ?_⟩
  have hcomp : f.toRingHom.comp (algebraMap R S) = algebraMap R T := by
    ext r
    exact f.commutes r
  change PrimeSpectrum.comap (f.toRingHom.comp (algebraMap R S)) Q = P
  rw [hcomp]
  exact hQ

/-- Every stage mapping to a faithfully flat colimit vertex is faithfully flat. -/
lemma faithfullyFlat_stage_of_faithfullyFlat_cocone
    {R : Type u} [CommRing R] {J : Type v} [Category J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F)
    (T : CommAlgCat.{u} R) (hpt : c.pt = T)
    [Module.FaithfullyFlat R T] (i : J) [Module.Flat R (F.obj i)] :
    Module.FaithfullyFlat R (F.obj i) := by
  rcases c with ⟨B, ι⟩
  change B = T at hpt
  subst B
  exact faithfullyFlat_of_algHom_to_faithfullyFlat (T := T) (ι.app i).hom

/-- A finitely presented faithfully flat algebra over a Henselian local ring has a
nonzero finite free algebra quotient. -/
lemma exists_finite_free_factor_of_faithfullyFlat_finitePresentation
    {R S : Type u} [CommRing R] [HenselianLocalRing R]
    [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Algebra.FinitePresentation R S] :
    ∃ T : CommAlgCat.{u} R, Module.Free R T ∧ Module.Finite R T ∧
      Nontrivial T ∧ Nonempty (CommAlgCat.of R S ⟶ T) := by
  obtain ⟨S', _, _, _, _, hqf, hfaith, hfp⟩ :=
    Algebra.exists_quasiFinite_faithfullyFlat_finitePresentation (R := R) (S := S)
  have : Algebra.QuasiFinite R S' := hqf
  have : Module.FaithfullyFlat R S' := hfaith
  have : Algebra.FinitePresentation R S' := hfp
  obtain ⟨T, _, _, U, _, _, hfin, hU, ⟨e⟩⟩ :=
    exists_prod_finite_not_quasiFiniteAt R S'
  have : Algebra.QuasiFinite R (T × U) :=
    (Algebra.QuasiFinite.iff_of_algEquiv e).mp hqf
  have : Algebra.QuasiFinite R U :=
    Algebra.QuasiFinite.of_surjective_algHom (AlgHom.snd R T U)
      (by intro x; exact ⟨(0, x), rfl⟩)
  have hUclosed (q : PrimeSpectrum U)
      (hq : q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R)) : False := by
    have : Algebra.QuasiFiniteAt R q.asIdeal :=
      Algebra.QuasiFinite.of_isLocalization q.asIdeal.primeCompl
    exact hU q.asIdeal hq inferInstance
  have hnontrivial : Nontrivial T := by
    obtain ⟨qS, hqS⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := R) (B := S')
      (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R)
    let qProd : PrimeSpectrum (T × U) := PrimeSpectrum.comap e.symm.toRingHom qS
    have hqProdOver : qProd.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := by
      have hqSover : qS.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := by
        constructor
        change IsLocalRing.maximalIdeal R = qS.asIdeal.comap (algebraMap R S')
        exact (congrArg PrimeSpectrum.asIdeal hqS).symm
      constructor
      have h := hqSover.over
      have hcomp : e.symm.toRingHom.comp (algebraMap R (T × U)) =
          algebraMap R S' := by
        ext r
        exact e.symm.commutes r
      simpa only [qProd, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap,
        hcomp] using h
    rcases hsplit : PrimeSpectrum.primeSpectrumProd T U qProd with qT | qU
    · exact qT.nontrivial
    · have hqProd : qProd = (PrimeSpectrum.primeSpectrumProd T U).symm (.inr qU) := by
        apply (PrimeSpectrum.primeSpectrumProd T U).injective
        simp [hsplit]
      have hqU : qU.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := by
        constructor
        have h := hqProdOver.over
        rw [hqProd, PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal] at h
        rw [h]
        ext r
        simp [Ideal.mem_comap, Ideal.prod]
      exact False.elim (hUclosed qU hqU)
  have : Module.Finite R T := hfin
  have hflat : Module.Flat R T := by
    have : Module.Flat R S' := inferInstance
    have : Module.Flat R (T × U) := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
    exact Module.Flat.of_retract (LinearMap.inl R T U) (LinearMap.fst R T U)
      (by ext x; rfl)
  have : Module.Flat R T := hflat
  have : Module.Free R T := Module.free_of_flat_of_isLocalRing
  refine ⟨CommAlgCat.of R T, inferInstance, inferInstance, hnontrivial, ?_⟩
  exact ⟨CommAlgCat.ofHom ((AlgHom.fst R T U).comp e.toAlgHom |>.comp
    (IsScalarTower.toAlgHom R S S'))⟩

/-- The structure maps of a diagram of algebras, read as a cone under the base ring in
commutative rings. -/
private def constAlgebraMap {A : Type u} [CommRing A] {J : Type v} [SmallCategory J]
    (F : J ⥤ CommAlgCat.{u} A) :
    (Functor.const J).obj (CommRingCat.of A) ⟶
      F ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u} where
  app j := CommRingCat.ofHom (algebraMap A (F.obj j))
  naturality i j f := by
    ext r
    exact ((F.map f).hom.commutes r).symm

/-- A finitely presented algebra mapping to a filtered colimit of algebras already maps to
one of its stages. -/
lemma exists_stage_hom_of_finitePresentation {A : Type u} [CommRing A]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    [PreservesColimitsOfShape J (forget CommRingCat.{u})]
    (F : J ⥤ CommAlgCat.{u} A) {c : Cocone F} (hc : IsColimit c)
    (S : CommAlgCat.{u} A) [Algebra.FinitePresentation A S] (g : S ⟶ c.pt) :
    ∃ i : J, Nonempty (S ⟶ F.obj i) := by
  let G := forget₂ (CommAlgCat.{u} A) CommRingCat.{u}
  have : IsConnected J := IsFiltered.isConnected J
  have : PreservesColimitsOfShape J G := preservesColimitsOfShape_forget₂_commAlgCat A J
  obtain ⟨i, g', hg', -⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of A) (F ⋙ G) (constAlgebraMap F)
    (CommRingCat.ofHom (algebraMap A S)) (G.mapCocone c) (isColimitOfPreserves G hc)
    (by
      simpa only [CommRingCat.hom_ofHom] using
        RingHom.finitePresentation_algebraMap.mpr
          (inferInstance : Algebra.FinitePresentation A S))
    (G.map g) (fun i => by
      ext r
      change g.hom (algebraMap A S r) = (c.ι.app i).hom (algebraMap A (F.obj i) r)
      rw [g.hom.commutes, (c.ι.app i).hom.commutes]
      rfl)
  have h (r : A) : g'.hom (algebraMap A S r) = algebraMap A (F.obj i) r := by
    have hr := congrArg (fun k : CommRingCat.of A ⟶ (F ⋙ G).obj i => k.hom r) hg'
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, constAlgebraMap] at hr
    exact hr
  exact ⟨i, ⟨CommAlgCat.ofHom ⟨g'.hom, h⟩⟩⟩

end Stacks.Examples.FlatAlgebraNotFilteredColimit

end
