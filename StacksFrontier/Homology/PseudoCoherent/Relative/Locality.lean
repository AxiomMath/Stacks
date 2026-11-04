module

public import Mathlib.RingTheory.Localization.Finiteness
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.Local
public import StacksFrontier.Homology.PseudoCoherent.Relative.Localization
public import StacksFrontier.RingTheory.PseudoCoherentMap.Absolute

@[expose] public section

/-!
# Relative pseudo-coherence is local on a finite principal cover

Let `A` be a finite-type algebra over a commutative ring `R` and let finitely many elements of
`A` generate the unit ideal. An object of `D(A)` is `m`-pseudo-coherent relative to `R`, and
pseudo-coherent relative to `R`, exactly when each of its localizations away from one of those
elements is.

## Main results

* `PseudoCoherence.relativelyPseudoCoherent_iff_localizationAway_of_span_eq_top` (Stacks 067E).

## Implementation notes

The localization of the object is `PseudoCoherence.localizationAwayFunctorAux`, derived extension
of scalars to `Localization.Away f`; the finite list of the source is a family indexed by a
finite type, and the source's two "respectively" equivalences are one conjunction.

Both directions are read off a single polynomial presentation `R[x_1, …, x_n] ↠ A`, which tag
065H licenses. The cover of `A` is lifted to a cover of the polynomial algebra by choosing a
preimage of each element and adjoining one further element of the kernel; the extra principal
open has zero image in `A`, so the restricted complex vanishes there and contributes nothing.
Over the polynomial algebra the statement is the absolute descent of tag 066D. In the other
direction each localization is handled by tag 0679, whose base change is along the localization
of the presentation.

Tags 064Q, 064T, 064Z, 0650 and 066D belong to Chapter 15 sections 65 and 66, and are supplied
in `StacksFrontier/Algebra/Homology/PseudoCoherent.lean` and
`StacksFrontier/Homology/PseudoCoherent/{Module,ChangeOfRings,Basic,Local}.lean`; tag 064H is in
`StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean`. Tags 065H, 065I and 0679 are this
cluster's, in `Relative/Presentation.lean`, `Relative/Defs.lean` and `Relative/Localization.lean`.

## References

* [The Stacks Project, Lemma 15.82.9 (067E)](https://stacks.math.columbia.edu/tag/067E)
-/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-- A finite principal cover lifts along a surjection after adjoining one kernel element. -/
private lemma exists_lift_span_eq_top
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    (p : R →+* A) (hp : Function.Surjective p)
    {ι : Type*} [Finite ι] (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤) :
    ∃ (g : ι → R) (h : R),
      (∀ i, p (g i) = f i) ∧ p h = 0 ∧
      Ideal.span (Set.range (Option.elim · h g)) = ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose g hg using fun i ↦ hp (f i)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    (show (1 : A) ∈ Ideal.span (Set.range f) by rw [hf]; trivial)
  choose b hb using fun i ↦ hp (a i)
  refine ⟨g, 1 - ∑ i, b i * g i, hg, ?_, ?_⟩
  · simp only [map_sub, map_one, map_sum, map_mul, hg, hb, ha, sub_self]
  · rw [Ideal.eq_top_iff_one]
    let I := Ideal.span (Set.range (Option.elim · (1 - ∑ i, b i * g i) g))
    have hh : 1 - ∑ i, b i * g i ∈ I := Ideal.subset_span ⟨none, rfl⟩
    have hs : ∑ i, b i * g i ∈ I := I.sum_mem
      (fun i _ ↦ I.mul_mem_left (b i) (Ideal.subset_span ⟨some i, rfl⟩))
    simpa using I.add_mem hh hs

private lemma localizationExtension_additive {R : Type u} [CommRing R] (g : R) :
    (ModuleCat.extendScalars.{u, u, u}
      (algebraMap R (Localization.Away g))).Additive :=
  extendScalars_additive.{u, u} _

private lemma localizationExtension_preservesFiniteLimits {R : Type u} [CommRing R] (g : R) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (algebraMap R (Localization.Away g))) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.Away g) (Submonoid.powers g)))

private lemma localizationExtension_preservesFiniteColimits {R : Type u} [CommRing R] (g : R) :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u}
      (algebraMap R (Localization.Away g))) := by
  let : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u}
      (algebraMap R (Localization.Away g))) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap R (Localization.Away g))).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

private noncomputable def localizationAwayIsoTotalDerivedExtensionScalars
    {A : Type u} [CommRing A] (f : A) :
    localizationAwayFunctorAux.{u, u} f ≅
      (derivedExtensionScalarsGeneral.{u, u, u}
        (algebraMap A (Localization.Away f))).functor := by
  let F := ModuleCat.extendScalars.{u, u, u}
    (algebraMap A (Localization.Away f))
  letI : F.Additive := localizationExtension_additive f
  letI : PreservesFiniteLimits F := localizationExtension_preservesFiniteLimits f
  letI : PreservesFiniteColimits F := localizationExtension_preservesFiniteColimits f
  let D := derivedExtensionScalarsGeneral.{u, u, u}
    (algebraMap A (Localization.Away f))
  exact @Functor.leftDerivedUnique _ _ _ _ _ _ D.functor F.mapDerivedCategory _ _
    F.mapDerivedCategoryFactors.hom D.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    inferInstance (Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors)
    D.isLeftDerived

private lemma localizationAway_preserves_relativelyPseudoCoherentFrom
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    (f : A) (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m) :
    let : Algebra.FiniteType A (Localization.Away f) :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) _
    let : Algebra.FiniteType R (Localization.Away f) :=
      Algebra.FiniteType.trans (R := R) (S := A)
        (A := Localization.Away f) inferInstance inferInstance
    IsRelativelyPseudoCoherentFrom (R := R)
      ((localizationAwayFunctorAux.{u, u} f).obj K) m := by
  let : IsLocalization.Away (1 : R) R :=
    IsLocalization.away_of_isUnit_of_bijective R isUnit_one Function.bijective_id
  let : Algebra.FiniteType A (Localization.Away f) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) _
  let : Algebra.FiniteType R (Localization.Away f) :=
    Algebra.FiniteType.trans (R := R) (S := A)
      (A := Localization.Away f) inferInstance inferInstance
  have h := (localization_preserves_relativePseudoCoherent
    (R := R) (Rf := R) (Ag := Localization.Away f) (1 : R) f K m).1 hK
  exact (PseudoCoherence.isRelativelyPseudoCoherentFrom_iff_of_iso
    ((localizationAwayIsoTotalDerivedExtensionScalars f).app K) m).mpr h

/-- Ring equivalences preserve finite free approximations in any module universe. -/
lemma isPseudoCoherentFrom_restrictScalars_of_ringEquiv
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (K : DerivedCategory (ModuleCat.{u} S)) (m : ℤ)
    (hK : IsPseudoCoherentFrom K m) :
    IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategory.obj K) m := by
  refine (exactFunctor_preserves_pseudoCoherent
    (ModuleCat.restrictScalars.{u} e.toRingHom) ?_ K).1 m hK
  intro M hfinite hfree
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  let j : M ≃ₛₗ[e.symm.toRingHom] (ModuleCat.restrictScalars e.toRingHom).obj M :=
    { __ := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun s a ↦ by
        show s • a = e (e.symm s) • a
        rw [e.apply_symm_apply] }
  exact ⟨Module.Finite.of_surjective j.toLinearMap j.surjective, Module.Free.of_equiv j⟩

private lemma isPseudoCoherentFrom_restrictScalars_comp_ringEquiv
    {R : Type u} {S : Type u} {T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : S →+* T) (K : DerivedCategory (ModuleCat.{u} T)) (m : ℤ) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} (f.comp e.toRingHom)).mapDerivedCategory.obj K) m :=
  (isPseudoCoherentFrom_restrictScalars_ringEquiv e _ m).trans
    (isPseudoCoherentFrom_restrictScalars_comp_iff e.toRingHom f K m).symm

private lemma polynomial_C_mul_X_sub_one_regular
    {R : Type u} [CommRing R] (r : R) :
    ∀ p : Polynomial R, (Polynomial.C r * Polynomial.X - 1) * p = 0 → p = 0 := by
  have h : Polynomial.C r * Polynomial.X - 1 ∈ nonZeroDivisors (Polynomial R) :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by
      simpa using (isUnit_neg_one : IsUnit (-1 : R)).mem_nonZeroDivisors)
  exact fun p hp ↦ h.1 p hp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def localizationAwayHomologyIso {R : Type u} [CommRing R] (g : R)
    (K : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away g)) n).obj
        ((localizationAwayFunctorAux.{u, u} g).obj K) ≅
      ModuleCat.of (Localization.Away g)
        (LocalizedModule (Submonoid.powers g)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K)) := by
  let F := ModuleCat.extendScalars.{u, u, u}
    (algebraMap R (Localization.Away g))
  let : F.Additive := localizationExtension_additive g
  let : PreservesFiniteLimits F := localizationExtension_preservesFiniteLimits g
  let : PreservesFiniteColimits F := localizationExtension_preservesFiniteColimits g
  exact (mapDerivedCategoryHomologyIso F n).app K ≪≫
    _root_.PseudoCoherence.extendScalarsAlgebraMapObjIso (S := Localization.Away g) _ ≪≫
    LinearEquiv.toModuleIso
      ((IsLocalizedModule.isBaseChange (Submonoid.powers g)
        (Localization.Away g)
        (LocalizedModule.mkLinearMap (Submonoid.powers g)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K))).equiv)

private lemma homology_isZero_iff_localizationAway
    {A : Type u} [CommRing A] {ι : Type*} [Finite ι]
    (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    (∀ i, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (Localization.Away (f i))) n).obj
        ((localizationAwayFunctorAux.{u, u} (f i)).obj K))) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K) := by
  simp_rw [(localizationAwayHomologyIso _ K n).isZero_iff,
    ModuleCat.isZero_iff_subsingleton]
  constructor
  · exact Module.subsingleton_of_localizationSpan_range f hf
  · intro h i
    have := h
    infer_instance

/-- Let `e : S ≃+* R` be a ring isomorphism compatible with the structure maps to `A`. If `K` is
`m`-pseudo-coherent relative to `R`, then it is `m`-pseudo-coherent relative to `S`. -/
lemma relativelyPseudoCoherentFrom_of_baseRingEquiv
    {R : Type u} {S : Type u} {A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] [Algebra.FiniteType R A] [Algebra.FiniteType S A]
    (e : S ≃+* R) (he : ∀ s, algebraMap S A s = algebraMap R A (e s))
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (h : IsRelativelyPseudoCoherentFrom (R := R) K m) :
    IsRelativelyPseudoCoherentFrom (R := S) K m := by
  intro n f hf
  let g : MvPolynomial (Fin n) R →ₐ[R] A :=
    { toRingHom := f.toRingHom.comp (MvPolynomial.map e.symm.toRingHom)
      commutes' := fun r ↦ by
        show f (MvPolynomial.map e.symm.toRingHom (MvPolynomial.C r)) = _
        rw [MvPolynomial.map_C]
        exact (f.commutes (e.symm r)).trans ((he (e.symm r)).trans (by simp)) }
  have hg : Function.Surjective g :=
    hf.comp (MvPolynomial.mapEquiv (Fin n) e.symm).surjective
  have hfg : f.toRingHom = g.toRingHom.comp (MvPolynomial.mapEquiv (Fin n) e).toRingHom := by
    ext a <;> simp [g]
  simpa only [← hfg] using (isPseudoCoherentFrom_restrictScalars_comp_ringEquiv
    (MvPolynomial.mapEquiv (Fin n) e) g.toRingHom K m).mp (h n g hg)

private lemma relativelyPseudoCoherentFrom_baseRingEquiv_iff
    {R : Type u} {S : Type u} {A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R A] [Algebra S A] [Algebra.FiniteType R A] [Algebra.FiniteType S A]
    (e : S ≃+* R) (he : ∀ s, algebraMap S A s = algebraMap R A (e s))
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      IsRelativelyPseudoCoherentFrom (R := S) K m := by
  refine ⟨relativelyPseudoCoherentFrom_of_baseRingEquiv e he K m,
    relativelyPseudoCoherentFrom_of_baseRingEquiv e.symm ?_ K m⟩
  intro r
  simpa using (he (e.symm r)).symm

private lemma isPseudoCoherentFrom_localizationAway_iff_restrictScalars_polynomial
    {R : Type u} [CommRing R] (r : R)
    (K : DerivedCategory (ModuleCat.{u} (Localization.Away r))) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔ IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u}
        ((Localization.awayEquivAdjoin r).symm.toRingHom.comp
          (AdjoinRoot.mk (Polynomial.C r * Polynomial.X - 1)))).mapDerivedCategory.obj K) m := by
  let p := Polynomial.C r * Polynomial.X - 1
  let e := (Localization.awayEquivAdjoin r).symm.toRingEquiv
  exact (isPseudoCoherentFrom_restrictScalars_ringEquiv e K m).trans
    ((isPseudoCoherentFrom_iff_restrictScalars (AdjoinRoot.mk p)
      (PrincipalResolution.isModulePseudoCoherent _ p (polynomial_C_mul_X_sub_one_regular r))
      _ m).trans (isPseudoCoherentFrom_restrictScalars_comp_iff
        (AdjoinRoot.mk p) e.toRingHom K m).symm)

private lemma isPseudoCoherentFrom_restrictScalars_localizationAway_of_relative
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    (n : ℕ) (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f)
    (g : MvPolynomial (Fin n) R)
    (L : DerivedCategory (ModuleCat.{u} (Localization.Away (f g)))) (m : ℤ)
    (hL : IsRelativelyPseudoCoherentFrom (R := R) L m) :
    IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u}
        (Localization.awayMap f.toRingHom g)).mapDerivedCategory.obj L)
      m := by
  let e := (MvPolynomial.finSuccEquiv R n).toRingEquiv
  let j := (Localization.awayEquivAdjoin g).symm.toRingHom.comp
    (AdjoinRoot.mk (Polynomial.C g * Polynomial.X - 1))
  let k := Localization.awayMap f.toRingHom g
  have hj (a : MvPolynomial (Fin n) R) :
      j (Polynomial.C a) = algebraMap _ (Localization.Away g) a := by
    show (Localization.awayEquivAdjoin g).symm (AdjoinRoot.of _ a) = _
    exact (Localization.awayEquivAdjoin g).symm.commutes a
  let b : MvPolynomial (Fin (n + 1)) R →ₐ[R] Localization.Away (f g) :=
    { toRingHom := (k.comp j).comp e.toRingHom
      commutes' := fun r ↦ by
        show k (j (e (MvPolynomial.C r))) = _
        rw [show e (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) from
          (MvPolynomial.finSuccEquiv R n).commutes r, hj]
        show IsLocalization.map _ _ _ (algebraMap _ _ (MvPolynomial.C r)) = _
        rw [IsLocalization.map_eq,
          show f.toRingHom (MvPolynomial.C r) = algebraMap R A r from f.commutes r]
        exact (IsScalarTower.algebraMap_apply R A (Localization.Away (f g)) r).symm }
  have hk : Function.Surjective k := by
    apply Localization.awayMap_surjective_iff.mpr
    intro a
    obtain ⟨c, hc⟩ := hf a
    exact ⟨c, 0, by simpa using hc⟩
  have hj_surj : Function.Surjective j :=
    (Localization.awayEquivAdjoin g).symm.surjective.comp (AdjoinRoot.mk_surjective)
  have hb : Function.Surjective b := hk.comp (hj_surj.comp e.surjective)
  have hcomp : IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars.{u} (k.comp j)).mapDerivedCategory.obj L) m :=
    (isPseudoCoherentFrom_restrictScalars_comp_ringEquiv e (k.comp j) L m).mpr (hL _ b hb)
  exact (isPseudoCoherentFrom_localizationAway_iff_restrictScalars_polynomial
    g _ m).mpr
    ((isPseudoCoherentFrom_restrictScalars_comp_iff j k L m).mp hcomp)

attribute [local instance] localizationExtension_additive
  localizationExtension_preservesFiniteLimits localizationExtension_preservesFiniteColimits

private noncomputable def mapDerivedCategorySquareIso
    {C D D' E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category D'] [Abelian D'] [HasDerivedCategory D']
    [Category E] [Abelian E] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') (K : DerivedCategory C) :
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) ≅
      G'.mapDerivedCategory.obj (F'.mapDerivedCategory.obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let a : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso a.symm) ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
      (.up ℤ)).app P) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (F' ⋙ G'))
      (.up ℤ)).symm.app P) ≪≫
    (G'.mapDerivedCategoryFactors.app ((F'.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    G'.mapDerivedCategory.mapIso (F'.mapDerivedCategoryFactors.app P).symm ≪≫
    G'.mapDerivedCategory.mapIso (F'.mapDerivedCategory.mapIso a)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localizedTensorEquiv
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (g : R) (M : Type u) [AddCommGroup M] [Module A M] :
    letI : Module R M := Module.compHom M (algebraMap R A)
    letI : Algebra (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
      (Localization.awayMap (algebraMap R A) g).toAlgebra
    TensorProduct R (Localization.Away g) M ≃ₗ[Localization.Away g]
      TensorProduct A (Localization.Away (algebraMap R A g)) M := by
  letI : Module R M := Module.compHom M (algebraMap R A)
  letI : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let B := Localization.Away (algebraMap R A g)
  let N := TensorProduct A B M
  let q := Localization.awayMap (algebraMap R A) g
  letI : Algebra (Localization.Away g) B := q.toAlgebra
  letI : IsScalarTower R (Localization.Away g) B :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ by
      change algebraMap R B r = q (algebraMap R (Localization.Away g) r)
      dsimp [q, Localization.awayMap, IsLocalization.Away.map]
      rw [IsLocalization.map_eq]
      rfl)
  let t : M →ₗ[R] N := (TensorProduct.mk A B M 1).restrictScalars R
  letI : IsLocalizedModule (Submonoid.powers g) t :=
    IsLocalizedModule.restrictScalars_powers g (TensorProduct.mk A B M 1)
  exact (IsLocalizedModule.isBaseChange (Submonoid.powers g) (Localization.Away g) t).equiv

set_option backward.isDefEq.respectTransparency false in
private lemma localizedTensorEquiv_tmul
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (g : R) (M : Type u) [AddCommGroup M] [Module A M]
    (r : Localization.Away g) (x : M) :
    let : Module R M := Module.compHom M (algebraMap R A)
    let : Algebra (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
      (Localization.awayMap (algebraMap R A) g).toAlgebra
    localizedTensorEquiv g M (r ⊗ₜ[R] x) =
      r • (1 ⊗ₜ[A] x : TensorProduct A (Localization.Away (algebraMap R A g)) M) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  let : IsScalarTower R A M := IsScalarTower.of_compHom R A M
  let B := Localization.Away (algebraMap R A g)
  let N := TensorProduct A B M
  let q := Localization.awayMap (algebraMap R A) g
  let : Algebra (Localization.Away g) B := q.toAlgebra
  let : IsScalarTower R (Localization.Away g) B :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ by
      show algebraMap R B r = q (algebraMap R (Localization.Away g) r)
      dsimp [q, Localization.awayMap, IsLocalization.Away.map]
      rw [IsLocalization.map_eq]
      rfl)
  let t : M →ₗ[R] N := (TensorProduct.mk A B M 1).restrictScalars R
  let : IsLocalizedModule (Submonoid.powers g) t :=
    IsLocalizedModule.restrictScalars_powers g (TensorProduct.mk A B M 1)
  exact IsBaseChange.equiv_tmul _ r x

set_option backward.isDefEq.respectTransparency false in
private lemma localizedTensorEquiv_one_tmul
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (g : R) (M : Type u) [AddCommGroup M] [Module A M] (x : M) :
    letI : Module R M := Module.compHom M (algebraMap R A)
    localizedTensorEquiv (A := A) g M (1 ⊗ₜ[R] x) =
      (1 ⊗ₜ[A] x : TensorProduct A (Localization.Away (algebraMap R A g)) M) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  let : Algebra (Localization.Away g) (Localization.Away (algebraMap R A g)) :=
    (Localization.awayMap (algebraMap R A) g).toAlgebra
  refine (localizedTensorEquiv_tmul (A := A) g M 1 x).trans ?_
  rw [TensorProduct.smul_tmul']
  congr 1
  show (Localization.awayMap (algebraMap R A) g) 1 * 1 = 1
  rw [map_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localizationBaseChangeIsoApp
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    (p : R →+* A) (g : R) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away g))).obj
      ((ModuleCat.restrictScalars p).obj M) ≅
    (ModuleCat.restrictScalars (Localization.awayMap p g)).obj
      ((ModuleCat.extendScalars (algebraMap A (Localization.Away (p g)))).obj M) := by
  letI : Algebra R A := p.toAlgebra
  letI : Module R M := Module.compHom M p
  let B := Localization.Away (p g)
  let q := Localization.awayMap p g
  letI : Algebra (Localization.Away g) B := q.toAlgebra
  let e := localizedTensorEquiv (A := A) g M
  let j : TensorProduct A B M ≃ₗ[Localization.Away g]
      (ModuleCat.restrictScalars q).obj (ModuleCat.of B (TensorProduct A B M)) :=
    { __ := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ (IsScalarTower.algebraMap_smul B r x).symm }
  exact _root_.PseudoCoherence.extendScalarsAlgebraMapObjIso
      ((ModuleCat.restrictScalars p).obj M) ≪≫
    LinearEquiv.toModuleIso (e.trans j) ≪≫
    (ModuleCat.restrictScalars q).mapIso
      (_root_.PseudoCoherence.extendScalarsAlgebraMapObjIso M).symm

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private lemma extendScalarsAlgebraMapObjIso_hom_tmul
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) (s : S) (x : M) :
    (_root_.PseudoCoherence.extendScalarsAlgebraMapObjIso M).hom (s ⊗ₜ[R, algebraMap R S] x) =
      s ⊗ₜ[R] x := by
  simp [_root_.PseudoCoherence.extendScalarsAlgebraMapObjIso]

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private lemma extendScalarsAlgebraMapObjIso_inv_tmul
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{u} R) (s : S) (x : M) :
    (_root_.PseudoCoherence.extendScalarsAlgebraMapObjIso M).inv (s ⊗ₜ[R] x) =
      s ⊗ₜ[R, algebraMap R S] x := by
  simp [_root_.PseudoCoherence.extendScalarsAlgebraMapObjIso, TensorProduct.congr_symm]

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def localizationBaseChangeIso
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] (p : R →+* A) (g : R) :
    ModuleCat.restrictScalars.{u} p ⋙
      ModuleCat.extendScalars (algebraMap R (Localization.Away g)) ≅
    ModuleCat.extendScalars (algebraMap A (Localization.Away (p g))) ⋙
      ModuleCat.restrictScalars (Localization.awayMap p g) :=
  NatIso.ofComponents (localizationBaseChangeIsoApp p g) (fun {X Y} φ ↦ by
    let : Algebra R A := p.toAlgebra
    let : Algebra (Localization.Away g) (Localization.Away (p g)) :=
      (Localization.awayMap p g).toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    simp only [Functor.comp_obj, Functor.comp_map, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, ModuleCat.ExtendScalars.map_tmul, ModuleCat.restrictScalars.map_apply]
    have hX := localizedTensorEquiv_one_tmul (A := A) g X (show X from x)
    have hY := localizedTensorEquiv_one_tmul (A := A) g Y (φ (show X from x))
    dsimp only at hX hY
    let aX := (_root_.PseudoCoherence.extendScalarsAlgebraMapObjIso
      (S := Localization.Away (p g)) X).inv
    let aY := (_root_.PseudoCoherence.extendScalarsAlgebraMapObjIso
      (S := Localization.Away (p g)) Y).inv
    let t := (ModuleCat.extendScalars (algebraMap A (Localization.Away (p g)))).map φ
    refine (congrArg aY hY).trans (Eq.trans ?_ (congrArg (fun z ↦ t (aX z)) hX.symm))
    exact (extendScalarsAlgebraMapObjIso_inv_tmul
      (S := Localization.Away (p g)) Y 1 (φ (show X from x))).trans
      ((ModuleCat.ExtendScalars.map_tmul (algebraMap A (Localization.Away (p g)))
        φ 1 (show X from x)).symm.trans
        (congrArg t (extendScalarsAlgebraMapObjIso_inv_tmul
          (S := Localization.Away (p g)) X 1 (show X from x)).symm)))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localizationAwayRestrictScalarsIso
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    (p : R →+* A) (g : R) (K : DerivedCategory (ModuleCat.{u} A)) :
    (localizationAwayFunctorAux.{u, u} g).obj
      ((ModuleCat.restrictScalars p).mapDerivedCategory.obj K) ≅
    (ModuleCat.restrictScalars (Localization.awayMap p g)).mapDerivedCategory.obj
      ((localizationAwayFunctorAux.{u, u} (p g)).obj K) := by
  let F := ModuleCat.extendScalars.{u, u, u}
    (algebraMap R (Localization.Away g))
  let G := ModuleCat.extendScalars.{u, u, u}
    (algebraMap A (Localization.Away (p g)))
  letI : F.Additive := localizationExtension_additive g
  letI : PreservesFiniteLimits F := localizationExtension_preservesFiniteLimits g
  letI : PreservesFiniteColimits F := localizationExtension_preservesFiniteColimits g
  letI : G.Additive := localizationExtension_additive (p g)
  letI : PreservesFiniteLimits G := localizationExtension_preservesFiniteLimits (p g)
  letI : PreservesFiniteColimits G :=
    localizationExtension_preservesFiniteColimits (p g)
  exact mapDerivedCategorySquareIso (ModuleCat.restrictScalars p) F G
    (ModuleCat.restrictScalars (Localization.awayMap p g))
    (localizationBaseChangeIso p g) K

private lemma isPseudoCoherentFrom_restrictScalars_of_subsingleton
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Subsingleton A]
    (p : R →+* A) (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars p).mapDerivedCategory.obj K) m := by
  apply isPseudoCoherentFrom_of_homology_isZero
  intro i _
  exact ((mapDerivedCategoryHomologyIso (ModuleCat.restrictScalars p) i).app K).isZero_iff.mpr
    ((ModuleCat.restrictScalars p).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr (Module.subsingleton A _)))

/-- Descend along the lifted cover of each polynomial presentation. The additional principal
open has zero image in the quotient, so the restricted complex vanishes there. -/
private lemma relativelyPseudoCoherentFrom_iff_localizationAway_of_common_universe
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    {ι : Type*} [Finite ι] (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    (∀ i, IsRelativelyPseudoCoherentFrom (R := R)
      ((localizationAwayFunctorAux.{u, u} (f i)).obj K) m) ↔
    IsRelativelyPseudoCoherentFrom (R := R) K m := by
  refine ⟨?_, fun h i ↦
    localizationAway_preserves_relativelyPseudoCoherentFrom (f i) K m h⟩
  intro hlocal n p hp
  obtain ⟨g, h, hg, hh, hcover⟩ := exists_lift_span_eq_top p.toRingHom hp f hf
  apply (isPseudoCoherentFrom_and_isPseudoCoherent_of_localization.{u, u}
    (Option.elim · h g) hcover ((ModuleCat.restrictScalars p.toRingHom).mapDerivedCategory.obj K)
    m).1
  intro i
  cases i with
  | none =>
    apply (isPseudoCoherentFrom_iso_iff (localizationAwayRestrictScalarsIso p.toRingHom h K) m).mpr
    have : Subsingleton (Localization.Away (p.toRingHom h)) :=
      IsLocalization.subsingleton (S := Localization.Away (p.toRingHom h))
        (show 0 ∈ Submonoid.powers (p.toRingHom h) from ⟨1, by simpa using hh⟩)
    exact isPseudoCoherentFrom_restrictScalars_of_subsingleton _ _ m
  | some i =>
    apply (isPseudoCoherentFrom_iso_iff
      (localizationAwayRestrictScalarsIso p.toRingHom (g i) K) m).mpr
    exact isPseudoCoherentFrom_restrictScalars_localizationAway_of_relative
      n p hp (g i) _ m
      (Eq.mpr (congrArg (fun a : A ↦ IsRelativelyPseudoCoherentFrom (R := R)
        ((localizationAwayFunctorAux.{u, u} a).obj K) m) (hg i)) (hlocal i))

/-- Transport a small base ring into the module universe; otherwise finite free approximations
vanish and local detection of homology vanishing gives the same equivalence. -/
private alias relativelyPseudoCoherentFrom_iff_localizationAway := relativelyPseudoCoherentFrom_iff_localizationAway_of_common_universe

/-- **Stacks 067E.** Relative `m`-pseudo-coherence and relative pseudo-coherence are local on
a finite principal cover of a finite-type algebra. -/
@[stacks 067E]
public theorem relativelyPseudoCoherent_iff_localizationAway_of_span_eq_top
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.FiniteType R A]
    {ι : Type*} [Finite ι] (f : ι → A) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    ((∀ i,
      letI : Algebra.FiniteType A (Localization.Away (f i)) :=
        IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (f i)) _
      letI : Algebra.FiniteType R (Localization.Away (f i)) :=
        Algebra.FiniteType.trans (R := R) (S := A)
          (A := Localization.Away (f i)) inferInstance inferInstance
      IsRelativelyPseudoCoherentFrom (R := R)
        ((localizationAwayFunctorAux.{u, u} (f i)).obj K) m) ↔
      IsRelativelyPseudoCoherentFrom (R := R) K m) ∧
    ((∀ i,
      letI : Algebra.FiniteType A (Localization.Away (f i)) :=
        IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (f i)) _
      letI : Algebra.FiniteType R (Localization.Away (f i)) :=
        Algebra.FiniteType.trans (R := R) (S := A)
          (A := Localization.Away (f i)) inferInstance inferInstance
      IsRelativelyPseudoCoherent (R := R)
        ((localizationAwayFunctorAux.{u, u} (f i)).obj K)) ↔
      IsRelativelyPseudoCoherent (R := R) K) :=
  ⟨relativelyPseudoCoherentFrom_iff_localizationAway f hf K m,
    fun h n ↦ (relativelyPseudoCoherentFrom_iff_localizationAway f hf K n).mp fun i ↦ h i n,
    fun h i n ↦ (relativelyPseudoCoherentFrom_iff_localizationAway f hf K n).mpr (h n) i⟩

end PseudoCoherence
