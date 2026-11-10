module

public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.Triangle
public import StacksFrontier.Homology.PseudoCoherent.Relative.Composition
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

@[expose] public section

/-!
# Relative pseudo-coherence and localization

Let `R` be a commutative ring, `R_f` a localization of `R` away from one element, and `A` a
finite-type `R_f`-algebra. Localizing `A` away from an element `g` and extending the scalars of
a complex along `A → A_g` turns relative pseudo-coherence over `R_f` into relative
pseudo-coherence over `R`: the two localizations together supply the extra polynomial variable
that a presentation over the smaller base needs.

## Main results

* `PseudoCoherence.localization_preserves_relativePseudoCoherent` (Stacks 0679).

## Implementation notes

Both localizations are expressed by `IsLocalization.Away`, and the derived tensor product with
`A_g` by the derived extension-of-scalars functor of tag 064H. Passing from `R_f` to `R`
replaces a presentation `R_f[x_1, …, x_n] ↠ A` by `R[x_0, …, x_n] ↠ A`, where the extra
variable is inverted: `R_f` is `R[x]/(f x - 1)` and that quotient is by a regular element, so
`A` stays pseudo-coherent as a module over the larger polynomial algebra and tag 064Z moves
`m`-pseudo-coherence across. Localizing the target is handled the same way, after flat base
change along `R → R_f` identifies the two ways of localizing a restricted complex, which is
where tag 0650 enters.

Tags 064Q, 064R, 064U, 064Z and 0650 belong to Chapter 15 section 65, and 064H to section 62;
they are supplied in `StacksFrontier/Algebra/Homology/PseudoCoherent.lean`,
`StacksFrontier/Homology/PseudoCoherent/{Triangle,Basic,ChangeOfRings}.lean` and
`StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean`. Tags 065H and 065I are this cluster's,
in `Relative/Presentation.lean` and `Relative/Defs.lean`.

## References

* [The Stacks Project, Lemma 15.82.11 (0679)](https://stacks.math.columbia.edu/tag/0679)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

private lemma pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars_derived
    {S : Type u} {B : Type u} [CommRing S] [CommRing B] (q : S →+* B)
    (hB : IsModulePseudoCoherent (R := S)
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of B B)))
    (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ) :
    (IsPseudoCoherentFrom K m ↔
      IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} q).mapDerivedCategory.obj K) m) ∧
    (IsPseudoCoherent K ↔
      IsPseudoCoherent ((ModuleCat.restrictScalars.{u} q).mapDerivedCategory.obj K)) := by
  let : DerivedCategory.Q.EssSurj := Localization.essSurj DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))
  obtain ⟨L, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage DerivedCategory.Q K
  let Ls := ((ModuleCat.restrictScalars.{u} q).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L
  have h := pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars.{u, u, u} q hB L m
  let er : DerivedCategory.Q.obj Ls ≅
      (ModuleCat.restrictScalars.{u} q).mapDerivedCategory.obj K :=
    (ModuleCat.restrictScalars q).mapDerivedCategoryFactors.symm.app L ≪≫
      (ModuleCat.restrictScalars q).mapDerivedCategory.mapIso e
  exact ⟨⟨fun hK => isPseudoCoherentFrom_of_iso (h.1.mp (isPseudoCoherentFrom_of_iso hK e.symm)) er,
      fun hK => isPseudoCoherentFrom_of_iso (h.1.mpr (isPseudoCoherentFrom_of_iso hK er.symm)) e⟩,
    ⟨fun hK => IsPseudoCoherent.ofIso (h.2.mp (IsPseudoCoherent.ofIso hK e.symm)) er,
      fun hK => IsPseudoCoherent.ofIso (h.2.mpr (IsPseudoCoherent.ofIso hK er.symm)) e⟩⟩

/-- The cokernel of a short exact sequence of pseudo-coherent modules is pseudo-coherent. -/
lemma isModulePseudoCoherent_of_shortExact
    {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (h₁ : IsModulePseudoCoherent (R := R) S.X₁)
    (h₂ : IsModulePseudoCoherent (R := R) S.X₂) :
    IsModulePseudoCoherent (R := R) S.X₃ := by
  refine (pseudoCoherent_iff_all _).mpr fun m => ?_
  exact isPseudoCoherent_of_distinguished_one m hS.singleTriangle hS.singleTriangle_distinguished
    ((pseudoCoherent_iff_all _).mp h₁ (m + 1)) ((pseudoCoherent_iff_all _).mp h₂ m)

/-- If `q : S → B` is surjective with kernel generated by a single non-zerodivisor, then `B` is
pseudo-coherent as an `S`-module: the two-term resolution `S --·r--> S --q--> B` is finite
free. -/
lemma isModulePseudoCoherent_of_ker_eq_span
    {S : Type u} {B : Type u} [CommRing S] [CommRing B]
    (q : S →+* B) (hq : Function.Surjective q)
    (r : S) (hr : IsRegular r) (hker : RingHom.ker q = Ideal.span {r}) :
    IsModulePseudoCoherent (R := S)
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of B B)) := by
  let M := (ModuleCat.restrictScalars q).obj (ModuleCat.of B B)
  let α : ModuleCat.of S S ⟶ ModuleCat.of S S :=
    ModuleCat.ofHom (LinearMap.mulLeft S r)
  let βₗ : S →ₗ[S] M :=
    { toFun := fun s => q s
      map_add' := q.map_add
      map_smul' := fun a b => q.map_mul a b }
  let β : ModuleCat.of S S ⟶ M := ModuleCat.ofHom (X := S) (Y := M) βₗ
  have hqr : q r = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self r
  have hab : α ≫ β = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change q (r * a) = 0
    simp [hqr]
  let T := ShortComplex.mk α β hab
  have : Mono α := (ModuleCat.mono_iff_injective α).mpr hr.left
  have : Epi β := (ModuleCat.epi_iff_surjective β).mpr hq
  have hT : T.ShortExact := by
    refine ⟨?_⟩
    rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    have ha' : a ∈ Ideal.span {r} := by
      rw [← hker]
      exact ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha'
    exact ⟨b, hb.symm⟩
  exact isModulePseudoCoherent_of_shortExact T hT
    (StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free _)
    (StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free _)

/-- `s·x - 1` is a non-zerodivisor in `R[x]`: a multiple of it has vanishing constant term, and
then each coefficient is `s` times the previous one. -/
lemma isRegular_C_mul_X_sub_one {R : Type u} [CommRing R] (r : R) :
    IsRegular (Polynomial.C r * Polynomial.X - 1) := by
  have hinj : Function.Injective (fun p : Polynomial R =>
      (Polynomial.C r * Polynomial.X - 1) * p) := by
    refine (injective_iff_map_eq_zero (LinearMap.mulLeft (Polynomial R)
      (Polynomial.C r * Polynomial.X - 1))).mpr fun p hp => Polynomial.ext fun n => ?_
    have hc (i : ℕ) := congrArg (fun q : Polynomial R => q.coeff i) hp
    induction n with
    | zero => simpa using hc 0
    | succ n ih =>
      simpa [sub_mul, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul, mul_assoc, ih]
        using hc (n + 1)
  exact (Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr hinj

private lemma isModulePseudoCoherent_adjoin_inv {R : Type u} [CommRing R] (r : R) :
    IsModulePseudoCoherent (R := Polynomial R)
      ((ModuleCat.restrictScalars (AdjoinRoot.mk (Polynomial.C r * Polynomial.X - 1))).obj
        (ModuleCat.of (AdjoinRoot (Polynomial.C r * Polynomial.X - 1))
          (AdjoinRoot (Polynomial.C r * Polynomial.X - 1)))) :=
  isModulePseudoCoherent_of_ker_eq_span _ AdjoinRoot.mk_surjective
    (Polynomial.C r * Polynomial.X - 1) (isRegular_C_mul_X_sub_one r) Ideal.mk_ker

/-- For a ring isomorphism `e : S ≃+* B`, a complex `K` in the derived category of `B`-modules is
`m`-pseudo-coherent if and only if its restriction of scalars along `e` is `m`-pseudo-coherent. -/
lemma isPseudoCoherentFrom_restrictScalars_ringEquiv
    {S : Type u} {B : Type u} [CommRing S] [CommRing B] (e : S ≃+* B)
    (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategory.obj K) m := by
  let M := (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of B B)
  let j : S ≃ₗ[S] M :=
    { e.toEquiv with
      map_add' := e.map_add
      map_smul' := e.map_mul }
  have : Module.Finite S M := Module.Finite.of_surjective j.toLinearMap j.surjective
  have : Module.Free S M := Module.Free.of_equiv j
  exact (pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars_derived
    e.toRingHom (StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free M) K m).1

private noncomputable def derivedExtensionScalarsIsoOfExact
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    [(ModuleCat.extendScalars.{u, u, u} f).Additive]
    [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f)]
    [PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f)] :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor ≅
      (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  let D := derivedExtensionScalarsGeneral.{u, u, u} f
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{u} R) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ F.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫ F.mapDerivedCategoryFactors.symm)

/-- Pseudo-coherence along `f` of the restriction along `g` gives it along `g.comp f`. -/
private lemma isPseudoCoherentFrom_restrictScalars_comp
    {R : Type u} {S : Type u} {T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (K : DerivedCategory (ModuleCat.{u} T)) (m : ℤ)
    (h : IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
      ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj K)) m) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory.obj K) m :=
  isPseudoCoherentFrom_of_iso h (restrictScalarsDerivedCompIso f g K).symm

private lemma exists_polynomialPresentation_isPseudoCoherentFrom_of_isLocalizationAway
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S]
    (K : DerivedCategory (ModuleCat.{u} S)) (m : ℤ)
    (hK : IsPseudoCoherentFrom K m) :
    ∃ q : Polynomial R →ₐ[R] S, Function.Surjective q ∧
      IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} q.toRingHom).mapDerivedCategory.obj K)
        m := by
  let p := Polynomial.C r * Polynomial.X - 1
  let e : AdjoinRoot p ≃ₐ[R] S := (Localization.awayEquivAdjoin r).symm.trans
    (IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) S)
  let q := e.toAlgHom.comp (AdjoinRoot.mkₐ p)
  refine ⟨q, e.surjective.comp AdjoinRoot.mk_surjective, ?_⟩
  have hE := (isPseudoCoherentFrom_restrictScalars_ringEquiv e.toRingEquiv K m).mp hK
  have hP := (pseudoCoherentFrom_and_pseudoCoherent_iff_restrictScalars_derived
    (AdjoinRoot.mk p) (isModulePseudoCoherent_adjoin_inv r) _ m).1.mp hE
  exact isPseudoCoherentFrom_restrictScalars_comp _ _ K m hP

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A presentation `P[x] ↠ B ↠ T` with `P = R[x₁, …, xₙ]`, along which `L` is `m`-pseudo-coherent,
makes `L` relatively `m`-pseudo-coherent over `R`. -/
private lemma isRelativelyPseudoCoherentFrom_of_polynomial_comp
    {R : Type u} {B : Type u} {T : Type u} [CommRing R] [CommRing B] [CommRing T]
    [Algebra R T] [Algebra.FiniteType R T] {n : ℕ} [Algebra R B]
    [Algebra (MvPolynomial (Fin n) R) B] [IsScalarTower R (MvPolynomial (Fin n) R) B]
    (q : Polynomial (MvPolynomial (Fin n) R) →ₐ[MvPolynomial (Fin n) R] B)
    (hq : Function.Surjective q) (β : B →ₐ[R] T) (hβ : Function.Surjective β)
    (L : DerivedCategory (ModuleCat.{u} T)) (m : ℤ)
    (hP : IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} q.toRingHom).mapDerivedCategory.obj
      ((ModuleCat.restrictScalars.{u} β.toRingHom).mapDerivedCategory.obj L)) m) :
    IsRelativelyPseudoCoherentFrom (R := R) L m := by
  let e := MvPolynomial.finSuccEquiv R n
  apply (isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u} L m).1.mp
  refine ⟨n + 1, (β.comp (q.restrictScalars R)).comp e.toAlgHom,
    hβ.comp (hq.comp e.surjective), ?_⟩
  exact isPseudoCoherentFrom_restrictScalars_comp _ _ L m
    ((isPseudoCoherentFrom_restrictScalars_ringEquiv e.toRingEquiv _ m).mp
      (isPseudoCoherentFrom_restrictScalars_comp _ _ L m hP))

private lemma isRelativelyPseudoCoherentFrom_of_isLocalizationAway
    {R : Type u} {Rf : Type u} {A : Type u}
    [CommRing R] [CommRing Rf] [CommRing A]
    [Algebra R Rf] (f : R) [IsLocalization.Away f Rf]
    [Algebra Rf A] [Algebra.FiniteType Rf A]
    [Algebra R A] [IsScalarTower R Rf A] [Algebra.FiniteType R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hK : IsRelativelyPseudoCoherentFrom (R := Rf) K m) :
    IsRelativelyPseudoCoherentFrom (R := R) K m := by
  obtain ⟨n, α, hα⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType Rf A)
  let P := MvPolynomial (Fin n) R
  let Pf := MvPolynomial (Fin n) Rf
  have : IsLocalization.Away (MvPolynomial.C f : P) Pf := by
    simpa only [Submonoid.map_powers] using
      (inferInstance : IsLocalization ((Submonoid.powers f).map MvPolynomial.C) Pf)
  obtain ⟨q, hq, hP⟩ :=
    exists_polynomialPresentation_isPseudoCoherentFrom_of_isLocalizationAway
      (MvPolynomial.C f : P)
      ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj K) m (hK n α hα)
  exact isRelativelyPseudoCoherentFrom_of_polynomial_comp q hq (α.restrictScalars R) hα K m hP

private lemma extendScalars_exact {R : Type u} {S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) := by
  let : Algebra R S := ((algebraMap S S).comp f).toAlgebra
  have : Module.Flat R S := hf
  let F := ModuleCat.extendScalars.{u, u, u} f
  have : F.Additive := extendScalars_additive f
  refine ((Functor.exact_tfae F).out 2 4).mp fun T hT => ?_
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  exact Module.Flat.lTensor_exact S hT

/-- For exact additive functors `F : C ⥤ D` and `G : D ⥤ E`, the isomorphism between the image of
`K` under the derived functor of `F ⋙ G` and its image under the composite of the derived functors
of `F` and `G`. -/
noncomputable def mapDerivedCategoryCompIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory C) :
    (F ⋙ G).mapDerivedCategory.obj K ≅
      G.mapDerivedCategory.obj (F.mapDerivedCategory.obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact (F ⋙ G).mapDerivedCategory.mapIso e.symm ≪≫
    (F ⋙ G).mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)).symm.app P) ≪≫
    (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso e)

/-- A natural isomorphism `e : F ≅ G` of exact additive functors induces an isomorphism between
the images of `K` under the derived functors of `F` and `G`. -/
noncomputable def mapDerivedCategoryIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory C) :
    F.mapDerivedCategory.obj K ≅ G.mapDerivedCategory.obj K := by
  let P := DerivedCategory.Q.objPreimage K
  let eK : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact F.mapDerivedCategory.mapIso eK.symm ≪≫ F.mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P) ≪≫
    (G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso eK

private noncomputable def localizationBaseChangeEquiv
    {R : Type u} {S : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra A B] [Algebra R B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R A r) B]
    (M : Type u) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    S ⊗[R] M ≃ₗ[S] B ⊗[A] M := by
  let j := (TensorProduct.mk A B M 1).restrictScalars R
  have hj : IsLocalizedModule (Submonoid.powers r) j :=
    IsLocalizedModule.restrictScalars (Submonoid.powers r) _
  exact (IsLocalizedModule.isBaseChange (Submonoid.powers r) S j).equiv

private lemma localizationBaseChangeEquiv_tmul
    {R : Type u} {S : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra A B] [Algebra R B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R A r) B]
    (M : Type u) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    (s : S) (m : M) :
    localizationBaseChangeEquiv r M (s ⊗ₜ[R] m) = (algebraMap S B s) ⊗ₜ[A] m := by
  simp only [localizationBaseChangeEquiv, IsBaseChange.equiv_tmul,
    LinearMap.restrictScalars_apply, TensorProduct.mk_apply, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_one]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def localizationExtendRestrictScalarsIso
    {R : Type u} {S : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [aRS₀ : Algebra R S] [Algebra R A] [aAB₀ : Algebra A B] [Algebra R B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R A r) B] :
    ModuleCat.restrictScalars.{u} (algebraMap R A) ⋙
        ModuleCat.extendScalars (algebraMap R S) ≅
      ModuleCat.extendScalars (algebraMap A B) ⋙
        ModuleCat.restrictScalars (algebraMap S B) := by
  have hRS : IsLocalization.Away r S := inferInstance
  have hAB : IsLocalization.Away (algebraMap R A r) B := inferInstance
  have hRAB : IsScalarTower R A B := inferInstance
  have hRSB : IsScalarTower R S B := inferInstance
  letI aRS : Algebra R S := (algebraMap R S).toAlgebra
  letI aAB : Algebra A B := (algebraMap A B).toAlgebra
  have : IsLocalization.Away r S :=
    (show aRS = aRS₀ from @toAlgebra_algebraMap R S _ _ aRS₀).symm ▸ hRS
  have : IsLocalization.Away (algebraMap R A r) B :=
    (show aAB = aAB₀ from @toAlgebra_algebraMap A B _ _ aAB₀).symm ▸ hAB
  have : IsScalarTower R A B :=
    (show aAB = aAB₀ from @toAlgebra_algebraMap A B _ _ aAB₀).symm ▸ hRAB
  have : IsScalarTower R S B :=
    (show aRS = aRS₀ from @toAlgebra_algebraMap R S _ _ aRS₀).symm ▸ hRSB
  refine NatIso.ofComponents (fun M => ?_) ?_
  · letI : Module R M := Module.compHom M (algebraMap R A)
    letI : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let e := localizationBaseChangeEquiv (S := S) (A := A) (B := B) r M
    let j : (ModuleCat.restrictScalars (algebraMap R A) ⋙
        ModuleCat.extendScalars (algebraMap R S)).obj M ≃ₗ[S]
        (ModuleCat.extendScalars (algebraMap A B) ⋙
          ModuleCat.restrictScalars (algebraMap S B)).obj M :=
      { e.toAddEquiv with
        map_smul' := fun s m => by
          change e (s • m) = algebraMap S B s • e m
          rw [e.map_smul, IsScalarTower.algebraMap_smul] }
    exact j.toModuleIso
  · intro M N φ
    let : Module R M := Module.compHom M (algebraMap R A)
    let : Module R N := Module.compHom N (algebraMap R A)
    let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
      change localizationBaseChangeEquiv (S := S) (A := A) (B := B) r N (s ⊗ₜ[R] φ m) =
        ((ModuleCat.extendScalars (algebraMap A B)).map φ)
          (localizationBaseChangeEquiv (S := S) (A := A) (B := B) r M (s ⊗ₜ[R] m))
      simp only [localizationBaseChangeEquiv_tmul]
      rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']

private lemma isPseudoCoherentFrom_localization_restrictScalars
    {R : Type u} {S : Type u} {A : Type u} {B : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra A B] [Algebra R B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R A r) B]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hK : IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) m) :
    IsPseudoCoherentFrom
      ((ModuleCat.restrictScalars (algebraMap S B)).mapDerivedCategory.obj
        ((derivedExtensionScalarsGeneral.{u, u, u}
          (algebraMap A B)).functor.obj K)) m := by
  let F := ModuleCat.restrictScalars.{u} (algebraMap R A)
  let G := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
  let J := ModuleCat.extendScalars.{u, u, u} (algebraMap A B)
  let H := ModuleCat.restrictScalars.{u} (algebraMap S B)
  have : G.Additive := extendScalars_additive _
  have : J.Additive := extendScalars_additive _
  have hG := extendScalars_exact (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers r)))
  have hJ := extendScalars_exact (algebraMap A B)
    (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat B (Submonoid.powers (algebraMap R A r))))
  have : PreservesFiniteLimits G := hG.1
  have : PreservesFiniteColimits G := hG.2
  have : PreservesFiniteLimits J := hJ.1
  have : PreservesFiniteColimits J := hJ.2
  have hGfree : ∀ M : ModuleCat.{u} R,
      Module.Finite R M → Module.Free R M →
        Module.Finite S (G.obj M) ∧ Module.Free S (G.obj M) := by
    intro M _ _
    let : Algebra R S := ((algebraMap S S).comp (algebraMap R S)).toAlgebra
    change Module.Finite S (S ⊗[R] M) ∧ Module.Free S (S ⊗[R] M)
    exact ⟨inferInstance, inferInstance⟩
  have h := (exactFunctor_preserves_pseudoCoherent G hGfree
    (F.mapDerivedCategory.obj K)).1 m hK
  let e := (mapDerivedCategoryCompIso F G K).symm ≪≫
    mapDerivedCategoryIso (F ⋙ G) (J ⋙ H) (localizationExtendRestrictScalarsIso r) K ≪≫
    mapDerivedCategoryCompIso J H K ≪≫
    H.mapDerivedCategory.mapIso ((derivedExtensionScalarsIsoOfExact
      (algebraMap A B)).symm.app K)
  exact isPseudoCoherentFrom_of_iso h e

private lemma isRelativelyPseudoCoherentFrom_localizationTarget
    {R : Type u} {A : Type u} {Ag : Type u}
    [CommRing R] [CommRing A] [CommRing Ag]
    [Algebra R A] [Algebra.FiniteType R A]
    (g : A) [Algebra A Ag] [IsLocalization.Away g Ag]
    [Algebra R Ag] [IsScalarTower R A Ag] [Algebra.FiniteType R Ag]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ)
    (hK : IsRelativelyPseudoCoherentFrom (R := R) K m) :
    IsRelativelyPseudoCoherentFrom (R := R)
      ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A Ag)).functor.obj K) m := by
  obtain ⟨n, α, hα⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  let P := MvPolynomial (Fin n) R
  let : Algebra P A := α.toRingHom.toAlgebra
  let : Algebra P Ag := ((algebraMap A Ag).comp α.toRingHom).toAlgebra
  have : IsScalarTower P A Ag := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨g', hg'⟩ := hα g
  have : IsLocalization.Away (algebraMap P A g') Ag := by
    change IsLocalization.Away (α g') Ag
    rw [hg']
    infer_instance
  let Pg := Localization.Away g'
  have : IsScalarTower R P Pg := inferInstance
  have : IsLocalization ((Submonoid.powers g').map α.toRingHom) Ag := by
    rw [Submonoid.map_powers]
    change IsLocalization.Away (algebraMap P A g') Ag
    infer_instance
  let β₀ : Pg →+* Ag :=
    IsLocalization.map Ag α.toRingHom (Submonoid.powers g').le_comap_map
  have hβ : Function.Surjective β₀ :=
    IsLocalization.map_surjective_of_surjective (Submonoid.powers g') Pg Ag hα
  let β : Pg →ₐ[R] Ag :=
    { β₀ with
      commutes' := fun r => by
        change β₀ (algebraMap P Pg (algebraMap R P r)) = algebraMap R Ag r
        dsimp only [β₀]
        rw [IsLocalization.map_eq]
        change algebraMap A Ag (α (algebraMap R P r)) = algebraMap R Ag r
        rw [α.commutes, ← IsScalarTower.algebraMap_apply R A Ag] }
  let : Algebra Pg Ag := β.toRingHom.toAlgebra
  have : IsScalarTower P Pg Ag :=
    IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (S := Pg) (Q := Ag)
        (g := α.toRingHom) (Submonoid.powers g').le_comap_map).symm
  let L := (derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A Ag)).functor.obj K
  obtain ⟨q, hq, hP⟩ :=
    exists_polynomialPresentation_isPseudoCoherentFrom_of_isLocalizationAway g'
      ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj L) m
      (isPseudoCoherentFrom_localization_restrictScalars (S := Pg) g' K m (hK n α hα))
  exact isRelativelyPseudoCoherentFrom_of_polynomial_comp q hq β hβ L m hP

/-- **Stacks 0679.** Localizing a complex that is relatively `m`-pseudo-coherent, respectively
pseudo-coherent, over `R_f` produces a complex with the corresponding property relative to
`R`. -/
@[stacks 0679]
public theorem localization_preserves_relativePseudoCoherent
    {R : Type u} {Rf : Type u} {A : Type u} {Ag : Type u}
    [CommRing R] [CommRing Rf] [CommRing A] [CommRing Ag]
    [Algebra R Rf] (f : R) [IsLocalization.Away f Rf]
    [Algebra Rf A] [Algebra.FiniteType Rf A]
    [Algebra R A] [IsScalarTower R Rf A]
    (g : A) [Algebra A Ag] [IsLocalization.Away g Ag]
    [Algebra R Ag] [IsScalarTower R A Ag]
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) :
    letI : Algebra.FiniteType R Rf :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) Rf
    letI : Algebra.FiniteType R A := Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R Rf) (inferInstance : Algebra.FiniteType Rf A)
    letI : Algebra.FiniteType A Ag :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) Ag
    letI : Algebra.FiniteType R Ag := Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R A) (inferInstance : Algebra.FiniteType A Ag)
    (IsRelativelyPseudoCoherentFrom (R := Rf) K m →
      IsRelativelyPseudoCoherentFrom (R := R)
        ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A Ag)).functor.obj K) m) ∧
    (IsRelativelyPseudoCoherent (R := Rf) K →
      IsRelativelyPseudoCoherent (R := R)
        ((derivedExtensionScalarsGeneral.{u, u, u} (algebraMap A Ag)).functor.obj
          K)) := by
  let : Algebra.FiniteType R Rf :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) Rf
  let : Algebra.FiniteType R A := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R Rf) (inferInstance : Algebra.FiniteType Rf A)
  let : Algebra.FiniteType A Ag :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers g) Ag
  let : Algebra.FiniteType R Ag := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R A) (inferInstance : Algebra.FiniteType A Ag)
  have hlocal (m' : ℤ) (hK : IsRelativelyPseudoCoherentFrom (R := Rf) K m') :
      IsRelativelyPseudoCoherentFrom (R := R)
        ((derivedExtensionScalarsGeneral.{u, u, u}
          (algebraMap A Ag)).functor.obj K) m' :=
    isRelativelyPseudoCoherentFrom_localizationTarget g K m'
      (isRelativelyPseudoCoherentFrom_of_isLocalizationAway f K m' hK)
  exact ⟨hlocal m, fun hK m' => hlocal m' (hK m')⟩

/-- **A localization away from one element of a relatively pseudo-coherent algebra is relatively
pseudo-coherent as a module over itself.** Let `A` be a finite-type `R`-algebra which is
pseudo-coherent relative to `R` as a module over itself, let `a : A` and let `Aₐ` be a
localization of `A` away from `a`. Then `Aₐ` is pseudo-coherent relative to `R` as a module over
itself.

Relative to `A` the statement is immediate from the presentation `A[x] ↠ Aₐ`, `x ↦ 1/a`, whose
kernel is generated by the single non-zerodivisor `a·x - 1`
(`PseudoCoherence.exists_polynomialPresentation_isPseudoCoherentFrom_of_isLocalizationAway`);
Stacks 065H then upgrades that one presentation to every presentation, and Stacks 067D
(`PseudoCoherence.relativelyPseudoCoherent_iff_of_comp`) moves the base from `A` down to `R`,
which is where the hypothesis on `A` is used. -/
public theorem isModuleRelativelyPseudoCoherent_localizationAway
    {R : Type u} {A : Type u} {Aa : Type u} [CommRing R] [CommRing A] [CommRing Aa]
    [Algebra R A] [Algebra.FiniteType R A] (a : A)
    [Algebra A Aa] [IsLocalization.Away a Aa]
    [Algebra R Aa] [IsScalarTower R A Aa]
    (hA : IsModuleRelativelyPseudoCoherent (R := R) (A := A) A) :
    letI : Algebra.FiniteType A Aa :=
      IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) Aa
    letI : Algebra.FiniteType R Aa := Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType R A) (inferInstance : Algebra.FiniteType A Aa)
    IsModuleRelativelyPseudoCoherent (R := R) (A := Aa) Aa := by
  let : Algebra.FiniteType A Aa :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) Aa
  let : Algebra.FiniteType R Aa := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R A) (inferInstance : Algebra.FiniteType A Aa)
  have hfree : ∀ m : ℤ, IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Aa) 0).obj (ModuleCat.of Aa Aa)) m :=
    (pseudoCoherent_iff_all _).mp
      (StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free (ModuleCat.of Aa Aa))
  have h1 : IsRelativelyPseudoCoherent (R := A)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Aa) 0).obj (ModuleCat.of Aa Aa)) := by
    intro m
    refine (isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u} _ m).1.mp ?_
    obtain ⟨q, hq, hP⟩ := exists_polynomialPresentation_isPseudoCoherentFrom_of_isLocalizationAway
      a _ m (hfree m)
    let e := MvPolynomial.uniqueAlgEquiv A (Fin 1)
    refine ⟨1, q.comp e.toAlgHom, hq.comp e.surjective, ?_⟩
    exact isPseudoCoherentFrom_restrictScalars_comp _ _ _ m
      ((isPseudoCoherentFrom_restrictScalars_ringEquiv e.toRingEquiv _ m).mp hP)
  exact (relativelyPseudoCoherent_iff_of_comp hA _ 0).2.mp h1

/-- **Relative `m`-pseudo-coherence of an algebra as a module over itself transports along an
isomorphism of `R`-algebras.** The source's presentations are carried to the target's by
composing with `e`, and the target, viewed as a module over the source through `e`, is the
source itself.

The degree `m` is fixed, which is the form a locality argument on a scheme consumes: it crosses
the gap between a concrete localization `Localization.Away a` and an abstract one, such as
`Γ(X, X.basicOpen a)`, inside a single degree. The statement for every degree at once is
`PseudoCoherence.isModuleRelativelyPseudoCoherent_of_algEquiv`. -/
public theorem isModuleRelativelyPseudoCoherentFrom_of_algEquiv
    {R : Type u} {A : Type u} {B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] (e : A ≃ₐ[R] B) (m : ℤ)
    (hA : IsModuleRelativelyPseudoCoherentFrom (R := R) (A := A) A m) :
    letI : Algebra.FiniteType R B := Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
    IsModuleRelativelyPseudoCoherentFrom (R := R) (A := B) B m := by
  let : Algebra.FiniteType R B := Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  let j : A ≃ₗ[A] (ModuleCat.restrictScalars.{u} e.toRingHom).obj (ModuleCat.of B B) :=
    { e.toRingEquiv.toEquiv with
      map_add' := e.map_add
      map_smul' := e.map_mul }
  let ι : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ≅
      (ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) :=
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso j.toModuleIso ≪≫
      (((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of B B)).symm
  intro n β hβ
  obtain ⟨k, α₀, hα₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  refine (isPseudoCoherentFrom_polynomialPresentation_independent.{u, u, u} _ m).1.mp
    ⟨k, e.toAlgHom.comp α₀, e.surjective.comp hα₀, ?_⟩ n β hβ
  exact isPseudoCoherentFrom_restrictScalars_comp _ _ _ m
    (IsPseudoCoherentFrom.ofIso (hA k α₀ hα₀)
      ((ModuleCat.restrictScalars.{u} α₀.toRingHom).mapDerivedCategory.mapIso ι))

/-- **Relative pseudo-coherence of an algebra as a module over itself transports along an
isomorphism of `R`-algebras.** Every degree of
`PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_of_algEquiv` at once. -/
public theorem isModuleRelativelyPseudoCoherent_of_algEquiv
    {R : Type u} {A : Type u} {B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A] (e : A ≃ₐ[R] B)
    (hA : IsModuleRelativelyPseudoCoherent (R := R) (A := A) A) :
    letI : Algebra.FiniteType R B := Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
    IsModuleRelativelyPseudoCoherent (R := R) (A := B) B :=
  fun m ↦ isModuleRelativelyPseudoCoherentFrom_of_algEquiv e m (hA m)

end PseudoCoherence
