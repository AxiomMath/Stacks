module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalSyntomicOpen
public import StacksFrontier.AlgebraicGeometry.Different.FiniteSyntomicMorphisms.UniversalTable
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections

/-!
# Smoothness of the universal finite syntomic locus

The open subscheme `U_d` of the scheme `X_d` of multiplication tables over which the universal
finite free family of rank `d` is syntomic (Tag 0FL0) is smooth over `Spec(ZZ)`.

## Main results

* `AlgebraicGeometry.universalSyntomicOpen_smooth_uLift`: `U_d` is smooth over the terminal
  scheme `Spec(ULift ZZ)` of an arbitrary universe.
* `AlgebraicGeometry.universalSyntomicOpen_smooth`: the same statement over `Spec(ZZ)` itself.

## Implementation notes

Smoothness is checked with the infinitesimal lifting criterion
`Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth` (Tag 02H6). Finite
presentation over the integers comes from the explicit finite presentation of the universal ring
`A_d`: the defining associativity, commutativity and unit relations form a finite set.

For the lifting property, let `i : T -> T'` be a first-order thickening of affine schemes and
`g : T -> U_d`. The universal property of Tag 0FL0 makes the base change of the universal family
along `T -> X_d` a syntomic algebra `A_0` over `R = Gamma(T)`, and it is finite free of rank `d`
with the image of `1` as its first basis vector. Tag 07M8
(`Stacks.Smoothing.exists_syntomic_lift_of_surjective`) lifts `A_0` to a syntomic algebra `A`
over `R' = Gamma(T')` with `A/IA = A_0`, where `I` is the (square-zero, hence nilpotent) kernel
of `R' -> R`. Flatness of `A` over `R'` lets a basis of `A/IA` be lifted to a basis of `A`
beginning with `1`, by
`Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent` (Tag 051F); its
multiplication table is a point of `X_d` over `T'` by the representability of Tag 05YM, and it
restricts along `i` to the point given by `g`. Since a thickening is a homeomorphism on points,
that point of `X_d` lands in the open `U_d`, which gives the required filler.

The multiplication table of a finite free algebra with respect to a basis whose first vector is
`1` is `AlgebraicGeometry.FiniteFreeAlgebra.ofBasis`; the two facts used about it are that it is
unchanged by an algebra equivalence matching the bases and that it is compatible with base
change. Identifying the table of the universal family itself with the identity point of `X_d`
is `AlgebraicGeometry.universalTotalGammaBasis_structure`, and it is what ties the construction
back to the universal object.

## References

* [Stacks Project, Tag 0FL1](https://stacks.math.columbia.edu/tag/0FL1)
* [Stacks Project, Tag 0FL0](https://stacks.math.columbia.edu/tag/0FL0)
* [Stacks Project, Tag 0FKZ](https://stacks.math.columbia.edu/tag/0FKZ)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
* [Stacks Project, Tag 051F](https://stacks.math.columbia.edu/tag/051F)
-/

public section

open CategoryTheory CategoryTheory.Limits
  AlgebraicGeometry.FiniteFreeAlgebra

universe u

/-- Over a flat module, a family whose reduction modulo a nilpotent ideal is a basis is itself a
basis. -/
private theorem Module.Flat.exists_basis_eq_of_mkQ {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Flat R M] {I : Ideal R} (hI : IsNilpotent I)
    (bQ : Module.Basis ι (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))) (x : ι → M)
    (hx : ∀ i, (I • (⊤ : Submodule R M)).mkQ (x i) = bQ i) :
    ∃ b : Module.Basis ι R M, ⇑b = x := by
  have h := (Module.Flat.linearIndependent_and_span_eq_top_mkQ_comp_iff_of_isNilpotent I hI x).mp
    (by
      rw [show (I • (⊤ : Submodule R M)).mkQ ∘ x = ⇑bQ from funext hx]
      exact ⟨bQ.linearIndependent, bQ.span_eq⟩)
  exact ⟨.mk h.1 h.2.ge, Module.Basis.coe_mk _ _⟩

/-- Let `R' → R` be surjective with kernel `I` and let the `R`-algebra `A₀` be identified with
`A ⧸ IA` for an `R'`-algebra `A`. A basis of `A₀` over `R` gives a basis of `A ⧸ I • ⊤` over
`R' ⧸ I` matching it under that identification. -/
private theorem Algebra.exists_basis_quotient_smul_top_of_ringEquiv
    {R' R A₀ A : Type*} [CommRing R'] [CommRing R] [CommRing A₀] [CommRing A]
    [Algebra R' R] [Algebra R A₀] [Algebra R' A]
    (hsurj : Function.Surjective (algebraMap R' R))
    (e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R' A) (RingHom.ker (algebraMap R' R)))
    (he : ∀ r : R', e (algebraMap R A₀ (algebraMap R' R r)) =
      Ideal.Quotient.mk _ (algebraMap R' A r))
    {ι : Type*} (b : Module.Basis ι R A₀) :
    ∃ bQ : Module.Basis ι (R' ⧸ RingHom.ker (algebraMap R' R))
        (A ⧸ RingHom.ker (algebraMap R' R) • (⊤ : Submodule R' A)),
      ∀ i a, (RingHom.ker (algebraMap R' R) • (⊤ : Submodule R' A)).mkQ a = bQ i ↔
        e.symm (Ideal.Quotient.mk _ a) = b i := by
  let eR : (R' ⧸ RingHom.ker (algebraMap R' R)) ≃+* R :=
    RingHom.quotientKerEquivOfSurjective hsurj
  let : Module (R' ⧸ RingHom.ker (algebraMap R' R)) A₀ := Module.compHom A₀ eR.toRingHom
  let ψ₀ : (A ⧸ RingHom.ker (algebraMap R' R) • (⊤ : Submodule R' A)) ≃ₗ[R']
      A ⧸ (RingHom.ker (algebraMap R' R)).map (algebraMap R' A) :=
    (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map _)).trans
      (Submodule.Quotient.restrictScalarsEquiv R' _)
  let ψ : (A ⧸ RingHom.ker (algebraMap R' R) • (⊤ : Submodule R' A)) ≃ₗ[R' ⧸
      RingHom.ker (algebraMap R' R)] A₀ :=
    { ψ₀.toAddEquiv.trans e.symm.toAddEquiv with
      map_smul' := by
        intro c x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
        rw [Submodule.mkQ_apply, Module.Quotient.mk_smul_mk]
        show e.symm (Ideal.Quotient.mk _ (r • a)) =
          eR (Ideal.Quotient.mk _ r) • e.symm (Ideal.Quotient.mk _ a)
        rw [RingHom.quotientKerEquivOfSurjective_apply_mk, Algebra.smul_def r a, map_mul,
          map_mul, ← he r, e.symm_apply_apply, Algebra.smul_def] }
  let b₀ : Module.Basis ι (R' ⧸ RingHom.ker (algebraMap R' R)) A₀ :=
    b.mapCoeffs eR.symm fun c x => by
      show eR (eR.symm c) • x = c • x
      rw [eR.apply_symm_apply]
  refine ⟨b₀.map ψ.symm, fun i a => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.eq_symm_apply, Module.Basis.mapCoeffs_apply]
  exact Iff.rfl

/-- Let `R' → R` be surjective with nilpotent kernel `I`, let `A` be a flat `R'`-algebra and let
the `R`-algebra `A₀` be identified with `A ⧸ IA`. A basis of `A₀` over `R` beginning with `1`
lifts to a basis of `A` over `R'` beginning with `1`. -/
private theorem Algebra.exists_basis_lift_of_ringEquiv_quotient
    {R' R A₀ A : Type*} [CommRing R'] [CommRing R] [CommRing A₀] [CommRing A]
    [Algebra R' R] [Algebra R A₀] [Algebra R' A] [Module.Flat R' A]
    (hsurj : Function.Surjective (algebraMap R' R))
    (hI : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (e : A₀ ≃+* A ⧸ Ideal.map (algebraMap R' A) (RingHom.ker (algebraMap R' R)))
    (he : ∀ r : R', e (algebraMap R A₀ (algebraMap R' R r)) =
      Ideal.Quotient.mk _ (algebraMap R' A r))
    {d : ℕ} [NeZero d] (b : Module.Basis (Fin d) R A₀) (hb : b 0 = 1) :
    ∃ b' : Module.Basis (Fin d) R' A, b' 0 = 1 ∧
      ∀ i, e.symm (Ideal.Quotient.mk _ (b' i)) = b i := by
  classical
  obtain ⟨bQ, hbQ⟩ := exists_basis_quotient_smul_top_of_ringEquiv hsurj e he b
  have hq := Submodule.mkQ_surjective (RingHom.ker (algebraMap R' R) • (⊤ : Submodule R' A))
  let x : Fin d → A := fun i => if i = 0 then 1 else (hq (bQ i)).choose
  have hx : ∀ i, (RingHom.ker (algebraMap R' R) • (⊤ : Submodule R' A)).mkQ (x i) = bQ i := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa [x] using (hbQ 0 1).2 (by rw [map_one, map_one, hb])
    · simpa [x, hi] using (hq (bQ i)).choose_spec
  obtain ⟨b', hb'⟩ := Module.Flat.exists_basis_eq_of_mkQ hI bQ x hx
  refine ⟨b', by simp [hb', x], fun i => (hbQ i (b' i)).1 ?_⟩
  rw [hb']
  exact hx i

namespace AlgebraicGeometry

open scoped BigOperators
open scoped TensorProduct

/-- The polynomial expressing associativity of the universal structure constants at one index. -/
private noncomputable def associativityRelation (d : ℕ) [NeZero d]
    (i j k m : Fin d) : MvPolynomial (CoeffIndex d) ℤ :=
  (∑ l, universalCoeff d i j l * universalCoeff d l k m) -
    ∑ l, universalCoeff d i l m * universalCoeff d j k l

/-- The polynomial expressing symmetry of the universal structure constants at one index. -/
private noncomputable def commutativityRelation (d : ℕ) [NeZero d]
    (i j k : Fin d) : MvPolynomial (CoeffIndex d) ℤ :=
  universalCoeff d i j k - universalCoeff d j i k

/-- The polynomial expressing that the first basis vector is a unit, at one index. -/
private noncomputable def unitRelation (d : ℕ) [NeZero d]
    (i j : Fin d) : MvPolynomial (CoeffIndex d) ℤ :=
  universalCoeff d i 0 j - MvPolynomial.C (if i = j then 1 else 0)

/-- The defining relations of the universal coefficient ring form a finite set: each of the three
families is indexed by a finite product of copies of `Fin d`. -/
private theorem universalRelations_finite (d : ℕ) [NeZero d] :
    (universalRelations d).Finite := by
  classical
  have key {α ι : Type} [Finite ι] (f : ι → α) : {p | ∃ i, p = f i}.Finite :=
    (Set.finite_range f).subset fun _ ⟨i, hi⟩ => ⟨i, hi.symm⟩
  simpa only [universalRelations, associativityRelation, commutativityRelation, unitRelation,
    Prod.exists] using
    ((key fun x : Fin d × Fin d × Fin d × Fin d =>
        associativityRelation d x.1 x.2.1 x.2.2.1 x.2.2.2).union
      (key fun x : Fin d × Fin d × Fin d => commutativityRelation d x.1 x.2.1 x.2.2)).union
      (key fun x : Fin d × Fin d => unitRelation d x.1 x.2)

/-- The universal coefficient ring `A_d` is of finite presentation over the integers, being a
polynomial ring in finitely many variables modulo finitely many relations. -/
theorem universalRing_finitePresentation (d : ℕ) [NeZero d] :
    Algebra.FinitePresentation ℤ (universalRing d) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (universalRelations_finite d))

/-- The base `X_d` is locally of finite presentation over the terminal scheme. -/
theorem scheme_locallyOfFinitePresentation (d : ℕ) [NeZero d] :
    LocallyOfFinitePresentation
      (specULiftZIsTerminal.from (scheme.{u} d)) := by
  have : Algebra.FinitePresentation ℤ (universalRing d) :=
    universalRing_finitePresentation d
  have : Algebra.FinitePresentation ℤ (ULift.{u} (universalRing d)) :=
    Algebra.FinitePresentation.equiv
      (ULift.algEquiv (R := ℤ) (A := universalRing d)).symm
  let : Algebra (ULift.{u} ℤ) (ULift.{u} (universalRing d)) :=
    Algebra.compHom _ ULift.ringEquiv.toRingHom
  have hfp : (algebraMap (ULift.{u} ℤ) (ULift.{u} (universalRing d))).FinitePresentation := by
    show ((algebraMap ℤ (ULift.{u} (universalRing d))).comp
      ULift.ringEquiv.toRingHom).FinitePresentation
    exact (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
      (RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective)
  rw [show specULiftZIsTerminal.from (scheme.{u} d) =
      Spec.map
        (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) (ULift.{u} (universalRing d)))) from
      specULiftZIsTerminal.hom_ext _ _, LocallyOfFinitePresentation.SpecMap_iff]
  exact hfp

/-- The open `U_d` is locally of finite presentation over the terminal scheme, being an open
subscheme of `X_d`. -/
private theorem universalSyntomicOpen_locallyOfFinitePresentation
    (d : ℕ) [NeZero d] :
    LocallyOfFinitePresentation
      (specULiftZIsTerminal.from (universalSyntomicOpen.{u} d).toScheme) := by
  have := scheme_locallyOfFinitePresentation.{u} d
  rw [show specULiftZIsTerminal.from (universalSyntomicOpen.{u} d).toScheme =
      (universalSyntomicOpen.{u} d).ι ≫
        specULiftZIsTerminal.from (scheme.{u} d) from
      specULiftZIsTerminal.hom_ext _ _]
  infer_instance

/-- **Stacks Project, Tag 0FL1.** The open subscheme `U_d` of the base of the universal finite
free family of rank `d` over which that family is syntomic (Tag 0FL0) is smooth over the
terminal scheme `Spec(ULift ZZ)`, which is `Spec(ZZ)` in the universe of the test schemes. -/
@[stacks 0FL1]
public instance universalSyntomicOpen_smooth_uLift (d : ℕ) [NeZero d] :
    Smooth (specULiftZIsTerminal.from (universalSyntomicOpen.{u} d).toScheme) := by
  rw [Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth]
  refine ⟨universalSyntomicOpen_locallyOfFinitePresentation d, ?_⟩
  intro T T' hT hT' i hi g h hgf
  classical
  let s := universalAlgebraStructure d
  letI := s.ring
  let F := universalFamily.{u} d s
  let fT : T ⟶ scheme.{u} d := g ≫ (universalSyntomicOpen.{u} d).ι
  haveI : IsAffine (universalTotalScheme.{u} d s) := by
    dsimp [universalTotalScheme]
    infer_instance
  haveI : IsClosedImmersion i := hi.1
  letI : Algebra Γ(scheme.{u} d, ⊤) Γ(universalTotalScheme.{u} d s, ⊤) := F.appTop.hom.toAlgebra
  letI : Algebra Γ(T, ⊤) Γ(pullback F fT, ⊤) := (pullback.snd F fT).appTop.hom.toAlgebra
  letI : Algebra Γ(T', ⊤) Γ(T, ⊤) := i.appTop.hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap Γ(T', ⊤) Γ(T, ⊤)) :=
    Scheme.Hom.app_surjective i ⊤ (isAffineOpen_top T')
  obtain ⟨A, _, _, hSyn, e, he⟩ := Stacks.Smoothing.exists_syntomic_lift_of_surjective _ _ _ hsurj
    (algebraSyntomic_of_affineSyntomic (pullback.snd F fT)
      ((factorsThrough_universalSyntomicOpen_iff d T fT).mp ⟨g, rfl⟩))
  have hI : IsNilpotent (RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app i ⊤))) := by
    refine ⟨2, ?_⟩
    have hh := congrArg (fun J : T'.IdealSheafData =>
      J.ideal ⟨⊤, isAffineOpen_top T'⟩) hi.2
    rw [Scheme.IdealSheafData.ideal_pow] at hh
    simpa [Scheme.Hom.ker_apply, Scheme.Hom.appTop] using hh
  haveI : Module.Flat Γ(T', ⊤) A := hSyn.flat
  obtain ⟨b, hb₀, hb⟩ := Algebra.exists_basis_lift_of_ringEquiv_quotient hsurj hI e he
    (affinePullbackGammaBasis F fT (Fin d) (universalTotalGammaBasis.{u} d))
    (affinePullbackGammaBasis_zero F fT d _ (universalTotalGammaBasis_zero.{u} d))
  let fT' : T' ⟶ scheme.{u} d := ((representation.{u} d).equiv T').symm (ofBasis b hb₀)
  have hcomm : i ≫ fT' = fT := by
    apply ((representation.{u} d).equiv T).injective
    rw [← (representation.{u} d).naturality i fT', Equiv.apply_symm_apply,
      ← affinePullbackGammaBasis_structure_of_map F fT _ (universalTotalGammaBasis_zero.{u} d)
        (universalTotalGammaBasis_structure.{u} d)]
    exact ofBasis_map _ (e.symm.toRingHom.comp (Ideal.Quotient.mk _))
      (fun r => e.symm_apply_eq.mpr (he r).symm) b hb₀ _ _ hb
  have hrange : Set.range fT' ⊆ Set.range (universalSyntomicOpen.{u} d).ι := by
    rintro _ ⟨t', rfl⟩
    obtain ⟨t, rfl⟩ := hi.isThickening.2 t'
    exact ⟨g t, (congrArg (fun f : T ⟶ scheme.{u} d => f t) hcomm).symm⟩
  refine ⟨IsOpenImmersion.lift (universalSyntomicOpen.{u} d).ι fT' hrange,
    specULiftZIsTerminal.hom_ext _ _, ?_⟩
  rw [← cancel_mono (universalSyntomicOpen.{u} d).ι, Category.assoc, IsOpenImmersion.lift_fac]
  exact hcomm

/-- **Stacks Project, Tag 0FL1.** The open subscheme `U_d` of Tag 0FL0 is smooth over
`Spec(ZZ)`, in the literal form of the source: the structure morphism to the spectrum of the
integers themselves. -/
@[stacks 0FL1]
public instance universalSyntomicOpen_smooth (d : ℕ) [NeZero d] :
    Smooth (specZIsTerminal.from (universalSyntomicOpen d).toScheme) := by
  let e : Spec (.of (ULift.{0} ℤ)) ⟶ Spec (.of ℤ) := specZIsTerminal.from _
  haveI : IsIso e := isIso_of_isTerminal specULiftZIsTerminal specZIsTerminal e
  haveI : Smooth e := inferInstance
  haveI : Smooth (specULiftZIsTerminal.from
      (universalSyntomicOpen d).toScheme) :=
    universalSyntomicOpen_smooth_uLift.{0} d
  rw [show specZIsTerminal.from (universalSyntomicOpen d).toScheme =
      specULiftZIsTerminal.from (universalSyntomicOpen d).toScheme ≫ e from
    specZIsTerminal.hom_ext _ _]
  infer_instance

end AlgebraicGeometry

end
