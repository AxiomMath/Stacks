module

public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.FibreDescent
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs

@[expose] public section

/-!
# Perfect ring maps and finite projective resolutions

A ring map `A → B` is perfect exactly when `B` can be written as `A[x_1, …, x_n]/I` in such a way
that `B`, viewed as a module over the polynomial algebra, admits a finite resolution by finite
projective modules over that algebra.

## Main results

* `RingHom.isPerfectRingMap_iff_exists_flat_roof`: perfectness of a ring map depends neither on
  the model of `D(A)` nor on the certified derived tensor product.
* `RingHom.isPerfectRingMap_iff_exists_finite_projective_resolution` (Stacks 068Y).

## Implementation notes

A presentation `B = A[x_1, …, x_n]/I` is recorded by a surjective `A`-algebra map
`α : A[x_1, …, x_n] → B`; the induced module structure on `B` is `Module.compHom B α.toRingHom`,
and a finite resolution by finite projective modules is a `ModuleResolution` over the polynomial
algebra whose terms are finite projective and which vanishes above some degree.

The two halves of perfectness are handled separately. Pseudo-coherence of the ring map quantifies
over every finite polynomial presentation, and Stacks 065H turns that into a statement about a
single presentation, so it matches the existential form above directly. Finite Tor dimension is
transported across the presentation: the chosen one makes `B` an algebra over
`P = A[x_1, …, x_n]`, and restriction of scalars along the flat map `A → P` identifies `B[0]` over
`A` with the restriction of `B[0]` over `P`.

Perfectness over `P` then follows from Stacks 068X, applied with `d = n`: the polynomial algebra is
flat over `A` and every fibre `P ⊗_A κ(p)` is a polynomial algebra over a field in `n` variables,
so has global dimension at most `n`. Its Tor-amplitude hypothesis is stated termwise on bounded
above flat representatives, which `StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_`
`hasTorAmplitude` supplies from Tor amplitude against the certified derived tensor product that
`RingHom.IsPerfectRingMap` carries. Conversely Stacks 0658 turns perfectness over `P` back into
pseudo-coherence together with a bounded flat representative, whose restriction of scalars is a
bounded flat representative over `A`, hence Tor amplitude by Stacks 0654.

Finite Tor dimension is quantified over the certified derived tensor product exactly as
`RingHom.IsPerfectRingMap` has it; no canonical derived tensor product is constructed.

`RingHom.isPerfectRingMap_iff_exists_flat_roof` holds for any model of `D(A)`: its right-hand
side, a bounded complex of flat modules joined to `B[0]` by a roof of quasi-isomorphisms, mentions
no derived category. The other statements here read `D(A)` in the standard model.

## References

* [The Stacks Project, Lemma 15.83.2 (068Y)](https://stacks.math.columbia.edu/tag/068Y)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

universe u v w

/-! ### Independence of the model and of the certificate -/

/-- Perfectness of a ring map depends neither on the model of `D(A)` nor on the certified derived
tensor product: it is pseudo-coherence together with a bounded complex of flat `A`-modules joined
to `B[0]` by a roof of quasi-isomorphisms. -/
public theorem isPerfectRingMap_iff_exists_flat_roof
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {derivedTensor :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A)}
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    IsPerfectRingMap A B derivedTensor comparison isLeftDerived ↔
      Algebra.PseudoCoherent A B ∧
        ∃ (a b : ℤ) (E : CochainComplex (ModuleCat.{u} A) ℤ), (∀ i, Module.Flat A (E.X i)) ∧
          E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
            CochainComplex.QuasiIsoRoof E
              ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)) :=
  and_congr_right' (StacksDraft.TorAmplitude.moduleHasFiniteTorDimension_iff_exists_flat_roof
    comparison isLeftDerived _)

attribute [local instance] HasDerivedCategory.standard

/-! ### Global dimension of the fibres of a polynomial algebra -/

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Global dimension is invariant under a ring isomorphism. -/
theorem ringGlobalDimension_le_of_ringEquiv
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (d : WithBot ℕ∞)
    (h : ringGlobalDimension S ≤ d) : ringGlobalDimension R ≤ d := by
  refine iSup_le fun M => ?_
  let N := (ModuleCat.restrictScalars e.symm.toRingHom).obj M
  let eM : N ≃ₛₗ[RingHomClass.toRingHom e.symm] M :=
    { __ := AddEquiv.refl M
      map_smul' := fun _ _ => rfl }
  rw [← ModuleCat.projectiveDimension_eq_of_semiLinearEquiv e.symm eM]
  exact (le_iSup (fun X : ModuleCat.{u} S => projectiveDimension X) N).trans h

open MvPolynomial in
/-- Every fibre of `A[x_1, …, x_n]` over `A` is a polynomial algebra in `n` variables over a
field, so has global dimension at most `n`. -/
theorem polynomial_fibre_globalDimension_le
    (A : Type u) [CommRing A] (n : ℕ) (p : PrimeSpectrum A) :
    ringGlobalDimension (TensorProduct A (MvPolynomial (Fin n) A) p.asIdeal.ResidueField)
      ≤ n := by
  let e :=
    (Algebra.TensorProduct.comm A (MvPolynomial (Fin n) A)
        p.asIdeal.ResidueField).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv A p.asIdeal.ResidueField).toRingEquiv
  apply ringGlobalDimension_le_of_ringEquiv e n
  simpa only [ringGlobalDimension, Nat.card_fin] using
    (isRegularRing_and_iSup_projectiveDimension_eq_and_isRegularLocalRing_localization.{u, 0, u}
      p.asIdeal.ResidueField (Fin n)).2.1.le

/-! ### Transport along a polynomial presentation -/

set_option backward.isDefEq.respectTransparency false in
/-- For a surjection `α : S → B` from an `A`-algebra `S`, the restriction to `A` of `B[0]` over
`S` is `B[0]` over `A`. -/
noncomputable def restrictScalarsSingleIso
    {A S B : Type u} [CommRing A] [CommRing S] [CommRing B]
    [Algebra A S] [Algebra A B] (α : S →ₐ[A] B) :
    letI : Module S B := Module.compHom B α.toRingHom
    (ModuleCat.restrictScalars (algebraMap A S)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B) := by
  let : Module S B := Module.compHom B α.toRingHom
  let F := ModuleCat.restrictScalars (algebraMap A S)
  let e : F.obj (ModuleCat.of S B) ≅ ModuleCat.of A B :=
    LinearEquiv.toModuleIso
      (X₁ := F.obj (ModuleCat.of S B)) (X₂ := ModuleCat.of A B)
      { __ := AddEquiv.refl B
        map_smul' := by
          intro a b
          change α (algebraMap A S a) * (show B from b) = a • (show B from b)
          rw [α.commutes, Algebra.smul_def] }
  exact (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of S B) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e

/-! ### Pseudo-coherence through one presentation -/

/-- A ring map is pseudo-coherent exactly when, for some finite polynomial presentation of the
target, the target becomes a pseudo-coherent object over the polynomial algebra. -/
private theorem _root_.Algebra.pseudoCoherent_iff_exists_polynomialPresentation
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.PseudoCoherent A B ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
        PseudoCoherence.IsPseudoCoherent
          ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) := by
  rw [Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent]
  constructor
  · rintro ⟨hfin, h⟩
    let := hfin
    obtain ⟨n, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp hfin
    exact ⟨n, α, hα, (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).mpr fun m => h m n α hα⟩
  · rintro ⟨n, α, hα, h⟩
    have hfin := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mpr
      ⟨n, α, hα⟩
    let := hfin
    exact ⟨hfin, fun m n' α' hα' =>
      (PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent (R := A)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) m).1.mp
        ⟨n, α, hα, (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).mp h m⟩ n' α' hα'⟩

/-- Over a presentation `α : A[x_1, …, x_n] → B`, the restriction of `B[0]` from `B` to the
polynomial algebra is `B[0]` over the polynomial algebra. -/
private noncomputable def restrictScalarsPresentationIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (α : MvPolynomial (Fin n) A →ₐ[A] B) :
    letI : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    (ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) A) B) :=
  ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategorySingleFunctor 0).app
    (ModuleCat.of B B)

/-- Over a presentation `α : A[x_1, …, x_n] → B`, the restriction to `A` of `B[0]` over `B` is
`B[0]` over `A`. -/
private noncomputable def restrictScalarsToBaseIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
    (α : MvPolynomial (Fin n) A →ₐ[A] B) :
    letI : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    (ModuleCat.restrictScalars (algebraMap A (MvPolynomial (Fin n) A))).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{u} α.toRingHom).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B) :=
  (ModuleCat.restrictScalars (algebraMap A (MvPolynomial (Fin n) A))).mapDerivedCategory.mapIso
      (restrictScalarsPresentationIso α) ≪≫ restrictScalarsSingleIso α

/-! ### Perfectness through one presentation -/

/-- A ring map is perfect exactly when, for some finite polynomial presentation of the target,
the target is a perfect module over the polynomial algebra. -/
private theorem isPerfectRingMap_iff_exists_perfect_polynomialPresentation
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    IsPerfectRingMap A B derivedTensor comparison isLeftDerived ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
        let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
        StacksDraft.Perfect.IsPerfectModule (R := MvPolynomial (Fin n) A) B := by
  constructor
  · rintro ⟨hpc, a, b, hamp⟩
    obtain ⟨n, α, hα, hpseudo⟩ :=
      (Algebra.pseudoCoherent_iff_exists_polynomialPresentation A B).mp hpc
    refine ⟨n, α, hα, ?_⟩
    let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    let G := ModuleCat.restrictScalars.{u} (algebraMap A (MvPolynomial (Fin n) A))
    let e₁ := restrictScalarsPresentationIso α
    let eR := restrictScalarsToBaseIso α
    exact StacksDraft.Perfect.isPerfect_of_iso e₁.symm
      (StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le
        a b n (polynomial_fibre_globalDimension_le A n) _ hpseudo fun E hbdd hflat he =>
          StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude
            comparison isLeftDerived _ a b hamp E hbdd hflat (he.map fun e => eR.symm ≪≫ e)).1
  · rintro ⟨n, α, hα, hperfect⟩
    let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    let G := ModuleCat.restrictScalars.{u} (algebraMap A (MvPolynomial (Fin n) A))
    let e₁ := restrictScalarsPresentationIso α
    let eR := restrictScalarsToBaseIso α
    obtain ⟨hpseudo, a, b, E, hEflat, hEGE, hELE, ⟨eE⟩⟩ :=
      (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension
        _).1.mp (StacksDraft.Perfect.isPerfect_of_iso e₁ hperfect)
    refine ⟨(Algebra.pseudoCoherent_iff_exists_polynomialPresentation A B).mpr
      ⟨n, α, hα, hpseudo⟩, a, b,
      (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative comparison isLeftDerived
        _ a b).mpr ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj E, fun i => ?_,
        (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := E) G a).2 hEGE,
        (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := E) G b).2 hELE,
        ⟨eR.symm ≪≫ G.mapDerivedCategory.mapIso eE ≪≫ G.mapDerivedCategoryFactors.app E⟩⟩⟩
    have := hEflat i
    let : Module A (E.X i) := Module.compHom (E.X i) (algebraMap A (MvPolynomial (Fin n) A))
    have : IsScalarTower A (MvPolynomial (Fin n) A) (E.X i) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    exact Module.Flat.trans A (MvPolynomial (Fin n) A) (E.X i)

/-! ### The theorem -/

/-- **Stacks 068Y.** A ring map `A → B` is perfect if and only if there is a presentation
`B = A[x_1, …, x_n]/I` for which `B`, as a module over `A[x_1, …, x_n]`, admits a finite
resolution by finite projective `A[x_1, …, x_n]`-modules. -/
@[stacks 068Y]
public theorem isPerfectRingMap_iff_exists_finite_projective_resolution
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    IsPerfectRingMap A B derivedTensor comparison isLeftDerived ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
        let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
        ∃ (d : ℕ) (F : ModuleResolution (MvPolynomial (Fin n) A) B),
          (∀ i : ℕ, Module.Finite (MvPolynomial (Fin n) A) (F.complex.X i) ∧
            Module.Projective (MvPolynomial (Fin n) A) (F.complex.X i)) ∧
          ∀ i : ℕ, d < i → IsZero (F.complex.X i) := by
  rw [isPerfectRingMap_iff_exists_perfect_polynomialPresentation]
  refine exists_congr fun n => exists_congr fun α => and_congr Iff.rfl ?_
  let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
  exact StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution B

end RingHom
