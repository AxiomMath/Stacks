module

public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.FibreDescent
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

@[expose] public section

/-!
# Perfect ring maps and finite projective resolutions

A ring map `A → B` is perfect exactly when `B` can be written as `A[x_1, …, x_n]/I` in such a way
that `B`, viewed as a module over the polynomial algebra, admits a finite resolution by finite
projective modules over that algebra, and then this holds for every such presentation.

## Main results

* `Algebra.perfect_iff_pseudoCoherent_and_exists_flat_roof` (Stacks 068Y): `Algebra.Perfect` is
  Stacks 067H (2) as worded, pseudo-coherence together with a bounded complex of flat modules
  joined to `B[0]` by a roof of quasi-isomorphisms.
* `Algebra.perfect_iff_pseudoCoherent_and_moduleHasFiniteTorDimension`: the same, with finite Tor
  dimension read off any certified derived tensor product on any model of `D(A)`.
* `Algebra.perfect_iff_exists_finite_projective_resolution`: Stacks 068Y as worded, for `A` and `B`
  in one universe.
* `Algebra.Perfect.exists_finite_projective_resolution`: Stacks 068Y at every presentation: a
  perfect algebra has a finite resolution by finite projective modules over the polynomial algebra
  of each of its finite polynomial presentations.
* `Algebra.Perfect.of_flat_of_finitePresentation` (Stacks 067J).

## Implementation notes

A presentation `B = A[x_1, …, x_n]/I` is recorded by a surjective `A`-algebra map
`α : A[x_1, …, x_n] → B`; the induced module structure on `B` is `Module.compHom B α.toRingHom`,
and a finite resolution by finite projective modules is a `ModuleResolution` over the polynomial
algebra whose terms are finite projective and which vanishes above some degree.

`Algebra.Perfect` is defined by the right-hand side of Stacks 068Y, read as pseudo-coherence and
finite projective dimension over a presentation, so Stacks 068Y compares it with Stacks 067H (2) as
worded. Neither side mentions a derived category, and neither does the forward direction of the
proof: the resolution by finite projective modules over `P = A[x_1, …, x_n]` that
`Algebra.perfect_iff_pseudoCoherent_and_exists_finite_projective_resolution` provides is a bounded
complex of projective `P`-modules joined to `B[0]` by a quasi-isomorphism, and restriction of
scalars along the flat map `A → P` makes it a bounded complex of flat `A`-modules.

The reverse direction is Stacks 068X, applied with `d = n` at any presentation: the polynomial
algebra is flat over `A` and every fibre `P ⊗_A κ(p)` is a polynomial algebra over a field in `n`
variables, so has global dimension at most `n`. Pseudo-coherence of the ring map quantifies over
every finite polynomial presentation, and Stacks 065H turns it into pseudo-coherence of `B` over
`P`. The Tor-amplitude hypothesis of Stacks 068X is stated termwise on bounded above flat
representatives, which `StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude`
supplies from the roof, read at the canonical certified derived tensor product. Perfectness over
`P` is then a finite resolution by finite projective `P`-modules (Stacks 066Q). These steps read
the standard model of a derived category; the reverse direction of Stacks 068Y and
`Algebra.Perfect.exists_finite_projective_resolution` share them, and their statements mention no
derived category. `Algebra.perfect_iff_pseudoCoherent_and_moduleHasFiniteTorDimension` then holds
at any model and any certificate, through the roof.

## References

* [The Stacks Project, Lemma 15.83.2 (068Y)](https://stacks.math.columbia.edu/tag/068Y)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingHom

universe u v w

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

/-! ### Stacks 068X at a presentation -/

/-- **A finite resolution by projective modules over a flat algebra is a flat roof.** A resolution
of a `P`-module `M` by projective `P`-modules that vanishes above degree `d`, over a flat
`A`-algebra `P`, restricts to a bounded complex of flat `A`-modules joined to `M[0]` by a roof of
quasi-isomorphisms. The complex is the cochain complex of the resolution read as a Mathlib
`ProjectiveResolution` (`ProjectiveResolution.cochainComplex`, with its quasi-isomorphism
`ProjectiveResolution.π'`), restricted to `A`. -/
private theorem exists_flat_roof_restrictScalars {A P : Type u} [CommRing A] [CommRing P]
    [Algebra A P] [Module.Flat A P] {M : Type u} [AddCommGroup M] [Module A M] [Module P M]
    [IsScalarTower A P M] {d : ℕ}
    (F : ModuleResolution P M) (hF : ∀ i : ℕ, Module.Projective P (F.complex.X i))
    (hzero : ∀ i : ℕ, d < i → IsZero (F.complex.X i)) :
    ∃ (a b : ℤ) (E : CochainComplex (ModuleCat.{u} A) ℤ), (∀ i, Module.Flat A (E.X i)) ∧
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
        CochainComplex.QuasiIsoRoof E
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) := by
  let G := ModuleCat.restrictScalars.{u} (algebraMap A P)
  let R : ProjectiveResolution (ModuleCat.of P M) :=
    { complex := F.complex
      projective := fun n => have := hF n; inferInstance
      hasHomology := F.hasHomology
      π := F.π
      quasiIso := F.quasiIso }
  let eM : G.obj (ModuleCat.of P M) ≃ₗ[A] M :=
    { toFun := fun m => (m : M)
      invFun := fun m => (m : G.obj (ModuleCat.of P M))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun a m => IsScalarTower.algebraMap_smul P a (show M from m) }
  have hGE : R.cochainComplex.IsStrictlyGE (-(d : ℤ)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat (by omega : i ≤ 0)
    exact (hzero k (by omega)).of_iso (R.cochainComplexXIso _ k)
  refine ⟨-(d : ℤ), 0, (G.mapHomologicalComplex _).obj R.cochainComplex, fun i => ?_,
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := R.cochainComplex) G _).2 hGE,
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := R.cochainComplex) G _).2
      inferInstance,
    ((CochainComplex.QuasiIsoRoof.of_quasiIso R.π' inferInstance).map G).precomp_right_iso
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).mapIso eM.toModuleIso.symm ≪≫
        ((G.mapCochainComplexSingleFunctor 0).app (ModuleCat.of P M)).symm)⟩
  let : Module A (R.cochainComplex.X i) := Module.compHom _ (algebraMap A P)
  have : IsScalarTower A P (R.cochainComplex.X i) := .of_algebraMap_smul fun _ _ => rfl
  exact Module.Flat.trans A P (R.cochainComplex.X i)

/-- **Stacks 068X at a presentation.** If `A → B` is pseudo-coherent and `B[0]` is joined by a roof
of quasi-isomorphisms to a bounded complex of flat `A`-modules, then for every finite polynomial
presentation `α : A[x_1, …, x_n] → B`, `B` has a finite resolution by finite projective
`A[x_1, …, x_n]`-modules: the fibres of the polynomial algebra over `A` have global dimension at
most `n`. -/
private theorem exists_finite_projective_resolution_of_exists_flat_roof {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.PseudoCoherent A B]
    (hroof : ∃ (a b : ℤ) (E : CochainComplex (ModuleCat.{u} A) ℤ), (∀ i, Module.Flat A (E.X i)) ∧
      E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
        CochainComplex.QuasiIsoRoof E
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)))
    {n : ℕ} (α : MvPolynomial (Fin n) A →ₐ[A] B) (hα : Function.Surjective α) :
    letI : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    ∃ (d : ℕ) (F : ModuleResolution (MvPolynomial (Fin n) A) B),
      (∀ i, Module.Finite (MvPolynomial (Fin n) A) (F.complex.X i) ∧
        Module.Projective (MvPolynomial (Fin n) A) (F.complex.X i)) ∧
      ∀ i, d < i → IsZero (F.complex.X i) := by
  let D := StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring A
  obtain ⟨a, b, hamp⟩ :=
    (StacksDraft.TorAmplitude.moduleHasFiniteTorDimension_iff_exists_flat_roof D.comparison
      D.isLeftDerived (ModuleCat.of A B)).mpr hroof
  have hpseudo := (PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent
    (R := A) ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) 0).2.mp
    ((Algebra.pseudoCoherent_iff_exists_polynomialPresentation A B).mp inferInstance) n α hα
  let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
  let eR := restrictScalarsToBaseIso α
  exact (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution B).mp
    (StacksDraft.Perfect.isPerfect_of_iso (restrictScalarsPresentationIso α).symm
      (StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le
        a b n (polynomial_fibre_globalDimension_le A n) _ hpseudo fun E hbdd hflat he =>
          StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude
            D.comparison D.isLeftDerived _ a b hamp E hbdd hflat (he.map fun e => eR.symm ≪≫ e)).1)

/-! ### `Algebra.Perfect` and Stacks 067H (2) as worded -/

/-- **Stacks 068Y.** An `A`-algebra `B` is perfect in the sense of `Algebra.Perfect` (a resolution
by finite free modules and finite projective dimension over a polynomial presentation) exactly when
it is perfect in the sense of Stacks 067H (2) as worded: pseudo-coherent, with `B` of finite Tor
dimension as an `A`-module, read off a bounded complex of flat `A`-modules joined to `B[0]` by a
roof of quasi-isomorphisms (Stacks 0654). The statement mentions no derived category. The forward
direction restricts a finite resolution by finite projective modules over a polynomial algebra to
`A`, reading no model; the reverse direction is Stacks 068X at a presentation, which reads
Stacks 066Q and 065H in the standard model. -/
@[stacks 068Y]
public theorem _root_.Algebra.perfect_iff_pseudoCoherent_and_exists_flat_roof {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.Perfect A B ↔
      Algebra.PseudoCoherent A B ∧
        ∃ (a b : ℤ) (E : CochainComplex (ModuleCat.{u} A) ℤ), (∀ i, Module.Flat A (E.X i)) ∧
          E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
            CochainComplex.QuasiIsoRoof E
              ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)) := by
  rw [Algebra.perfect_iff_pseudoCoherent_and_exists_finite_projective_resolution]
  refine and_congr_right fun _ => ⟨fun ⟨n, α, hα, d, F, hF, hd⟩ => ?_, fun hroof => ?_⟩
  · let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    have : Module.Flat A (MvPolynomial (Fin n) A) := Module.Flat.of_free
    have : IsScalarTower A (MvPolynomial (Fin n) A) B := .of_algebraMap_smul fun a b =>
      (congrArg (· * b) (α.commutes a)).trans (Algebra.smul_def a b).symm
    exact exists_flat_roof_restrictScalars F (fun i => (hF i).2) hd
  · obtain ⟨n, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
    exact ⟨n, α, hα, exists_finite_projective_resolution_of_exists_flat_roof hroof α hα⟩

/-- **Stacks 068Y as worded.** When `A` and `B` live in one universe, `B` is perfect over `A`
exactly when, for some presentation `α : A[x₁, …, xₙ] → B`, `B` itself, made an
`A[x₁, …, xₙ]`-module through `α`, has a finite resolution by finite projective modules: such a
resolution makes `A → B` pseudo-coherent, so pseudo-coherence drops from the right-hand side of
`Algebra.perfect_iff_pseudoCoherent_and_exists_finite_projective_resolution`. The statement
mentions no derived category; the proof reads Stacks 066Q and 0658 in the standard model, which
make `B` pseudo-coherent over the polynomial algebra. -/
public theorem _root_.Algebra.perfect_iff_exists_finite_projective_resolution {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] :
    Algebra.Perfect A B ↔
      ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
        letI : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
        ∃ (d : ℕ) (F : ModuleResolution (MvPolynomial (Fin n) A) B),
          (∀ i, Module.Finite (MvPolynomial (Fin n) A) (F.complex.X i) ∧
            Module.Projective (MvPolynomial (Fin n) A) (F.complex.X i)) ∧
          ∀ i, d < i → IsZero (F.complex.X i) := by
  refine Algebra.perfect_iff_pseudoCoherent_and_exists_finite_projective_resolution.trans
    (and_iff_right_of_imp fun ⟨n, α, hα, hres⟩ => ?_)
  let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
  obtain ⟨hpseudo, -⟩ :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension _).1.mp
      (StacksDraft.Perfect.isPerfect_of_iso (restrictScalarsPresentationIso α)
        ((StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution B).mpr
          hres))
  exact (Algebra.pseudoCoherent_iff_exists_polynomialPresentation A B).mpr ⟨n, α, hα, hpseudo⟩

/-- **Stacks 068Y at every presentation.** If `B` is perfect over `A`, then for every finite
polynomial presentation `α : A[x₁, …, xₙ] → B`, `B`, made an `A[x₁, …, xₙ]`-module through `α`, has
a finite resolution by finite projective modules, not only for the presentation that
`Algebra.perfect_iff_exists_finite_projective_resolution` provides. By Stacks 066Q
(`StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution`) this says that `B`
is a perfect `A[x₁, …, xₙ]`-module. The statement mentions no derived category; the proof is
Stacks 068X at `α`. -/
public theorem _root_.Algebra.Perfect.exists_finite_projective_resolution {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [h : Algebra.Perfect A B] {n : ℕ}
    (α : MvPolynomial (Fin n) A →ₐ[A] B) (hα : Function.Surjective α) :
    letI : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
    ∃ (d : ℕ) (F : ModuleResolution (MvPolynomial (Fin n) A) B),
      (∀ i, Module.Finite (MvPolynomial (Fin n) A) (F.complex.X i) ∧
        Module.Projective (MvPolynomial (Fin n) A) (F.complex.X i)) ∧
      ∀ i, d < i → IsZero (F.complex.X i) :=
  exists_finite_projective_resolution_of_exists_flat_roof
    (Algebra.perfect_iff_pseudoCoherent_and_exists_flat_roof.mp h).2 α hα

/-- **Stacks 067H (2) as worded, at any model and any certificate.** An `A`-algebra `B` is perfect
exactly when it is pseudo-coherent and `B` has finite Tor dimension as an `A`-module, read off any
certified derived tensor product on any model of `D(A)`. -/
public theorem _root_.Algebra.perfect_iff_pseudoCoherent_and_moduleHasFiniteTorDimension
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
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
    Algebra.Perfect A B ↔
      Algebra.PseudoCoherent A B ∧
        StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension derivedTensor comparison
          isLeftDerived (ModuleCat.of A B) :=
  Algebra.perfect_iff_pseudoCoherent_and_exists_flat_roof.trans
    (and_congr_right' (StacksDraft.TorAmplitude.moduleHasFiniteTorDimension_iff_exists_flat_roof
      comparison isLeftDerived _).symm)

/-- The Tor half of a perfect algebra, at any model of `D(A)` and any certified derived tensor
product: `B` has finite Tor dimension as an `A`-module. -/
public theorem _root_.Algebra.Perfect.moduleHasFiniteTorDimension {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] [h : Algebra.Perfect A B]
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
    StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension derivedTensor comparison isLeftDerived
      (ModuleCat.of A B) :=
  ((Algebra.perfect_iff_pseudoCoherent_and_moduleHasFiniteTorDimension comparison
    isLeftDerived).mp h).2

/-- **Stacks 067J.** A flat algebra of finite presentation is perfect.

`B` is isomorphic to the quotient of a polynomial algebra over `A` by the kernel of a presentation,
which lives in the universe of `A`. That quotient is pseudo-coherent
(`Algebra.PseudoCoherent.of_flat_of_finitePresentation`) and, being flat, is its own bounded flat
roof, so it is perfect by Stacks 068Y; `Algebra.Perfect.equiv` carries this back to `B`. -/
@[stacks 067J]
public theorem _root_.Algebra.Perfect.of_flat_of_finitePresentation (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] [Algebra.FinitePresentation A B] :
    Algebra.Perfect A B := by
  obtain ⟨n, α, hα, -⟩ := Algebra.FinitePresentation.out (R := A) (A := B)
  let e := Ideal.quotientKerAlgEquivOfSurjective hα
  have : Module.Flat A (MvPolynomial (Fin n) A ⧸ ker α) := .of_linearEquiv e.toLinearEquiv
  have : Algebra.FinitePresentation A (MvPolynomial (Fin n) A ⧸ ker α) := .equiv e.symm
  refine Algebra.Perfect.equiv ?_ e
  exact Algebra.perfect_iff_pseudoCoherent_and_exists_flat_roof.mpr
    ⟨.of_flat_of_finitePresentation _ _, 0, 0, _,
      HomologicalComplex.flat_single_obj_X _ (ComplexShape.up ℤ) 0, inferInstance, inferInstance,
      .of_iso (Iso.refl _)⟩

end RingHom
