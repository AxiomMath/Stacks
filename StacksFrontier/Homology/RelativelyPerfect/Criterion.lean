module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.RelativelyPerfect.Tensor
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.GlobalDimension
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.Homology.TorAmplitude.Termwise
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
public import StacksFrontier.RingTheory.PseudoCoherentMap.Surjection
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

@[expose] public noncomputable section

/-!
# Relative perfection is detected by boundedness of the derived fibres

Let `R → A` be a flat ring map of finite presentation and let `K` be a pseudo-coherent object of
`D(A)`. Then `K` is perfect relative to `R` (Stacks 0DHS) if and only if `K` is bounded below and
for every prime `p` of `R` the derived fibre `K ⊗_R^L κ(p)` is bounded below.

## Main results

* `PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow`
  (Stacks 0GHJ).

## Implementation notes

Both conditions of the criterion are *boundedness below*, of `K` itself and of each derived fibre;
neither asks the fibres to be perfect.

The forward implication reads relative perfection on a bounded representative whose terms are flat
over `R`, which is `PseudoCoherence.exists_bounded_relativelyFlat_representative` of
`StacksFrontier.Homology.RelativelyPerfect.Tensor` in the form produced by pseudo-coherence: a
bounded-above complex `P` of finite free `A`-modules, whose restriction of scalars `E` is a
bounded-above complex of `R`-flat modules. For such an `E` derived Tor amplitude against the
certified derived tensor product is the termwise condition
(`StacksDraft.TorAmplitude.hasTorAmplitude_iff_termwise_of_flat`, Stacks 0653), and termwise Tor
amplitude in `[a, b]` bounds cohomology below by `a` both for `E` itself — tested against the
tensor unit — and for every extension of scalars of `E`, in particular for the derived fibres,
which `E` computes because it is K-flat (Stacks 064K).

The reverse implication is the source's argument. Writing `A` as a quotient of a polynomial algebra
`B = R[x_1, …, x_n]`, Stacks 0E1T moves pseudo-coherence of `K` over `A` to pseudo-coherence of its
restriction `L` over `B`, and relative perfection of `L` over `R` gives relative perfection of `K`
by Stacks 0DHU together with the restriction-of-scalars comparison. Perfection of `L` over `B` is
Stacks 068W: for a bounded-below pseudo-coherent complex, perfection over `B` follows from the
derived fibres over the primes of `B` being bounded below. That last input is where the polynomial
presentation is used: the fibre of `B` over a prime `p` of `R` is a polynomial algebra over `κ(p)`,
hence of global dimension at most `n` (Stacks 00OQ and 00OE), so by Stacks 066P the base change to
the fibre loses at most `n` in the lower bound, and the assumed bound on the derived fibre over `R`
becomes a bound on the derived fibre over `B`.

Pseudo-coherence over `A` has one spelling in the tree, not two: both Stacks 0DHS and Stacks 068W
are stated with `StacksDraft.PseudoCoherence.IsPseudoCoherent`. The short name
`PseudoCoherence.IsPseudoCoherent` is not a second notion — it is that same constant, exported
into the root `PseudoCoherence` namespace by
`StacksFrontier.Homology.PseudoCoherent.Characterization` — so applying 068W to an object known to
be pseudo-coherent for 0DHS needs no conversion.

The projective-resolution model of the derived tensor product is compared with the termwise one
here as well, because Stacks 066P records Tor amplitude in that model while the base-change step
needs the termwise one. The comparison is replayed untagged: the providers that own it
(`StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel` and
`StacksFrontier.Homology.RelativelyPerfect.Representative`) keep it private, and it is a dedup
target.

The module structures over `R` obtained by restriction of scalars are recognized behind the
`ModuleCat` wrapper only under a relaxed transparency during unification, so the file sets
`backward.isDefEq.respectTransparency` to `false`, as its providers do.

## References

* [The Stacks Project, Lemma 15.85.9 (0GHJ)](https://stacks.math.columbia.edu/tag/0GHJ)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

open scoped TensorProduct ChangeOfRings

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

/-! ### Restriction of scalars and cohomological bounds -/

/-- An exact additive functor commutes with the cohomology of the derived category. -/
private def homologyMapDerivedIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (i : ℤ) :
    (DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C i).obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact (DerivedCategory.homologyFunctor D i).mapIso
      (F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors D i).app _ ≪≫
    (ShortComplex.mapHomologyIso (P.sc i) F) ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C i).app P).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor C i).mapIso e)

/-- Restriction of scalars detects vanishing of derived cohomology. -/
private lemma isZero_homology_restrictScalars_iff
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  rw [(homologyMapDerivedIso (ModuleCat.restrictScalars f) K i).isZero_iff]
  simp only [ModuleCat.isZero_iff_subsingleton]
  rfl

/-- Restriction of scalars preserves and reflects lower cohomological bounds. -/
private lemma isGE_restrictScalars_iff
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ) :
    ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K).IsGE a ↔ K.IsGE a := by
  simp only [DerivedCategory.isGE_iff, isZero_homology_restrictScalars_iff]

/-- Restriction of scalars detects exactness in every degree of a complex. -/
private lemma isZero_homology_restrictComplex_iff
    {R : Type u} {A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    IsZero (((ModuleCat.restrictScalars f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P |>.homology i) ↔ IsZero (P.homology i) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

/-! ### The projective-resolution model against the termwise one -/

/-- For a K-flat complex `P`, the projective-resolution model
`StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology P M i` of `H^i(P ⊗ᴸ_R M)` is the
  degree-`i` cohomology of the
termwise tensor product complex `P ⊗ M`. -/
def derivedTensorHomologyIsoTermwise {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (M : ModuleCat.{u} R) (i : ℤ) :
    StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology P M i ≅
      (StacksDraft.TorAmplitude.Termwise.tensorComplex P M).homology i := by
  have hq : QuasiIso ((tensorLeft P).map (ProjectiveResolution.of M).π') :=
    StacksDraft.TorAmplitude.quasiIso_tensorLeft_map P hP _
  have hiso : IsIso (HomologicalComplex.homologyMap
      ((tensorLeft P).map (ProjectiveResolution.of M).π') i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance
  exact asIso (HomologicalComplex.homologyMap
      ((tensorLeft P).map (ProjectiveResolution.of M).π') i) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      (StacksDraft.TorAmplitude.tensorSwapIso P
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) ≪≫
        StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso M P ≪≫
        (NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M)
          (ComplexShape.up ℤ)).app P)

/-- At a K-flat complex, projective-resolution Tor amplitude is termwise Tor amplitude. -/
private lemma termwise_torAmplitude_of_derived {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude P a b) :
      StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn P a b :=
  fun M i hi => (derivedTensorHomologyIsoTermwise P hP M i).isZero_iff.1 (h M i hi)

/-! ### Termwise Tor amplitude bounds cohomology from below -/

/-- Testing termwise Tor amplitude against the tensor unit bounds cohomology from below. -/
private lemma isGE_of_termwise_torAmplitude
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ) (hP : StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn P a b) : P.IsGE a := by
  let e : StacksDraft.TorAmplitude.Termwise.tensorComplex P (𝟙_ (ModuleCat.{u} R)) ≅ P :=
    HomologicalComplex.Hom.isoOfComponents (fun j => ρ_ (P.X j))
      (fun j k _ => (MonoidalCategory.rightUnitor_naturality (P.d j k)).symm)
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hP _ i (Or.inl hi)).of_iso (HomologicalComplex.homologyMapIso e i).symm

/-- The underlying module of an algebra over itself, restricted along `algebraMap`, is the algebra
itself as a module. -/
private def restrictScalarsSelfEquiv {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
  { Equiv.refl S with
    map_add' := fun _ _ => rfl
    map_smul' r s := by
      change S at s
      change (algebraMap R S r) * (s : S) = r • (s : S)
      exact (Algebra.smul_def r (s : S)).symm }

/-- Extension followed by restriction of scalars is tensoring with the scalar algebra. -/
private def restrictExtendScalarsIso
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
    StacksDraft.TorAmplitude.Termwise.tensorComplex P (ModuleCat.of R S) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · let e := (TensorProduct.congr restrictScalarsSelfEquiv (LinearEquiv.refl R (P.X i))).trans
      ((TensorProduct.comm R S (P.X i)).trans
        (TensorProduct.congr (LinearEquiv.refl R (P.X i))
          (LinearEquiv.refl R S)))
    let e' : (((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)).X i ≃ₗ[R]
        (StacksDraft.TorAmplitude.Termwise.tensorComplex P (ModuleCat.of R S)).X i :=
      { __ := e.toAddEquiv
        map_smul' r z := by
          change TensorProduct R ((ModuleCat.restrictScalars (algebraMap R S)).obj
            (ModuleCat.of S S)) (P.X i) at z
          change e (r • z) = r • e z
          exact e.map_smul r z }
    exact e'.toModuleIso
  · intro i j hij
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

/-- Extension of scalars preserves the lower bound of a termwise Tor amplitude. -/
private lemma isGE_extendScalars_of_termwise_torAmplitude
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hP : StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn P a b) :
    CochainComplex.IsGE
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) a := by
  let : Algebra R S := f.toAlgebra
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (isZero_homology_restrictComplex_iff f _ i).1 <|
    (hP (ModuleCat.of R S) i (Or.inl hi)).of_iso
      (HomologicalComplex.homologyMapIso (restrictExtendScalarsIso (S := S) P) i)

/-- Finite global dimension bounds the loss of a lower cohomological bound under base change. -/
private lemma isGE_extendScalars_of_globalDimension_le
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (d : ℕ) (hd : ringGlobalDimension R ≤ d)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b n : ℤ)
    [P.IsStrictlyLE n] [∀ i, Module.Flat R (P.X i)]
    (hP : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.homology i)) :
    CochainComplex.IsGE
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      (a - (d : ℤ)) := by
  have hamp := (StacksDraft.TorAmplitude.torAmplitude_and_finiteTorDimension_of_globalDimension_le
    R d hd).2.1 P a b hP
  exact isGE_extendScalars_of_termwise_torAmplitude f P (a - d) b
    (termwise_torAmplitude_of_derived P (CochainComplex.KFlat.kFlat_of_flat P n) (a - d) b hamp)

/-! ### Comparisons of scalar changes -/

/-- Restriction of scalars through a factorization gives the same derived object. -/
private def restrictScalarsCompDerivedIso
    {R : Type*} {B : Type*} {A : Type*} [CommRing R] [CommRing B] [CommRing A]
    (f : R →+* B) (g : B →+* A) (h : R →+* A) (hh : h = g.comp f)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.restrictScalars h).mapDerivedCategory.obj K ≅
      (ModuleCat.restrictScalars f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars g).mapDerivedCategory.obj K) := by
  let F := ModuleCat.restrictScalars g
  let G := ModuleCat.restrictScalars f
  let H := ModuleCat.restrictScalars h
  let P := DerivedCategory.Q.objPreimage K
  let eP : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let e := Functor.mapHomologicalComplexCompIso
    (ModuleCat.restrictScalarsComp' f g h hh).symm (ComplexShape.up ℤ)
  exact H.mapDerivedCategory.mapIso eP.symm ≪≫ H.mapDerivedCategoryFactors.app P ≪≫
    DerivedCategory.Q.mapIso (e.symm.app P) ≪≫
    (G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P).symm ≪≫
    G.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso eP)

/-- Ordinary base change in a tensor-product square commutes with restriction of scalars. -/
private def tensorBaseChangeComplexIso
    {R : Type u} {B : Type u} {S : Type u}
    [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    (P : CochainComplex (ModuleCat.{u} B) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R (TensorProduct R B S))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars.{u, u, u}
          (algebraMap B (TensorProduct R B S))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≅
      StacksDraft.TorAmplitude.Termwise.tensorComplex
        (((ModuleCat.restrictScalars (algebraMap R B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) (ModuleCat.of R S) := by
  let (i : ℤ) : Module R (P.X i) := Module.compHom (P.X i) (algebraMap R B)
  let (i : ℤ) : IsScalarTower R B (P.X i) := IsScalarTower.of_compHom R B (P.X i)
  let eB (i : ℤ) : TensorProduct B (TensorProduct R B S) (P.X i) ≃ₗ[B]
      TensorProduct R (P.X i) S :=
    TensorProduct.comm B (TensorProduct R B S) (P.X i) ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R B B (P.X i) S
  let C := TensorProduct R B S
  let coeff := restrictScalarsSelfEquiv (R := B) (S := C)
  let eR (i : ℤ) : ((ModuleCat.restrictScalars (algebraMap R C)).obj
      ((ModuleCat.extendScalars.{u, u, u}
        (algebraMap B C)).obj (P.X i))) ≃ₗ[R] TensorProduct R (P.X i) S :=
    { __ := ((TensorProduct.congr coeff (LinearEquiv.refl B (P.X i))).trans (eB i)).toAddEquiv
      map_smul' r z := by
        change TensorProduct B ((ModuleCat.restrictScalars (algebraMap B C)).obj
          (ModuleCat.of C C)) (P.X i) at z
        change ((TensorProduct.congr coeff (LinearEquiv.refl B (P.X i))).trans (eB i))
          ((algebraMap R B r) • z) = r • _
        rw [map_smul, IsScalarTower.algebraMap_smul]
        rfl }
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · exact ((eR i).trans
      (TensorProduct.congr (LinearEquiv.refl R (P.X i))
        (LinearEquiv.refl R S))).toModuleIso
  · intro i j hij
    apply ModuleCat.hom_ext
    ext z
    induction z using TensorProduct.inductionOn with
    | add z t hz ht => simpa only [map_add] using congrArg₂ (· + ·) hz ht
    | tmul c y =>
      induction c using TensorProduct.inductionOn with
      | add c d hc hd => simp only [TensorProduct.add_tmul, map_add, hc, hd]
      | tmul b t =>
        change (P.d i j).hom (b • y) ⊗ₜ[R] t =
          (b • (P.d i j).hom y) ⊗ₜ[R] t
        rw [map_smul]

/-- A fibre of a polynomial algebra in finitely many variables has finite global dimension. -/
private lemma globalDimension_polynomial_fibre_le
    {R : Type u} [CommRing R] (ι : Type*) [Finite ι] (p : PrimeSpectrum R) :
    ringGlobalDimension (TensorProduct R (MvPolynomial ι R) p.asIdeal.ResidueField) ≤
      Nat.card ι := by
  let C := TensorProduct R (MvPolynomial ι R) p.asIdeal.ResidueField
  let e : C ≃+* MvPolynomial ι p.asIdeal.ResidueField :=
    (Algebra.TensorProduct.comm R (MvPolynomial ι R) p.asIdeal.ResidueField).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv R p.asIdeal.ResidueField (σ := ι)).toRingEquiv
  have : IsNoetherianRing C :=
    isNoetherianRing_of_surjective (MvPolynomial ι p.asIdeal.ResidueField) C
      e.symm.toRingHom e.symm.surjective
  have : IsRegularRing C := IsRegularRing.of_ringEquiv e.symm
  have hdim : ringKrullDim C = (Nat.card ι : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_ringEquiv e, MvPolynomial.ringKrullDim_of_isNoetherianRing]
    simp [ENat.card_eq_coe_natCard]
  have heq : ringGlobalDimension C = (Nat.card ι : WithBot ℕ∞) := by
    apply ((isRegularRing_tfae (R := C) (Nat.card ι)).out 2 1).mp
    exact ⟨inferInstance, hdim⟩
  exact heq.le

/-! ### Flat representatives and derived fibres -/

/-- Restriction of scalars along a flat algebra turns a complex of free modules into a complex
with flat terms. -/
private lemma flat_restrictScalars_obj_X {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (P : CochainComplex (ModuleCat.{u} S) ℤ)
    [∀ i, Module.Free S (P.X i)] (i : ℤ) :
    Module.Flat R ((((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).X i) := by
  let : Module R (P.X i) := Module.compHom (P.X i) (algebraMap R S)
  let : IsScalarTower R S (P.X i) := IsScalarTower.of_compHom R S (P.X i)
  exact Module.Flat.trans R S (P.X i)

/-- A bounded-above complex with flat terms computes the total derived extension of scalars. -/
private def totalDerivedExtensionScalarsObjIsoOfFlat {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (E : CochainComplex (ModuleCat.{u} R) ℤ) (c : ℤ) [E.IsStrictlyLE c]
    [∀ i, Module.Flat R (E.X i)] {X : DerivedCategory (ModuleCat.{u} R)}
    (e : DerivedCategory.Q.obj E ≅ X) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      f).functor.obj X ≅
      DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  have hflat : CochainComplex.KFlat.{u, u} E := CochainComplex.KFlat.kFlat_of_flat E c
  have hiso : IsIso (D.comparison.app E) := D.comparison_isIso_of_kFlat E hflat
  exact D.functor.mapIso e.symm ≪≫ @asIso _ _ _ _ (D.comparison.app E) hiso

/-- For `B` flat over `R` and an `R`-algebra `S`, a lower bound on the derived base change to `S`
of `L ∈ D(B)` bounds below the termwise base change to `B ⊗_R S` of a free representative of
`L`. -/
private lemma isZero_homology_extendScalars_tensorProduct
    {R B S : Type u} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra R S]
    [Module.Flat R B] (P : CochainComplex (ModuleCat.{u} B) ℤ) (c : ℤ) [P.IsStrictlyLE c]
    [∀ i, Module.Free B (P.X i)] {L : DerivedCategory (ModuleCat.{u} B)}
    (eP : DerivedCategory.Q.obj P ≅ L) (a : ℤ)
    (ha : ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R S)).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj L)).IsGE a)
    (i : ℤ) (hi : i < a) :
    IsZero ((((ModuleCat.extendScalars.{u, u, u}
      (algebraMap B (TensorProduct R B S))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        P).homology i) := by
  let G := ModuleCat.restrictScalars (algebraMap R B)
  let E : CochainComplex (ModuleCat.{u} R) ℤ :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : E.IsStrictlyLE c :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P G c).2 inferInstance
  have : ∀ i, Module.Flat R (E.X i) := flat_restrictScalars_obj_X (R := R) P
  let EF : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E
  have hEF : IsZero (EF.homology i) :=
    ((DerivedCategory.isGE_iff _ a).1 ha i hi).of_iso
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) i).app EF).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).mapIso
          (totalDerivedExtensionScalarsObjIsoOfFlat (algebraMap R S) E c
            ((G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso eP)).symm)
  exact (isZero_homology_restrictComplex_iff (algebraMap R (TensorProduct R B S)) _ i).1
    ((((isZero_homology_restrictComplex_iff (algebraMap R S) EF i).2 hEF).of_iso
      (HomologicalComplex.homologyMapIso (restrictExtendScalarsIso (S := S) E) i).symm).of_iso
        (HomologicalComplex.homologyMapIso
          (tensorBaseChangeComplexIso (R := R) (B := B) (S := S) P) i))

/-- Let `B = R[x_i]` be a polynomial algebra in finitely many variables and `L` a pseudo-coherent
object of `D(B)` whose derived fibres over the primes of `R` are bounded below. Then the derived
fibres of `L` over the primes of `B` are bounded below. -/
theorem exists_isZero_homology_derivedFibre_mvPolynomial
    {R : Type u} [CommRing R] (ι : Type) [Finite ι]
    (L : DerivedCategory (ModuleCat.{u} (MvPolynomial ι R)))
    (hL : StacksDraft.PseudoCoherence.IsPseudoCoherent L)
    (hLfibre : ∀ p : PrimeSpectrum R, ∃ a : ℤ,
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R p.asIdeal.ResidueField)).functor.obj
          ((ModuleCat.restrictScalars (algebraMap R (MvPolynomial ι R))).mapDerivedCategory.obj
            L)).IsGE a)
    (q : PrimeSpectrum (MvPolynomial ι R)) :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} q.asIdeal.ResidueField) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap (MvPolynomial ι R) q.asIdeal.ResidueField)).functor.obj L)) := by
  let B := MvPolynomial ι R
  let p := PrimeSpectrum.comap (algebraMap R B) q
  let : Module R p.asIdeal.ResidueField :=
    (inferInstance : Algebra R p.asIdeal.ResidueField).toModule
  let C := TensorProduct R B p.asIdeal.ResidueField
  let fC : B →+* C := algebraMap B C
  let k := q.asIdeal.ResidueField
  let gC : C →+* k :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R B k)
      (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R B) rfl)
      (fun _ _ => Commute.all ..)).toRingHom
  have hcomp : gC.comp fC = algebraMap B k :=
    RingHom.ext fun _ => by simp [gC, fC, C, Algebra.TensorProduct.algebraMap_apply]
  obtain ⟨P, hP, ⟨eP⟩⟩ := hL
  obtain ⟨c, hc⟩ := hP.upperBound
  have : P.IsStrictlyLE c := hc
  have (i : ℤ) : Module.Free B (P.X i) := (hP.finiteFree i).2
  have (i : ℤ) : Projective (P.X i) := inferInstance
  obtain ⟨a, ha⟩ := hLfibre p
  let PC : CochainComplex (ModuleCat.{u} C) ℤ :=
    ((ModuleCat.extendScalars.{u, u, u} fC).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : PC.IsStrictlyLE c :=
    (CochainComplex.isStrictlyLE_iff PC c).2 fun i hi =>
      (ModuleCat.extendScalars fC).map_isZero (P.isZero_of_isStrictlyLE c i hi)
  have (i : ℤ) : Module.Flat C (PC.X i) := Module.Flat.of_linearEquiv
    (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv B C (P.X i))
  have hPC (i : ℤ) : i < a ∨ c < i → IsZero (PC.homology i) := by
    rintro (hi | hi)
    · exact isZero_homology_extendScalars_tensorProduct P c eP a ha i hi
    · exact (CochainComplex.isLE_iff PC c).1 (by infer_instance) i hi |>
        (HomologicalComplex.exactAt_iff_isZero_homology PC i).1
  have := isGE_extendScalars_of_globalDimension_le gC (Nat.card ι)
    (globalDimension_polynomial_fibre_le ι p) PC a c c hPC
  let eqC : ((ModuleCat.extendScalars.{u, u, u}
      (algebraMap B k)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ≅
      ((ModuleCat.extendScalars gC).mapHomologicalComplex (ComplexShape.up ℤ)).obj PC := by
    let ee := (Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp fC gC).symm (ComplexShape.up ℤ)).app P
    rw [hcomp] at ee
    exact ee.symm
  let Dq := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap B k)
  have hqiso : IsIso (Dq.comparison.app P) := Dq.comparison_isIso_of_projective P c
  let eq : Dq.functor.obj L ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars gC).mapHomologicalComplex (ComplexShape.up ℤ)).obj PC) :=
    Dq.functor.mapIso eP.symm ≪≫ @asIso _ _ _ _ (Dq.comparison.app P) hqiso ≪≫
      DerivedCategory.Q.mapIso eqC
  exact ⟨a - Nat.card ι, (DerivedCategory.isGE_iff _ _).1
    (DerivedCategory.TStructure.t.isGE_of_iso eq.symm _)⟩

/-! ### Stacks 0GHJ -/

/-- The forward implication of Stacks 0GHJ: a pseudo-coherent `K` that is perfect relative to `R`
is bounded below, and so are its derived fibres over the primes of `R`. -/
theorem isBoundedBelow_and_fibres_isBoundedBelow_of_isRelativelyPerfect
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hperfect : IsRelativelyPerfect.{u, u, u} derivedTensor comparison isLeftDerived K) :
    (∃ a : ℤ, K.IsGE a) ∧
      ∀ p : PrimeSpectrum R, ∃ a : ℤ,
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap R p.asIdeal.ResidueField)).functor.obj
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)).IsGE a := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := hK
  obtain ⟨c, hc⟩ := hP.upperBound
  have : P.IsStrictlyLE c := hc
  have (i : ℤ) : Module.Free A (P.X i) := (hP.finiteFree i).2
  let G := ModuleCat.restrictScalars (algebraMap R A)
  let E : CochainComplex (ModuleCat.{u} R) ℤ :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : E.IsStrictlyLE c :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff P G c).2 hc
  have hEflat : ∀ i, Module.Flat R (E.X i) := flat_restrictScalars_obj_X (R := R) P
  let eE : DerivedCategory.Q.obj E ≅ G.mapDerivedCategory.obj K :=
    (G.mapDerivedCategoryFactors.app P).symm ≪≫ G.mapDerivedCategory.mapIso eP
  obtain ⟨a, b, hamp⟩ := hperfect.2
  have hampE : StacksDraft.TorAmplitude.HasTorAmplitude derivedTensor comparison isLeftDerived
      (DerivedCategory.Q.obj E) a b := by
    intro M i hi
    exact (hamp M i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
        ((derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).mapIso eE))
  have hterm : StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn E a b :=
    (StacksDraft.TorAmplitude.hasTorAmplitude_iff_termwise_of_flat comparison isLeftDerived E
      ⟨c, fun i hi => E.isZero_of_isStrictlyLE c i hi⟩ hEflat a b).1 hampE
  have := isGE_of_termwise_torAmplitude E a b hterm
  refine ⟨⟨a, (isGE_restrictScalars_iff (algebraMap R A) K a).1
    (DerivedCategory.TStructure.t.isGE_of_iso eE a)⟩, fun p => ⟨a, ?_⟩⟩
  have := isGE_extendScalars_of_termwise_torAmplitude
    (algebraMap R p.asIdeal.ResidueField) E a b hterm
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (totalDerivedExtensionScalarsObjIsoOfFlat (algebraMap R p.asIdeal.ResidueField) E c eE).symm a

/-- The reverse implication of Stacks 0GHJ: a bounded-below pseudo-coherent `K` whose derived
fibres over the primes of `R` are bounded below is perfect relative to `R`. -/
theorem isRelativelyPerfect_of_isBoundedBelow_and_fibres_isBoundedBelow
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hbounded : ∃ a : ℤ, K.IsGE a)
    (hfibres : ∀ p : PrimeSpectrum R, ∃ a : ℤ,
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R p.asIdeal.ResidueField)).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)).IsGE a) :
    IsRelativelyPerfect.{u, u, u} derivedTensor comparison isLeftDerived K := by
  obtain ⟨n, f₀, hsurj₀, -⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  let B := MvPolynomial (Fin n) R
  let f : B →ₐ[R] A := f₀
  have hsurj : Function.Surjective f := hsurj₀
  let : Algebra B A := f.toRingHom.toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let L := (ModuleCat.restrictScalars (algebraMap B A)).mapDerivedCategory.obj K
  have hL : StacksDraft.PseudoCoherence.IsPseudoCoherent L :=
    ((pseudoCoherent_tfae_of_surjective.{u}
      (R := R) (B := B) (A := A) hsurj K 0).1.out 1 4).1 hK
  let e : (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K ≅
      (ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj L :=
    restrictScalarsCompDerivedIso (algebraMap R B) (algebraMap B A)
      (algebraMap R A) (IsScalarTower.algebraMap_eq R B A) K
  have hlocal :=
    StacksDraft.Perfect.isPerfect_iff_isPerfect_at_primes_of_isBoundedBelow_and_stalkwise_criteria
      L hL
  have hperfect : StacksDraft.Perfect.IsPerfect L :=
    (hlocal.2.2.2.2 (hbounded.imp fun a => (isGE_restrictScalars_iff (algebraMap B A) K a).2)).2
      (hlocal.2.2.1.2 (exists_isZero_homology_derivedFibre_mvPolynomial (Fin n) L hL fun p =>
        (hfibres p).imp fun a ha => by
          have := ha
          exact DerivedCategory.TStructure.t.isGE_of_iso
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap R p.asIdeal.ResidueField)).functor.mapIso e) a))
  obtain ⟨a, b, hab⟩ := (isRelativelyPerfect_of_isPerfect.{u, u, u}
    (R := R) (A := B) derivedTensor comparison isLeftDerived L hperfect).2
  refine ⟨hK, a, b, fun M i hi => (hab M i hi).of_iso ?_⟩
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
    ((derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).mapIso e)

/-- **Stacks 0GHJ.** Let `R → A` be a flat ring map of finite presentation and let `K` be a
pseudo-coherent object of `D(A)`. Then `K` is perfect relative to `R` if and only if `K` is
bounded below and, for every prime `p` of `R`, the derived fibre `K ⊗_R^L κ(p)` is bounded
below. -/
@[stacks 0GHJ]
theorem isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} R) ⥤
        DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
    (comparison : ∀ M : ModuleCat.{u} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    IsRelativelyPerfect.{u, u, u} derivedTensor comparison isLeftDerived K ↔
      (∃ a : ℤ, K.IsGE a) ∧
        ∀ p : PrimeSpectrum R, ∃ a : ℤ,
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap R p.asIdeal.ResidueField)).functor.obj
            ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)).IsGE a :=
  ⟨isBoundedBelow_and_fibres_isBoundedBelow_of_isRelativelyPerfect derivedTensor comparison
      isLeftDerived K hK,
    fun ⟨hbounded, hfibres⟩ => isRelativelyPerfect_of_isBoundedBelow_and_fibres_isBoundedBelow
      derivedTensor comparison isLeftDerived K hK hbounded hfibres⟩

end PseudoCoherence
