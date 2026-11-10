module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.QuasiIsoFromDerivedIso
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.CochainScalarTower
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.RelativelyPerfect.CochainBaseChange
public import StacksFrontier.Homology.RelativelyPerfect.Criterion
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.GlobalDimension
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.Homology.TorAmplitude.Termwise
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleFlat

@[expose] public noncomputable section

/-!
# Computing derived Hom from a pseudo-coherent complex

Let `R → A` be flat. If `K` is pseudo-coherent and `L` has finite Tor-dimension over `R`, then
`K` and `L` admit representatives `P` and `F` such that `P` is bounded above with finite free
terms and `F` is bounded with terms flat over `R`. The complex `Homᴬ(P, F)` is bounded below,
termwise flat over `R`, computes derived Hom, and continues to do so after arbitrary base change
on `R`.

## Main definitions

* `StacksDraft.RelativelyPerfect.IsCanonicalHomComplexBaseChangeIso`: the property singling out
  the canonical comparison between the scalar extension of a Hom complex and the Hom complex of
  the scalar extensions.

## Main results

* `StacksDraft.RelativelyPerfect.exists_homComplex_representation` (Stacks 0E1U): simultaneous
  choice of the two representatives, computation of derived Hom, compatibility with arbitrary
  base change, and the finite-presentation refinement for a relatively perfect second argument.

## Implementation notes

Objects of the derived categories are presented by cochain complexes. That a Hom complex
represents derived Hom is the standard cohomological characterization: its degree-`n` classes map
bijectively to morphisms into the `n`-fold shift; this is supplied by Stacks 0A66
(`homComplex_represents_RHom`). Under base change the asserted isomorphism of Hom complexes
records the canonical termwise base-change identification.

The ring and module universes are independent. The Tor-amplitude hypothesis raises the
coefficient ring with `ULift` to the ambient module universe, restricting scalars along its
canonical ring equivalence. This accommodates the projective-resolution Tor-amplitude model
`StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude`, whose ring and module universes
  coincide, without restricting the
original ring or module universes.

The final refinement uses relative `R`-perfectness as in Stacks 0DHS: pseudo-coherence over `A`
together with the finite Tor dimension over `R` already assumed. Its proof truncates a finite-free
representative of `L`, whose boundary cokernel is both relatively flat and finitely presented.

Pseudo-coherence enters through `StacksDraft.PseudoCoherence.pseudoCoherent_iff_all` (Stacks
064U), which produces a representative only up to an isomorphism of `D(A)`. Flatness of the
boundary cokernel, on the other hand, is Stacks 0653 in its termwise form, and reaching it from
the projective-resolution Tor amplitude of the target needs an actual quasi-isomorphism of
complexes; `CochainComplex.exists_quasiIso_of_derived_iso` produces one, using that a bounded
above complex of projectives is K-projective. `PseudoCoherence.derivedTensorHomologyIsoTermwise`,
in `RelativelyPerfect/Criterion.lean`, and the two isomorphisms of double complexes identify the
projective-resolution model of
`H^i(P ⊗ᴸ M)` with the cohomology of the termwise tensor product at a K-flat `P`; they stand in
for the symmetric monoidal structure on cochain complexes (Stacks 0FNI), which is owned
elsewhere, and carry no tag.

## References

* [The Stacks Project, Lemma 15.85.13 (0E1U)](https://stacks.math.columbia.edu/tag/0E1U)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ChangeOfRings TensorProduct

namespace StacksDraft.RelativelyPerfect

open StacksDraft.PseudoCoherence

universe u v w uR uA uM uB

/-- An isomorphism between the scalar extension of a Hom complex and the Hom complex of the
scalar extensions is the canonical one if, on every homogeneous component, it sends
`a ⊗ z` evaluated at `b ⊗ x` to `ab ⊗ z(x)`. -/
public def IsCanonicalHomComplexBaseChangeIso
    {A : Type u} {A' : Type v} [CommRing A] [CommRing A'] (f : A →+* A')
    (P F : CochainComplex (ModuleCat.{w} A) ℤ)
    (e : ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR A P F) ≅
      CochainComplex.HomComplexR A'
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)) : Prop :=
  ∀ (n p q : ℤ) (hpq : p + n = q) (a b : A')
    (z : CochainComplex.HomComplex.Cochain P F n) (x : P.X p),
    (((e.hom.f n).hom (a ⊗ₜ[A, f] z)).v p q hpq).hom (b ⊗ₜ[A, f] x) =
      (a * b) ⊗ₜ[A, f] ((z.v p q hpq).hom x)

attribute [local instance] HasDerivedCategory.standard

/-! ### The two representatives -/

/-- Pseudo-coherence in every degree produces a bounded above complex of finite free modules
together with a quasi-isomorphism onto the given complex. -/
@[sga "6 II 2.3.2" "b)"]
private lemma exists_boundedAbove_finiteFree_of_pseudoCoherentFrom
    {A : Type u} [CommRing A] (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : ∀ m : ℤ, IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m) :
    ∃ (P : CochainComplex (ModuleCat.{v} A) ℤ) (d : ℤ) (π : P ⟶ K),
      P.IsStrictlyLE d ∧
      (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧ QuasiIso π := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (pseudoCoherent_iff_all (DerivedCategory.Q.obj K)).mpr hK
  obtain ⟨d, hd⟩ := hP.upperBound
  have := hd
  have hff (i : ℤ) : Module.Finite A (P.X i) ∧ Module.Free A (P.X i) := hP.finiteFree i
  have (i : ℤ) : Module.Free A (P.X i) := (hff i).2
  have (i : ℤ) : Projective (P.X i) := inferInstance
  obtain ⟨π, hπ⟩ := CochainComplex.exists_quasiIso_of_derived_iso P K d e
  exact ⟨P, d, π, hd, hff, hπ⟩

/-! ### Bounds and flatness of the Hom complex -/

/-- The Hom complex out of a complex bounded above by `d` into a complex bounded below by `a`
vanishes strictly below `a - d`. -/
private lemma homComplexR_isStrictlyGE
    {A : Type u} [CommRing A] (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (d a : ℤ) [P.IsStrictlyLE d] [F.IsStrictlyGE a] :
    (CochainComplex.HomComplexR A P F).IsStrictlyGE (a - d) := by
  apply (CochainComplex.isStrictlyGE_iff _ _).mpr
  intro n hn
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ ?_⟩
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  by_cases hp : d < p
  · exact (P.isZero_of_isStrictlyLE d p hp).eq_of_src _ _
  · exact (F.isZero_of_isStrictlyGE a q (by omega)).eq_of_tgt _ _

/-- Homomorphisms from a finite free module into a finitely presented module form a finitely
presented module. -/
private lemma hom_finitePresentation_of_finiteFree
    {A : Type u} [CommRing A] (M N : ModuleCat.{v} A)
    [Module.Finite A M] [Module.Free A M] [Module.FinitePresentation A N] :
    Module.FinitePresentation A (M ⟶ N) := by
  let := Module.Free.ChooseBasisIndex.fintype A M
  let e := (Module.Free.chooseBasis A M).constr A (M' := N)
  exact Module.FinitePresentation.of_equiv
    (e.trans (ModuleCat.homLinearEquiv (M := M) (N := N)).symm)

/-- Each term of the Hom complex from a finite free complex into a bounded complex of finitely
presented modules is finitely presented. -/
private lemma homComplexR_finitePresentation
    {A : Type u} [CommRing A] (P F : CochainComplex (ModuleCat.{v} A) ℤ)
    (a b n : ℤ) [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    [∀ i, Module.FinitePresentation A (F.X i)] :
    Module.FinitePresentation A ((CochainComplex.HomComplexR A P F).X n) := by
  let := finite_homCochain_support n a b
  let (t : {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b}) :
      Module.FinitePresentation A (P.X t.val.p ⟶ F.X t.val.q) :=
    hom_finitePresentation_of_finiteFree _ _
  exact Module.FinitePresentation.of_equiv (homCochainRestrict P F n a b).symm

/-- A finite product of flat modules is flat. -/
private alias flat_pi_of_finite := Stacks.Cech.flat_pi_of_finite

/-- Homomorphisms from a finite free `A`-module into an `A`-module which is flat over `R` form an
`A`-module which is flat over `R`. -/
private lemma hom_flat_of_finiteFree
    {R : Type w} {A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (M N : ModuleCat.{v} A) [Module.Finite A M] [Module.Free A M]
    [Module.Flat R ((ModuleCat.restrictScalars f).obj N)] :
    Module.Flat R ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (M ⟶ N))) := by
  let := Module.Free.ChooseBasisIndex.fintype A M
  let e := ((Module.Free.chooseBasis A M).constr A (M' := N)).trans
    (ModuleCat.homLinearEquiv (M := M) (N := N)).symm
  let eR := ((ModuleCat.restrictScalars f).mapIso e.toModuleIso).toLinearEquiv
  have : Module.Flat R ((ModuleCat.restrictScalars f).obj
      (ModuleCat.of A (Module.Free.ChooseBasisIndex A M → N))) := by
    change Module.Flat R (Module.Free.ChooseBasisIndex A M →
      ((ModuleCat.restrictScalars f).obj N))
    exact flat_pi_of_finite _
  exact Module.Flat.of_linearEquiv eR.symm

/-- Each term of the Hom complex from a finite free complex into a bounded complex of relatively
flat modules is relatively flat. -/
private lemma homComplexR_flat
    {R : Type w} {A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (P F : CochainComplex (ModuleCat.{v} A) ℤ) (a b n : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)]
    [∀ i, Module.Flat R ((ModuleCat.restrictScalars f).obj (F.X i))] :
    Module.Flat R ((ModuleCat.restrictScalars f).obj
      ((CochainComplex.HomComplexR A P F).X n)) := by
  let := finite_homCochain_support n a b
  let e := ((ModuleCat.restrictScalars f).mapIso
    (homCochainRestrict P F n a b).toModuleIso).toLinearEquiv
  let (t : {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b}) :
      Module.Flat R ((ModuleCat.restrictScalars f).obj
        (ModuleCat.of A (P.X t.val.p ⟶ F.X t.val.q))) :=
    hom_flat_of_finiteFree f _ _
  have : Module.Flat R ((ModuleCat.restrictScalars f).obj (ModuleCat.of A
      ((t : {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b}) →
        (P.X t.val.p ⟶ F.X t.val.q)))) := by
    change Module.Flat R
      ((t : {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b}) →
        ((ModuleCat.restrictScalars f).obj
          (ModuleCat.of A (P.X t.val.p ⟶ F.X t.val.q))))
    exact flat_pi_of_finite _
  exact Module.Flat.of_linearEquiv e

/-! ### Base change of the Hom complex -/

open scoped ModuleCat.Algebra

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower

/-- The base-change map on cochains sends `a ⊗ z`, evaluated at `b ⊗ x`, to `ab ⊗ z(x)`. -/
lemma homCochainBaseChange_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (n p q : ℤ) (hpq : p + n = q)
    (a b : B) (z : CochainComplex.HomComplex.Cochain P F n) (x : P.X p) :
    (((homCochainBaseChange f P F n) (a ⊗ₜ[A, f] z)).v p q hpq).hom
        (b ⊗ₜ[A, f] x) = (a * b) ⊗ₜ[A, f] ((z.v p q hpq).hom x) := by
  let := f.toAlgebra
  simp only [homCochainBaseChange]
  change ((a • (z.map (ModuleCat.extendScalars f))).v p q hpq).hom
    (b ⊗ₜ[A] x) = _
  change a • (b ⊗ₜ[A] (z.v p q hpq).hom x) = _
  exact TensorProduct.smul_tmul' a b _

/-- A canonical base-change isomorphism of Hom complexes is unique. -/
private lemma canonicalHomComplexBaseChangeIso_unique
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ)
    (e₁ e₂ : ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (CochainComplex.HomComplexR A P F) ≅
      CochainComplex.HomComplexR B
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F))
    (h₁ : IsCanonicalHomComplexBaseChangeIso f P F e₁)
    (h₂ : IsCanonicalHomComplexBaseChangeIso f P F e₂) : e₁ = e₂ := by
  let := f.toAlgebra
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => erw [map_add, map_add, ht, ht']
  | tmul a z =>
    apply CochainComplex.HomComplex.Cochain.ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => erw [map_add, map_add, ht, ht']
    | tmul b x =>
      exact (h₁ n p q hpq a b z x).trans (h₂ n p q hpq a b z x).symm

/-- There is exactly one canonical base-change isomorphism of Hom complexes out of a finite free
complex into a bounded complex. -/
private lemma existsUnique_canonicalHomComplexBaseChangeIso
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (a b : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Free A (P.X i)] :
    ∃! e : ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.HomComplexR A P F) ≅
      CochainComplex.HomComplexR B
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj F),
      IsCanonicalHomComplexBaseChangeIso f P F e := by
  have (n : ℤ) : IsIso ((homComplexBaseChange f P F).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (homCochainBaseChange_bijective f P F a b n)
  have : IsIso (homComplexBaseChange f P F) :=
    HomologicalComplex.Hom.isIso_of_components _
  refine ⟨asIso (homComplexBaseChange f P F), ?_, ?_⟩
  · exact homCochainBaseChange_tmul f P F
  · intro e he
    exact canonicalHomComplexBaseChangeIso_unique f P F e _ he
      (homCochainBaseChange_tmul f P F)

/-- After base change, the Hom complex out of a finite free complex still computes derived
Hom. -/
private lemma homComplex_baseChange_represents_RHom
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{w} A) ℤ) (d n : ℤ)
    [P.IsStrictlyLE d] [∀ i, Module.Free A (P.X i)] :
    let P' := ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj P
    let F' := ((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj F
    Function.Bijective
      (fun (z : CochainComplex.HomComplex.CohomologyClass P' F' n) ↦
        DerivedCategory.Qh.map
          (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z)) := by
  let := f.toAlgebra
  let Ext := (ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)
  have (i : ℤ) : Module.Free B ((Ext.obj P).X i) := by
    change Module.Free B (B ⊗[A] (P.X i))
    infer_instance
  have (i : ℤ) : Projective ((Ext.obj P).X i) := inferInstance
  exact homComplex_represents_RHom (Ext.obj P) (Ext.obj F) d n

/-! ### The projective-resolution model of the derived tensor product

At a K-flat complex the projective-resolution model of `H^i(P ⊗ᴸ M)` and the cohomology of the
termwise tensor product agree, so the two Tor-amplitude conditions transfer along a
quasi-isomorphism. -/

/-- A quasi-isomorphism identifies the vanishing of homology in each degree. -/
private lemma isZero_homology_iff_of_quasiIso {C : Type*} [Category C] [Abelian C]
    {P L : CochainComplex C ℤ} (π : P ⟶ L) [QuasiIso π] (i : ℤ) :
    IsZero (P.homology i) ↔ IsZero (L.homology i) :=
  have : IsIso (HomologicalComplex.homologyMap π i) :=
    (quasiIsoAt_iff_isIso_homologyMap _ i).1 inferInstance
  (asIso (HomologicalComplex.homologyMap π i)).isZero_iff

/-- A K-flat complex quasi-isomorphic to a complex of projective-resolution Tor amplitude in
`[a, b]` has termwise Tor amplitude in `[a, b]`. -/
private lemma termwise_torAmplitude_of_quasiIso {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (π : P ⟶ L) [QuasiIso π] (hP : P.KFlat)
    (a b : ℤ) (hL : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude L a b) :
    StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn P a b := by
  intro M i hi
  have hkf : (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M).KFlat :=
    StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective
      (ProjectiveResolution.of M).cochainComplex 0 inferInstance
  have : QuasiIso ((tensorRight (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)).map
    π) :=
    StacksDraft.TorAmplitude.quasiIso_tensorRight_map hkf π
  refine (PseudoCoherence.derivedTensorHomologyIsoTermwise P hP M i).isZero_iff.1 ?_
  exact (isZero_homology_iff_of_quasiIso
    ((tensorRight (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)).map π) i).2
    (hL M i hi)

/-- Projective-resolution Tor amplitude gives the corresponding cohomological bounds. -/
private lemma isZero_homology_of_torAmplitude {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hK : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b) (i : ℤ) (hi : i < a ∨ b <
      i) :
    IsZero (K.homology i) :=
  (hK (ModuleCat.of R R) i hi).of_iso
    (StacksDraft.TorAmplitude.derivedTensorHomologyUnitIso R K i).symm

/-! ### Truncating a relatively flat representative -/

/-- Restriction of scalars detects the vanishing of homology. -/
private lemma isZero_homology_of_restrictScalars
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] (f : R →+* A)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (i : ℤ)
    (h : IsZero (((ModuleCat.restrictScalars f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P |>.homology i)) :
    IsZero (P.homology i) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
  exact ((P.sc i).exact_map_iff_of_faithful (ModuleCat.restrictScalars f)).mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr h)

/-- Restriction of scalars detects a lower cohomological bound. -/
private lemma isGE_of_restrictScalars
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] (f : R →+* A)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (a : ℤ)
    (h : ∀ i : ℤ, i < a → IsZero
      (((ModuleCat.restrictScalars f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P |>.homology i)) :
    P.IsGE a := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_homology_of_restrictScalars f P i (h i hi)

/-- The degree-`a` term of a lower truncation is the cokernel of the incoming differential. -/
private def truncGEXIsoCokernel {A : Type v} [Ring A]
    (P : CochainComplex (ModuleCat.{w} A) ℤ) (a : ℤ) :
    (P.truncGE a).X a ≅ cokernel (P.d (a - 1) a) :=
  P.truncGEXIsoOpcycles a ≪≫
    IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel (a - 1) a (by simp))
      (colimit.isColimit _)

/-- Truncating a complex of finite free modules leaves finitely presented terms. -/
private lemma finitePresentation_truncGE
    {A : Type v} [Ring A] (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hP : ∀ i, Module.Finite A (P.X i) ∧ Module.Free A (P.X i))
    (a i : ℤ) : Module.FinitePresentation A ((P.truncGE a).X i) := by
  rcases lt_trichotomy i a with hi | hiEq | hi
  · have : Subsingleton ((P.truncGE a).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp ((P.truncGE a).isZero_of_isStrictlyGE a i hi)
    infer_instance
  · subst i
    have := (hP (a - 1)).1
    have := (hP a).1
    have := (hP a).2
    have := Module.finitePresentation_of_projective A (P.X a)
    have := PseudoCoherence.finitePresentation_cokernel (P.d (a - 1) a)
    let e := truncGEXIsoCokernel P a
    exact Module.FinitePresentation.of_equiv e.symm.toLinearEquiv
  · have := (hP i).1
    have := (hP i).2
    have := Module.finitePresentation_of_projective A (P.X i)
    exact Module.FinitePresentation.of_equiv (P.truncGEXIso a i hi).symm.toLinearEquiv

/-- A lower truncation has relatively flat terms when its boundary cokernel is flat. -/
private lemma flat_restrictScalars_truncGE
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] (f : R →+* A)
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ) (a : ℤ)
    (hflat : ∀ i, Module.Flat R ((ModuleCat.restrictScalars f).obj (P.X i)))
    [Module.Flat R (cokernel ((ModuleCat.restrictScalars f).map
      (P.d (a - 1) a)) : ModuleCat.{max u v} R)] (i : ℤ) :
    Module.Flat R ((ModuleCat.restrictScalars f).obj ((P.truncGE a).X i)) := by
  let U := ModuleCat.restrictScalars f
  rcases lt_trichotomy i a with hi | hiEq | hi
  · have : Subsingleton (U.obj ((P.truncGE a).X i)) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (U.map_isZero ((P.truncGE a).isZero_of_isStrictlyGE a i hi))
    rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
    intro N N' _ _ _ _ g _
    exact fun x y _ ↦ Subsingleton.elim x y
  · subst i
    let e := truncGEXIsoCokernel P a
    exact Module.Flat.of_linearEquiv
      (U.mapIso e ≪≫ PreservesCokernel.iso U (P.d (a - 1) a)).toLinearEquiv
  · have := hflat i
    exact Module.Flat.of_linearEquiv (U.mapIso (P.truncGEXIso a i hi)).toLinearEquiv

/-- Restriction along a flat scalar extension preserves flat modules. -/
private lemma flat_restrictScalars_of_flat
    {R : Type w} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (M : ModuleCat.{v} A) [Module.Flat A M] :
    Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M) := by
  have : Module.Flat A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
    ‹Module.Flat A M›
  have : IsScalarTower R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.trans R A ((ModuleCat.restrictScalars (algebraMap R A)).obj M)

/-- Truncating a relatively flat representative at a lower Tor bound gives a bounded
relatively flat representative. -/
private lemma exists_bounded_flat_of_boundedAbove_flat
    {R : Type (max u w)} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (P L : CochainComplex (ModuleCat.{max u w} A) ℤ) (a b d : ℤ) [P.IsStrictlyLE d]
    (hflat : ∀ i, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i)))
    (π : P ⟶ L) [QuasiIso π]
    (hL : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj L) a b) :
    (P.truncGE a).IsStrictlyLE d ∧
      (∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj
        ((P.truncGE a).X i))) ∧
      Nonempty (DerivedCategory.Q.obj (P.truncGE a) ≅ DerivedCategory.Q.obj L) := by
  let U := ModuleCat.restrictScalars (algebraMap R A)
  let PR : CochainComplex (ModuleCat.{max u w} R) ℤ :=
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let LR : CochainComplex (ModuleCat.{max u w} R) ℤ :=
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let πR : PR ⟶ LR := (U.mapHomologicalComplex (ComplexShape.up ℤ)).map π
  have : PR.IsStrictlyLE d := inferInstance
  have hPRflat : ∀ n : ℤ, Module.Flat R (PR.X n) := hflat
  have : ∀ n : ℤ, Module.Flat R (PR.X n) := hPRflat
  have hPRkflat : PR.KFlat :=
    (CochainComplex.KFlat.kFlat_of_flat PR d)
  have htor : StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn PR a b :=
    termwise_torAmplitude_of_quasiIso PR LR πR hPRkflat a b hL
  have : Module.Flat R (cokernel (U.map (P.d (a - 1) a)) : ModuleCat.{max u w} R) :=
    StacksDraft.TorAmplitude.Termwise.cokernel_flat_of_termwise_torAmplitude PR a b hPRflat htor
  have hGE : P.IsGE a := by
    refine isGE_of_restrictScalars (algebraMap R A) P a fun i hi ↦ ?_
    have hLz : IsZero (LR.homology i) :=
      isZero_homology_of_torAmplitude LR a b hL i (Or.inl hi)
    exact (isZero_homology_iff_of_quasiIso πR i).2 hLz
  have := hGE
  exact ⟨PseudoCoherence.truncGE_isStrictlyLE P a d,
    flat_restrictScalars_truncGE (algebraMap R A) P a hflat,
    ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫
      asIso (DerivedCategory.Q.map π)⟩⟩

/-- Finite relative Tor dimension yields a bounded relatively flat representative. -/
private lemma exists_bounded_flat_of_finiteTorDimension
    {R : Type (max u w)} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (L : CochainComplex (ModuleCat.{max u w} A) ℤ) (a b : ℤ)
    (hL : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj L) a b) :
    ∃ F : CochainComplex (ModuleCat.{max u w} A) ℤ,
      (∃ d : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE d) ∧
      (∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i))) ∧
      Nonempty (DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L) := by
  let U := ModuleCat.restrictScalars (algebraMap R A)
  let LR : CochainComplex (ModuleCat.{max u w} R) ℤ :=
    (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hbounded : ∃ M : ℤ, ∀ n : ℤ, M ≤ n → IsZero (L.homology n) := by
    exact ⟨b + 1, fun n hn ↦ isZero_homology_of_restrictScalars _ L n
      (isZero_homology_of_torAmplitude LR a b hL n (Or.inr (by omega)))⟩
  obtain ⟨d, ⟨P⟩⟩ := ProjectiveResolutionLemma.statement2 L hbounded
  have := P.boundedAbove
  have := P.quasiIso
  have hflat : ∀ i, Module.Flat R (U.obj (P.complex.X i)) := by
    intro i
    have := P.projective i
    have : Module.Flat A (P.complex.X i) := inferInstance
    exact flat_restrictScalars_of_flat (P.complex.X i)
  obtain ⟨hLE, hf, e⟩ := exists_bounded_flat_of_boundedAbove_flat P.complex L a b d hflat P.α hL
  exact ⟨P.complex.truncGE a, ⟨d, inferInstance, hLE⟩, hf, e⟩

/-- Pseudo-coherence gives finite presentation of the terms in the bounded relatively
flat representative. -/
private lemma exists_bounded_flat_finitePresentation_of_pseudoCoherentFrom
    {R : Type (max u w)} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (L : CochainComplex (ModuleCat.{max u w} A) ℤ) (a b : ℤ)
    (hL : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj L) a b)
    (hpseudo : ∀ m : ℤ, IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m) :
    ∃ F : CochainComplex (ModuleCat.{max u w} A) ℤ,
      (∃ d : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE d) ∧
      (∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i))) ∧
      (∀ i, Module.FinitePresentation A (F.X i)) ∧
      Nonempty (DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L) := by
  obtain ⟨P, d, π, hd, hP, hπ⟩ :=
    exists_boundedAbove_finiteFree_of_pseudoCoherentFrom L hpseudo
  have := hd
  have := hπ
  have hflat : ∀ i, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i)) := by
    intro i
    have := (hP i).2
    have : Module.Flat A (P.X i) := Module.Flat.of_free
    exact flat_restrictScalars_of_flat (P.X i)
  obtain ⟨hLE, hf, e⟩ := exists_bounded_flat_of_boundedAbove_flat P L a b d hflat π hL
  exact ⟨P.truncGE a, ⟨d, inferInstance, hLE⟩, hf,
    fun i ↦ finitePresentation_truncGE P hP a i, e⟩

/-- The relatively flat representative can be chosen finitely presented whenever
its derived object is pseudo-coherent. -/
private lemma exists_bounded_flat_with_finitePresentation
    {R : Type (max u w)} {A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (L : CochainComplex (ModuleCat.{max u w} A) ℤ) (a b : ℤ)
    (hL : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj L) a b) :
    ∃ F : CochainComplex (ModuleCat.{max u w} A) ℤ,
      (∃ d : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE d) ∧
      (∀ i, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i))) ∧
      Nonempty (DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L) ∧
      ((∀ m : ℤ, IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m) →
        ∀ i, Module.FinitePresentation A (F.X i)) := by
  classical
  by_cases h : ∀ m : ℤ, IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m
  · obtain ⟨F, hb, hf, hp, he⟩ :=
      exists_bounded_flat_finitePresentation_of_pseudoCoherentFrom L a b hL h
    exact ⟨F, hb, hf, he, fun _ ↦ hp⟩
  · obtain ⟨F, hb, hf, he⟩ := exists_bounded_flat_of_finiteTorDimension L a b hL
    exact ⟨F, hb, hf, he, fun hp ↦ (h hp).elim⟩

/-! ### The main statement -/

/-- **Stacks 0E1U.** For a flat map `R → A`, a pseudo-coherent complex `K` and a
complex `L` of finite Tor-dimension over `R` admit representatives `P` and `F` for which
`Homᴬ(P, F)` is a bounded-below complex of `R`-flat `A`-modules computing derived Hom.
The construction commutes with every base change `R → R'`. If `A` is finitely presented
over `R` and `L` is perfect relative to `R`, the terms of `F` and of the Hom complex may moreover
be chosen finitely presented over `A`. -/
@[stacks 0E1U]
public theorem exists_homComplex_representation
    (R : Type uR) (A : Type uA) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    (K L : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ) :
    letI : HasDerivedCategory (ModuleCat.{max uR uA uM} R) :=
      HasDerivedCategory.standard (ModuleCat.{max uR uA uM} R)
    letI : HasDerivedCategory (ModuleCat.{max uR uA uM} A) :=
      HasDerivedCategory.standard (ModuleCat.{max uR uA uM} A)
    (∀ m : ℤ, IsPseudoCoherentFrom ((DerivedCategory.Q).obj K) m) →
    (∃ a b : ℤ,
      StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
        (((ModuleCat.restrictScalars
          ((algebraMap R A).comp
            (ULift.ringEquiv : ULift.{max uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
              (.up ℤ)).obj L)
        a b) →
    ∃ (P F : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
      (_eP : (DerivedCategory.Q).obj P ≅ (DerivedCategory.Q).obj K)
      (_eF : (DerivedCategory.Q).obj F ≅ (DerivedCategory.Q).obj L),
      (∃ d : ℤ, P.IsStrictlyLE d) ∧
      (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧
      (∃ a b : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Flat R
        ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i))) ∧
      (∃ c : ℤ, (CochainComplex.HomComplexR A P F).IsStrictlyGE c) ∧
      (∀ i : ℤ, Module.Flat R
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          ((CochainComplex.HomComplexR A P F).X i))) ∧
      (∀ n : ℤ, Function.Bijective
        (fun (z : CochainComplex.HomComplex.CohomologyClass P F n) ↦
          DerivedCategory.Qh.map
            (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z))) ∧
      (∀ (R' : Type uB) [CommRing R'] [Algebra R R'],
        let A' := A ⊗[R] R'
        let f : A →+* A' := Algebra.TensorProduct.includeLeftRingHom
        let Ext := (ModuleCat.extendScalars.{uA, max uA uB, max uR uA uM} f).mapHomologicalComplex
          (ComplexShape.up ℤ)
        let P' := Ext.obj P
        let F' := Ext.obj F
        let E' := Ext.obj (CochainComplex.HomComplexR A P F)
        letI : HasDerivedCategory (ModuleCat.{max uR uA uM uB} A') :=
          HasDerivedCategory.standard (ModuleCat.{max uR uA uM uB} A')
        ∃! e : E' ≅ CochainComplex.HomComplexR A' P' F',
          IsCanonicalHomComplexBaseChangeIso f P F e ∧
            ∀ n : ℤ,
              IsIso (HomologicalComplex.homologyMap e.hom n) ∧
                Function.Bijective
                  (fun (z : CochainComplex.HomComplex.CohomologyClass P' F' n) ↦
                    DerivedCategory.Qh.map
                      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z))) ∧
      (Algebra.FinitePresentation R A →
        (∀ m : ℤ, IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m) →
        (∀ i : ℤ, Module.FinitePresentation A (F.X i)) ∧
          ∀ n : ℤ,
            Module.FinitePresentation A ((CochainComplex.HomComplexR A P F).X n)) := by
  intro hK hL
  let : Algebra (ULift.{max uA uM} R) A := ULift.algebra' R A
  have : Module.Flat (ULift.{max uA uM} R) A := Module.Flat.ulift_left_iff.mpr inferInstance
  obtain ⟨P, d, πK, hd, hP, hπK⟩ :=
    exists_boundedAbove_finiteFree_of_pseudoCoherentFrom K hK
  obtain ⟨a, b, hL⟩ := hL
  obtain ⟨F, ⟨c, hGE, hLE⟩, hFlift, ⟨eF⟩, hfp⟩ :=
    exists_bounded_flat_with_finitePresentation.{uA, max uR uM} (R := ULift.{max uA uM} R) L a b hL
  have hF (i : ℤ) : Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i)) := by
    have h := hFlift i
    change Module.Flat (ULift.{max uA uM} R)
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i)) at h
    exact Module.Flat.ulift_left_iff.mp h
  have := hd
  have := hπK
  have := hGE
  have := hLE
  have (i : ℤ) : Module.Finite A (P.X i) := (hP i).1
  have (i : ℤ) : Module.Free A (P.X i) := (hP i).2
  have (i : ℤ) : Projective (P.X i) := inferInstance
  have (i : ℤ) : Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i)) := hF i
  refine ⟨P, F, asIso (DerivedCategory.Q.map πK), eF, ⟨d, hd⟩, hP, ⟨a, c, hGE, hLE⟩, hF,
    ⟨a - d, homComplexR_isStrictlyGE P F d a⟩,
    (fun i ↦ homComplexR_flat (algebraMap R A) P F a c i),
    (fun n ↦ homComplex_represents_RHom P F d n), ?_, ?_⟩
  · intro R' _ _
    dsimp only
    let A' := A ⊗[R] R'
    let f : A →+* A' := Algebra.TensorProduct.includeLeftRingHom
    obtain ⟨e, he, huniq⟩ := existsUnique_canonicalHomComplexBaseChangeIso f P F a c
    refine ⟨e, ⟨he, ?_⟩, fun e' he' ↦ huniq e' he'.1⟩
    intro n
    exact ⟨inferInstance, homComplex_baseChange_represents_RHom f P F d n⟩
  · intro _ hpseudo
    have (i : ℤ) : Module.FinitePresentation A (F.X i) := hfp hpseudo i
    exact ⟨hfp hpseudo, fun n ↦ homComplexR_finitePresentation P F a c n⟩

end StacksDraft.RelativelyPerfect
