module

public import StacksFrontier.Homology.RelativelyPerfect.Representative
public import StacksFrontier.Homology.Tor.IndependenceFlatModule
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
import all StacksFrontier.Homology.RelativelyPerfect.Representative

@[expose] public noncomputable section

/-!
# Hom complexes of relatively flat representatives and derived base change

Let `R → A` be flat, `K, L ∈ D(A)` with `K` pseudo-coherent and `L` of finite Tor dimension over
`R`. A *representative pair* is a bounded above complex `P` of finite free `A`-modules
representing `K` together with a bounded complex `F` of `R`-flat `A`-modules representing `L`.
Such pairs exist, and for every such pair:

* `E = Hom^•(P, F)` is a bounded below complex of `R`-flat `A`-modules representing
  `RHom_A(K, L)`;
* for every ring map `R → R'`, with `A' = A ⊗_R R'`, the complex `E ⊗_A A'` represents
  `RHom_{A'}(K ⊗ᴸ_A A', L ⊗ᴸ_A A')`: the termwise base changes `P ⊗_A A'` and `F ⊗_A A'`
  represent the derived base changes `K ⊗ᴸ_A A'` and `L ⊗ᴸ_A A'`, and `E ⊗_A A'` is canonically
  `Hom^•(P ⊗_A A', F ⊗_A A')`, which computes derived Hom over `A'`.

If `R → A` is of finite presentation and `L` is moreover pseudo-coherent (so `R`-perfect), the
pair can be chosen with `F` and `E` termwise finitely presented.

## Main definitions

* `StacksDraft.RelativelyPerfect.IsRelativeHomRepresentativePair`: the conditions on the pair
  `(P, F)`.
* `StacksDraft.RelativelyPerfect.cohomologyClassToDerivedHom`: the map from degree-`n` cohomology
  classes of `Hom^•(P, F)` to morphisms `X ⟶ Y⟦n⟧` of the derived category, read through given
  identifications of `P` with `X` and of `F` with `Y`.

## Main results

* `StacksDraft.RelativelyPerfect.IsRelativeHomRepresentativePair.represents_RHom_baseChange`:
  clauses (a) and (b) for an arbitrary representative pair.
* `StacksDraft.RelativelyPerfect.relativeHomComplex_represents_RHom` (Stacks 0E1U): existence of
  representative pairs, clauses (a) and (b) for every one of them, and the finite-presentation
  refinement.

## Implementation notes

The derived base change `- ⊗ᴸ_A A'` is the total derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` along the left
coprojection `A → A ⊗[R] R'`. A bounded above complex of projectives computes it by
construction; the bounded complex `F` of `R`-flat modules is K-flat over `R` ([stacks 064K]), so
it computes it by Tor independence of `A` and `R'` over `R` ([stacks 0661]), which is
`RingTheory.TorIndependence.isIso_comparison_of_kFlat_restrictScalars`. This is where flatness
of `R → A` and `R`-flatness of the terms of `F` are used.

That a complex represents derived Hom is the cohomological characterization of
`StacksDraft.RelativelyPerfect.Representative`: its degree-`n` cohomology classes map
bijectively to morphisms into the `n`-th shift ([stacks 0A66]).

All rings and modules live in one universe.

## References

* [The Stacks Project, Lemma 15.85.13 (0E1U)](https://stacks.math.columbia.edu/tag/0E1U)
-/

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

namespace StacksDraft.RelativelyPerfect

open StacksDraft.PseudoCoherence

universe u

/-- The map from degree-`n` cohomology classes of `Hom^•(P, F)` to morphisms `X ⟶ Y⟦n⟧` in the
derived category, where `X` and `Y` are identified with `P` and `F` by `eP` and `eF`: a class is
sent to the morphism `P ⟶ F⟦n⟧` it defines in the homotopy category, localized and conjugated by
`eP` and `eF`. -/
def cohomologyClassToDerivedHom {B : Type u} [CommRing B]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (P F : CochainComplex (ModuleCat.{u} B) ℤ) {X Y : DerivedCategory (ModuleCat.{u} B)}
    (eP : DerivedCategory.Q.obj P ≅ X) (eF : DerivedCategory.Q.obj F ≅ Y) (n : ℤ)
    (z : CochainComplex.HomComplex.CohomologyClass P F n) : X ⟶ Y⟦n⟧ :=
  (((DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).app P ≪≫ eP).homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).app (F⟦n⟧) ≪≫
        (DerivedCategory.Q.commShiftIso n).app F ≪≫ (shiftFunctor _ n).mapIso eF))
    (DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z))

/-- Conjugating by isomorphisms preserves bijectivity of the map from cohomology classes. -/
private lemma bijective_cohomologyClassToDerivedHom {B : Type u} [CommRing B]
    [HasDerivedCategory (ModuleCat.{u} B)]
    (P F : CochainComplex (ModuleCat.{u} B) ℤ) {X Y : DerivedCategory (ModuleCat.{u} B)}
    (eP : DerivedCategory.Q.obj P ≅ X) (eF : DerivedCategory.Q.obj F ≅ Y) (n : ℤ)
    (h : Function.Bijective
      (fun (z : CochainComplex.HomComplex.CohomologyClass P F n) ↦
        DerivedCategory.Qh.map (CochainComplex.HomComplex.CohomologyClass.homAddEquiv z))) :
    Function.Bijective (cohomologyClassToDerivedHom P F eP eF n) :=
  (Equiv.bijective _).comp h

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A pair of representatives as in Stacks 0E1U: `P` is a bounded above complex of finite free
`A`-modules and `F` is a bounded complex of `A`-modules which are flat over `R`. -/
def IsRelativeHomRepresentativePair (R : Type u) {A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (P F : CochainComplex (ModuleCat.{u} A) ℤ) : Prop :=
  (∃ d : ℤ, P.IsStrictlyLE d) ∧
    (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧
    (∃ a b : ℤ, F.IsStrictlyGE a ∧ F.IsStrictlyLE b) ∧
    ∀ i : ℤ, Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i))

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- **Clauses (a) and (b) of Stacks 0E1U for a given representative pair.** Let `R → A` be flat,
and let `P ≅ K` and `F ≅ L` in `D(A)` be a bounded above complex of finite free `A`-modules and a
bounded complex of `R`-flat `A`-modules. Then:

(a) `E = Hom^•(P, F)` is bounded below with `R`-flat terms, and represents `RHom_A(K, L)`: its
degree-`n` cohomology classes correspond bijectively to morphisms `K ⟶ L⟦n⟧` in `D(A)`;

(b) for every ring map `R → R'`, with `A' = A ⊗_R R'` and `D` the derived base change
`- ⊗ᴸ_A A'`, the termwise base changes `P' = P ⊗_A A'` and `F' = F ⊗_A A'` represent `D K` and
`D L`, the degree-`n` cohomology classes of `Hom^•(P', F')` correspond bijectively to morphisms
`D K ⟶ (D L)⟦n⟧` in `D(A')`, and `E ⊗_A A'` is canonically isomorphic to `Hom^•(P', F')`.
So `E ⊗_A A'` represents `RHom_{A'}(K ⊗ᴸ_A A', L ⊗ᴸ_A A')`. -/
theorem IsRelativeHomRepresentativePair.represents_RHom_baseChange [Module.Flat R A]
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} {P F : CochainComplex (ModuleCat.{u} A) ℤ}
    (h : IsRelativeHomRepresentativePair R P F)
    (eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K)
    (eF : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L) :
    (∃ c : ℤ, (CochainComplex.HomComplexR A P F).IsStrictlyGE c) ∧
      (∀ i : ℤ, Module.Flat R
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          ((CochainComplex.HomComplexR A P F).X i))) ∧
      (∀ n : ℤ, Function.Bijective (cohomologyClassToDerivedHom P F eP eF n)) ∧
      ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
        let f : A →+* A ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
        let Ext := (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)
        let D := (totalDerivedExtensionScalars.{u, u, u} f).functor
        ∃ (eP' : DerivedCategory.Q.obj (Ext.obj P) ≅ D.obj (DerivedCategory.Q.obj K))
          (eF' : DerivedCategory.Q.obj (Ext.obj F) ≅ D.obj (DerivedCategory.Q.obj L)),
          (∀ n : ℤ, Function.Bijective
            (cohomologyClassToDerivedHom (Ext.obj P) (Ext.obj F) eP' eF' n)) ∧
          ∃! e : Ext.obj (CochainComplex.HomComplexR A P F) ≅
              CochainComplex.HomComplexR (A ⊗[R] R') (Ext.obj P) (Ext.obj F),
            IsCanonicalHomComplexBaseChangeIso f P F e := by
  obtain ⟨⟨d, hd⟩, hP, ⟨a, b, ha, hb⟩, hF⟩ := h
  have := hd
  have := ha
  have := hb
  have (i : ℤ) : Module.Finite A (P.X i) := (hP i).1
  have (i : ℤ) : Module.Free A (P.X i) := (hP i).2
  have (i : ℤ) : Projective (P.X i) := inferInstance
  have (i : ℤ) : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (F.X i)) :=
    hF i
  refine ⟨⟨a - d, homComplexR_isStrictlyGE P F d a⟩,
    fun i ↦ homComplexR_flat (algebraMap R A) P F a b i,
    fun n ↦ bijective_cohomologyClassToDerivedHom P F eP eF n
      (homComplex_represents_RHom P F d n), ?_⟩
  intro R' _ _
  dsimp only
  let f : A →+* A ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
  let D := totalDerivedExtensionScalars.{u, u, u} f
  have hPcmp : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P d
  have hFcmp : IsIso (D.comparison.app F) := by
    have : CochainComplex.IsStrictlyLE (((ModuleCat.restrictScalars
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) b :=
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff F
        (ModuleCat.restrictScalars (algebraMap R A)) b).2 inferInstance
    have : ∀ n : ℤ, Module.Flat R ((((ModuleCat.restrictScalars
        (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n) := hF
    exact RingTheory.TorIndependence.isIso_comparison_of_kFlat_restrictScalars
      (R := R) (A := A) (B := R') (T := A ⊗[R] R')
      RingTheory.TorIndependence.torIndependent_of_flat_left F
      (CochainComplex.KFlat.kFlat_of_flat _ b)
  let eP' := (asIso (D.comparison.app P)).symm ≪≫ D.functor.mapIso eP
  let eF' := (asIso (D.comparison.app F)).symm ≪≫ D.functor.mapIso eF
  obtain ⟨e, he, huniq⟩ := existsUnique_canonicalHomComplexBaseChangeIso f P F a b
  refine ⟨eP', eF', fun n ↦ ?_, e, he, huniq⟩
  exact bijective_cohomologyClassToDerivedHom _ _ eP' eF' n
    (homComplex_baseChange_represents_RHom f P F d n)

/-- **Stacks 0E1U.** Let `R → A` be a flat ring map, and let `K, L ∈ D(A)` with `K`
pseudo-coherent and `L` of finite Tor dimension over `R`. Then:

(1)–(2) there are a bounded above complex `P` of finite free `A`-modules representing `K` and a
bounded complex `F` of `R`-flat `A`-modules representing `L`;

given any such choices,

(a) `E = Hom^•(P, F)` is a bounded below complex of `R`-flat `A`-modules representing
`RHom_A(K, L)`;

(b) for every ring map `R → R'`, with `A' = A ⊗_R R'`, the complex `E ⊗_A A'` represents
`RHom_{A'}(K ⊗ᴸ_A A', L ⊗ᴸ_A A')`: `P ⊗_A A'` and `F ⊗_A A'` represent the derived base changes
of `K` and `L`, their Hom complex computes the morphisms between these, and `E ⊗_A A'` is
canonically that Hom complex (see
`StacksDraft.RelativelyPerfect.IsRelativeHomRepresentativePair.represents_RHom_baseChange`).

If moreover `R → A` is of finite presentation and `L` is `R`-perfect (pseudo-coherent, its finite
Tor dimension over `R` being already assumed), the choices can be made with every `F^p`, and
consequently every `E^n`, a finitely presented `A`-module.

Objects of `D(A)` are presented by cochain complexes `K` and `L`; finite Tor dimension over `R`
is Tor amplitude in some `[a, b]` of `L` viewed as a complex of `R`-modules. -/
@[stacks 0E1U]
theorem relativeHomComplex_represents_RHom [Module.Flat R A]
    (K L : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ m : ℤ, IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m)
    (hL : ∃ a b : ℤ, StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj L) a b) :
    (∃ (P F : CochainComplex (ModuleCat.{u} A) ℤ)
        (_ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K)
        (_ : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L),
        IsRelativeHomRepresentativePair R P F) ∧
      (∀ (P F : CochainComplex (ModuleCat.{u} A) ℤ)
        (eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K)
        (eF : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L),
        IsRelativeHomRepresentativePair R P F →
        (∃ c : ℤ, (CochainComplex.HomComplexR A P F).IsStrictlyGE c) ∧
          (∀ i : ℤ, Module.Flat R
            ((ModuleCat.restrictScalars (algebraMap R A)).obj
              ((CochainComplex.HomComplexR A P F).X i))) ∧
          (∀ n : ℤ, Function.Bijective (cohomologyClassToDerivedHom P F eP eF n)) ∧
          ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
            let f : A →+* A ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
            let Ext := (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)
            let D := (totalDerivedExtensionScalars.{u, u, u} f).functor
            ∃ (eP' : DerivedCategory.Q.obj (Ext.obj P) ≅ D.obj (DerivedCategory.Q.obj K))
              (eF' : DerivedCategory.Q.obj (Ext.obj F) ≅ D.obj (DerivedCategory.Q.obj L)),
              (∀ n : ℤ, Function.Bijective
                (cohomologyClassToDerivedHom (Ext.obj P) (Ext.obj F) eP' eF' n)) ∧
              ∃! e : Ext.obj (CochainComplex.HomComplexR A P F) ≅
                  CochainComplex.HomComplexR (A ⊗[R] R') (Ext.obj P) (Ext.obj F),
                IsCanonicalHomComplexBaseChangeIso f P F e) ∧
      (Algebra.FinitePresentation R A →
        (∀ m : ℤ, IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m) →
        ∃ (P F : CochainComplex (ModuleCat.{u} A) ℤ)
          (_ : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj K)
          (_ : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L),
          IsRelativeHomRepresentativePair R P F ∧
            (∀ i : ℤ, Module.FinitePresentation A (F.X i)) ∧
            ∀ n : ℤ, Module.FinitePresentation A ((CochainComplex.HomComplexR A P F).X n)) := by
  obtain ⟨P, d, πK, hd, hP, hπK⟩ := exists_boundedAbove_finiteFree_of_pseudoCoherentFrom K hK
  obtain ⟨a, b, hL⟩ := hL
  obtain ⟨F, ⟨c, hGE, hLE⟩, hF, ⟨eF⟩, hfp⟩ :=
    exists_bounded_flat_with_finitePresentation.{u, u} (R := R) L a b hL
  have := hπK
  have hpair : IsRelativeHomRepresentativePair R P F := ⟨⟨d, hd⟩, hP, ⟨a, c, hGE, hLE⟩, hF⟩
  refine ⟨⟨P, F, asIso (DerivedCategory.Q.map πK), eF, hpair⟩,
    fun P F eP eF h ↦ h.represents_RHom_baseChange eP eF, fun _ hpseudo ↦ ?_⟩
  have := hGE
  have := hLE
  have (i : ℤ) : Module.Finite A (P.X i) := (hP i).1
  have (i : ℤ) : Module.Free A (P.X i) := (hP i).2
  have (i : ℤ) : Module.FinitePresentation A (F.X i) := hfp hpseudo i
  exact ⟨P, F, asIso (DerivedCategory.Q.map πK), eF, hpair, hfp hpseudo,
    fun n ↦ homComplexR_finitePresentation P F a c n⟩

end StacksDraft.RelativelyPerfect
