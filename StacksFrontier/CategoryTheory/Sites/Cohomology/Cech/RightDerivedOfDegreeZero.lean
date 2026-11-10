module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedOfDegreeZeroViaDeltaFunctors
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.Homology.Injectives.Sheaf.AbelianPresheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.DeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.InjectivePresheafVanishing
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology is the right derived functor of `Ȟ⁰`

Let `C` be a category, let `U` be an object of `C` and let `E = {U_i → U}_{i ∈ I}` be a family
of morphisms with target `U` all of whose finite nonempty fibre products exist. Stacks 03AU
identifies the Čech cohomology functors `Ȟ^p(E, -)` on abelian presheaves, as a cohomological
`δ`-functor, with the right derived functors `R^p Ȟ⁰(E, -)` of degree-zero Čech cohomology
`Ȟ⁰(E, -) : PAb(C) ⥤ Ab`.

Stacks 03AU asserts two things, and both are proved here.

**The `δ`-functor isomorphism.** Abelian presheaves have enough injectives (Stacks 01DK) and
`Ȟ⁰(E, -)` is left exact, so the right derived functors exist. The Čech cohomology of an
injective abelian presheaf vanishes in positive degrees (Stacks 03OR), and so do the higher
right derived functors of any additive functor (Stacks 015B), so both `δ`-functors are
effaceable, hence universal (Stacks 010T). Two universal `δ`-functors with isomorphic
degree-zero parts are uniquely isomorphic (Stacks 010U), and the degree-zero parts are
identified by the canonical comparison `Ȟ⁰(E, -) ⟶ R⁰ Ȟ⁰(E, -)`, which is invertible because
`Ȟ⁰(E, -)` is left exact (Stacks 05TD).

**The functorial quasi-isomorphism** `Č^•(E, F) ⟶ RȞ⁰(E, F)` in `D⁺(Ab)`. The source argues
with the double complex `Č^•(E, I^•)` of an injective resolution `F → I^•`: both legs of the
span `Č^•(E, F) ⟶ Tot(Č^•(E, I^•)) ⟵ Ȟ⁰(E, I^•)` are quasi-isomorphisms by Stacks 0133,
because the columns of the double complex are exact in positive degrees (the Čech complex
functor is exact, Stacks 03AQ) and the rows are exact in positive degrees (Stacks 03OR); and
`Ȟ⁰(E, I^•)` computes `RȞ⁰(E, F)` because `I^•` is a bounded below complex of injectives.
Since quasi-isomorphisms are invertible in `D⁺(Ab)`, this is an isomorphism there, and it is
natural in `F` because the chosen injective resolution is functorial up to the homotopies that
the derived category divides out.

## Main results

* `Stacks.CechSite.preservesFiniteLimits_cechH0`: degree-zero Čech cohomology is left exact.
* `Stacks.CechSite.isUniversal_cechCohomologyDeltaFunctor` of
  `Cech/RightDerivedOfDegreeZeroViaDeltaFunctors.lean`: Čech cohomology is a universal
  `δ`-functor.
* `Stacks.CechSite.cechH0RightDerived_isUniversal`: so are the right derived functors of
  degree-zero Čech cohomology.
* `Stacks.CechSite.existsUnique_cechCohomologyIsoRightDerived`: **Stacks 03AU**, the canonical
  isomorphism of `δ`-functors `Ȟ^•(E, -) ≅ R^• Ȟ⁰(E, -)`, unique with its prescribed
  degree-zero component.

## Main definitions

* `Stacks.CechSite.cechH0RightDerived`: the `n`-th right derived functor `R^n Ȟ⁰(E, -)`.
* `Stacks.CechSite.cechH0RightDerivedDeltaFunctor`: those functors, as a `δ`-functor.
* `Stacks.CechSite.cechCohomologyDeltaFunctorIsoRightDerived`: the canonical `δ`-functor
  isomorphism of
  Stacks 03AU.
* `Stacks.CechSite.cechComplexIsoRightDerivedFunctor`: **Stacks 03AU**, the functorial
  quasi-isomorphism from the Čech complex to `RȞ⁰(E, -)`, as an isomorphism of functors into
  the bounded below derived category of abelian groups.

## Implementation notes

The right derived functors used here are the `ℤ`-indexed ones of
`CategoryTheory.Functor.rightDerivedPlus`, computed in the bounded below derived category; they
are assembled into a `CategoryTheory.DeltaFunctor` by
`Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor`, whose `n`-th functor is `R^n` on the
nose. Čech cohomology is taken in the form of `Stacks.CechSite.cechCohomologyDeltaFunctor`
(Stacks 03AR), whose `n`-th functor is likewise literally the `n`-th Čech cohomology functor of
Stacks 03AM, so no comparison isomorphism intervenes in either indexing.

"Canonically isomorphic" is made precise by the uniqueness clause: the degree-zero component of
the isomorphism is pinned to `Stacks.RightDerivedPlus.rightDerivedPlusZeroIso`, which is `H⁰` of
the unit of the derived functor and so is the canonical comparison map `F ⟶ R⁰F` of Stacks 05TD,
and an isomorphism of universal `δ`-functors is determined by its degree-zero component.

The second half quantifies over the right derived functor: `RȞ⁰(E, -)` is any functor
`D⁺(PAb(C)) ⥤ D⁺(Ab)` carrying the derived-functor unit of `Ȟ⁰(E, -)`, rather than the chosen
`CategoryTheory.Functor.rightDerivedFunctorPlus`. This is the statement the source makes, and
it is the form the Čech-to-cohomology spectral sequence (Stacks 03AZ) consumes.

The span argument is carried out, for a general functor `G` into cochain complexes with an
augmentation `η : F(-)[0] ⟶ G(-)`, by the private `exactComplexIsoDerived` of the `Comparison`
section; the Čech-specific input is the augmentation `cechAugmentation`. Those helpers are
private, so `cechComplexIsoRightDerivedFunctor` carries `@[no_expose]`: the body of an exposed
`public def` may not name a private declaration, and nothing downstream needs to unfold it.

Several `rw`s in this file are configured with `transparency := .default`. In each case the goal
mentions a term whose type is spelled through `HomologicalComplex₂.flip`, `single` or
`extendSingleIso`, and is type-correct only once those semireducible definitions are unfolded,
which `rw` and `simp` do not do at their default reducible transparency. Where even that is not
enough — the naturality of the comparison isomorphism, where `simp` will not descend into the
composite at all — the step is written in term mode as a `calc` chain of `Category.assoc` and
`congrArg`.

The coefficient universe contains the object, morphism and family-index universes, which is the
small-site convention of the source. It is forced by Stacks 03OR as formalized
(`Stacks.CechSite.injective_presheaf_cechCohomology_isZero`), whose presentation of the Čech
complex as a `Hom` complex out of the integral Čech complex needs the coefficient universe to
contain the universes of `C`; the companion statements 03AW and 03AX are formalized at the same
universe.

## References

* [Stacks Project, Tag 03AU](https://stacks.math.columbia.edu/tag/03AU)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03AR](https://stacks.math.columbia.edu/tag/03AR)
* [Stacks Project, Tag 03OR](https://stacks.math.columbia.edu/tag/03OR)
* [Stacks Project, Tag 01DK](https://stacks.math.columbia.edu/tag/01DK)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 010U](https://stacks.math.columbia.edu/tag/010U)
* [Stacks Project, Tag 015B](https://stacks.math.columbia.edu/tag/015B)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
* [Stacks Project, Tag 03AQ](https://stacks.math.columbia.edu/tag/03AQ)
* [Stacks Project, Tag 03AP](https://stacks.math.columbia.edu/tag/03AP)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits

section EnoughInjectives

universe t uD vD

/-- **Stacks 01DK**, at the universe of this file: abelian presheaves on `D` with values in a
universe containing those of `D` have enough injectives. It is introduced with `letI` in each
declaration below that needs it, rather than as an instance, because the coefficient universe is
not determined by the goal. -/
theorem enoughInjectives_presheaf (D : Type uD) [Category.{vD} D] :
    EnoughInjectives (Dᵒᵖ ⥤ AddCommGrpCat.{max uD vD t}) :=
  enoughInjectives_of_hasFunctorialInjectiveEmbeddings (Dᵒᵖ ⥤ AddCommGrpCat.{max uD vD t})
    (Stacks.Injectives.presheaf_hasFunctorialInjectiveEmbeddings.{uD, vD, t} D)

end EnoughInjectives

universe w v a u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- The degree-zero Čech cohomology functor `Ȟ⁰(E, -) : PAb(C) ⥤ Ab` of Stacks 03AM, in the
packaging of the `δ`-functor of Stacks 03AR. -/
abbrev cechH0Functor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}) ⥤ AddCommGrpCat.{max u v w a} :=
  (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1.functor 0

/-- **Stacks 03AU**, the hypothesis of the lemma: degree-zero Čech cohomology is a left exact
functor from abelian presheaves to abelian groups. It is left exact because it is the
degree-zero part of a cohomological `δ`-functor. -/
theorem preservesFiniteLimits_cechH0 :
    PreservesFiniteLimits (cechH0Functor.{w, v, a, u} E) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  exact fun S hS ↦ ⟨(cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1.exact_map hS 0,
    (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1.mono_map_f hS⟩

/-- **Stacks 03AU.** The `n`-th right derived functor `R^n Ȟ⁰(E, -)` of degree-zero Čech
cohomology, formed in the bounded below derived category of abelian presheaves. -/
def cechH0RightDerived (n : ℤ) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}) ⥤ AddCommGrpCat.{max u v w a} :=
  letI := enoughInjectives_presheaf.{max w a, u, v} C
  (cechH0Functor.{w, v, a, u} E).rightDerivedPlus n

/-- **Stacks 03AU.** The right derived functors of degree-zero Čech cohomology, assembled into
a cohomological `δ`-functor by Stacks 05TE. -/
def cechH0RightDerivedDeltaFunctor :
    DeltaFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}) AddCommGrpCat.{max u v w a} :=
  letI := enoughInjectives_presheaf.{max w a, u, v} C
  Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor (cechH0Functor.{w, v, a, u} E)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure (cechH0Functor.{w, v, a, u} E))
    (Stacks.DerivedIndexing.canonicalδ (cechH0Functor.{w, v, a, u} E)) (fun _ _ ↦ rfl)

/-- The `n`-th functor of `cechH0RightDerivedDeltaFunctor` is, on the nose, the `n`-th right
derived functor of degree-zero Čech cohomology. -/
@[simp]
theorem cechH0RightDerivedDeltaFunctor_functor (n : ℕ) :
    (cechH0RightDerivedDeltaFunctor.{w, v, a, u} E).functor n =
      cechH0RightDerived.{w, v, a, u} E (n : ℤ) := rfl

/-- **Stacks 03AU**, second step: the `δ`-functor of the right derived functors of degree-zero
Čech cohomology is universal. By Stacks 010T it suffices that the higher right derived functors
vanish on injective abelian presheaves, which is Stacks 015B. -/
theorem cechH0RightDerived_isUniversal :
    (cechH0RightDerivedDeltaFunctor.{w, v, a, u} E).IsUniversal := by
  have := enoughInjectives_presheaf.{max w a, u, v} C
  refine DeltaFunctor.isUniversal_of_isZero_injective
    (cechH0RightDerivedDeltaFunctor.{w, v, a, u} E) (fun n I _ ↦ ?_)
  rw [cechH0RightDerivedDeltaFunctor_functor]
  exact Functor.isZero_rightDerivedPlus_obj_injective (cechH0Functor.{w, v, a, u} E)
    ((n + 1 : ℕ) : ℤ) (by omega) I

/-- The canonical comparison `Ȟ⁰(E, -) ≅ R⁰ Ȟ⁰(E, -)` in degree zero: it is `H⁰` of the unit of
the derived functor, invertible by Stacks 05TD because `Ȟ⁰(E, -)` is left exact. -/
def cechH0IsoRightDerivedZero :
    cechH0Functor.{w, v, a, u} E ≅ cechH0RightDerived.{w, v, a, u} E 0 :=
  letI := enoughInjectives_presheaf.{max w a, u, v} C
  letI := preservesFiniteLimits_cechH0.{w, v, a, u} E
  (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (cechH0Functor.{w, v, a, u} E)).symm

/-- **Stacks 03AU.** The canonical isomorphism of `δ`-functors from Čech cohomology to the right
derived functors of degree-zero Čech cohomology. -/
def cechCohomologyDeltaFunctorIsoRightDerived :
    (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1 ≅
      cechH0RightDerivedDeltaFunctor.{w, v, a, u} E :=
  letI := enoughInjectives_presheaf.{max w a, u, v} C
  letI := isUniversal_cechCohomologyDeltaFunctor.{w, v, a, u} E
  letI := cechH0RightDerived_isUniversal.{w, v, a, u} E
  DeltaFunctor.IsUniversal.isoOfIso (cechH0IsoRightDerivedZero.{w, v, a, u} E)

/-- The degree-zero component of `cechCohomologyDeltaFunctorIsoRightDerived` is the canonical
comparison
`Ȟ⁰(E, -) ⟶ R⁰ Ȟ⁰(E, -)`. -/
@[simp]
theorem cechCohomologyDeltaFunctorIsoRightDerived_hom_app_zero :
    (cechCohomologyDeltaFunctorIsoRightDerived.{w, v, a, u} E).hom.app 0 =
      (cechH0IsoRightDerivedZero.{w, v, a, u} E).hom :=
  let := enoughInjectives_presheaf.{max w a, u, v} C
  let := isUniversal_cechCohomologyDeltaFunctor.{w, v, a, u} E
  let := cechH0RightDerived_isUniversal.{w, v, a, u} E
  DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero
    (F := (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1)
    (G := cechH0RightDerivedDeltaFunctor.{w, v, a, u} E)
    (cechH0IsoRightDerivedZero.{w, v, a, u} E)

/-- **Stacks Project, Tag 03AU.** The Čech cohomology functors `Ȟ^p(E, -)` of a family of
morphisms with fixed target are canonically isomorphic, as a cohomological `δ`-functor on
abelian presheaves, to the right derived functors `R^p Ȟ⁰(E, -)` of degree-zero Čech cohomology.

"Canonically" is the uniqueness clause: there is exactly one isomorphism of `δ`-functors whose
degree-zero component is the canonical comparison `Ȟ⁰(E, -) ⟶ R⁰ Ȟ⁰(E, -)` of Stacks 05TD, and
it is `Stacks.CechSite.cechCohomologyDeltaFunctorIsoRightDerived`. -/
@[stacks 03AU "the canonical δ-functor isomorphism"]
theorem existsUnique_cechCohomologyIsoRightDerived :
    ∃! e : (cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).1 ≅
        cechH0RightDerivedDeltaFunctor.{w, v, a, u} E,
      e.hom.app 0 = (cechH0IsoRightDerivedZero.{w, v, a, u} E).hom := by
  have := enoughInjectives_presheaf.{max w a, u, v} C
  have := isUniversal_cechCohomologyDeltaFunctor.{w, v, a, u} E
  have := cechH0RightDerived_isUniversal.{w, v, a, u} E
  exact ⟨cechCohomologyDeltaFunctorIsoRightDerived.{w, v, a, u} E,
    cechCohomologyDeltaFunctorIsoRightDerived_hom_app_zero.{w, v, a, u} E, fun e' he' ↦
      DeltaFunctor.IsUniversal.iso_ext
        (he'.trans (cechCohomologyDeltaFunctorIsoRightDerived_hom_app_zero.{w, v, a, u} E).symm)⟩

/-! ### A functor to complexes that computes a right derived functor

The second half of Stacks 03AU is the functorial quasi-isomorphism from the Čech complex to
`RȞ⁰(E, -)`. The source argues with the double complex `Č^•(E, I^•)` attached to an injective
resolution `F → I^•`: both legs of the span

`Č^•(E, F) ⟶ Tot(Č^•(E, I^•)) ⟵ Ȟ⁰(E, I^•)`

are quasi-isomorphisms, by [Stacks, Tag 0133], because the columns of the double complex are
exact in positive degrees (the Čech complex functor is exact, Stacks 03AQ) and the rows are
exact in positive degrees (Stacks 03OR). The construction below is this argument for a general
functor `G` into complexes together with an augmentation `η : F[0] ⟶ G`, so that `G` plays the
role of `Č^•(E, -)` and `F` that of `Ȟ⁰(E, -)`.
-/

section Comparison

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]

open HomologicalComplex StacksDraft.TotalComplexQuasiIso

/-- The image of a morphism of double complexes under the flip. -/
private abbrev flipHom {K L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (f : K ⟶ L) : K.flip ⟶ L.flip :=
  (HomologicalComplex₂.flipFunctor B (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f

/-- The identification of the total complex of a double complex with that of its flip is natural
in the double complex. -/
private lemma totalFlip_naturality
    {K L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : K ⟶ L)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)] :
    HomologicalComplex₂.total.map (flipHom f) (ComplexShape.up ℤ) ≫
        (L.totalFlipIso (ComplexShape.up ℤ)).hom =
      (K.totalFlipIso (ComplexShape.up ℤ)).hom ≫
        HomologicalComplex₂.total.map f (ComplexShape.up ℤ) := by
  ext n p q h
  simp only [comp_f, HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc,
    Units.smul_def, HomologicalComplex₂.flipFunctor_map_f_f]
  -- `K.flip` must be unfolded for the goal to be type-correct, which `rw` does only at
  -- default transparency; see the module docstring.
  rw (transparency := .default) [Preadditive.zsmul_comp, HomologicalComplex₂.ιTotal_map,
    Preadditive.comp_zsmul]
  rfl

/-- A first-quadrant double complex vanishes in negative second degrees and in negative columns:
the hypotheses of `hasTotal_of_bounded` and `quasiIso_total_map` with `a = 0`. -/
private lemma firstQuadrant_bounds
    {K : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ)}
    (h : ∀ p q, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) :
    (∀ p q, q < 0 → IsZero ((K.X p).X q)) ∧ ∀ p, p < 0 → IsZero (K.X p) :=
  ⟨fun p q hq ↦ h p q (Or.inr hq), fun p hp ↦ (IsZero.iff_id_eq_zero _).2 (by
    ext q
    exact (h p q (Or.inl hp)).eq_of_src _ _)⟩

/-- **Stacks 0133, in the form used here.** A morphism of first-quadrant double complexes whose
columns are quasi-isomorphisms induces a quasi-isomorphism on total complexes. -/
private lemma total_quasiIso_flip
    {K L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ)} (f : K ⟶ L)
    [K.HasTotal (ComplexShape.up ℤ)] [L.HasTotal (ComplexShape.up ℤ)]
    (hK : ∀ p q, p < 0 ∨ q < 0 → IsZero ((K.X p).X q))
    (hL : ∀ p q, p < 0 ∨ q < 0 → IsZero ((L.X p).X q))
    (hf : ∀ q, QuasiIso ((flipHom f).f q)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) := by
  have hK' := firstQuadrant_bounds (K := K.flip) fun p q h ↦ hK q p h.symm
  have hL' := firstQuadrant_bounds (K := L.flip) fun p q h ↦ hL q p h.symm
  have := quasiIso_total_map (flipHom f) 0 hK'.1 hK'.2 hL'.1 hL'.2 hf
  have : QuasiIso ((K.totalFlipIso (ComplexShape.up ℤ)).hom ≫
      HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) := by
    rw [← totalFlip_naturality]
    infer_instance
  exact quasiIso_of_comp_left (K.totalFlipIso (ComplexShape.up ℤ)).hom _

/-- The canonical morphism from a complex to the total complex of that complex placed in the
column `0`. -/
private def columnUnit (K : CochainComplex B ℤ)
    [(singleColumn K 0).HasTotal (ComplexShape.up ℤ)] :
    K ⟶ (singleColumn K 0).total (ComplexShape.up ℤ) :=
  (shiftFunctorZero (CochainComplex B ℤ) ℤ).inv.app K ≫ totalSingleColumnUnit K 0

/-- `columnUnit` is an isomorphism. -/
private lemma columnUnit_isIso (K : CochainComplex B ℤ)
    [(singleColumn K 0).HasTotal (ComplexShape.up ℤ)] : IsIso (columnUnit K) := by
  have := isIso_totalSingleColumnUnit K 0
  dsimp [columnUnit]
  infer_instance

/-- `columnUnit` is natural in the complex. -/
private lemma columnUnit_naturality {K L : CochainComplex B ℤ} (f : K ⟶ L)
    [(singleColumn K 0).HasTotal (ComplexShape.up ℤ)]
    [(singleColumn L 0).HasTotal (ComplexShape.up ℤ)] :
    f ≫ columnUnit L = columnUnit K ≫ HomologicalComplex₂.total.map
      ((single (CochainComplex B ℤ) (ComplexShape.up ℤ) 0).map f) (ComplexShape.up ℤ) := by
  dsimp only [columnUnit]
  have h := (shiftFunctorZero (CochainComplex B ℤ) ℤ).inv.naturality f
  dsimp only [Functor.id_map] at h
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  exact congrArg ((shiftFunctorZero (CochainComplex B ℤ) ℤ).inv.app K ≫ ·)
    (by simpa using totalSingleColumnUnit_naturality f 0)

section Span

variable (G : A ⥤ CochainComplex B ℤ) [G.Additive] (hG : ∀ X, (G.obj X).IsStrictlyGE 0)

/-- The double complex `G(K^•)` obtained by applying `G` termwise to a complex `K` of `A`. -/
private abbrev appliedBicomplex (K : CochainComplex A ℤ) :
    HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

include hG in
/-- `G(K^•)` is a first-quadrant double complex when `K` is bounded below by `0`. -/
private lemma bicomplex_nonnegative (K : CochainComplex A ℤ) [K.IsStrictlyGE 0] :
    ∀ p q, p < 0 ∨ q < 0 →
      IsZero (((appliedBicomplex G K).X p).X q) := by
  rintro p q (hp | hq)
  · exact (HomologicalComplex.eval B (ComplexShape.up ℤ) q).map_isZero
      (G.map_isZero (K.isZero_of_isStrictlyGE 0 p hp))
  · have := hG (K.X p)
    exact (G.obj (K.X p)).isZero_of_isStrictlyGE 0 q hq

include hG in
/-- The total complex of `G(K^•)` exists. -/
private lemma bicomplex_hasTotal (K : CochainComplex A ℤ) [K.IsStrictlyGE 0] :
    (appliedBicomplex G K).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded _ 0 (firstQuadrant_bounds (bicomplex_nonnegative G hG K)).1
    (firstQuadrant_bounds (bicomplex_nonnegative G hG K)).2

/-- The left leg of the comparison span, before taking total complexes: the morphism of double
complexes `G(X)[0] ⟶ G(K^•)` induced by a resolution `X[0] ⟶ K^•`, viewing `G(X)` as the
column `0`. -/
private def leftBicomplex {X : A} {K : CochainComplex A ℤ}
    (l : (single A (ComplexShape.up ℤ) 0).obj X ⟶ K) :
    singleColumn (G.obj X) 0 ⟶ appliedBicomplex G K :=
  (singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app X ≫
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map l

/-- `leftBicomplex` is natural in a commuting square of resolutions. -/
private lemma leftBicomplex_naturality {X Y : A} {K L : CochainComplex A ℤ}
    (l : (single A (ComplexShape.up ℤ) 0).obj X ⟶ K)
    (l' : (single A (ComplexShape.up ℤ) 0).obj Y ⟶ L)
    (f : X ⟶ Y) (g : K ⟶ L)
    (h : l ≫ g = (single A (ComplexShape.up ℤ) 0).map f ≫ l') :
    leftBicomplex G l ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map g =
      (single (CochainComplex B ℤ) (ComplexShape.up ℤ) 0).map (G.map f) ≫ leftBicomplex G l' := by
  dsimp only [leftBicomplex]
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun k ↦ k ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map l')
      ((singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.naturality f).symm

include hG in
/-- The left leg of the span is a quasi-isomorphism on total complexes: `G` preserves the
quasi-isomorphism `X[0] ⟶ K^•` columnwise. -/
private lemma leftBicomplex_quasiIso [G.PreservesHomology]
    {X : A} {K : CochainComplex A ℤ} [K.IsStrictlyGE 0]
    (l : (single A (ComplexShape.up ℤ) 0).obj X ⟶ K) [hql : QuasiIso l]
    [(singleColumn (G.obj X) 0).HasTotal (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (HomologicalComplex₂.total.map (leftBicomplex G l) (ComplexShape.up ℤ)) := by
  have hsingle (p q : ℤ) (h : p < 0 ∨ q < 0) :
      IsZero (((singleColumn (G.obj X) 0).X p).X q) := by
    rcases eq_or_ne p 0 with rfl | hp
    · have := hG X
      exact IsZero.of_iso ((G.obj X).isZero_of_isStrictlyGE 0 q (by omega))
        ((HomologicalComplex.eval B (ComplexShape.up ℤ) q).mapIso
          (singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj X)))
    · exact isZero_singleColumn_X_X _ _ _ hp q
  refine total_quasiIso_flip (leftBicomplex G l) hsingle (bicomplex_nonnegative G hG K) fun q ↦ ?_
  have : QuasiIso (leftBicomplex G l) := by
    dsimp [leftBicomplex]
    have : QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map l) := inferInstance
    infer_instance
  exact inferInstanceAs (QuasiIso
    (((HomologicalComplex.eval B (ComplexShape.up ℤ) q).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (leftBicomplex G l)))

variable (F : A ⥤ B) [F.PreservesZeroMorphisms]
  (η : F ⋙ single B (ComplexShape.up ℤ) 0 ⟶ G)

/-- The right leg of the comparison span, before taking total complexes: the morphism of double
complexes `F(K^•)[0] ⟶ G(K^•)` induced by the augmentation `η`. -/
private def rightBicomplex (K : CochainComplex A ℤ) :
    singleRowZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      appliedBicomplex G K :=
  (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K

/-- `rightBicomplex` is natural in the complex. -/
private lemma rightBicomplex_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    ((single B (ComplexShape.up ℤ) 0).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫ rightBicomplex G F η L =
      rightBicomplex G F η K ≫ (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f :=
  (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).naturality f

include hG in
/-- The right leg of the span is a quasi-isomorphism on total complexes as soon as `η` is a
quasi-isomorphism at every term of the complex. -/
private lemma rightBicomplex_quasiIso (K : CochainComplex A ℤ) [K.IsStrictlyGE 0]
    [(singleRowZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).HasTotal
      (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)]
    (hη : ∀ n, QuasiIso (η.app (K.X n))) :
    QuasiIso (HomologicalComplex₂.total.map (rightBicomplex G F η K) (ComplexShape.up ℤ)) :=
  quasiIso_total_map _ 0
    (fun p q hq ↦ isZero_singleRowZero_X_X _ p q hq)
    (fun p hp ↦ isZero_singleRowZero_X _ 0 p hp)
    (firstQuadrant_bounds (bicomplex_nonnegative G hG K)).1
    (firstQuadrant_bounds (bicomplex_nonnegative G hG K)).2 hη

/-- The left leg `G(X) ⟶ Tot(G(K^•))` of the comparison span. -/
private def leftTotal {X : A} {K : CochainComplex A ℤ}
    (l : (single A (ComplexShape.up ℤ) 0).obj X ⟶ K)
    [(singleColumn (G.obj X) 0).HasTotal (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)] :
    G.obj X ⟶ (appliedBicomplex G K).total (ComplexShape.up ℤ) :=
  columnUnit _ ≫ HomologicalComplex₂.total.map (leftBicomplex G l) (ComplexShape.up ℤ)

/-- `leftTotal` is natural in a commuting square of resolutions. -/
private lemma leftTotal_naturality {X Y : A} {K L : CochainComplex A ℤ}
    (l : (single A (ComplexShape.up ℤ) 0).obj X ⟶ K)
    (l' : (single A (ComplexShape.up ℤ) 0).obj Y ⟶ L)
    (f : X ⟶ Y) (g : K ⟶ L)
    (h : l ≫ g = (single A (ComplexShape.up ℤ) 0).map f ≫ l')
    [(singleColumn (G.obj X) 0).HasTotal (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)]
    [(singleColumn (G.obj Y) 0).HasTotal (ComplexShape.up ℤ)]
    [(appliedBicomplex G L).HasTotal (ComplexShape.up ℤ)] :
    G.map f ≫ leftTotal G l' = leftTotal G l ≫ HomologicalComplex₂.total.map
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map g) (ComplexShape.up ℤ) := by
  dsimp only [leftTotal]
  rw [← Category.assoc, columnUnit_naturality, Category.assoc,
    ← HomologicalComplex₂.total.map_comp, ← leftBicomplex_naturality G l l' f g h,
    HomologicalComplex₂.total.map_comp, Category.assoc]

/-- The right leg `F(K^•) ⟶ Tot(G(K^•))` of the comparison span. -/
private def rightTotal (K : CochainComplex A ℤ)
    [(singleRowZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).HasTotal
      (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⟶
      (appliedBicomplex G K).total (ComplexShape.up ℤ) :=
  totalSingleRowZeroUnit _ ≫
    HomologicalComplex₂.total.map (rightBicomplex G F η K) (ComplexShape.up ℤ)

/-- `rightTotal` is natural in the complex. -/
private lemma rightTotal_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L)
    [(singleRowZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).HasTotal
      (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)]
    [(singleRowZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)).HasTotal
      (ComplexShape.up ℤ)]
    [(appliedBicomplex G L).HasTotal (ComplexShape.up ℤ)] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫ rightTotal G F η L =
      rightTotal G F η K ≫ HomologicalComplex₂.total.map
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) (ComplexShape.up ℤ) := by
  dsimp only [rightTotal]
  rw [← Category.assoc, ← totalSingleRowZeroUnit_naturality, Category.assoc,
    ← HomologicalComplex₂.total.map_comp, rightBicomplex_naturality,
    HomologicalComplex₂.total.map_comp, Category.assoc]

include hG in
/-- The left leg of the span is a quasi-isomorphism. -/
private lemma leftTotal_quasiIso [G.PreservesHomology]
    {X : A} {K : CochainComplex A ℤ} [K.IsStrictlyGE 0]
    (l : (single A (ComplexShape.up ℤ) 0).obj X ⟶ K) [hql : QuasiIso l]
    [(singleColumn (G.obj X) 0).HasTotal (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)] :
    QuasiIso (leftTotal G l) := by
  have := columnUnit_isIso (G.obj X)
  have := leftBicomplex_quasiIso G hG l
  dsimp [leftTotal]
  infer_instance

include hG in
/-- The right leg of the span is a quasi-isomorphism. -/
private lemma rightTotal_quasiIso (K : CochainComplex A ℤ) [K.IsStrictlyGE 0]
    [(singleRowZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).HasTotal
      (ComplexShape.up ℤ)]
    [(appliedBicomplex G K).HasTotal (ComplexShape.up ℤ)]
    (hη : ∀ n, QuasiIso (η.app (K.X n))) :
    QuasiIso (rightTotal G F η K) := by
  have := isIso_totalSingleRowZeroUnit
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have := rightBicomplex_quasiIso G hG F η K hη
  dsimp [rightTotal]
  infer_instance

end Span

/-! #### From the span to the derived category -/

/-- The localization `K⁺(A) ⥤ D⁺(A)` of bounded below complexes factors through the bounded
below homotopy category. -/
private def plusQhIso (D : Type*) [Category* D] [Abelian D] [HasDerivedCategory D] :
    HomotopyCategory.Plus.quotient D ⋙ DerivedCategory.Plus.Qh ≅ DerivedCategory.Plus.Q :=
  (Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Plus.ι (C := D)))
    (CochainComplex.Plus D)).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι D) (DerivedCategory.quotientCompQhIso D))

/-- The unit of a right derived functor, read on bounded below complexes rather than on the
bounded below homotopy category. -/
private def derivedUnit (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF) :
    F.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⟶ DerivedCategory.Plus.Q ⋙ RF :=
  Functor.whiskerLeft F.mapCochainComplexPlus (plusQhIso B).inv ≫
    Functor.whiskerLeft (HomotopyCategory.Plus.quotient A) α ≫
    Functor.whiskerRight (plusQhIso A).hom RF

/-- The unit of a right derived functor is invertible at a bounded below complex of injective
objects. -/
private lemma derivedUnit_isIso (F : A ⥤ B) [F.Additive] [EnoughInjectives A]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) (hK : ∀ n, Injective (K.obj.X n)) :
    IsIso ((derivedUnit F RF α).app K) := by
  have ha : IsIso (α.app ((HomotopyCategory.Plus.quotient A).obj K)) := by
    obtain ⟨K, n, hn⟩ := K
    have : ∀ n, Injective (K.X n) := hK
    let L : CochainComplex (InjectiveObject A) ℤ :=
      HomologicalComplex.liftObjectProperty _ K inferInstance
    have hL : L.IsStrictlyGE n := by
      rwa [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι A)]
    exact inferInstanceAs (IsIso (α.app ((HomotopyCategory.Plus.quotient A).obj
      ((InjectiveObject.ι A).mapCochainComplexPlus.obj ⟨L, n, hL⟩))))
  dsimp only [derivedUnit, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact IsIso.comp_isIso' (by infer_instance) (IsIso.comp_isIso' ha (by infer_instance))

/-- The isomorphism between the two ends of a span of isomorphisms. -/
private def spanIso {D : Type*} [Category* D] {Y Z T : D}
    (f : Y ⟶ T) (g : Z ⟶ T) [IsIso f] [IsIso g] : Y ≅ Z :=
  asIso f ≪≫ (asIso g).symm

/-- `spanIso` is natural in a morphism of spans. -/
private lemma spanIso_naturality {D : Type*} [Category* D] {Y Z T Y' Z' T' : D}
    (f : Y ⟶ T) (g : Z ⟶ T) (f' : Y' ⟶ T') (g' : Z' ⟶ T')
    [IsIso f] [IsIso g] [IsIso f'] [IsIso g']
    (b₁ : Y ⟶ Y') (b₂ : Z ⟶ Z') (t : T ⟶ T')
    (h₁ : b₁ ≫ f' = f ≫ t) (h₂ : b₂ ≫ g' = g ≫ t) :
    b₁ ≫ (spanIso f' g').hom = (spanIso f g).hom ≫ b₂ := by
  apply (cancel_mono g').mp
  simp only [spanIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc]
  rw [IsIso.inv_hom_id, Category.comp_id, h₁, h₂, IsIso.inv_hom_id_assoc]

/-- The identification of `X[0]` with the extension by zero of the `ℕ`-graded complex `X[0]` is
natural in `X`. -/
private lemma extendSingle_naturality {Y Z : A} (f : Y ⟶ Z) :
    (single A (ComplexShape.up ℤ) 0).map f ≫
        (extendSingleIso ComplexShape.embeddingUpNat Z 0 0 ComplexShape.embeddingUpNat_f_zero).inv =
      (extendSingleIso ComplexShape.embeddingUpNat Y 0 0 ComplexShape.embeddingUpNat_f_zero).inv ≫
        extendMap ((CochainComplex.single₀ A).map f) ComplexShape.embeddingUpNat := by
  apply from_single_hom_ext
  simp only [comp_f, single_map_f_self]
  rw [extendSingleIso_inv_f, extendSingleIso_inv_f,
    extendMap_f _ _ (i := 0) (i' := 0) ComplexShape.embeddingUpNat_f_zero]
  simp only [CochainComplex.single₀_obj_zero, CochainComplex.single₀ObjXSelf, Iso.refl_inv,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc,
    CochainComplex.single₀_map_f_zero, Iso.cancel_iso_hom_left]
  -- The two `extendXIso`s are at `single A (up ℕ) 0` and at the abbreviation `single₀ A`,
  -- which `rw` identifies only at default transparency.
  rw (transparency := .default) [Iso.inv_hom_id_assoc]

/-- The chosen injective resolution of an object, as a bounded below complex graded by `ℤ`. -/
private abbrev resolutionComplex {Y : A} (I : CategoryTheory.InjectiveResolution Y) :
    CochainComplex.Plus A :=
  ⟨I.cocomplex.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩

/-- The augmentation `Y[0] ⟶ I^•` of an injective resolution, read in degrees graded by `ℤ`. -/
private def resolutionι {Y : A} (I : CategoryTheory.InjectiveResolution Y) :
    (single A (ComplexShape.up ℤ) 0).obj Y ⟶ (resolutionComplex I).obj :=
  (extendSingleIso ComplexShape.embeddingUpNat Y 0 0 ComplexShape.embeddingUpNat_f_zero).inv ≫
    extendMap I.ι ComplexShape.embeddingUpNat

/-- The augmentation of an injective resolution is a quasi-isomorphism. -/
private lemma resolutionι_quasiIso {Y : A} (I : CategoryTheory.InjectiveResolution Y) :
    QuasiIso (resolutionι I) := by
  dsimp [resolutionι]
  infer_instance

/-- Every term of an injective resolution, extended by zero, is injective. -/
private lemma resolution_injective {Y : A} (I : CategoryTheory.InjectiveResolution Y) (n : ℤ) :
    Injective ((resolutionComplex I).obj.X n) := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    exact Injective.of_iso (I.cocomplex.extendXIso ComplexShape.embeddingUpNat
      (i := n) rfl).symm inferInstance
  · exact ((resolutionComplex I).obj.isZero_of_isStrictlyGE 0 n (by omega)).injective

/-- The lift of a morphism to the chosen injective resolutions. -/
private def resolutionMap {Y Z : A} (I : CategoryTheory.InjectiveResolution Y)
    (J : CategoryTheory.InjectiveResolution Z) (f : Y ⟶ Z) :
    resolutionComplex I ⟶ resolutionComplex J :=
  ObjectProperty.homMk (extendMap (CategoryTheory.InjectiveResolution.desc f J I)
    ComplexShape.embeddingUpNat)

/-- The square relating `resolutionMap` to the augmentations commutes. -/
private lemma resolutionMap_comm {Y Z : A} (I : CategoryTheory.InjectiveResolution Y)
    (J : CategoryTheory.InjectiveResolution Z) (f : Y ⟶ Z) :
    resolutionι I ≫ (resolutionMap I J f).hom =
      (single A (ComplexShape.up ℤ) 0).map f ≫ resolutionι J := by
  dsimp only [resolutionι, resolutionMap, ObjectProperty.homMk_hom]
  rw [Category.assoc, ← extendMap_comp, CategoryTheory.InjectiveResolution.desc_commutes,
    extendMap_comp, ← Category.assoc, ← extendSingle_naturality, Category.assoc]

/-- `X ↦ X[0]`, landing in bounded below complexes. -/
private def singlePlus (D : Type*) [Category* D] [Abelian D] : D ⥤ CochainComplex.Plus D :=
  ObjectProperty.lift _ (single D (ComplexShape.up ℤ) 0) (fun _ ↦ ⟨0, inferInstance⟩)

/-- A quasi-isomorphism of bounded below complexes becomes invertible in `D⁺`. -/
private lemma plusQ_isIso {K L : CochainComplex.Plus A} (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso (DerivedCategory.Plus.Q.map f) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) :=
    inferInstanceAs (IsIso (DerivedCategory.Q.map f.hom))
  exact isIso_of_fully_faithful DerivedCategory.Plus.ι _

/-- **The key comparison.** Let `G : A ⥤ C(B)` be an exact functor into cochain complexes whose
values are bounded below by `0`, let `F : A ⥤ B` be additive, and let
`η : F(-)[0] ⟶ G(-)` be an augmentation which is a quasi-isomorphism at every injective object
of `A`. Then `G` computes the right derived functor of `F`: for any right derived functor `RF`
of `F` on bounded below derived categories, `G(-)` and `RF((-)[0])` are naturally isomorphic
in `D(B)`.

This is the span argument of [Stacks, Tag 03AU]: a resolution `X[0] ⟶ I^•` gives
`G(X) ⟶ Tot(G(I^•)) ⟵ F(I^•)`, both legs quasi-isomorphisms, and `F(I^•)` computes `RF(X)`
because `I^•` is a bounded below complex of injectives. -/
private def exactComplexIsoDerived (G : A ⥤ CochainComplex B ℤ) [G.Additive]
    [G.PreservesHomology] (hG : ∀ X, (G.obj X).IsStrictlyGE 0)
    (F : A ⥤ B) [F.Additive] (η : F ⋙ single B (ComplexShape.up ℤ) 0 ⟶ G)
    (hη : ∀ I : A, Injective I → QuasiIso (η.app I)) [EnoughInjectives A]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] :
    G ⋙ DerivedCategory.Q ≅
      (singlePlus A ⋙ DerivedCategory.Plus.Q ⋙ RF) ⋙ DerivedCategory.Plus.ι := by
  let I (Y : A) := CategoryTheory.injectiveResolution Y
  let K (Y : A) := resolutionComplex (I Y)
  have hK (Y : A) : (K Y).obj.IsStrictlyGE 0 := inferInstance
  let l (Y : A) : (singlePlus A).obj Y ⟶ K Y := ObjectProperty.homMk (resolutionι (I Y))
  have hl (Y : A) : QuasiIso (l Y).hom := resolutionι_quasiIso (I Y)
  have ht (Y : A) : (appliedBicomplex G (K Y).obj).HasTotal (ComplexShape.up ℤ) :=
    bicomplex_hasTotal G hG (K Y).obj
  have hs (Y : A) : (singleColumn (G.obj Y) 0).HasTotal (ComplexShape.up ℤ) :=
    hasTotal_singleColumn _ _
  have hr (Y : A) : (singleRowZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (K Y).obj)).HasTotal (ComplexShape.up ℤ) :=
    hasTotal_of_bounded _ 0 (isZero_singleRowZero_X_X _)
      (fun p hp ↦ isZero_singleRowZero_X _ 0 p hp)
  let aL (Y : A) := leftTotal G (l Y).hom
  let aR (Y : A) := rightTotal G F η (K Y).obj
  have haL (Y : A) : QuasiIso (aL Y) :=
    leftTotal_quasiIso G hG (X := Y) (l Y).hom (hql := hl Y)
  have haR (Y : A) : QuasiIso (aR Y) := rightTotal_quasiIso G hG F η (K Y).obj
    (fun n ↦ hη _ (resolution_injective (I Y) n))
  have hu (Y : A) : IsIso ((derivedUnit F RF α).app (K Y)) :=
    derivedUnit_isIso F RF α (K Y) (resolution_injective (I Y))
  have hli (Y : A) : IsIso (DerivedCategory.Plus.Q.map (l Y)) := plusQ_isIso (l Y)
  -- The left half of the span: `G(Y) ⟶ Tot(G(I^•)) ⟵ F(I^•)`, both legs quasi-isomorphisms.
  let s₁ (Y : A) := spanIso (DerivedCategory.Q.map (aL Y)) (DerivedCategory.Q.map (aR Y))
  -- The right half: `F(I^•) ⟶ RF(I^•) ⟵ RF(Y[0])`, the first leg because `I^•` is a bounded
  -- below complex of injectives and the second because `Y[0] ⟶ I^•` is a quasi-isomorphism.
  let s₂ (Y : A) := spanIso
    (DerivedCategory.Plus.ι.map ((derivedUnit F RF α).app (K Y)))
    (DerivedCategory.Plus.ι.map (RF.map (DerivedCategory.Plus.Q.map (l Y))))
  refine NatIso.ofComponents (fun Y ↦ s₁ Y ≪≫ s₂ Y) ?_
  intro Y Z f
  let g : K Y ⟶ K Z := resolutionMap (I Y) (I Z) f
  have comm : (l Y).hom ≫ g.hom = (single A (ComplexShape.up ℤ) 0).map f ≫ (l Z).hom :=
    resolutionMap_comm (I Y) (I Z) f
  have haL' := congrArg DerivedCategory.Q.map
    (leftTotal_naturality G (l Y).hom (l Z).hom f g.hom comm : G.map f ≫ aL Z = aL Y ≫ _)
  have haR' := congrArg DerivedCategory.Q.map (rightTotal_naturality G F η g.hom :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map g.hom ≫ aR Z = aR Y ≫ _)
  simp only [Functor.map_comp] at haL' haR'
  have hu' := congrArg DerivedCategory.Plus.ι.map ((derivedUnit F RF α).naturality g)
  simp only [Functor.map_comp, Functor.comp_map] at hu'
  have huQ : DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g.hom) ≫
        DerivedCategory.Plus.ι.map ((derivedUnit F RF α).app (K Z)) =
      DerivedCategory.Plus.ι.map ((derivedUnit F RF α).app (K Y)) ≫
        DerivedCategory.Plus.ι.map (RF.map (DerivedCategory.Plus.Q.map g)) := hu'
  have hl := congrArg (fun t ↦ DerivedCategory.Plus.ι.map (RF.map (DerivedCategory.Plus.Q.map t)))
    (ObjectProperty.hom_ext _ comm : l Y ≫ g = (singlePlus A).map f ≫ l Z)
  simp only [Functor.map_comp] at hl
  have he₁ := spanIso_naturality _ _ _ _ _ _ _ haL' haR'
  have he₂ := spanIso_naturality
    (DerivedCategory.Plus.ι.map ((derivedUnit F RF α).app (K Y)))
    (DerivedCategory.Plus.ι.map (RF.map (DerivedCategory.Plus.Q.map (l Y))))
    (DerivedCategory.Plus.ι.map ((derivedUnit F RF α).app (K Z)))
    (DerivedCategory.Plus.ι.map (RF.map (DerivedCategory.Plus.Q.map (l Z)))) _ _ _ huQ hl.symm
  exact ((CommSq.mk he₁).vert_comp (CommSq.mk he₂)).w

end Comparison

/-! ### The augmentation of the Čech complex -/

section Augmentation

variable {B : Type*} [Category* B] [Abelian B]

open HomologicalComplex

/-- The augmentation `H⁰(K)[0] ⟶ K` of a cochain complex graded by `ℕ`. -/
private def homologyZeroι (K : CochainComplex B ℕ) :
    (CochainComplex.single₀ B).obj (K.homology 0) ⟶ K :=
  (K.fromSingle₀Equiv _).symm ⟨K.isoHomologyπ₀.inv ≫ K.iCycles 0, by simp⟩

/-- The degree-zero component of `homologyZeroι`. -/
private lemma homologyZeroι_f (K : CochainComplex B ℕ) :
    (homologyZeroι K).f 0 = K.isoHomologyπ₀.inv ≫ K.iCycles 0 := by
  simp [homologyZeroι]

/-- `homologyZeroι` is natural in the complex. -/
private lemma homologyZeroι_naturality {K L : CochainComplex B ℕ} (f : K ⟶ L) :
    (CochainComplex.single₀ B).map (homologyMap f 0) ≫ homologyZeroι L = homologyZeroι K ≫ f := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [comp_f, CochainComplex.single₀_map_f_zero, homologyZeroι_f]
  -- The source of the degree-zero component is `((single _ 0).obj (H⁰ K)).X 0`, which is the
  -- honest `H⁰ K` only after unfolding `single`; `rw` sees that at default transparency only.
  rw (transparency := .default) [← Category.assoc, K.isoHomologyπ₀_inv_naturality f,
    Category.assoc, cyclesMap_i, Category.assoc]

/-- `homologyZeroι` is a quasi-isomorphism when the complex has no homology in positive
degrees. -/
private lemma homologyZeroι_quasiIso (K : CochainComplex B ℕ)
    (hK : ∀ n, 0 < n → IsZero (K.homology n)) : QuasiIso (homologyZeroι K) := by
  rw [quasiIso_iff]
  intro n
  by_cases hn : n = 0
  · subst n
    have hs : IsIso (iCycles ((CochainComplex.single₀ B).obj (K.homology 0)) 0) :=
      isIso_iCycles _ 0 1 (by simp) (single_obj_d _ _ _ _ _)
    have hc : cyclesMap (homologyZeroι K) 0 =
        iCycles ((CochainComplex.single₀ B).obj (K.homology 0)) 0 ≫ K.isoHomologyπ₀.inv := by
      apply (cancel_mono (K.iCycles 0)).mp
      rw (transparency := .default) [cyclesMap_i, homologyZeroι_f]
      exact (Category.assoc _ _ _).symm
    have h1 : IsIso (cyclesMap (homologyZeroι K) 0) := by
      rw [hc]
      exact IsIso.comp_isIso' hs (Iso.isIso_inv _)
    have h2 : IsIso (homologyπ ((CochainComplex.single₀ B).obj (K.homology 0)) 0 ≫
        homologyMap (homologyZeroι K) 0) := by
      rw [homologyπ_naturality]
      infer_instance
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsIso.of_isIso_comp_left
      (homologyπ ((CochainComplex.single₀ B).obj (K.homology 0)) 0) _
  · rw [quasiIsoAt_iff_exactAt _ n (ExactAt.of_isZero (isZero_single_obj_X _ _ _ n hn))]
    exact (K.exactAt_iff_isZero_homology n).2 (hK n (by omega))

/-- The `ℤ`-graded single complex is the extension by zero of the `ℕ`-graded one, naturally in
the object. -/
private def singleIsoExtendSingle (B : Type*) [Category* B] [Abelian B] :
    single B (ComplexShape.up ℤ) 0 ≅
      CochainComplex.single₀ B ⋙ ComplexShape.embeddingUpNat.extendFunctor B :=
  NatIso.ofComponents
    (fun W ↦
      (extendSingleIso ComplexShape.embeddingUpNat W 0 0 ComplexShape.embeddingUpNat_f_zero).symm)
    (fun f ↦ extendSingle_naturality (A := B) f)

/-- The augmentation `H⁰(K)[0] ⟶ K`, with both sides graded by `ℤ`. -/
private def homologyZeroExtendedι (K : CochainComplex B ℕ) :
    (single B (ComplexShape.up ℤ) 0).obj (K.homology 0) ⟶
      K.extend ComplexShape.embeddingUpNat :=
  (singleIsoExtendSingle B).hom.app (K.homology 0) ≫
    extendMap (homologyZeroι K) ComplexShape.embeddingUpNat

/-- `homologyZeroExtendedι` is natural in the complex. -/
private lemma homologyZeroExtendedι_naturality {K L : CochainComplex B ℕ} (f : K ⟶ L) :
    (single B (ComplexShape.up ℤ) 0).map (homologyMap f 0) ≫ homologyZeroExtendedι L =
      homologyZeroExtendedι K ≫ extendMap f ComplexShape.embeddingUpNat := by
  dsimp only [homologyZeroExtendedι]
  rw (transparency := .default) [← Category.assoc,
    (singleIsoExtendSingle B).hom.naturality (homologyMap f 0), Category.assoc,
    ← extendMap_comp, homologyZeroι_naturality, extendMap_comp]
  exact (Category.assoc _ _ _).symm

/-- `homologyZeroExtendedι` is a quasi-isomorphism when the complex has no homology in positive
degrees. -/
private lemma homologyZeroExtendedι_quasiIso (K : CochainComplex B ℕ)
    (hK : ∀ n, 0 < n → IsZero (K.homology n)) : QuasiIso (homologyZeroExtendedι K) := by
  have h0 := homologyZeroι_quasiIso K hK
  have h1 : QuasiIso (extendMap (homologyZeroι K) ComplexShape.embeddingUpNat) := inferInstance
  have h2 : QuasiIso ((singleIsoExtendSingle B).hom.app (K.homology 0)) :=
    quasiIso_of_isIso _
  dsimp only [homologyZeroExtendedι]
  exact quasiIso_comp _ _ (hφ := h2) (hφ' := h1)

end Augmentation

/-! ### The functorial quasi-isomorphism of Stacks 03AU -/

section CechComparison

open HomologicalComplex

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The Čech complex of an abelian presheaf, as a complex graded by `ℤ`. -/
private abbrev cechZFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}) ⥤ CochainComplex AddCommGrpCat.{max u v w a} ℤ :=
  cechComplexPlusFunctor E ⋙ CochainComplex.Plus.ι _

/-- The augmentation `Ȟ⁰(E, F)[0] ⟶ Č^•(E, F)` of the Čech complex, natural in `F`. -/
private def cechAugmentation :
    cechH0Functor.{w, v, a, u} E ⋙ single AddCommGrpCat.{max u v w a} (ComplexShape.up ℤ) 0 ⟶
      cechZFunctor.{w, v, a, u} E :=
  let Kf := cechComplexFunctor (A := AddCommGrpCat.{max u v w a}) E
  let ι : (Kf ⋙ homologyFunctor _ (ComplexShape.up ℕ) 0) ⋙
      single _ (ComplexShape.up ℤ) 0 ⟶ cechZFunctor.{w, v, a, u} E :=
    { app F := homologyZeroExtendedι (Kf.obj F)
      naturality _ _ f := homologyZeroExtendedι_naturality (Kf.map f) }
  Functor.whiskerRight
    (eqToHom ((cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).2 0))
    (single _ (ComplexShape.up ℤ) 0) ≫ ι

/-- The augmentation of the Čech complex is a quasi-isomorphism at an injective abelian
presheaf: by Stacks 03OR the higher Čech cohomology of such a presheaf vanishes. -/
private lemma cechAugmentation_quasiIso (I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}) [Injective I] :
    QuasiIso ((cechAugmentation.{w, v, a, u} E).app I) := by
  have h1 := homologyZeroExtendedι_quasiIso
    ((cechComplexFunctor (A := AddCommGrpCat.{max u v w a}) E).obj I)
    (fun n hn ↦ injective_presheaf_cechCohomology_isZero.{w, v, u, a} E I n hn)
  have h2 : QuasiIso ((single AddCommGrpCat.{max u v w a} (ComplexShape.up ℤ) 0).map
      ((eqToHom ((cechCohomologyDeltaFunctor.{w, v, max u v a, u} E).2 0)).app I)) :=
    quasiIso_of_isIso _
  dsimp [cechAugmentation]
  exact quasiIso_comp _ _ (hφ := h2) (hφ' := h1)

/-- The Čech complex functor, read in `ℤ`-graded complexes, is exact: this is Stacks 03AQ,
transported along the fully faithful extension by zero. -/
private lemma cechZFunctor_exact :
    PreservesFiniteLimits (cechZFunctor.{w, v, a, u} E) ∧
      PreservesFiniteColimits (cechZFunctor.{w, v, a, u} E) := by
  obtain ⟨_, _⟩ := (exactFunctor_iff _).1 (cechComplexPlusFunctor_exact.{w, v, u, max u v a} E)
  have : (CochainComplex.plus AddCommGrpCat.{max u v w a}).IsClosedUnderFiniteLimits :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : (CochainComplex.plus AddCommGrpCat.{max u v w a}).IsClosedUnderFiniteColimits :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  constructor <;> dsimp [cechZFunctor] <;> infer_instance

/-- The Čech complex functor, read in `ℤ`-graded complexes, is additive. -/
private lemma cechZFunctor_additive : (cechZFunctor.{w, v, a, u} E).Additive :=
  (exactFunctor_le_additiveFunctor _ _) _ (cechZFunctor_exact.{w, v, a, u} E)

set_option synthInstance.maxHeartbeats 400000 in
-- the closing `infer_instance` searches for `PreservesHomology` of the Čech complex functor
/-- The Čech complex functor, read in `ℤ`-graded complexes, preserves homology. -/
private lemma cechZFunctor_preservesHomology [(cechZFunctor.{w, v, a, u} E).Additive] :
    (cechZFunctor.{w, v, a, u} E).PreservesHomology := by
  obtain ⟨_, _⟩ := cechZFunctor_exact.{w, v, a, u} E
  infer_instance

/-- **Stacks Project, Tag 03AU**, the functorial quasi-isomorphism. For any right derived
functor `RȞ⁰(E, -) : D⁺(PAb(C)) ⥤ D⁺(Ab)` of degree-zero Čech cohomology, the Čech complex is
isomorphic, functorially in the abelian presheaf, to `RȞ⁰(E, -)` applied to the presheaf placed
in degree zero.

The isomorphism is the span of [Stacks, Tag 03AU]: for an injective resolution `F → I^•`, both
`Č^•(E, F) ⟶ Tot(Č^•(E, I^•))` and `Ȟ⁰(E, I^•) ⟶ Tot(Č^•(E, I^•))` are quasi-isomorphisms,
the first because the Čech complex functor is exact (Stacks 03AQ) and the second because the
higher Čech cohomology of an injective presheaf vanishes (Stacks 03OR). -/
@[no_expose,
  stacks 03AU "the functorial quasi-isomorphism",
  sga "7 VI 3.1(b)" "RH^0 = Čech complex"]
def cechComplexIsoRightDerivedFunctor
    (RF : DerivedCategory.Plus (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}) ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w a})
    (α : (cechH0Functor.{w, v, a, u} E).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.Plus.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}))] :
    cechComplexPlusFunctor (A := AddCommGrpCat.{max u v w a}) E ⋙
        DerivedCategory.Plus.Q (C := AddCommGrpCat.{max u v w a}) ≅
      DerivedCategory.Plus.singleFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a}) 0 ⋙ RF := by
  have := enoughInjectives_presheaf.{max w a, u, v} C
  have := cechZFunctor_additive.{w, v, a, u} E
  have := cechZFunctor_preservesHomology.{w, v, a, u} E
  refine (Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι (C := AddCommGrpCat.{max u v w a})))
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v w a})).preimageIso ?_
  exact exactComplexIsoDerived (cechZFunctor.{w, v, a, u} E)
    (fun F ↦ by
      change CochainComplex.IsStrictlyGE
        (((cechComplexFunctor E).obj F).extend ComplexShape.embeddingUpNat) 0
      infer_instance)
    (cechH0Functor.{w, v, a, u} E) (cechAugmentation.{w, v, a, u} E)
    (fun I _ ↦ cechAugmentation_quasiIso.{w, v, a, u} E I) RF α

end CechComparison

end Stacks.CechSite

end
