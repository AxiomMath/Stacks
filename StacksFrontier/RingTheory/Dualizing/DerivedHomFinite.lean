module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Derived Hom out of a ring map and finite injective dimension

Let `f : A →+* B` be a homomorphism of rings. Coextension of scalars `Hom_A(B, -)` is right
adjoint to the exact functor of restriction of scalars, so it carries injective `A`-modules to
injective `B`-modules; applied degreewise it therefore carries a bounded complex of injective
`A`-modules to a bounded complex of injective `B`-modules, in the same degrees. Since a bounded
complex of injectives is K-injective, it computes any right derived functor of coextension of
scalars. Together these say that `RHom_A(B, -)` does not increase injective amplitude: if `K`
has injective amplitude in `[a, b]` over `A`, then `RHom_A(B, K)` has injective amplitude in
`[a, b]` over `B`.

This is the first of the three conditions in the definition of a dualizing complex (Tag 0A7B),
and hence the first third of Tag 0AX0, which says that for a finite map of Noetherian rings
`RHom_A(B, ω)` is dualizing over `B` when `ω` is dualizing over `A`. Nothing here needs `A` or
`B` Noetherian, nor `f` finite: finiteness only enters in the two remaining conditions, through
the coherence of `Ext^i_A(B, ω)` and through biduality.

## Main results

* `Dualizing.injective_coextendScalars_obj` — Tag 08XR: coextension of scalars carries injective
  modules to injective modules.
* `Dualizing.rightDerivedCoextendObjIso` — a K-injective complex computes any right derived
  functor of coextension of scalars: `RF(Q I) ≅ Q(Hom_A(B, I))`.
* `Dualizing.hasInjectiveAmplitude_obj` and `Dualizing.hasFiniteInjectiveDimension_obj` — such a
  right derived functor preserves injective amplitude and finite injective dimension.
* `Dualizing.hasFiniteInjectiveDimension_derivedHom_obj` — the same statement for the canonical
  derived functor `Dualizing.derivedHom`.
* `Dualizing.isBounded_of_hasFiniteInjectiveDimension` — an object of finite injective dimension
  is cohomologically bounded.
* `Dualizing.derivedCategoryBPlus_of_isDualizingComplex` — a dualizing complex lies in
  `D⁺_Coh(A)`.

## Implementation notes

The hypotheses on the derived functor are those of Tag 0A72: an arbitrary functor `RF` on
derived categories together with a natural transformation `α` exhibiting it as a right derived
functor of coextension of scalars. Stating the results this way means they apply to the
canonical functor `Dualizing.derivedHom` of Tag 0A70 — which is spelled out in
`hasFiniteInjectiveDimension_derivedHom_obj` — without the proofs depending on how that functor
was constructed.

## References

* [Stacks Project, Tag 08XR](https://stacks.math.columbia.edu/tag/08XR)
* [Stacks Project, Tag 070Y](https://stacks.math.columbia.edu/tag/070Y)
* [Stacks Project, Tag 0A5S](https://stacks.math.columbia.edu/tag/0A5S)
* [Stacks Project, Tag 0AX0](https://stacks.math.columbia.edu/tag/0AX0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### Coextension of scalars and injectives -/

section Coextend

variable {A B : Type u} [Ring A] [Ring B]

/-- **Stacks 08XR.** For a ring map `f : A →+* B` and an injective `A`-module `M`, the
`B`-module `Hom_A(B, M)` is injective. Indeed coextension of scalars is right adjoint to
restriction of scalars, which is exact and in particular preserves monomorphisms. -/
@[stacks 08XR]
theorem injective_coextendScalars_obj (f : A →+* B) (M : ModuleCat.{max v u} A) [Injective M] :
    Injective ((ModuleCat.coextendScalars.{u, u, max v u} f).obj M) :=
  (ModuleCat.restrictCoextendScalarsAdj.{v, u, u} f).map_injective M inferInstance

/-- Degreewise coextension of scalars carries a complex of injective `A`-modules to a complex
of injective `B`-modules. -/
theorem injective_coextendComplex_obj_X (f : A →+* B)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (hI : ∀ i, Injective (I.X i)) (i : ℤ) :
    Injective (((coextendComplex.{u, u, v} f).obj I).X i) := by
  have := hI i
  exact injective_coextendScalars_obj f (I.X i)

/-- Degreewise coextension of scalars does not lower the bottom degree of a complex: it is an
additive functor, so it preserves the vanishing of the terms below that degree. -/
theorem isStrictlyGE_coextendComplex_obj (f : A →+* B)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ) [I.IsStrictlyGE n] :
    ((coextendComplex.{u, u, v} f).obj I).IsStrictlyGE n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (ModuleCat.coextendScalars.{u, u, max v u} f).map_isZero
    (I.isZero_of_isStrictlyGE n i hi)

/-- Degreewise coextension of scalars does not raise the top degree of a complex. -/
theorem isStrictlyLE_coextendComplex_obj (f : A →+* B)
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (n : ℤ) [I.IsStrictlyLE n] :
    ((coextendComplex.{u, u, v} f).obj I).IsStrictlyLE n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (ModuleCat.coextendScalars.{u, u, max v u} f).map_isZero
    (I.isZero_of_isStrictlyLE n i hi)

end Coextend

/-! ### Cohomological boundedness from finite injective dimension -/

section Bounded

open StacksDraft.InjectiveDimension

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- The cohomology of `Q I` vanishes in degree `n` if the term `I.X n` is zero. -/
private theorem isZero_homologyFunctor_obj_q_obj_of_isZero_X (I : CochainComplex C ℤ) (n : ℤ)
    (h : IsZero (I.X n)) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj (DerivedCategory.Q.obj I)) := by
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors C n).app I)
  change IsZero (I.homology n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ h

/-- The cohomology of `Q I` vanishes in the degrees where `I` itself vanishes. -/
theorem isZero_homologyFunctor_obj_q_obj_of_isStrictlyGE (I : CochainComplex C ℤ) (a n : ℤ)
    [I.IsStrictlyGE a] (h : n < a) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj (DerivedCategory.Q.obj I)) :=
  isZero_homologyFunctor_obj_q_obj_of_isZero_X I n (I.isZero_of_isStrictlyGE a n h)

/-- The cohomology of `Q I` vanishes in the degrees where `I` itself vanishes. -/
theorem isZero_homologyFunctor_obj_q_obj_of_isStrictlyLE (I : CochainComplex C ℤ) (b n : ℤ)
    [I.IsStrictlyLE b] (h : b < n) :
    IsZero ((DerivedCategory.homologyFunctor C n).obj (DerivedCategory.Q.obj I)) :=
  isZero_homologyFunctor_obj_q_obj_of_isZero_X I n (I.isZero_of_isStrictlyLE b n h)

/-- An object with injective amplitude in `[a, b]` is cohomologically bounded. -/
theorem isBounded_of_hasInjectiveAmplitude {K : DerivedCategory C} {a b : ℤ}
    (hK : HasInjectiveAmplitude K a b) : DerivedCategoryB.IsBounded K := by
  obtain ⟨I, hGE, hLE, -, ⟨e⟩⟩ := hK
  have := hGE
  have := hLE
  refine DerivedCategoryB.isBounded_of_iso e.symm ⟨⟨a, fun n hn => ?_⟩, ⟨b, fun n hn => ?_⟩⟩
  · exact isZero_homologyFunctor_obj_q_obj_of_isStrictlyGE I a n hn
  · exact isZero_homologyFunctor_obj_q_obj_of_isStrictlyLE I b n hn

/-- An object of finite injective dimension is cohomologically bounded. -/
theorem isBounded_of_hasFiniteInjectiveDimension {K : DerivedCategory C}
    (hK : HasFiniteInjectiveDimension K) : DerivedCategoryB.IsBounded K :=
  let ⟨_, _, hK⟩ := hK
  isBounded_of_hasInjectiveAmplitude hK

end Bounded

/-- A dualizing complex over a Noetherian ring lies in `D⁺_Coh(A)`: it is cohomologically
bounded below by finite injective dimension, and its cohomology modules are finite by
definition. This is the hypothesis under which Tag 0A72 applies to it. -/
theorem derivedCategoryBPlus_of_isDualizingComplex {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{max v u} A)} (hK : IsDualizingComplex K) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} A ↦ Module.Finite A M) K :=
  ⟨(isBounded_of_hasFiniteInjectiveDimension hK.finiteInjectiveDimension).1,
    hK.finiteCohomology⟩

/-! ### Right derived functors of coextension of scalars -/

section RightDerived

open StacksDraft.InjectiveDimension

variable {A B : Type u} [Ring A] [Ring B] (f : A →+* B)
  (RF : DerivedCategory (ModuleCat.{max v u} A) ⥤ DerivedCategory (ModuleCat.{max v u} B))
  (α : (ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))]

/-- **Stacks 070Y** for coextension of scalars: a K-injective complex computes any right
derived functor of coextension of scalars, so the structural map `α` is an isomorphism there. -/
theorem isIso_app_of_isKInjective (I : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (hI : I.IsKInjective) : IsIso (α.app ((HomotopyCategory.quotient _ _).obj I)) := by
  have : EnoughInjectives (ModuleCat.{max v u} A) := ModuleCat.enoughInjectives.{v, u} A
  exact (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (fun L ↦ by
      obtain ⟨J, q, hq, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective L
      exact ⟨J, q, hJ, hq⟩)).2 DerivedCategory.Qh RF α I hI

/-- For a K-injective complex `I` of `A`-modules, the value of a right derived functor of
coextension of scalars at `I` is computed by the complex `Hom_A(B, I)`. -/
noncomputable def rightDerivedCoextendObjIso (I : CochainComplex (ModuleCat.{max v u} A) ℤ)
    (hI : I.IsKInjective) :
    RF.obj (DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj ((coextendComplex.{u, u, v} f).obj I) :=
  have := isIso_app_of_isKInjective f RF α I hI
  RF.mapIso ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).app I).symm ≪≫
    (asIso (α.app ((HomotopyCategory.quotient _ _).obj I))).symm ≪≫
    DerivedCategory.Qh.mapIso
      (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app I) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} B)).app _

include f α in
/-- A right derived functor of coextension of scalars preserves injective amplitude: a bounded
complex of injectives representing `K` is carried, degreewise and in the same degrees, to a
bounded complex of injectives representing `RHom_A(B, K)`. -/
theorem hasInjectiveAmplitude_obj {K : DerivedCategory (ModuleCat.{max v u} A)} {a b : ℤ}
    (hK : HasInjectiveAmplitude K a b) : HasInjectiveAmplitude (RF.obj K) a b := by
  obtain ⟨I, hGE, hLE, hinj, ⟨e⟩⟩ := hK
  have := hGE
  have := hLE
  have := hinj
  exact ⟨(coextendComplex.{u, u, v} f).obj I,
    isStrictlyGE_coextendComplex_obj f I a,
    isStrictlyLE_coextendComplex_obj f I b,
    injective_coextendComplex_obj_X f I hinj,
    ⟨RF.mapIso e ≪≫
      rightDerivedCoextendObjIso f RF α I (CochainComplex.isKInjective_of_injective I a)⟩⟩

include f α in
/-- A right derived functor of coextension of scalars preserves finite injective dimension.
This is the first of the three conditions of Tag 0AX0. -/
theorem hasFiniteInjectiveDimension_obj {K : DerivedCategory (ModuleCat.{max v u} A)}
    (hK : HasFiniteInjectiveDimension K) : HasFiniteInjectiveDimension (RF.obj K) :=
  let ⟨a, b, hK⟩ := hK
  ⟨a, b, hasInjectiveAmplitude_obj f RF α hK⟩

end RightDerived

section DerivedHom

open StacksDraft.InjectiveDimension

variable {A B : Type u} [Ring A] [Ring B]

/-- The canonical derived Hom functor `RHom_A(B, -)` of Tag 0A70 preserves injective amplitude.
-/
theorem hasInjectiveAmplitude_derivedHom_obj (f : A →+* B)
    {K : DerivedCategory (ModuleCat.{max v u} A)} {a b : ℤ}
    (hK : HasInjectiveAmplitude K a b) :
    HasInjectiveAmplitude ((derivedHom.{u, v, u} f).obj K) a b := by
  have := coextendScalars_hasPointwiseRightDerivedFunctor.{u, v, u} f
  exact hasInjectiveAmplitude_obj f _
    (((ModuleCat.coextendScalars.{u, u, max v u} f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ))) hK

/-- **Tag 0AX0, first condition.** The canonical derived Hom functor `RHom_A(B, -)` of Tag 0A70
preserves finite injective dimension; no finiteness or Noetherian hypothesis is needed. -/
theorem hasFiniteInjectiveDimension_derivedHom_obj (f : A →+* B)
    {K : DerivedCategory (ModuleCat.{max v u} A)}
    (hK : HasFiniteInjectiveDimension K) :
    HasFiniteInjectiveDimension ((derivedHom.{u, v, u} f).obj K) :=
  let ⟨a, b, hK⟩ := hK
  ⟨a, b, hasInjectiveAmplitude_derivedHom_obj f hK⟩

end DerivedHom

end Dualizing

end
