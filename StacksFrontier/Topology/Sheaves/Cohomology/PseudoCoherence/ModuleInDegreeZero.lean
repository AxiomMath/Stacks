module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationNextCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.CohomologyFiniteness

/-!
# Pseudo-coherence of a sheaf of modules placed in degree zero

Let `F` be a sheaf of `𝒪_X`-modules on a ringed space `X` and let `F[0]` be the object of the
derived category it defines, concentrated in degree zero. Then

* `F[0]` is `0`-pseudo-coherent if and only if `F` is of finite type, and
* `F[0]` is `(-1)`-pseudo-coherent if and only if `F` is finitely presented.

In both cases the forward implication is the finiteness of the top cohomology sheaf of a
pseudo-coherent complex ([Stacks, Tag 08DN]), applied to `F[0]`, whose cohomology is `F` in
degree `0` and zero elsewhere. The converse constructions are explicit: a finite family of local
generating sections gives an epimorphism `𝒪_U^{⊕n} ↠ F|_U`, and `𝒪_U^{⊕n}[0] ⟶ F|_U[0]` is then
a strictly perfect approximation in degrees `≥ 0`; a finite local presentation gives a two-term
complex `𝒪_U^{⊕r} ⟶ 𝒪_U^{⊕n}` in degrees `-1, 0` mapping to `F|_U[0]` by an isomorphism on
cohomology in every degree, hence a strictly perfect approximation in degrees `≥ -1`.

## Main results

In the namespace `AlgebraicGeometry.RingedSpace`:

* `isPseudoCoherentComplexFrom_single_zero_of_isFiniteType`: if `F` is of finite type, then
  `F[0]` is `0`-pseudo-coherent.
* `isPseudoCoherentComplexFrom_single_neg_one_of_isFinitePresentation`: if `F` is finitely
  presented, then `F[0]` is `(-1)`-pseudo-coherent.

## Implementation notes

The two-term complex is Mathlib's `HomologicalComplex.double`, and the comparison with `F|_U[0]`
is `HomologicalComplex.mkHomFromDouble`. That this comparison is an isomorphism on degree-zero
cohomology is `isIso_homologyMap_double`, proved by exhibiting both sides as cokernels: the
degree-zero short complex of the two-term complex has zero differential out of degree zero, so
its homology is the cokernel of its differential in, and the presentation says exactly that this
cokernel is the module.

Approximations are built in two steps. `exists_approximation_of_epi` and
`exists_approximation_of_cokernel` produce an approximation of the degree-zero complex on a
module over the restricted ringed space, with no mention of `restrictComplex`; then
`exists_approximation_restrictComplex` transports it along `restrictComplexSingleIso`. Keeping
the identification of `restrictComplex (F[0]) U` with `(F|_U)[0]` to that one small declaration
is what makes the approximations elaborate: produced inside a single `refine` alongside
metavariables for the ringed space and the index type, that same identification does not.

The local data of finite type and of finite presentation lives on the slice site over the
neighbourhood, while strictly perfect approximations live on the restricted ringed space, so the
generating sections and the presentation are transported along
`AlgebraicGeometry.RingedSpace.PseudoCoherence.sheafOfModulesEquivRestrict`.

## References

* [Stacks Project, Lemma 20.46.13 (09V9)](https://stacks.math.columbia.edu/tag/09V9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

attribute [local instance] AlgebraicGeometry.RingedSpace.overToRestricted_additive
  AlgebraicGeometry.RingedSpace.overToRestricted_isEquivalence

universe v' u'

/-- A map out of a two-term complex in degrees `((up ℤ).prev 0, 0)` is an isomorphism on
degree-zero homology as soon as its target has no differential into or out of degree zero and
the map is, in degree zero, a cokernel of the differential of the two-term complex.

Both homology objects are cokernels: the degree-zero short complex of the two-term complex has
zero differential out of degree zero, so its homology is the cokernel of its differential in,
while the target's vanishing differentials make its degree-zero homology its degree-zero term. -/
theorem isIso_homologyMap_double {C : Type u'} [Category.{v'} C] [Preadditive C]
    [HasZeroObject C] [CategoryWithHomology C]
    {A B M : C} {f : A ⟶ B} {g : B ⟶ M} {hfg : f ≫ g = 0}
    (hc : IsColimit (CokernelCofork.ofπ g hfg))
    (hrel : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev 0) 0)
    (hne : (ComplexShape.up ℤ).prev 0 ≠ 0)
    {L : CochainComplex C ℤ} (α : HomologicalComplex.double f hrel ⟶ L) (e : L.X 0 ≅ M)
    (hLd : L.d ((ComplexShape.up ℤ).prev 0) 0 = 0)
    (hLd' : L.d 0 ((ComplexShape.up ℤ).next 0) = 0)
    (hα : α.f 0 = (HomologicalComplex.doubleXIso₁ f hrel hne).hom ≫ g ≫ e.inv) :
    IsIso (HomologicalComplex.homologyMap α 0) := by
  have hnxt : (ComplexShape.up ℤ).next 0 ≠ 0 := by rw [CochainComplex.next]; omega
  have hdiff : (HomologicalComplex.double f hrel).d ((ComplexShape.up ℤ).prev 0) 0 ≫
        (HomologicalComplex.doubleXIso₁ f hrel hne).hom =
      (HomologicalComplex.doubleXIso₀ f hrel).hom ≫ f := by
    rw [HomologicalComplex.double_d f hrel hne, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hiff : ∀ ⦃W : C⦄ (φ : B ⟶ W), f ≫ φ = 0 ↔
      (HomologicalComplex.double f hrel).d ((ComplexShape.up ℤ).prev 0) 0 ≫
        (HomologicalComplex.doubleXIso₁ f hrel hne).hom ≫ φ = 0 := fun ⦃_W⦄ φ => by
    rw [← Category.assoc, hdiff, Category.assoc]
    exact (comp_eq_zero_iff_of_epi (HomologicalComplex.doubleXIso₀ f hrel).hom).symm
  have hc₀ : IsColimit (CokernelCofork.ofπ (f := f) (g ≫ e.inv)
      (by rw [← Category.assoc, hfg, zero_comp])) :=
    IsCokernel.cokernelIso (f := f) (l := g ≫ e.inv) hc e.symm (by simp)
  have hc₁ := CokernelCofork.isColimitOfIsColimitOfIff hc₀
    ((HomologicalComplex.double f hrel).d ((ComplexShape.up ℤ).prev 0) 0)
    (HomologicalComplex.doubleXIso₁ f hrel hne) hiff
  have hc₂ := CokernelCofork.IsColimit.ofId (L.d ((ComplexShape.up ℤ).prev 0) 0) hLd
  have hgD : (HomologicalComplex.double f hrel).d 0 ((ComplexShape.up ℤ).next 0) = 0 :=
    HomologicalComplex.double_d_eq_zero₁ f hrel 0 _ hnxt
  have hcomm : α.f 0 ≫ 𝟙 (L.X 0) =
      ((HomologicalComplex.doubleXIso₁ f hrel hne).hom ≫ g ≫ e.inv) ≫ 𝟙 (L.X 0) := by
    rw [hα]
  let γ := ShortComplex.HomologyMapData.ofIsColimitCokernelCofork
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map α)
    hgD _ hc₁ hLd' _ hc₂ (𝟙 (L.X 0)) hcomm
  show IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) 0).map α))
  rw [γ.left.homologyMap_eq]
  have : IsIso γ.left.φH := by
    show IsIso (𝟙 (L.X 0))
    infer_instance
  infer_instance

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- The identification of modules on the slice site over `U` with modules on the restricted
space `X|_U` sends the structure sheaf to the structure sheaf. This is the form the transport
of generating sections and of presentations along that identification asks for. -/
def overEquivRestrictedFunctorUnitIso (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.unit (structureSheafOfRings (X.restrict U.isOpenEmbedding)) ≅
      (PseudoCoherence.sheafOfModulesEquivRestrict X U).functor.obj
        (SheafOfModules.unit ((structureSheafOfRings X).over U)) :=
  Iso.refl _

/-- Restricting to an open subspace the complex concentrated in degree zero on a module gives
the complex concentrated in degree zero on the restricted module. -/
def restrictComplexSingleIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (F : OXMod.{u, u} X) :
    (CochainComplex.singleFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj
        ((restrictModules X U).obj F) ≅
      restrictComplex ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F) U :=
  ((HomologicalComplex.singleMapHomologicalComplex (restrictModules X U)
    (ComplexShape.up ℤ) 0).app F).symm

/-- A free sheaf of `𝒪_X`-modules on a finite index type is a direct summand of a finite free
module: it is isomorphic to `𝒪_X^{⊕ n}` for `n` the cardinality of the index type. -/
theorem isDirectSummandOfFiniteFree_free (X : RingedSpace.{u, u}) (I : Type u) [Finite I] :
    IsDirectSummandOfFiniteFree
      (SheafOfModules.free (R := structureSheafOfRings X) I) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  refine (isDirectSummandOfFiniteFree_iff_retract _).mpr
    ⟨Fintype.card I, ⟨Iso.retract (Iso.trans ?_
      (AlgebraicGeometry.RingedSpace.finiteFreeIsoFree X _).symm)⟩⟩
  exact (SheafOfModules.freeFunctor (R := structureSheafOfRings X)).mapIso
    (Equiv.toIso ((Fintype.equivFin I).trans Equiv.ulift.symm))

/-- A complex of `𝒪_X`-modules that is zero outside a finite set of degrees and a direct summand
of a finite free module inside it is strictly perfect. -/
private theorem isStrictlyPerfect_of_isZero_X {Y : RingedSpace.{u, u}}
    {K : CochainComplex (OXMod.{u, u} Y) ℤ} {S : Set ℤ} (hS : S.Finite)
    (hz : ∀ j ∉ S, IsZero (K.X j)) (hd : ∀ j ∈ S, IsDirectSummandOfFiniteFree (K.X j)) :
    IsStrictlyPerfect K where
  bounded := hS.subset fun j hj => by_contra fun h => hj (hz j h)
  directSummand j := by
    by_cases h : j ∈ S
    · exact hd j h
    · exact isDirectSummandOfFiniteFree_of_isZero (hz j h)

/-- A single-degree complex on a direct summand of a finite free `𝒪_X`-module is strictly
perfect. -/
theorem isStrictlyPerfect_single {Y : RingedSpace.{u, u}} {M : OXMod.{u, u} Y}
    (hM : IsDirectSummandOfFiniteFree M) (n : ℤ) :
    IsStrictlyPerfect ((CochainComplex.singleFunctor (OXMod.{u, u} Y) n).obj M) :=
  isStrictlyPerfect_of_isZero_X (Set.finite_singleton n)
    (fun i hi => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n M i hi)
    fun i hi => by
      subst hi
      exact isDirectSummandOfFiniteFree_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i M) hM

/-- A single-degree complex on an epimorphism is an epimorphism on cohomology in that degree. -/
theorem epi_homologyMap_singleFunctor_map {C : Type*} [Category* C] [Abelian C]
    {A B : C} (f : A ⟶ B) [Epi f] :
    Epi (HomologicalComplex.homologyMap
      ((CochainComplex.singleFunctor C 0).map f) 0) := by
  refine (epi_comp_iff_of_isIso _
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 B).hom).mp ?_
  show Epi (HomologicalComplex.homologyMap
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f) 0 ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 B).hom)
  rw [HomologicalComplex.singleObjHomologySelfIso_hom_naturality]
  infer_instance

/-- An epimorphism from a free module on a finite index type makes the complex concentrated in
degree zero on the free module a strictly perfect approximation in degrees `≥ 0`. -/
theorem exists_approximation_of_epi {Y : RingedSpace.{u, u}} {I : Type u} [Finite I]
    {N : OXMod.{u, u} Y}
    (g : SheafOfModules.free (R := structureSheafOfRings Y) I ⟶ N) [Epi g] :
    ∃ P : CochainComplex (OXMod.{u, u} Y) ℤ, IsStrictlyPerfect P ∧
      ∃ α : P ⟶ (CochainComplex.singleFunctor (OXMod.{u, u} Y) 0).obj N,
        (∀ j : ℤ, 0 < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α 0) := by
  refine ⟨(CochainComplex.singleFunctor (OXMod.{u, u} Y) 0).obj
      (SheafOfModules.free (R := structureSheafOfRings Y) I),
    isStrictlyPerfect_single (isDirectSummandOfFiniteFree_free Y I) 0,
    (CochainComplex.singleFunctor (OXMod.{u, u} Y) 0).map g, fun j hj => ?_,
    epi_homologyMap_singleFunctor_map g⟩
  refine IsZero.isIso ?_ ?_ _
  · exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ j (by omega)
  · exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 N j (by omega)

/-- A presentation of a sheaf of modules as the cokernel of a map between free modules on finite
index types makes the two-term complex it defines a strictly perfect approximation of the
complex concentrated in degree zero, in degrees `≥ -1`. -/
theorem exists_approximation_of_cokernel {Y : RingedSpace.{u, u}} {I J : Type u}
    [Finite I] [Finite J] {N : OXMod.{u, u} Y}
    {f : SheafOfModules.free (R := structureSheafOfRings Y) I ⟶
      SheafOfModules.free (R := structureSheafOfRings Y) J}
    {g : SheafOfModules.free (R := structureSheafOfRings Y) J ⟶ N} {hfg : f ≫ g = 0}
    (hc : IsColimit (CokernelCofork.ofπ g hfg)) :
    ∃ P : CochainComplex (OXMod.{u, u} Y) ℤ, IsStrictlyPerfect P ∧
      ∃ α : P ⟶ (CochainComplex.singleFunctor (OXMod.{u, u} Y) 0).obj N,
        (∀ j : ℤ, -1 < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α (-1)) := by
  have hrel : (ComplexShape.up ℤ).Rel ((ComplexShape.up ℤ).prev 0) 0 := by
    rw [CochainComplex.prev]; simp [ComplexShape.up]
  have hne : (ComplexShape.up ℤ).prev 0 ≠ 0 := by rw [CochainComplex.prev]; omega
  have hstrict : IsStrictlyPerfect (HomologicalComplex.double f hrel) := by
    refine isStrictlyPerfect_of_isZero_X
      ((Set.finite_singleton ((ComplexShape.up ℤ).prev 0)).union (Set.finite_singleton 0))
      (fun j hj => HomologicalComplex.isZero_double_X f hrel j (fun h => hj (.inl h))
        fun h => hj (.inr h))
      fun j hj => ?_
    rcases hj with rfl | rfl
    · exact isDirectSummandOfFiniteFree_of_iso (HomologicalComplex.doubleXIso₀ f hrel)
        (isDirectSummandOfFiniteFree_free Y I)
    · exact isDirectSummandOfFiniteFree_of_iso (HomologicalComplex.doubleXIso₁ f hrel hne)
        (isDirectSummandOfFiniteFree_free Y J)
  obtain ⟨α, hαf⟩ : ∃ α : HomologicalComplex.double f hrel ⟶
      (CochainComplex.singleFunctor (OXMod.{u, u} Y) 0).obj N,
      α.f 0 = (HomologicalComplex.doubleXIso₁ f hrel hne).hom ≫ g ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv :=
    ⟨HomologicalComplex.mkHomFromDouble hrel hne 0
        (g ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).inv)
        (by rw [zero_comp, ← Category.assoc, hfg, zero_comp]) (fun k _ => by simp),
      by rw [HomologicalComplex.mkHomFromDouble_f₁]⟩
  have hα0 : IsIso (HomologicalComplex.homologyMap α 0) :=
    isIso_homologyMap_double hc hrel hne α
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N) (by simp) (by simp) hαf
  refine ⟨HomologicalComplex.double f hrel, hstrict, α, fun j hj => ?_, ?_⟩
  · by_cases hj0 : j = 0
    · subst hj0
      exact hα0
    · refine IsZero.isIso ?_ ?_ _
      · refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
        simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂] using
          HomologicalComplex.isZero_double_X f hrel j
            (by rw [CochainComplex.prev]; omega) hj0
      · exact HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 N j hj0
  · exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 N (-1)
      (by omega)).epi _

/-- Transport a strictly perfect approximation of the complex concentrated in degree zero on
`F|_U` into one of the restriction to `U` of the complex concentrated in degree zero on `F`. -/
theorem exists_approximation_restrictComplex (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (F : OXMod.{u, u} X) (m : ℤ)
    (h : ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧
      ∃ α : P ⟶ (CochainComplex.singleFunctor
          (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) 0).obj ((restrictModules X U).obj F),
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m)) :
    ∃ P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ,
      IsStrictlyPerfect P ∧
      ∃ α : P ⟶ restrictComplex ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F) U,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m) := by
  obtain ⟨P, hP, α, h₁, h₂⟩ := h
  refine ⟨P, hP, α ≫ (restrictComplexSingleIso X U F).hom, fun j hj => ?_, ?_⟩
  · rw [HomologicalComplex.homologyMap_comp]
    have := h₁ j hj
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    exact (epi_comp_iff_of_isIso _ _).2 h₂

/-- The complex concentrated in degree zero on a sheaf of modules of finite type is
`0`-pseudo-coherent. -/
theorem isPseudoCoherentComplexFrom_single_zero_of_isFiniteType (F : OXMod.{u, u} X)
    (hF : F.IsFiniteType) :
    IsPseudoCoherentComplexFrom
      ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F) 0 := by
  classical
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (self := hF) F
  intro x
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff X.carrier σ.X).mp σ.coversTop).exists_mem x
  have := hσ.isFiniteType i
  obtain ⟨s, hs⟩ : ∃ s : ((restrictModules X (σ.X i)).obj F).GeneratingSections, Finite s.I :=
    ⟨(σ.generators i).map (PseudoCoherence.sheafOfModulesEquivRestrict X (σ.X i)).functor
      (overEquivRestrictedFunctorUnitIso X (σ.X i)), inferInstance⟩
  exact ⟨σ.X i, hxi, exists_approximation_restrictComplex X (σ.X i) F 0
    (exists_approximation_of_epi s.π)⟩

/-- The complex concentrated in degree zero on a finitely presented sheaf of modules is
`(-1)`-pseudo-coherent. -/
@[sga "6 I 2.9" "(i)⇒(ii)"]
theorem isPseudoCoherentComplexFrom_single_neg_one_of_isFinitePresentation
    (F : OXMod.{u, u} X) (hF : F.IsFinitePresentation) :
    IsPseudoCoherentComplexFrom
      ((CochainComplex.singleFunctor (OXMod.{u, u} X) 0).obj F) (-1) := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData (self := hF) F
  intro x
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff X.carrier q.X).mp q.coversTop).exists_mem x
  have hfin := hq.isFinite_presentation i
  obtain ⟨P, hPgen, hPrel⟩ : ∃ P : ((restrictModules X (q.X i)).obj F).Presentation,
      Finite P.generators.I ∧ Finite P.relations.I :=
    ⟨(q.presentation i).map (PseudoCoherence.sheafOfModulesEquivRestrict X (q.X i)).functor
      (overEquivRestrictedFunctorUnitIso X (q.X i)),
      hfin.isFiniteType_generators.finite, hfin.isFiniteType_relations.finite⟩
  exact ⟨q.X i, hxi, exists_approximation_restrictComplex X (q.X i) F (-1)
    (exists_approximation_of_cokernel P.isColimit)⟩

end AlgebraicGeometry.RingedSpace

end
