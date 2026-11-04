module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveCotangentPresentation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.FibreCriterion
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Openness of versality for a naive obstruction theory

Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in groupoids over the big fppf
site of `S` satisfying (RS*). Let `x` be an object of `𝒳` over `U = Spec A` with `A` of finite
type over a ring `Λ` whose spectrum is an affine open of `S` through which `U → S` factors, and
let `ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)`. Suppose that `ξ` computes the lifting
obstruction and the tangent functor of `x`, and that the cohomology of `E` is finite over `A`.
If `x` is versal at a closed point `u₀` of `U`, then `x` is versal at every finite type point of
some open neighbourhood of `u₀`.

The proof runs through the cone `C` of `ξ`, which sits in a distinguished triangle
`E ⟶ NL_{A/Λ} ⟶ C ⟶ E[1]`. The long exact cohomology sequence of the derived fibre of this
triangle at a point `u` turns the two conditions of the versality criterion — surjectivity of
`H^{-1}(E ⊗^L κ(u)) → H^{-1}(NL_{A/Λ} ⊗^L κ(u))` and injectivity in degree `0` — into the single
condition `H^{-1}(C ⊗^L κ(u)) = 0`. Both `E` and `NL_{A/Λ}` are pseudo-coherent, hence so is `C`,
and the fibrewise splitting criterion [stacks 068U] makes the vanishing of `H^{-1}` of the derived
fibre of a pseudo-coherent complex spread from one point to a standard open neighbourhood.

## Main definitions

* `Deformation.Artin.derivedFibreHomologyMap` — the map induced on the cohomology of the derived
  fibre at a point of `Spec A` by a morphism of `D(A)`.
* `Deformation.Artin.NaiveObstructionAt` — assumptions (1) and (2) of the source at a single
  object: the lifting criterion across every deformation situation, and an isomorphism of
  functors `T_x(−) ⟶ Ext⁰_A(E, −)` carrying the canonical element to the composition
  `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`.
* `Deformation.Artin.NaiveVersalityCriterion` — the cohomological criterion for versality at a
  finite type point.

## Main results

* `Deformation.Artin.isPseudoCoherent_derivedNaiveCotangentComplex` — the naive cotangent complex
  of a finite type algebra over a Noetherian ring is pseudo-coherent.
* `Deformation.Artin.exists_isOpen_isVersalAt_of_naiveObstructionAt` — **Stacks 07YN**: versality
  at a closed point propagates to all finite type points of an open neighbourhood.

## Implementation notes

The source's data — an affine scheme of finite type over `S` mapping into an affine open
`Spec Λ ⊆ S`, together with an object of `𝒳` above it — is `Deformation.Artin.ChartedObject`,
the index of clause (1) of a naive obstruction theory. Assumptions (1) and (2) of the source are
the corresponding fields of `Deformation.Artin.NaiveObstructionTheory` read at that single
object, and are collected in `Deformation.Artin.NaiveObstructionAt`; assumption (3), finiteness
of the cohomology of `E`, is a separate hypothesis because it alone is used directly.

The derived fibre `K ⊗^L_A κ(u)` is the unbounded derived base change of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` along
`A → κ(u)`; this is the same reading of the derived fibre that
`StacksDraft.Perfect.FibreCohomologyVanishes` uses, so the fibrewise splitting criterion applies
to it on the nose.

The source invokes its versality criterion (Stacks 07YM) twice: once at the closed point `u₀`, to
produce the vanishing of `H^{-1}` of the derived fibre of the cone, and once at every finite type
point of the resulting neighbourhood, to deduce versality there. Here that criterion is carried
as the hypothesis `Deformation.Artin.NaiveVersalityCriterion`, which states it in full: granted
assumptions (1) and (2), at a finite type point the two cohomological conditions imply
versality, and at a closed point versality implies them. Everything else in the proof is
discharged here; `Deformation.Artin.isOpenVersalityAt_of_naiveObstructionAt` is the same
statement with the criterion proved.

## References

* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ComplexShape (upIntRelNegOneZero)
open CochainComplex.DerivedExtensionScalars

universe u v w

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-! ### Pseudo-coherence of the naive cotangent complex -/

section PseudoCoherence

/-- A complex of finite modules over a Noetherian ring which vanishes in large degrees is
pseudo-coherent, by the characterization of pseudo-coherence through finite cohomology. -/
private lemma isPseudoCoherent_Q_obj_of_finite_X {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero (K.X i))
    (hfin : ∀ i : ℤ, Module.Finite A (K.X i)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj K) := by
  have hiso (i : ℤ) :
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (DerivedCategory.Q.obj K) ≅
        K.homology i := (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app K
  refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    (DerivedCategory.Q.obj K) 0 A).2.1.mpr ⟨⟨b, fun i hi => ?_⟩, fun i => ?_⟩
  · exact (hiso i).isZero_iff.mpr
      ((HomologicalComplex.ExactAt.of_isZero (hb i hi)).isZero_homology)
  · have := hfin i
    have : Module.Finite A (K.homology i) :=
      StacksDraft.PseudoCoherence.finite_homology_of_finite_X K i
    exact Module.Finite.equiv (hiso i).symm.toLinearEquiv

open NaiveCotangent in
/-- The naive cotangent complex of a finite type algebra over a Noetherian ring is
pseudo-coherent. A finite presentation computes `NL_{A/Λ}` by a two-term complex whose terms
`I/I²` and `Ω_{P/Λ} ⊗_P A` are finite `A`-modules. -/
public theorem isPseudoCoherent_derivedNaiveCotangentComplex (Λ A : Type u) [CommRing Λ]
    [CommRing A] [Algebra Λ A] [IsNoetherianRing Λ] [Algebra.FiniteType Λ A] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (derivedNaiveCotangentComplex Λ A) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing Λ A
  have : Algebra.FinitePresentation Λ A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let G : Algebra.Generators Λ A
      (ULift.{u} (Fin (Algebra.Presentation.ofFinitePresentationVars Λ A))) :=
    (Algebra.Presentation.ofFinitePresentation Λ A).toGenerators.reindex Equiv.ulift
  let T : TwoTerm A := nlRestrict A G
  let d : ModuleCat.of A T.X₁ ⟶ ModuleCat.of A T.X₀ := ModuleCat.ofHom T.d
  have hz : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero ((twoTermComplex T).X i) := fun i h₁ h₀ =>
    HomologicalComplex.isZero_double_X _ upIntRelNegOneZero i h₁ h₀
  have hfin (i : ℤ) : Module.Finite A ((twoTermComplex T).X i) := by
    obtain rfl | h₁ := eq_or_ne i (-1)
    · have : Module.Finite A (ModuleCat.of A T.X₁) :=
        Algebra.Extension.Cotangent.finite G.fg_ker_of_finitePresentation
      exact Module.Finite.equiv
        (HomologicalComplex.doubleXIso₀ d upIntRelNegOneZero).symm.toLinearEquiv
    obtain rfl | h₀ := eq_or_ne i 0
    · have : Module.Finite A (ModuleCat.of A T.X₀) := Module.Finite.of_basis G.cotangentSpaceBasis
      exact Module.Finite.equiv
        (HomologicalComplex.doubleXIso₁ d upIntRelNegOneZero
          NaiveCotangent.TwoTerm.negOne_ne_zero).symm.toLinearEquiv
    have : Subsingleton ((twoTermComplex T).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (hz i h₁ h₀)
    exact Module.Finite.of_finite
  exact (isPseudoCoherent_Q_obj_of_finite_X (twoTermComplex T) 0
    (fun i hi => hz i (by omega) (by omega)) hfin).ofIso
    (derivedNaiveCotangentComplexIso Λ A G (G.defaultHom _))

end PseudoCoherence

/-! ### Spreading out the vanishing of a fibre cohomology module -/

section Spreading

/-- Derived base change along `R → R_f → A` agrees with derived base change along the
composition, on a pseudo-coherent object. -/
private lemma derivedExtension_localization_obj
    {R A : Type u} [CommRing R] [CommRing A] (f : R) (g : Localization.Away f →+* A)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    Nonempty ((totalDerivedExtensionScalars.{u, u, u} g).functor.obj
        ((StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} f).obj K) ≅
      (totalDerivedExtensionScalars.{u, u, u}
        (g.comp (algebraMap R (Localization.Away f)))).functor.obj K) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hP.upperBound
  let F := ModuleCat.extendScalars (algebraMap R (Localization.Away f))
  let PA : CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have (i : ℤ) : Module.Free R (P.X i) := (hP.finiteFree i).2
  have (i : ℤ) : Module.Projective R (P.X i) := inferInstance
  have : ∀ i, Projective (P.X i) := fun i => inferInstance
  have : P.IsStrictlyLE b := hb
  have : PA.IsStrictlyLE b := by
    dsimp only [PA]
    infer_instance
  have : ∀ i, Projective (PA.X i) := fun i => by
    have : Module.Projective (Localization.Away f) (PA.X i) :=
      Module.Projective.of_equiv
        (StacksDraft.PseudoCoherence.extendScalarsTensorIso
          (S := Localization.Away f) (P.X i)).toLinearEquiv.symm
    infer_instance
  let Dg := totalDerivedExtensionScalars.{u, u, u} g
  let Dgf := totalDerivedExtensionScalars.{u, u, u}
    (g.comp (algebraMap R (Localization.Away f)))
  let loc := StacksDraft.PseudoCoherence.localizationAwayFunctorAux.{u, u} f
  have ef : loc.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj PA := by
    have : F.Additive := _root_.extendScalars_additive _
    have : PreservesFiniteLimits F :=
      _root_.extendScalars_preservesFiniteLimits_of_flat' _
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))
    exact F.mapDerivedCategoryFactors.app P
  exact ⟨Dg.functor.mapIso (loc.mapIso e.symm ≪≫ ef) ≪≫
    @asIso _ _ _ _ (Dg.comparison.app PA) (Dg.comparison_isIso_of_projective PA b) ≪≫
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp (algebraMap R (Localization.Away f)) g)
          (ComplexShape.up ℤ)) DerivedCategory.Q).symm.app P ≪≫
    (@asIso _ _ _ _ (Dgf.comparison.app P) (Dgf.comparison_isIso_of_projective P b)).symm ≪≫
      Dgf.functor.mapIso e⟩

/-- If a complex is the direct sum of a part concentrated in degrees `≥ i + 1` represented by a
bounded complex of projectives and a part concentrated in degrees `≤ i - 1`, then the degree-`i`
cohomology of every derived base change of it vanishes. -/
private lemma isZero_derivedExtension_of_split
    {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A)
    (K U L : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) (e : K ≅ U ⊞ L) [L.IsLE (i - 1)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyGE (i + 1)] [P.IsStrictlyLE b] [∀ j, Projective (P.X j)]
    (eP : U ≅ DerivedCategory.Q.obj P) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((totalDerivedExtensionScalars.{u, u, u} g).functor.obj K)) := by
  let D := totalDerivedExtensionScalars.{u, u, u} g
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let PA : CochainComplex (ModuleCat.{u} A) ℤ :=
    ((ModuleCat.extendScalars g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have : D.functor.Additive := D.additive
  have : (D.functor ⋙ H).Additive := inferInstance
  have : (D.functor.obj L).IsLE (i - 1) := D.maps_t_le L (i - 1)
  have hL : IsZero (H.obj (D.functor.obj L)) :=
    DerivedCategory.isZero_of_isLE _ (i - 1) i (by omega)
  have : PA.IsStrictlyGE (i + 1) := by
    dsimp only [PA]
    infer_instance
  have hU : IsZero (H.obj (D.functor.obj U)) :=
    (H.mapIso (D.functor.mapIso eP ≪≫ @asIso _ _ _ _ (D.comparison.app P)
        (D.comparison_isIso_of_projective P b)
      : D.functor.obj U ≅ DerivedCategory.Q.obj PA)).isZero_iff.mpr
      (DerivedCategory.isZero_of_isGE _ (i + 1) i (by omega))
  have hz : IsZero ((D.functor ⋙ H).obj (U ⊞ L)) := by
    rw [IsZero.iff_id_eq_zero, ← (D.functor ⋙ H).map_id, ← biprod.total, Functor.map_add,
      Functor.map_comp, Functor.map_comp, hU.eq_of_tgt ((D.functor ⋙ H).map biprod.fst) 0,
      hL.eq_of_tgt ((D.functor ⋙ H).map biprod.snd) 0]
    simp
  exact hz.of_iso ((D.functor ⋙ H).mapIso e)

/-- **The open form of [stacks 068U].** If the degree-`i` cohomology of the derived fibre of a
pseudo-coherent complex vanishes at a prime `p`, then it vanishes at every prime of a standard
open neighbourhood `D(f)` of `p`. -/
private lemma exists_basicOpen_fibreCohomologyVanishes {R : Type u} [CommRing R] (p : Ideal R)
    [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hp : StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} p K i) :
    ∃ f : R, f ∉ p ∧ ∀ q : PrimeSpectrum R, f ∉ q.asIdeal →
      StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} q.asIdeal K i := by
  obtain ⟨f, hf, _, ⟨P, b, hGE, hLE, _, hProj, ⟨eP⟩, _⟩, e, _, _⟩ :=
    StacksDraft.Perfect.exists_localization_iso_biprod_truncGE_truncLE p K hK i hp
  refine ⟨f, hf, fun q hq => ?_⟩
  have hunit : IsUnit (algebraMap R q.asIdeal.ResidueField f) :=
    isUnit_iff_ne_zero.mpr fun h =>
      hq ((Ideal.algebraMap_residueField_eq_zero (I := q.asIdeal)).mp h)
  let g : Localization.Away f →+* q.asIdeal.ResidueField := IsLocalization.Away.lift f hunit
  have hg : g.comp (algebraMap R (Localization.Away f)) = algebraMap R q.asIdeal.ResidueField :=
    IsLocalization.Away.lift_comp f hunit
  have : P.IsStrictlyGE (i + 1) := hGE
  have : P.IsStrictlyLE b := hLE
  have (j : ℤ) : Module.Projective (Localization.Away f) (P.X j) := hProj j
  have : ∀ j, Projective (P.X j) := fun j => inferInstance
  obtain ⟨ec⟩ := derivedExtension_localization_obj f g K hK
  have hzDirect :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} q.asIdeal.ResidueField)
      i).mapIso ec).isZero_iff.mp (isZero_derivedExtension_of_split g _ _ _ i e P b eP)
  rw [hg] at hzDirect
  exact (StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology
    q.asIdeal K hK i).mpr hzDirect

end Spreading

/-! ### Cohomology of a distinguished triangle -/

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- In a distinguished triangle, if the first morphism is surjective on degree-`i` cohomology and
injective on degree-`i + 1` cohomology, then the degree-`i` cohomology of the third object
vanishes. -/
private lemma isZero_homology_obj₃_of_epi_mono (T : Triangle (DerivedCategory C))
    (hT : T ∈ distinguishedTriangles) (i j : ℤ) (hj : i + 1 = j)
    (hEpi : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁))
    (hMono : Mono ((DerivedCategory.homologyFunctor C j).map T.mor₁)) :
    IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃) := by
  subst hj
  have h₁ : (DerivedCategory.homologyFunctor C i).map T.mor₂ = 0 := by
    apply (cancel_epi ((DerivedCategory.homologyFunctor C i).map T.mor₁)).1
    rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero, comp_zero]
  have h₂ : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 := by
    apply (cancel_mono ((DerivedCategory.homologyFunctor C (i + 1)).map T.mor₁)).1
    rw [DerivedCategory.HomologySequence.δ_comp T hT i (i + 1) rfl, zero_comp]
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_X₂ h₁ h₂

/-- The converse: vanishing of the degree-`i` cohomology of the third object of a distinguished
triangle makes the first morphism surjective in degree `i` and injective in degree `i + 1`. -/
private lemma epi_mono_of_isZero_homology_obj₃ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distinguishedTriangles) (i j : ℤ) (hj : i + 1 = j)
    (hz : IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃)) :
    Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) ∧
      Mono ((DerivedCategory.homologyFunctor C j).map T.mor₁) := by
  subst hj
  exact ⟨(DerivedCategory.HomologySequence.exact₂ T hT i).epi_f (hz.eq_of_tgt _ _),
    (DerivedCategory.HomologySequence.exact₁ T hT i (i + 1) rfl).mono_g (hz.eq_of_src _ _)⟩

end Triangle

/-! ### The derived fibre at a point of an affine scheme -/

/-- The map `H^n(K ⊗^L_A κ(u)) ⟶ H^n(L ⊗^L_A κ(u))` induced on the cohomology of the derived
fibre at a point `u` of `Spec A` by a morphism `K ⟶ L` of `D(A)`. -/
public abbrev derivedFibreHomologyMap {A : Type u} [CommRing A]
    {K L : DerivedCategory (ModuleCat.{u} A)} (ξ : K ⟶ L) (u : Spec (.of A)) (n : ℤ) :=
  letI : u.asIdeal.IsPrime := u.isPrime
  (DerivedCategory.homologyFunctor (ModuleCat.{u} u.asIdeal.ResidueField) n).map
    ((totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A u.asIdeal.ResidueField)).functor.map ξ)

/-! ### Versality at the finite type points of an open neighbourhood -/

section Versality

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {c : AffineChart S}

/-- The object of `𝒳` attached to a charted object lies over `Spec A`, viewed as a scheme over
`S`. -/
public theorem ChartedObject.overScheme_eq (P : ChartedObject B S hS p c) :
    (p ⋙ Over.post B.inclusion).obj P.point = Over.mk P.obj.alg.toScheme :=
  congrArg ((Over.post B.inclusion).obj) P.obj.obj.2

variable (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (P : ChartedObject B S hS p c)
  (hΩ : B.Contains (Spec (squareZeroRing P.ring (differentialsModule c.ring P.ring))))
  (E : DerivedCategory (ModuleCat.{u} P.ring)) (ξ : E ⟶ P.naiveCotangent)

/-- Assumptions (1) and (2) of Stacks 07YN at a single object `x` of `𝒳` over `Spec A`: for every
deformation situation `(x, A' → A)` the object `x` lifts to `Spec A'` exactly when the composition
`E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` vanishes, and there is an isomorphism of functors
`T_x(−) ⟶ Ext⁰_A(E, −)` under which `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}` is the image of the canonical
element of `T_x(Ω_{A/Λ})`.

These are the fields of `Deformation.Artin.NaiveObstructionTheory` concerning `T_x` and the
lifting criterion, read at the single charted object `P`. -/
public structure NaiveObstructionAt where
  /-- Assumption (1): the lifting criterion across a deformation situation. -/
  hasLift_iff_xi_comp_eq_zero : ∀ (t : DeformationSituation B S hS P.obj.alg)
      [Algebra t.top.carrier P.ring] [Algebra c.ring t.top.carrier]
      [IsScalarTower c.ring t.top.carrier P.ring]
      (_hmap : algebraMap t.top.carrier P.ring = t.hom.ringMap)
      (_hchart : Spec.map (CommRingCat.ofHom (algebraMap c.ring t.top.carrier)) ≫ c.immersion =
        t.top.toScheme),
    AffineObject.HasLift hp P.obj t ↔
      ξ ≫ naiveCotangentBaseMap c.ring t.top.carrier P.ring = 0
  /-- Assumption (2): the transformation `T_x(M) ⟶ Ext⁰_A(E, M)`. -/
  tangentMap : ∀ M : SiteModule P.ring B,
    ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w)) →
      DerivedCategory.Ext E
        ((DerivedCategory.singleFunctor (ModuleCat.{u} P.ring) 0).obj M.obj) 0
  /-- Assumption (2): the transformation is additive. -/
  tangentMap_add : ∀ (M : SiteModule P.ring B)
      (a a' : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w))),
    tangentMap M (a + a') = tangentMap M a + tangentMap M a'
  /-- Assumption (2): the transformation is natural in the coefficient module. -/
  tangentMap_natural : ∀ (M N : SiteModule P.ring B) (f : M ⟶ N)
      (a : ((P.tangent hp hRS).functor.obj M : Type (max (u + 1) v w))),
    tangentMap N ((P.tangent hp hRS).functor.map f a) =
      extPushforward E f.hom 0 (tangentMap M a)
  /-- Assumption (2): the transformation is an isomorphism. -/
  tangentMap_bijective : ∀ M : SiteModule P.ring B, Function.Bijective (tangentMap M)
  /-- Assumption (2): the canonical element of `T_x(Ω_{A/Λ})` goes to the composition
  `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`. -/
  tangentMap_canonicalElement :
    tangentMap (differentialsSiteModule c.ring P.ring B hΩ)
        (canonicalDeformationElement c.ring P.ring B S hS P.obj.alg.toScheme P.obj.alg.mem
          p P.point P.obj.obj.2 hp hRS hΩ c.immersion P.factorization).element =
      ShiftedHom.mk₀ (0 : ℤ) rfl (ξ ≫ naiveCotangentToDifferentials c.ring P.ring)

/-- **The versality criterion of Stacks 07YM**, as a hypothesis. Granted assumptions (1) and (2)
of Stacks 07YN, at a finite type point `u` of `Spec A`: if `ξ` is surjective on `H^{-1}` and
injective on `H^0` of the derived fibre at `u`, then `x` is versal at `u`; and conversely, if `u`
is a closed point at which `x` is versal, then `ξ` has those two properties at `u`. -/
public def NaiveVersalityCriterion : Prop :=
  ∀ (_data : NaiveObstructionAt hp hRS P hΩ E ξ) (u : Spec (.of P.ring)), IsFiniteTypePoint u →
    ((Function.Surjective (derivedFibreHomologyMap ξ u (-1)) ∧
        Function.Injective (derivedFibreHomologyMap ξ u 0)) →
      IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u P.point
        P.overScheme_eq) ∧
    (IsClosed ({u} : Set (Spec (.of P.ring))) →
      IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u P.point
        P.overScheme_eq →
      Function.Surjective (derivedFibreHomologyMap ξ u (-1)) ∧
        Function.Injective (derivedFibreHomologyMap ξ u 0))

/-- **Stacks 07YN.** Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in groupoids
over the big fppf site of `S` satisfying (RS*). Let `x` be an object of `𝒳` over an affine scheme
`U = Spec A` of finite type over `S` mapping into the affine open `Spec Λ ⊆ S`, and let
`ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)` for which

1. for every deformation situation `(x, A' → A)` the object `x` lifts to `Spec A'` exactly when
   `E ⟶ NL_{A/Λ} ⟶ NL_{A/A'}` is zero;
2. there is an isomorphism of functors `T_x(−) ⟶ Ext⁰_A(E, −)` carrying the canonical element to
   `E ⟶ NL_{A/Λ} ⟶ Ω_{A/Λ}`;
3. the cohomology modules of `E` are finite `A`-modules.

If `x` is versal at a closed point `u₀ ∈ U` then there is an open neighbourhood `U' ⊆ U` of `u₀`
such that `x` is versal at every finite type point of `U'`. -/
public theorem exists_isOpen_isVersalAt_of_naiveObstructionAt [IsLocallyNoetherian S]
    [Algebra.FiniteType c.ring P.ring]
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} P.ring)).minus E)
    (data : NaiveObstructionAt hp hRS P hΩ E ξ)
    (hFinite : ∀ n : ℤ,
      Module.Finite P.ring ((DerivedCategory.homologyFunctor (ModuleCat.{u} P.ring) n).obj E))
    (hcriterion : NaiveVersalityCriterion hp hRS P hΩ E ξ)
    (u₀ : Spec (.of P.ring)) (hu₀ : IsClosed ({u₀} : Set (Spec (.of P.ring))))
    (hversal : IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u₀ P.point
      P.overScheme_eq) :
    ∃ V : Set (Spec (.of P.ring)), IsOpen V ∧ u₀ ∈ V ∧
      ∀ u ∈ V, IsFiniteTypePoint u →
        IsVersalAt (Over.mk P.obj.alg.toScheme) (p ⋙ Over.post B.inclusion) u P.point
          P.overScheme_eq := by
  have : IsLocallyNoetherian (Spec (.of c.ring)) :=
    isLocallyNoetherian_of_isOpenImmersion c.immersion
  have : IsNoetherianRing c.ring :=
    (isLocallyNoetherian_Spec (R := CommRingCat.of c.ring)).mp inferInstance
  have : IsNoetherianRing P.ring := Algebra.FiniteType.isNoetherianRing c.ring P.ring
  have hEpc : StacksDraft.PseudoCoherence.IsPseudoCoherent E := by
    obtain ⟨N, hN⟩ := (DerivedCategory.minus_iff E).1 hE
    exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      E 0 P.ring).2.1.mpr ⟨⟨N - 1, fun n hn => hN n (by omega)⟩, hFinite⟩
  obtain ⟨Cone, β, γ, hT⟩ := distinguished_cocone_triangle ξ
  have hCpc : StacksDraft.PseudoCoherence.IsPseudoCoherent Cone :=
    (StacksDraft.PseudoCoherence.isPseudoCoherent_of_distinguished (Triangle.mk ξ β γ) hT).1
      hEpc (isPseudoCoherent_derivedNaiveCotangentComplex c.ring P.ring)
  have key (u : Spec (.of P.ring)) :
      (Function.Surjective (derivedFibreHomologyMap ξ u (-1)) ∧
          Function.Injective (derivedFibreHomologyMap ξ u 0)) ↔
        (letI := u.isPrime;
          StacksDraft.Perfect.FibreCohomologyVanishes.{u, u} u.asIdeal Cone (-1)) := by
    have : u.asIdeal.IsPrime := u.isPrime
    rw [StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology u.asIdeal Cone hCpc (-1)]
    let T := (totalDerivedExtensionScalars.{u, u, u}
      (algebraMap P.ring u.asIdeal.ResidueField)).functor.mapTriangle.obj (Triangle.mk ξ β γ)
    have hT' : T ∈ distinguishedTriangles := Functor.map_distinguished _ _ hT
    simp only [← ModuleCat.epi_iff_surjective, ← ModuleCat.mono_iff_injective]
    exact ⟨fun h => isZero_homology_obj₃_of_epi_mono T hT' (-1) 0 (by norm_num) h.1 h.2,
      fun h => epi_mono_of_isZero_homology_obj₃ T hT' (-1) 0 (by norm_num) h⟩
  have : u₀.asIdeal.IsPrime := u₀.isPrime
  obtain ⟨f, hf, hV⟩ := exists_basicOpen_fibreCohomologyVanishes u₀.asIdeal Cone hCpc (-1)
    ((key u₀).mp ((hcriterion data u₀ (isFiniteTypePoint_of_isClosed_singleton hu₀)).2 hu₀ hversal))
  exact ⟨(PrimeSpectrum.basicOpen f : Set (PrimeSpectrum P.ring)),
    (PrimeSpectrum.basicOpen f).isOpen, hf, fun u hu hufin =>
      (hcriterion data u hufin).1 ((key u).mpr (hV u hu))⟩

end Versality

end Deformation.Artin

end
