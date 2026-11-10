module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartEtaComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleLocallyFree
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ObstructionSubscheme
public import StacksFrontier.Algebra.Homology.ProjectiveHomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.Modules.AffineOpenStalkRank
public import StacksFrontier.Homology.Eta.Perfect.EtaHomologyLocalization
public import StacksFrontier.Homology.Perfect.LocalizedHomologyBaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.MinimalChainModel

/-!
# Blowing up complexes, II: the obstruction subscheme (More on Flatness, Tag 0GTZ)

Let `(X, D, M)` be a good triple as in Situation 0F8S and let `T ⊆ D` be the closed subscheme cut
out by the glued obstruction ideals (`ComplexAndDivisorSituation.obstructionIdealSheaf`), with
closed immersion `i : T ⟶ D`.  This file computes the cohomology sheaves of `Li^*(Lη_I M)` and
proves More on Flatness, Tag 0GTZ.

Over `T ∩ U`, for a good affine chart `(U, A, f, M^•)`, the coordinate ring of `T ∩ U` is the ring
`C = (A ⧸ fA) ⧸ J(M^•, f)` of More on Algebra, Tag 0F81 (`AffineChart.obstructionQuotEquiv`), and
the restriction of the `n`-th cohomology sheaf of `Li^*(Lη_I M)` is the sheaf associated with
`H^n(η_f M^• ⊗_A C)`, a finite projective `C`-module by that tag.  This gives part (2).  At a
point over the locally free locus `W` of `M` the cohomology of the chart complex is free, and the
ranks of both stalks are computed from the localized cohomology of the décalage, which there
agrees with that of `M^•` (Cohomology, Tag 0GTA, read on the chart through Tag 0F7P) and commutes
with base change; this gives part (3).

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.etaPullbackHomology`: the `n`-th cohomology sheaf
  of `Lh^*(Lη_I M)`, for a morphism `h : Y ⟶ X`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.objectHomology`: the `n`-th cohomology sheaf of
  `M`.

## Main results

* `ComplexAndDivisorSituation.isFiniteLocallyFree_etaPullbackHomology`: part (2).
* `ComplexAndDivisorSituation.finrank_stalk_etaPullbackHomology`: part (3).
* `ComplexAndDivisorSituation.exists_subscheme_isClosedImmersion_etaPullbackHomology`:
  **More on Flatness, Tag 0GTZ.**

## Implementation notes

The derived pullback and the derived décalage are formed at the standard models of the derived
categories, where this library constructs them; the statements only involve the cohomology
sheaves, which are sheaves of modules and do not depend on a model.  The object `M` of the triple
lives at an arbitrary model.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0GTA](https://stacks.math.columbia.edu/tag/0GTA)
* [Stacks Project, Tag 0F7P](https://stacks.math.columbia.edu/tag/0F7P)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect Stacks.Decalage.DirectSumIdeal
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

variable {S : ComplexAndDivisorSituation.{u, d}}

namespace AffineChart

/-- The affine open `T ∩ U` of a closed subscheme `T ⊆ D` lying over the affine open of a chart. -/
def subschemeAffineOpen (C : AffineChart S) (T : S.D.subscheme.IdealSheafData) :
    T.subscheme.affineOpens :=
  ⟨T.subschemeι ⁻¹ᵁ C.divisorAffineOpen.1, T.isAffineOpen_preimage_subschemeι C.divisorAffineOpen⟩

/-- The affine open `T ∩ U` is contained in the preimage of `U` under the composite closed
immersion `T ⟶ D ⟶ X`. -/
theorem subschemeAffineOpen_le (C : AffineChart S) (T : S.D.subscheme.IdealSheafData) :
    ((C.subschemeAffineOpen T : T.subscheme.affineOpens) : T.subscheme.Opens) ≤
      (T.subschemeι ≫ S.D.subschemeι) ⁻¹ᵁ (C.U : S.X.Opens) :=
  fun _ hx => hx

/-- The map of coordinate rings `A = Γ(X, U) ⟶ Γ(T, T ∩ U)`. -/
abbrev subschemeRingHom (C : AffineChart S) (T : S.D.subscheme.IdealSheafData) :
    Γ(S.X, C.U) ⟶ Γ(T.subscheme, C.subschemeAffineOpen T) :=
  (T.subschemeι ≫ S.D.subschemeι).appLE C.U (C.subschemeAffineOpen T)
    (C.subschemeAffineOpen_le T)

/-- The map of coordinate rings `Γ(X, U) ⟶ Γ(T, T ∩ U)` sends a section to the class, in the
coordinate ring `Γ(D, D ∩ U) ⧸ T(D ∩ U)` of `T ∩ U`, of its restriction to `D ∩ U`. -/
theorem subschemeRingHom_apply (C : AffineChart S) (T : S.D.subscheme.IdealSheafData)
    (a : Γ(S.X, C.U)) :
    (C.subschemeRingHom T).hom a = (T.subschemeObjIso C.divisorAffineOpen).inv.hom
      (Ideal.Quotient.mk _ ((S.D.subschemeι.app C.U.1).hom a)) := by
  rw [subschemeRingHom, Scheme.Hom.comp_appLE]
  change (T.subscheme.presheaf.map (homOfLE _).op).hom ((T.subschemeι.app
    (C.divisorAffineOpen : S.D.subscheme.Opens)).hom ((S.D.subschemeι.app C.U.1).hom a)) = _
  rw [Scheme.IdealSheafData.subschemeι_app T C.divisorAffineOpen]
  change (T.subscheme.presheaf.map (𝟙 (Opposite.op
    ((C.subschemeAffineOpen T : T.subscheme.affineOpens) : T.subscheme.Opens)))).hom _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **The coordinate ring of `T ∩ U` for the obstruction subscheme.**  When the ideal of `T` over
`D ∩ U` is the obstruction ideal `J(M^•, f)` of the chart, the coordinate ring of `T ∩ U` is
`(A ⧸ fA) ⧸ J(M^•, f)`, the ring `C` of More on Algebra, Tag 0F81. -/
def obstructionQuotEquiv (C : AffineChart S) (T : S.D.subscheme.IdealSheafData)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    (Γ(S.X, C.U) ⧸ Ideal.span {C.f}) ⧸ etaTotalDirectSumIdeal C.complex C.f ≃+*
      Γ(T.subscheme, C.subschemeAffineOpen T) :=
  (@Ideal.quotientEquiv _ _ _ _ (etaTotalDirectSumIdeal C.complex C.f)
      (T.ideal C.divisorAffineOpen) inferInstance inferInstance C.divisorQuotEquiv.symm hT).trans
    (T.subschemeObjIso C.divisorAffineOpen).commRingCatIsoToRingEquiv.symm

/-- **The map `A ⟶ Γ(T, T ∩ U)` is the quotient map `A ⟶ (A ⧸ fA) ⧸ J(M^•, f)`**, read through
`obstructionQuotEquiv`. -/
theorem subschemeRingHom_eq (C : AffineChart S) (T : S.D.subscheme.IdealSheafData)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    (C.subschemeRingHom T).hom = (C.obstructionQuotEquiv T hT).toRingHom.comp
      ((Ideal.Quotient.mk (etaTotalDirectSumIdeal C.complex C.f)).comp
        (Ideal.Quotient.mk (Ideal.span {C.f}))) := by
  ext a
  rw [subschemeRingHom_apply]
  change _ = (T.subschemeObjIso C.divisorAffineOpen).inv.hom
    (Ideal.Quotient.mk _ (C.divisorQuotEquiv.symm (Ideal.Quotient.mk _ a)))
  rw [divisorQuotEquiv_symm_mk]

/-- The two spellings of the cochain complex of a bounded complex of finite free modules agree. -/
def associatedComplexIso {A : Type u} [CommRing A] (M : BoundedComplex A) :
    Stacks.Decalage.ObstructionIdeal.associatedComplex M ≅ M.toCochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j (hij : i + 1 = j)
    subst hij
    simp [Stacks.Decalage.ObstructionIdeal.associatedComplex, BoundedComplex.toCochainComplex_d])

/-- Being finite projective transfers along a linear equivalence. -/
private theorem finite_projective_of_linearEquiv {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (h : Module.Finite R M ∧ Module.Projective R M) :
    Module.Finite R N ∧ Module.Projective R N :=
  have := h.1
  have := h.2
  ⟨.equiv e, .of_equiv e⟩

/-- **The cohomology of the décalage over `T ∩ U` is finite projective.**  For a chart with
principal determinantal ideals and a closed subscheme `T ⊆ D` cutting out the obstruction ideal
over `D ∩ U`, every cohomology module of `η_f M^• ⊗_A Γ(T, T ∩ U)` is a finite projective
`Γ(T, T ∩ U)`-module: `Γ(T, T ∩ U)` is the ring `(A ⧸ fA) ⧸ J(M^•, f)` of More on Algebra,
Tag 0F81, which asserts exactly this. -/
theorem finite_projective_homology_subschemeRingHom (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (T : S.D.subscheme.IdealSheafData)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) (n : ℤ) :
    Module.Finite Γ(T.subscheme, C.subschemeAffineOpen T)
        ((StacksDraft.Perfect.baseChangeComplex (C.subschemeRingHom T).hom
          (EtaComplex.etaObject C.f C.complex.toCochainComplex)).homology n) ∧
      Module.Projective Γ(T.subscheme, C.subschemeAffineOpen T)
        ((StacksDraft.Perfect.baseChangeComplex (C.subschemeRingHom T).hom
          (EtaComplex.etaObject C.f C.complex.toCochainComplex)).homology n) := by
  let τ := C.obstructionQuotEquiv T hT
  let φ₀ := (Ideal.Quotient.mk (etaTotalDirectSumIdeal C.complex C.f)).comp
    (Ideal.Quotient.mk (Ideal.span {C.f}))
  let P := EtaComplex.etaObject C.f C.complex.toCochainComplex
  obtain ⟨hfin₀, hproj₀⟩ :=
    finite_projective_etaHomology_quotient_etaTotalDirectSumIdeal C.complex C.f C.regular hI n
  -- the cohomology over `C` of the décalage, in the spelling of the chart
  let e₀ : (StacksDraft.Perfect.baseChangeComplex φ₀ P).homology n ≅
      ((((ModuleCat.extendScalars φ₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (EtaComplex.etaObject C.f
          (Stacks.Decalage.ObstructionIdeal.associatedComplex C.complex))).homology n) :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (((ModuleCat.extendScalars φ₀).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (Stacks.BlowUpComplexes.etaObjectIso C.f (associatedComplexIso C.complex)).symm)
  obtain ⟨_, _⟩ := finite_projective_of_linearEquiv e₀.toLinearEquiv.symm ⟨hfin₀, hproj₀⟩
  -- base change along the isomorphism `C ≅ Γ(T, T ∩ U)`
  have hflat : τ.toRingHom.Flat := RingHom.Flat.of_bijective τ.bijective
  have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} τ.toRingHom) :=
    extendScalars_preservesFiniteLimits_of_flat' τ.toRingHom hflat
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} τ.toRingHom) :=
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} τ.toRingHom).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} τ.toRingHom) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  let e : (StacksDraft.Perfect.baseChangeComplex (τ.toRingHom.comp φ₀) P).homology n ≅
      (ModuleCat.extendScalars τ.toRingHom).obj
        ((StacksDraft.Perfect.baseChangeComplex φ₀ P).homology n) :=
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
        (StacksDraft.Perfect.baseChangeComplexCompIso φ₀ τ.toRingHom P).symm ≪≫
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
        (ModuleCat.extendScalars τ.toRingHom) (ComplexShape.up ℤ) n).app _
  rw [subschemeRingHom_eq C T hT]
  let := τ.toRingHom.toAlgebra
  exact finite_projective_of_linearEquiv e.toLinearEquiv.symm
    ⟨inferInstanceAs (Module.Finite _ (TensorProduct ((Γ(S.X, C.U) ⧸ Ideal.span {C.f}) ⧸
      etaTotalDirectSumIdeal C.complex C.f) Γ(T.subscheme, C.subschemeAffineOpen T)
      ((StacksDraft.Perfect.baseChangeComplex φ₀ P).homology n))),
    inferInstanceAs (Module.Projective _ (TensorProduct ((Γ(S.X, C.U) ⧸ Ideal.span {C.f}) ⧸
      etaTotalDirectSumIdeal C.complex C.f) Γ(T.subscheme, C.subschemeAffineOpen T)
      ((StacksDraft.Perfect.baseChangeComplex φ₀ P).homology n)))⟩

/-- The décalage of the complex of a chart is bounded above. -/
theorem isStrictlyLE_etaObject (C : AffineChart S) :
    ∃ b : ℤ, (EtaComplex.etaObject C.f C.complex.toCochainComplex).IsStrictlyLE b := by
  obtain ⟨b, hb⟩ := C.complex.bounded.bddAbove
  refine ⟨b, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine C.isZero_etaComplex_X ?_
  by_contra h
  exact (not_le_of_gt hi) (hb h)

end AffineChart

/-- **The cohomology sheaves of `Lh^*(Lη_I M)`.**  For a morphism of schemes `h : Y ⟶ X`, the
`n`-th cohomology sheaf of the derived pullback along `h` of the derived décalage `Lη_I M` of the
object of the triple.  The derived pullback and the derived décalage are formed at the standard
models of the derived categories, where this library constructs them; the cohomology sheaf itself
is a sheaf of `𝒪_Y`-modules and does not depend on a model. -/
def etaPullbackHomology (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (n : ℤ) : Y.Modules :=
  haveI := S.isEffectiveCartierDivisor
  letI := HasDerivedCategory.standard S.X.Modules
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing S.X.toRingedSpace))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))
  letI := HasDerivedCategory.standard Y.Modules
  (DerivedCategory.homologyFunctor Y.Modules n).obj
    ((derivedPullback h.toLRSHom.toShHom).obj
      ((Stacks.Divisors.Eta.derivedEtaData S.D).functor.obj S.standardObject))

/-- **More on Flatness, Tag 0GTZ part (2), on a closed subscheme cutting out the obstruction
ideals.**  Let `(X, D, M)` be a good triple and let `i : T ⟶ D` be a closed subscheme whose ideal
over `D ∩ U` is the obstruction ideal `J(M^•, f)` for every good affine chart `(U, A, f, M^•)`.
Then every cohomology sheaf of `Li^*(Lη_I M)` is finite locally free.

Over `T ∩ U` the cohomology sheaf is the sheaf associated with the cohomology of
`η_f M^• ⊗_A Γ(T, T ∩ U)`
(`AffineChart.nonempty_restrict_homology_derivedPullback_derivedEta_iso`), which is finite
projective because `Γ(T, T ∩ U)` is the ring of More on Algebra, Tag 0F81
(`AffineChart.finite_projective_homology_subschemeRingHom`); the sheaf associated with a finite
projective module is finite locally free (Tag 05JM), and finite local freeness is local. -/
theorem isFiniteLocallyFree_etaPullbackHomology (hS : S.IsGoodTriple)
    (T : S.D.subscheme.IdealSheafData)
    (hT : ∀ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      T.ideal C.divisorAffineOpen = C.obstructionIdeal) (n : ℤ) :
    Scheme.Modules.IsFiniteLocallyFree
      (S.etaPullbackHomology (T.subschemeι ≫ S.D.subschemeι) n) := by
  refine Scheme.Modules.isFiniteLocallyFree_of_iSup_eq_top
    (fun C : {C : AffineChart S // ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal} =>
      ((C.1.subschemeAffineOpen T : T.subscheme.affineOpens) : T.subscheme.Opens)) ?_ ?_
  · rw [eq_top_iff]
    intro t _
    obtain ⟨C, hI, hz⟩ := S.exists_good_chart_mem_preimage hS (T.subschemeι t)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨C, hI⟩, hz⟩
  · rintro ⟨C, hI⟩
    obtain ⟨e⟩ := C.nonempty_restrict_homology_derivedPullback_derivedEta_iso hI
      (T.subschemeι ≫ S.D.subschemeι) (C.subschemeAffineOpen T) (C.subschemeAffineOpen_le T) n
    refine Scheme.Modules.IsFiniteLocallyFree.of_iso e.symm ?_
    obtain ⟨hfin, hproj⟩ := C.finite_projective_homology_subschemeRingHom hI T (hT C hI) n
    have htilde := (tilde_isFiniteLocallyFree_iff Γ(T.subscheme, C.subschemeAffineOpen T)
      ((StacksDraft.Perfect.baseChangeComplex (C.subschemeRingHom T).hom
        (EtaComplex.etaObject C.f C.complex.toCochainComplex)).homology n)).mpr
      ((Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr ⟨hfin, hproj⟩)
    exact htilde.restrict _

/-- The `n`-th cohomology sheaf of the object `M` of a triple, as an `𝒪_X`-module. -/
abbrev objectHomology (S : ComplexAndDivisorSituation.{u, d}) (n : ℤ) : S.X.Modules :=
  (DerivedCategory.homologyFunctor (OXMod.{u, u} S.X.toRingedSpace) n).obj S.M

/-- Localizations at equal primes have equal ranks. -/
private theorem finrank_localizedModule_congr {R : Type u} [CommRing R] (N : Type u)
    [AddCommGroup N] [Module R N] {p₁ p₂ : Ideal R} [p₁.IsPrime] [p₂.IsPrime] (h : p₁ = p₂) :
    Module.finrank (Localization.AtPrime p₁) (LocalizedModule p₁.primeCompl N) =
      Module.finrank (Localization.AtPrime p₂) (LocalizedModule p₂.primeCompl N) := by
  subst h
  rfl

/-- Localizations at equal primes are free together. -/
private theorem free_localizedModule_congr {R : Type u} [CommRing R] (N : Type u)
    [AddCommGroup N] [Module R N] {p₁ p₂ : Ideal R} [p₁.IsPrime] [p₂.IsPrime] (h : p₁ = p₂)
    (hN : Module.Free (Localization.AtPrime p₂) (LocalizedModule p₂.primeCompl N)) :
    Module.Free (Localization.AtPrime p₁) (LocalizedModule p₁.primeCompl N) := by
  subst h
  exact hN

/-- **More on Flatness, Tag 0GTZ part (3), on a closed subscheme cutting out the obstruction
ideals.**  Let `(X, D, M)` be a good triple and let `i : T ⟶ D` be a closed subscheme whose ideal
over `D ∩ U` is the obstruction ideal `J(M^•, f)` for every good affine chart.  At a point `t` of
`T` whose image `x` in `X` lies in the locally free locus `W` of `M`, the rank of `H^n(M)_x` over
`𝒪_{X, x}` is the rank of `H^n(Li^*(Lη_I M))_t` over `𝒪_{T, t}`.

Choose a good chart `(U, A, f, M^•)` at `x` with `U ⊆ W`.  The two stalks are the localizations,
at the primes `p` of `x` and `q` of `t`, of `H^n(M^•)` and of `H^n(η_f M^• ⊗_A Γ(T, T ∩ U))`
(`finrank_stalk_eq_finrank_localizedModule`).  As `U ⊆ W` every `H^i(M^•)_p` is free, so the
cohomology of the décalage agrees with that of `M^•` at `p` (Cohomology, Tag 0GTA:
`nonempty_localizedEtaHomologyEquiv`, from Tag 0F7P), and the décalage, a complex of projectives
whose cohomology is free at `p`, has cohomology commuting with base change there
(`free_finrank_localizedModule_homology_baseChange`). -/
theorem finrank_stalk_etaPullbackHomology (hS : S.IsGoodTriple)
    (T : S.D.subscheme.IdealSheafData)
    (_hT : ∀ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      T.ideal C.divisorAffineOpen = C.obstructionIdeal)
    (t : T.subscheme) (ht : S.D.subschemeι (T.subschemeι t) ∈ S.locallyFreeLocus) (n : ℤ) :
    Module.finrank (S.X.presheaf.stalk (S.D.subschemeι (T.subschemeι t)))
        ((S.objectHomology n).presheaf.stalk (S.D.subschemeι (T.subschemeι t))) =
      Module.finrank (T.subscheme.presheaf.stalk t)
        ((S.etaPullbackHomology (T.subschemeι ≫ S.D.subschemeι) n).presheaf.stalk t) := by
  set x := S.D.subschemeι (T.subschemeι t)
  obtain ⟨C, hI, hxU, hUW⟩ := S.exists_good_chart_le_locallyFreeLocus hS x
    (S.D.mem_supportSet_subschemeι (T.subschemeι t)) ht
  let V := C.subschemeAffineOpen T
  have htV : t ∈ ((V : T.subscheme.affineOpens) : T.subscheme.Opens) := hxU
  let t' : ((V : T.subscheme.affineOpens) : T.subscheme.Opens).toScheme := ⟨t, htV⟩
  let x' : (C.U : S.X.Opens).toScheme := ⟨x, hxU⟩
  -- the stalk of `H^n(Li^* Lη_I M)` at `t`
  obtain ⟨eT⟩ := C.nonempty_restrict_homology_derivedPullback_derivedEta_iso hI
    (T.subschemeι ≫ S.D.subschemeι) V (C.subschemeAffineOpen_le T) n
  have hR := finrank_stalk_eq_finrank_localizedModule V
    (S.etaPullbackHomology (T.subschemeι ≫ S.D.subschemeι) n) _ eT t'
  -- the stalk of `H^n(M)` at `x`
  have hL := finrank_stalk_eq_finrank_localizedModule C.U (S.objectHomology n)
    _ (C.chartHomologyIso n) x'
  -- the primes
  let φ := (C.subschemeRingHom T).hom
  have hpq : (V.2.primeIdealOf t').asIdeal.comap φ = (C.U.2.primeIdealOf x').asIdeal :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE (f := T.subschemeι ≫
      S.D.subschemeι) (C.U : S.X.Opens) C.U.2 _ V.2 (C.subschemeAffineOpen_le T) htV)
  -- the cohomology of `M^•` is free at every prime of `A`
  have hCW : (C.U.1 : Set S.X) ⊆ RingedSpace.cohomologyFiniteFreeLocus S.M := fun y hy => hUW hy
  have hfreeM : ∀ i, Module.Free (Localization.AtPrime (C.U.2.primeIdealOf x').asIdeal)
      (LocalizedModule (C.U.2.primeIdealOf x').asIdeal.primeCompl
        (C.complex.toCochainComplex.homology i)) := fun i =>
    C.free_localizedModule_homology_of_subset_cohomologyFiniteFreeLocus hCW x' i
  have heta : ∀ i, Nonempty (LocalizedModule (C.U.2.primeIdealOf x').asIdeal.primeCompl
      ((EtaComplex.etaObject C.f C.complex.toCochainComplex).homology i) ≃ₗ[
        Localization.AtPrime (C.U.2.primeIdealOf x').asIdeal]
      LocalizedModule (C.U.2.primeIdealOf x').asIdeal.primeCompl
        (C.complex.toCochainComplex.homology i)) := fun i =>
    Stacks.Decalage.Cohomology.nonempty_localizedEtaHomologyEquiv C.complex C.regular _ i
      (hfreeM i)
  obtain ⟨b, hb⟩ := C.isStrictlyLE_etaObject
  have hproj : ∀ i, Module.Projective Γ(S.X, C.U)
      ((EtaComplex.etaObject C.f C.complex.toCochainComplex).X i) := fun i =>
    (C.finite_projective_etaComplex_X hI i).2
  have hfreeP : ∀ i, Module.Free (Localization.AtPrime ((V.2.primeIdealOf t').asIdeal.comap φ))
      (LocalizedModule ((V.2.primeIdealOf t').asIdeal.comap φ).primeCompl
        ((EtaComplex.etaObject C.f C.complex.toCochainComplex).homology i)) := fun i =>
    have := hfreeM i
    free_localizedModule_congr _ hpq (Module.Free.of_equiv (heta i).some.symm)
  obtain ⟨-, hrank⟩ := StacksDraft.Perfect.free_finrank_localizedModule_homology_baseChange φ
    (EtaComplex.etaObject C.f C.complex.toCochainComplex) b hproj (V.2.primeIdealOf t').asIdeal
    hfreeP n
  exact hL.trans ((heta n).some.finrank_eq.symm.trans
    ((finrank_localizedModule_congr _ hpq).symm.trans (hrank.symm.trans hR.symm)))

/-- **More on Flatness, Tag 0GTZ.**  Let `X`, `D`, `I`, `M` be as in Situation 0F8S.  If
`(X, D, M)` is a good triple, then there exists a closed immersion `i : T ⟶ D` of finite
presentation such that

1. `T` scheme theoretically contains `D ∩ W`, where `W ⊆ X` is the maximal open over which the
   cohomology sheaves of `M` are locally free: the ideal sheaf of `T` vanishes on `D ∩ W`;
2. the cohomology sheaves of `Li^*(Lη_I M)` are (finite) locally free; and
3. for every point `t ∈ T` with image `x = i(t) ∈ W`, the rank of `H^n(M)_x` over `𝒪_{X, x}`
   and the rank of `H^n(Li^*(Lη_I M))_t` over `𝒪_{T, t}` agree, for every `n`.

The closed subscheme `T ⊆ D` is cut out by the ideal sheaf `obstructionIdealSheaf`, which on a
good affine chart `(U, A, f, M^•)` is the total obstruction ideal `J(M^•, f)` of More on Algebra,
Tag 0F81; these ideals glue because they do not depend on the chart (Tag 0GSW, flat base
change, and `etaTotalDirectSumIdeal_unit_mul`).  A closed immersion is quasi-compact and
separated, so being of finite presentation is being locally of finite presentation, which holds
because the obstruction ideals are finitely generated.  Here `Li^*(Lη_I M)` is the derived
pullback along `T ⟶ D ⟶ X` of the derived décalage of `M`, and its `n`-th cohomology sheaf is
`etaPullbackHomology`; `W` is `ComplexAndDivisorSituation.locallyFreeLocus`, the open of the
points at which every cohomology sheaf of `M` has a finite free stalk, which by Stacks 0GT1 is
the maximal open over which these sheaves are finite locally free. -/
@[stacks 0GTZ "the existence of the closed immersion i : T → D of finite presentation together \
with parts (1), (2) and (3); locally free in (2) is proved in the stronger form finite locally \
free, and part (3) is stated for every degree n"]
theorem exists_subscheme_isClosedImmersion_etaPullbackHomology (hS : S.IsGoodTriple) :
    ∃ T : S.D.subscheme.IdealSheafData,
      IsClosedImmersion T.subschemeι ∧ LocallyOfFinitePresentation T.subschemeι ∧
      T.comap (S.D.subschemeι ⁻¹ᵁ S.locallyFreeLocus).ι = ⊥ ∧
      (∀ n : ℤ, Scheme.Modules.IsFiniteLocallyFree
        (S.etaPullbackHomology (T.subschemeι ≫ S.D.subschemeι) n)) ∧
      ∀ t : T.subscheme, S.D.subschemeι (T.subschemeι t) ∈ S.locallyFreeLocus → ∀ n : ℤ,
        Module.finrank (S.X.presheaf.stalk (S.D.subschemeι (T.subschemeι t)))
            ((S.objectHomology n).presheaf.stalk (S.D.subschemeι (T.subschemeι t))) =
          Module.finrank (T.subscheme.presheaf.stalk t)
            ((S.etaPullbackHomology (T.subschemeι ≫ S.D.subschemeι) n).presheaf.stalk t) := by
  have hT : ∀ C : AffineChart S, (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      (S.obstructionIdealSheaf hS).ideal C.divisorAffineOpen = C.obstructionIdeal :=
    fun C hI => ideal_obstructionIdealSheaf hS C hI
  obtain ⟨hfp, h1⟩ := S.locallyOfFinitePresentation_and_comap_eq_bot_obstructionIdealSheaf hS
  exact ⟨S.obstructionIdealSheaf hS, inferInstance, hfp, h1,
    fun n => isFiniteLocallyFree_etaPullbackHomology hS _ hT n,
    fun t ht n => finrank_stalk_etaPullbackHomology hS _ hT t ht n⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
