module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative.TrivialSummands
public import StacksFrontier.Homology.Perfect.MinimalRepresentative.LocalRing
public import StacksFrontier.Homology.Perfect.MinimalRepresentative.HomEquations
import all StacksFrontier.Homology.Perfect.MinimalRepresentative.ElementarySplitting
import all StacksFrontier.Homology.Perfect.MinimalRepresentative.TrivialSummands
import all StacksFrontier.Homology.Perfect.MinimalRepresentative.LocalRing
import all StacksFrontier.Homology.Perfect.MinimalRepresentative.HomEquations

/-!
# Minimal representatives on a principal neighbourhood of a prime

The minimal free model over the local ring at a prime `p` descends to a principal neighbourhood of
`p`: a perfect object has there a bounded free representative whose ranks are the dimensions of
the cohomology of its derived fibre at `p` (`exists_away_bounded_free_complex_representing`,
[stacks 0BCD]), and a bounded below pseudo-coherent object whose derived fibre at `p` has no
cohomology below `a` is perfect there, with such a representative concentrated in degrees `≥ a`
(`exists_away_bounded_free_complex_representing_of_fibre_vanishing_below`, [stacks 0BYP]). Both
have general forms, suffixed `_of_datum`, for arbitrary total derived extension-of-scalars data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct ChangeOfRings

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### Minimal free representatives near a prime -/

/-- The comparison between localization of modules and extension of scalars to the localized
ring, as a chosen isomorphism of functors. -/
private noncomputable def localizedModuleFunctorIsoExtendScalars
    {R : Type u} [CommRing R] (S : Submonoid R) :
    ModuleCat.localizedModuleFunctor.{max v u} S ≅
      ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization S)) :=
  (exists_extendScalars_iso_localizedModuleFunctor.{u, v} S).some.symm

set_option backward.isDefEq.respectTransparency false in
/-- Localizing a standard finite free module gives the standard finite free module of the same
rank over the localized ring. -/
private theorem localized_finite_free_iso {R : Type u} [CommRing R] (S : Submonoid R) (n : ℕ) :
    Nonempty (((ModuleCat.localizedModuleFunctor.{max v u} S).obj
      (ModuleCat.of R (ULift.{v} (Fin n → R)))) ≅
        ModuleCat.of (Localization S) (ULift.{v} (Fin n → Localization S))) := by
  let M := ModuleCat.of R (ULift.{v} (Fin n → R))
  let b : Module.Basis (Fin n) R M := (Pi.basisFun R (Fin n)).map ULift.moduleEquiv.symm
  have : IsLocalizedModule S (M.localizedModuleMkLinearMap S) :=
    ModuleCat.localizedModule_isLocalizedModule M S
  let bS := b.ofIsLocalizedModule (Localization S) S (M.localizedModuleMkLinearMap S)
  exact ⟨(bS.equivFun.trans ULift.moduleEquiv.symm).toModuleIso⟩

/-- Transport a complex along a termwise isomorphism, recording the transported differentials. -/
private theorem exists_complex_of_termwise_iso
    {C : Type*} [Category C] [Preadditive C]
    (P : CochainComplex C ℤ) (X : ℤ → C) (e : ∀ i, X i ≅ P.X i) :
    ∃ (d : ∀ i, X i ⟶ X (i + 1)) (hd : ∀ i, d i ≫ d (i + 1) = 0),
      Nonempty (CochainComplex.of X d hd ≅ P) := by
  let d (i : ℤ) := (e i).hom ≫ P.d i (i + 1) ≫ (e (i + 1)).inv
  have hd (i : ℤ) : d i ≫ d (i + 1) = 0 := by simp [d]
  refine ⟨d, hd, ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩⟩
  intro i j hij
  change i + 1 = j at hij
  subst j
  simp [CochainComplex.of_d, d]

/-- A bounded above complex of projectives computes derived extension of scalars to a
localization, so its termwise localization represents the derived localization. -/
private theorem localized_complex_represents_derivedExtensionScalars
    {R : Type u} [CommRing R] (S : Submonoid R)
    (Dloc : TotalDerivedExtensionScalars.{u, v, u}
      (algebraMap R (Localization S)))
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) (b : ℤ)
    [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] :
    Nonempty (DerivedCategory.Q.obj
      (((ModuleCat.localizedModuleFunctor.{max v u} S).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≅ Dloc.functor.obj (DerivedCategory.Q.obj P)) := by
  have hc : IsIso (Dloc.comparison.app P) := Dloc.comparison_isIso_of_projective P b
  exact ⟨DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (localizedModuleFunctorIsoExtendScalars.{u, v} S)
      (ComplexShape.up ℤ)).app P) ≪≫ (@asIso _ _ _ _ (Dloc.comparison.app P) hc).symm⟩

/-- The standard finite free module of rank zero is a zero object. -/
private theorem isZero_standard_free_of_rank_zero {R : Type u} [CommRing R] (n : ℕ) (h : n = 0) :
    IsZero (ModuleCat.of R (ULift.{v} (Fin n → R))) := by
  subst h
  exact ModuleCat.isZero_of_subsingleton _

/-- A zero module over a field has dimension zero. -/
private theorem finrank_eq_zero_of_isZero {k : Type u} [Field k] {M : ModuleCat.{max v u} k}
    (h : IsZero M) : Module.finrank k M = 0 :=
  have := ModuleCat.subsingleton_of_isZero h
  Module.finrank_zero_of_subsingleton

/-- Outside a pair of bounds, the homology of a strictly bounded complex vanishes. -/
private theorem homology_isZero_of_not_mem_bounds
    {k : Type u} [Ring k] (Dc : CochainComplex (ModuleCat.{max v u} k) ℤ)
    (a b i : ℤ) (ha : Dc.IsStrictlyGE a) (hb : Dc.IsStrictlyLE b)
    (hi : i ∉ Set.Icc a b) : IsZero (Dc.homology i) := by
  rw [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with hi | hi
  · exact (HomologicalComplex.ExactAt.of_isZero
      (Dc.isZero_of_isStrictlyGE a i hi)).isZero_homology
  · exact (HomologicalComplex.ExactAt.of_isZero
      (Dc.isZero_of_isStrictlyLE b i (by omega))).isZero_homology

/-- Over a field, a perfect object has finite-dimensional cohomology, nonzero in only finitely
many degrees. -/
private theorem finite_homology_and_support_of_isPerfect
    {k : Type u} [Field k] (Kk : DerivedCategory (ModuleCat.{max v u} k)) (hK : IsPerfect Kk) :
    (∀ i, Module.Finite k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj Kk)) ∧
      ∃ a b : ℤ, ∀ i, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj Kk) := by
  obtain ⟨Dc, a, b, ha, hb, hfin, _, ⟨e⟩⟩ := hK
  let eH (i : ℤ) : Dc.homology i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj Kk :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} k) i).app Dc).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).mapIso e.symm
  refine ⟨fun i => ?_, a, b, fun i hi => ?_⟩
  · let := finite_homology_of_finite_term.{u, v} Dc i (hfin i)
    exact Module.Finite.equiv (eH i).toLinearEquiv
  · exact (homology_isZero_of_not_mem_bounds.{u, v} Dc a b i ha hb hi).of_iso (eH i).symm

/-- The fibre of a perfect object at a prime has finite-dimensional cohomology, nonzero in only
finitely many degrees. -/
private theorem finite_fibre_homology_and_support
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (Dk : TotalDerivedExtensionScalars.{u, v, u} (algebraMap R p.ResidueField))
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) :
    (∀ i, Module.Finite p.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.ResidueField) i).obj
        (Dk.functor.obj K))) ∧
      {i | Module.finrank p.ResidueField
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.ResidueField) i).obj
          (Dk.functor.obj K)) ≠ 0}.Finite := by
  obtain ⟨hfin, a, b, hab⟩ := finite_homology_and_support_of_isPerfect.{u, v}
    (Dk.functor.obj K) (isPerfect_totalDerived.{u, v} Dk hK)
  refine ⟨hfin, (Set.finite_Icc a b).subset ?_⟩
  intro i hi
  by_contra h
  exact hi (finrank_eq_zero_of_isZero.{u, v} (hab i h))

/-- Over a local ring a perfect object has a strictly bounded representative whose term in degree
`i` is free of rank the dimension of the `i`-th cohomology of its derived fibre. -/
private theorem exists_bounded_free_local_model
    {R : Type u} [CommRing R] [IsLocalRing R]
    (D : TotalDerivedExtensionScalars.{u, v, u} (IsLocalRing.residue R))
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) :
    ∃ (P : CochainComplex (ModuleCat.{max v u} R) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i, Nonempty (P.X i ≅ ModuleCat.of R (ULift.{v} (Fin (Module.finrank
          (IsLocalRing.ResidueField R) ((DerivedCategory.homologyFunctor
            (ModuleCat.{max v u} (IsLocalRing.ResidueField R)) i).obj
              (D.functor.obj K))) → R)))) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨_, a, b, hab⟩ := finite_homology_and_support_of_isPerfect.{u, v}
    (D.functor.obj K) (isPerfect_totalDerived.{u, v} D hK)
  obtain ⟨_, c, _, P, hPc, ⟨hPX, hPK⟩, _⟩ :=
    exists_unique_boundedAbove_free_complex_representing_of_datum.{u, v} D K
      ((isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, v} K).1.mp hK).1
  refine ⟨P, a, c, (CochainComplex.isStrictlyGE_iff P a).2 ?_, hPc, hPX, hPK⟩
  intro i hi
  have hz := hab i (by simp only [Set.mem_Icc]; omega)
  exact IsZero.of_iso (isZero_standard_free_of_rank_zero.{u, v} _
    (finrank_eq_zero_of_isZero.{u, v} hz)) (hPX i).some

/-- Over the local ring at a prime, a perfect object has a strictly bounded representative whose
term in degree `i` is free of rank the dimension of the `i`-th cohomology of the fibre at that
prime. -/
private theorem exists_bounded_free_atPrime_model
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (Dk : TotalDerivedExtensionScalars.{u, v, u} (algebraMap R p.ResidueField))
    (Dp : TotalDerivedExtensionScalars.{u, v, u}
      (algebraMap R (Localization.AtPrime p)))
    (Dres : TotalDerivedExtensionScalars.{u, v, u}
      (IsLocalRing.residue (Localization.AtPrime p)))
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) :
    ∃ (P : CochainComplex (ModuleCat.{max v u} (Localization.AtPrime p)) ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i, Nonempty (P.X i ≅ ModuleCat.of (Localization.AtPrime p)
          (ULift.{v} (Fin (Module.finrank p.ResidueField
            ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.ResidueField) i).obj
              (Dk.functor.obj K))) → Localization.AtPrime p)))) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ Dp.functor.obj K) := by
  obtain ⟨P, a, b, ha, hb, hPX, hPK⟩ := exists_bounded_free_local_model.{u, v} Dres
    (Dp.functor.obj K) (isPerfect_totalDerived.{u, v} Dp hK)
  obtain ⟨e⟩ := totalDerived_comp_of_isPerfect.{u, v} Dp Dres
    (show TotalDerivedExtensionScalars.{u, v, u}
      ((IsLocalRing.residue (Localization.AtPrime p)).comp
        (algebraMap R (Localization.AtPrime p))) from Dk) hK
  refine ⟨P, a, b, ha, hb, fun i => ?_, hPK⟩
  have hr := ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.ResidueField) i).mapIso
    e).toLinearEquiv.finrank_eq
  rw [← hr]
  exact hPX i

set_option backward.isDefEq.respectTransparency false in
/-- The general form of [stacks 0BCD], for arbitrary total derived extension-of-scalars data: let
`R` be a commutative ring, `p` a prime of `R` and `K` a perfect object of `D(R)`. The dimensions
`dᵢ = dim_{κ(p)} Hⁱ(Dk.functor.obj K)` are finite and only finitely many of them are nonzero, and
there is an `f ∈ R` outside `p` together with a strictly bounded complex over `R_f` whose term in
degree `i` is free of rank exactly `dᵢ` and which represents `Df.functor.obj K` for every datum
`Df` along `R → R_f`.

The data `Dp` and `Dres` along `R → R_p` and `R_p → κ(p)` are used in the proof and do not appear
in the conclusion. The source statement, for the canonical data, is
`StacksDraft.Perfect.exists_away_bounded_free_complex_representing`. -/
theorem exists_away_bounded_free_complex_representing_of_datum
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (Dk : TotalDerivedExtensionScalars.{u, v, u} (algebraMap R p.ResidueField))
    (Dp : TotalDerivedExtensionScalars.{u, v, u}
      (algebraMap R (Localization.AtPrime p)))
    (Dres : TotalDerivedExtensionScalars.{u, v, u}
      (IsLocalRing.residue (Localization.AtPrime p)))
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) :
    let k := p.ResidueField
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj (Dk.functor.obj K)
    (∀ i, Module.Finite k (H i)) ∧
      {i | Module.finrank k (H i) ≠ 0}.Finite ∧
      ∃ f : R, f ∉ p ∧
        ∀ Df : TotalDerivedExtensionScalars.{u, v, u}
            (algebraMap R (Localization.Away f)),
          ∃ (P : CochainComplex (ModuleCat.{max v u} (Localization.Away f)) ℤ) (a b : ℤ),
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
              (∀ i, Nonempty (P.X i ≅ ModuleCat.of (Localization.Away f)
                (ULift.{v} (Fin (Module.finrank k (H i)) → Localization.Away f)))) ∧
              Nonempty ((DerivedCategory.Q).obj P ≅ Df.functor.obj K) := by
  classical
  dsimp only
  let k := p.ResidueField
  let H (i : ℤ) := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
    (Dk.functor.obj K)
  let r (i : ℤ) := Module.finrank k (H i)
  obtain ⟨hfin, hsupp⟩ := finite_fibre_homology_and_support.{u, v} p Dk K hK
  refine ⟨hfin, hsupp, ?_⟩
  obtain ⟨P, aP, bP, hPa, hPb, hPX, ⟨hPK⟩⟩ :=
    exists_bounded_free_atPrime_model.{u, v} p Dk Dp Dres K hK
  obtain ⟨L, aL, bL, hLa, hLb, hLfin, hLproj, ⟨hKL⟩⟩ := hK
  let := hLa
  let := hLb
  let := hPb
  let := hLfin
  let := hLproj
  have hLprojc (i : ℤ) : Projective (L.X i) := inferInstance
  let := hLprojc
  have hLfp (i : ℤ) : Module.FinitePresentation R (L.X i) :=
    Module.finitePresentation_of_projective R (L.X i)
  let := hLfp
  let S := p.primeCompl
  let F := ModuleCat.localizedModuleFunctor.{max v u} S
  let FL := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let X (i : ℤ) := ModuleCat.of R (ULift.{v} (Fin (r i) → R))
  have hXfp (i : ℤ) : Module.FinitePresentation R (X i) :=
    Module.finitePresentation_of_projective R (X i)
  let := hXfp
  have hPproj (i : ℤ) : Projective (P.X i) :=
    Projective.of_iso (hPX i).some.symm inferInstance
  let := hPproj
  have hFLproj (i : ℤ) : Projective (FL.X i) := by
    let e := (localizedModuleFunctorIsoExtendScalars.{u, v} S).app (L.X i)
    apply Projective.of_iso e.symm
    exact (ModuleCat.extendRestrictScalarsAdj _).map_projective (L.X i) inferInstance
  let := hFLproj
  have hFLLE : CochainComplex.IsStrictlyLE FL bL := by dsimp only [FL]; infer_instance
  let := hFLLE
  have hPKp : P.IsKProjective := CochainComplex.isKProjective_of_projective P bP
  let := hPKp
  have hFLKp : CochainComplex.IsKProjective FL := CochainComplex.isKProjective_of_projective FL bL
  let := hFLKp
  obtain ⟨hFL⟩ := localized_complex_represents_derivedExtensionScalars.{u, v} S Dp L bL
  obtain ⟨e⟩ := homotopyEquivOfDerivedIso.{u, v} P FL
    (hPK ≪≫ Dp.functor.mapIso hKL ≪≫ hFL.symm)
  let eX (i : ℤ) : F.obj (X i) ≅ P.X i :=
    (localized_finite_free_iso.{u, v} S (r i)).some ≪≫ (hPX i).some.symm
  obtain ⟨d, hd, ⟨eP⟩⟩ := exists_complex_of_termwise_iso P (fun i => F.obj (X i)) eX
  let T : Set ℤ := Set.Icc aL bL ∪ {i | r i ≠ 0}
  have hT : T.Finite := (Set.finite_Icc aL bL).union hsupp
  have hX (i : ℤ) (hi : i ∉ T) : IsZero (X i) := by
    have hr : r i = 0 := by simpa [T] using (not_or.mp hi).2
    exact isZero_standard_free_of_rank_zero.{u, v} _ hr
  have hLz (i : ℤ) (hi : i ∉ T) : IsZero (L.X i) := by
    have hi' : i ∉ Set.Icc aL bL := fun h => hi (Or.inl h)
    simp only [Set.mem_Icc, not_and_or, not_le] at hi'
    rcases hi' with hi' | hi'
    · exact L.isZero_of_isStrictlyGE aL i hi'
    · exact L.isZero_of_isStrictlyLE bL i (by omega)
  obtain ⟨s, Q, hQX, ⟨eQ⟩⟩ := exists_away_homotopy_model.{u, max v u} S L X T hT hX hLz d hd
    ((HomotopyEquiv.ofIso eP).trans e)
  obtain ⟨a, ha⟩ := hT.bddBelow
  obtain ⟨b, hb⟩ := hT.bddAbove
  refine ⟨s, s.property, fun Df => ?_⟩
  let G := ModuleCat.localizedModuleFunctor.{max v u} (Submonoid.powers (s : R))
  refine ⟨Q, a, b, ?_, ?_, ?_, ?_⟩
  · apply (CochainComplex.isStrictlyGE_iff Q a).2
    intro i hi
    rw [hQX]
    exact G.map_isZero (hX i (fun h => (not_le_of_gt hi) (ha h)))
  · apply (CochainComplex.isStrictlyLE_iff Q b).2
    intro i hi
    rw [hQX]
    exact G.map_isZero (hX i (fun h => (not_le_of_gt hi) (hb h)))
  · intro i
    rw [hQX]
    exact localized_finite_free_iso.{u, v} (Submonoid.powers (s : R)) (r i)
  · obtain ⟨eGL⟩ := localized_complex_represents_derivedExtensionScalars.{u, v}
      (Submonoid.powers (s : R)) Df L bL
    exact ⟨asIso (DerivedCategory.Q.map eQ.hom) ≪≫ eGL ≪≫ (Df.functor.mapIso hKL).symm⟩

/-- **Stacks 0BCD.** Let `R` be a commutative ring, `p` a prime of `R` and `K` a perfect object of
`D(R)`. The dimensions `dᵢ = dim_{κ(p)} Hⁱ(K ⊗ᴸ_R κ(p))` are finite and only finitely many of them
are nonzero, and there is an `f ∈ R` outside `p` together with a strictly bounded complex over
`R_f` whose term in degree `i` is free of rank exactly `dᵢ` and which represents
`K ⊗ᴸ_R R_f`. -/
@[stacks 0BCD]
theorem exists_away_bounded_free_complex_representing
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max v u} R)) (hK : IsPerfect K) :
    let k := p.ResidueField
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
        ((totalDerivedExtensionScalars.{u, u, v} (algebraMap R k)).functor.obj K)
    (∀ i, Module.Finite k (H i)) ∧
      {i | Module.finrank k (H i) ≠ 0}.Finite ∧
      ∃ f : R, f ∉ p ∧
        ∃ (P : CochainComplex (ModuleCat.{max v u} (Localization.Away f)) ℤ) (a b : ℤ),
          P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ i, Nonempty (P.X i ≅ ModuleCat.of (Localization.Away f)
              (ULift.{v} (Fin (Module.finrank k (H i)) → Localization.Away f)))) ∧
            Nonempty ((DerivedCategory.Q).obj P ≅
              (totalDerivedExtensionScalars.{u, u, v}
                (algebraMap R (Localization.Away f))).functor.obj K) := by
  obtain ⟨hfin, hsupp, f, hf, hcont⟩ :=
    exists_away_bounded_free_complex_representing_of_datum.{u, v} p
      (totalDerivedExtensionScalars.{u, u, v} (algebraMap R p.ResidueField))
      (totalDerivedExtensionScalars.{u, u, v} (algebraMap R (Localization.AtPrime p)))
      (totalDerivedExtensionScalars.{u, u, v}
        (IsLocalRing.residue (Localization.AtPrime p))) K hK
  exact ⟨hfin, hsupp, f, hf,
    hcont (totalDerivedExtensionScalars.{u, u, v} (algebraMap R (Localization.Away f)))⟩

/-! ### Bounded free representatives of bounded below pseudo-coherent complexes -/

/-- The terms of a bounded above finite free complex are projective. -/
private theorem projective_term_of_isBoundedAboveFiniteFree {R : Type u} [CommRing R]
    {E : CochainComplex (ModuleCat.{max v u} R) ℤ}
    (hE : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree E) (i : ℤ) : Projective (E.X i) :=
  have := (hE.finiteFree i).2
  ModuleCat.projective_of_free (Module.Free.chooseBasis R _)

/-- A chosen bounded above finite free representative of a pseudo-coherent object computes its
derived base change. -/
private theorem totalDerived_obj_iso_of_representative
    {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (D : TotalDerivedExtensionScalars.{u, v, u} f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (E : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hE : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree E)
    (eE : DerivedCategory.Q.obj E ≅ K) :
    Nonempty (D.functor.obj K ≅ DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E)) := by
  obtain ⟨b, hb⟩ := hE.upperBound
  let := hb
  have hproj := projective_term_of_isBoundedAboveFiniteFree.{u, v} hE
  let := hproj
  have hIso : IsIso (D.comparison.app E) := D.comparison_isIso_of_projective E b
  exact ⟨D.functor.mapIso eE.symm ≪≫ (@asIso _ _ _ _ (D.comparison.app E) hIso) ≪≫
    (Iso.refl _ : (extensionOfScalarsComplexGeneral.{u, v, u} f).obj E ≅
      DerivedCategory.Q.obj _)⟩

/-- Two successive total derived extensions of scalars agree with the total derived extension of
scalars along the composite, on pseudo-coherent objects. -/
private theorem totalDerived_comp_of_isPseudoCoherent
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {f : R →+* A} {g : A →+* B}
    (Df : TotalDerivedExtensionScalars.{u, v, u} f)
    (Dg : TotalDerivedExtensionScalars.{u, v, u} g)
    (Dgf : TotalDerivedExtensionScalars.{u, v, u} (g.comp f))
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    Nonempty (Dg.functor.obj (Df.functor.obj K) ≅ Dgf.functor.obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  let := hb
  have hproj := projective_term_of_isBoundedAboveFiniteFree.{u, v} hE
  let := hproj
  let F := ModuleCat.extendScalars.{u, u, max v u} f
  let EA := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  have hEA : CochainComplex.IsStrictlyLE EA b := by dsimp only [EA]; infer_instance
  let := hEA
  have hEAproj (i : ℤ) : Projective (EA.X i) :=
    projective_extendScalars.{u, v} f (E.X i) (hproj i)
  let := hEAproj
  have hf : IsIso (Df.comparison.app E) := Df.comparison_isIso_of_projective E b
  have hg : IsIso (Dg.comparison.app EA) := Dg.comparison_isIso_of_projective EA b
  have hgf : IsIso (Dgf.comparison.app E) := Dgf.comparison_isIso_of_projective E b
  exact ⟨Dg.functor.mapIso (Df.functor.mapIso e.symm ≪≫
      @asIso _ _ _ _ (Df.comparison.app E) hf) ≪≫
    @asIso _ _ _ _ (Dg.comparison.app EA) hg ≪≫
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max v u} f g)
        (ComplexShape.up ℤ)) DerivedCategory.Q).symm.app E ≪≫
    (@asIso _ _ _ _ (Dgf.comparison.app E) hgf).symm ≪≫ Dgf.functor.mapIso e⟩

/-- The composite comparison, stated for a ring map presented as a composite by an equation
rather than syntactically. -/
theorem totalDerived_comp_of_isPseudoCoherent_of_eq
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] {f : R →+* A} {g : A →+* B}
    {h : R →+* B} (hcomp : g.comp f = h)
    (Df : TotalDerivedExtensionScalars.{u, v, u} f)
    (Dg : TotalDerivedExtensionScalars.{u, v, u} g)
    (Dh : TotalDerivedExtensionScalars.{u, v, u} h)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    Nonempty (Dg.functor.obj (Df.functor.obj K) ≅ Dh.functor.obj K) := by
  subst hcomp
  exact totalDerived_comp_of_isPseudoCoherent.{u, v} Df Dg Dh hK

/-- Derived localization away from an element agrees with total derived extension of scalars to
the localization: both are left derived functors of the same functor. -/
private noncomputable def localizationAwayFunctorIsoTotalDerived
    {R : Type u} [CommRing R] (f : R)
    (D : TotalDerivedExtensionScalars.{u, v, u}
      (algebraMap R (Localization.Away f))) :
    PseudoCoherence.localizationAwayFunctorAux.{u, v} f ≅ D.functor := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away f))
  let : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away f) (Submonoid.powers f)))
  let : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u}
      (algebraMap R (Localization.Away f))).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactors
  change F.mapDerivedCategory ≅ D.functor
  let comparison : DerivedCategory.Q ⋙ D.functor ⟶
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  have : D.functor.IsLeftDerivedFunctor comparison W := D.isLeftDerived
  exact Functor.leftDerivedUnique (LF := F.mapDerivedCategory) (LF' := D.functor)
    (α := F.mapDerivedCategoryFactors.hom) (α'₂ := comparison) (W := W)

/-- Vanishing of one cohomology module of the derived fibre, read off a total derived extension of
scalars datum, is the condition [stacks 068U] consumes. -/
private theorem fibreCohomologyVanishes_of_isZero_homology
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (Dk : TotalDerivedExtensionScalars.{u, v, u} (algebraMap R p.ResidueField))
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.ResidueField) i).obj
      (Dk.functor.obj K))) :
    FibreCohomologyVanishes.{u, v} p K i := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  refine ⟨E, hE, ⟨eE⟩, ?_⟩
  obtain ⟨e⟩ := totalDerived_obj_iso_of_representative.{u, v} Dk E hE eE
  have h1 : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} p.ResidueField) i).obj
      (DerivedCategory.Q.obj (residueFieldComplex.{u, v} p E))) :=
    hz.of_iso ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} p.ResidueField) i).mapIso e.symm)
  exact h1.of_iso ((DerivedCategory.homologyFunctorFactors
    (ModuleCat.{max v u} p.ResidueField) i).app (residueFieldComplex.{u, v} p E)).symm

/-- Derived localization away from an element preserves lower cohomological bounds. -/
private theorem localizationAway_isGE {R : Type u} [CommRing R] (f : R)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (c : ℤ) (hK : K.IsGE c) :
    ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K).IsGE c := by
  rw [DerivedCategory.isGE_iff] at hK ⊢
  intro i hi
  exact (Functor.map_isZero (ModuleCat.extendScalars
    (algebraMap R (Localization.Away f))) (hK i hi)).of_iso
      ((localizationAwayHomologyFunctorIso.{u, v} f i).app K)

/-- A complex whose degreewise ranks vanish below `a` is strictly bounded below by `a`. -/
private theorem strictLowerBound_of_rank_zero {R : Type u} [CommRing R]
    (complex : CochainComplex (ModuleCat.{max v u} R) ℤ) (rank : ℤ → ℕ) (lower : ℤ)
    (hterms : ∀ i : ℤ, Nonempty (complex.X i ≅
      ModuleCat.of R (ULift.{v} (Fin (rank i) → R))))
    (hzero : ∀ i : ℤ, i < lower → rank i = 0) :
    complex.IsStrictlyGE lower := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  obtain ⟨e⟩ := hterms i
  exact (isZero_standard_free_of_rank_zero.{u, v} _ (hzero i hi)).of_iso e

/-- Refine a principal open of a principal localization to a principal open of the base: an
element of `R_f` outside the image of `p` is, up to associates, the image of an element of `R`
outside `p`, and the two localizations agree. -/
private theorem exists_principal_refinement
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (f : R) (hf : f ∉ p)
    (g : Localization.Away f) (hg : g ∉ p.map (algebraMap R (Localization.Away f))) :
    ∃ h : R, h ∉ p ∧ IsLocalization.Away h (Localization.Away g) := by
  let n := (IsLocalization.Away.sec f g).1
  have hassoc := IsLocalization.Away.associated_sec_fst (S := Localization.Away f) f g
  have hn : n ∉ p := by
    intro hmem
    exact hg ((Ideal.mem_iff_of_associated hassoc).mp
      (Ideal.mem_map_of_mem (algebraMap R (Localization.Away f)) hmem))
  exact ⟨f * n, ‹p.IsPrime›.mul_notMem hf hn, .mul_of_associated _ _ g hassoc⟩

/-- Extension of scalars along a homomorphism of fields is exact. -/
private theorem extendScalars_field_exact {k l : Type u} [Field k] [Field l] (φ : k →+* l) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} φ) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, max v u} φ) := by
  let F := ModuleCat.extendScalars.{u, u, max v u} φ
  let : Algebra k l := φ.toAlgebra
  have hflat : RingHom.Flat φ := by
    rw [← φ.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
    infer_instance
  refine ⟨extendScalars_preservesFiniteLimits_of_flat'.{u, v} φ hflat, ?_⟩
  let : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{max v u, u, u} φ).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits F

/-- The fibre dimensions of a pseudo-coherent object are unchanged by enlarging the residue
field along a homomorphism: the derived fibre over the larger field is the base change of the
derived fibre over the smaller one. -/
private theorem finrank_homology_totalDerived_comp
    {R : Type u} [CommRing R] {k l : Type u} [Field k] [Field l]
    {ψ : R →+* k} {χ : R →+* l} {φ : k →+* l} (hφ : φ.comp ψ = χ)
    (Dψ : TotalDerivedExtensionScalars.{u, v, u} ψ)
    (Dχ : TotalDerivedExtensionScalars.{u, v, u} χ)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    Module.finrank l ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} l) i).obj
        (Dχ.functor.obj K)) =
      Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
        (Dψ.functor.obj K)) := by
  subst hφ
  obtain ⟨E, hE, ⟨eE⟩⟩ := hK
  obtain ⟨eψ⟩ := totalDerived_obj_iso_of_representative.{u, v} Dψ E hE eE
  obtain ⟨eχ⟩ := totalDerived_obj_iso_of_representative.{u, v} Dχ E hE eE
  let Eψ := ((ModuleCat.extendScalars.{u, u, max v u} ψ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj E
  let G := ModuleCat.extendScalars.{u, u, max v u} φ
  obtain ⟨hGlim, hGcolim⟩ := extendScalars_field_exact.{u, v} φ
  let := hGlim
  let := hGcolim
  have hψ : Module.finrank k ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} k) i).obj (Dψ.functor.obj K)) = Module.finrank k (Eψ.homology i) :=
    (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).mapIso eψ ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} k) i).app
        Eψ).toLinearEquiv).finrank_eq
  have hχ : Module.finrank l ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} l) i).obj (Dχ.functor.obj K)) =
      Module.finrank l (G.obj (Eψ.homology i)) := by
    refine (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} l) i).mapIso eχ ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} l) i).app _ ≪≫
      ?_).toLinearEquiv).finrank_eq
    exact (HomologicalComplex.homologyFunctor (ModuleCat.{max v u} l) (ComplexShape.up ℤ)
        i).mapIso ((NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp.{u, max v u} ψ φ) (ComplexShape.up ℤ)).app E) ≪≫
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso G
        (ComplexShape.up ℤ) i).app Eψ
  rw [hψ, hχ]
  let := (hE.finiteFree i)
  exact finrank_extendScalars.{u, v} φ (Eψ.homology i)

set_option backward.isDefEq.respectTransparency false in
/-- Extension of scalars carries the standard finite free module to the standard finite free
module of the same rank: base change of the standard basis is a basis. -/
theorem extendScalars_standard_free_iso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (n : ℕ) :
    Nonempty ((ModuleCat.extendScalars.{u, u, max v u} φ).obj
        (ModuleCat.of A (ULift.{v} (Fin n → A))) ≅
      ModuleCat.of B (ULift.{v} (Fin n → B))) := by
  let M := ModuleCat.of A (ULift.{v} (Fin n → A))
  let b : Module.Basis (Fin n) A M := (Pi.basisFun A (Fin n)).map ULift.moduleEquiv.symm
  let : Algebra A B := φ.toAlgebra
  have heq : (inferInstance : Module A B) = Module.compHom B φ :=
    Module.ext' _ _ (by intro r s; rfl)
  cases heq
  exact ⟨((Algebra.TensorProduct.basis B b).equivFun.trans
    ULift.moduleEquiv.symm).toModuleIso⟩

/-- A bounded below pseudo-coherent object whose derived fibre at `p` has no cohomology below `a`
becomes perfect after localizing away from a single element outside `p`. -/
private theorem exists_away_isPerfect_of_fibre_vanishing
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (hbounded : ∃ c : ℤ, K.IsGE c) (a : ℤ)
    (hvanish : ∀ i : ℤ, i < a → FibreCohomologyVanishes.{u, v} p K i) :
    ∃ f : R, f ∉ p ∧ IsPerfect ((PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K) := by
  obtain ⟨c, hc⟩ := hbounded
  have hd : min a c - 1 < a := by omega
  obtain ⟨f, hf, hperfect, _, _⟩ :=
    exists_localization_iso_biprod_truncGE_truncLE.{u, v} p K hK (min a c - 1)
      (hvanish (min a c - 1) hd)
  refine ⟨f, hf, ?_⟩
  let Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} f).obj K
  let := hc
  have hKf : Kf.IsGE (min a c) := localizationAway_isGE.{u, v} f K (min a c)
    (DerivedCategory.TStructure.t.isGE_of_ge K (min a c) c (min_le_right _ _))
  let := hKf
  obtain ⟨P, l, r, hPge, hPle, hPfin, hPproj, ⟨eP⟩⟩ := hperfect
  have eP' : (DerivedCategory.TStructure.t.truncGE (min a c)).obj Kf ≅
      DerivedCategory.Q.obj P := by simpa using eP
  exact ⟨P, l, r, hPge, hPle, hPfin, hPproj,
    ⟨asIso ((DerivedCategory.TStructure.t.truncGEπ (min a c)).app Kf) ≪≫ eP'⟩⟩

/-- Perfectness transports along an isomorphism in the derived category. -/
private theorem isPerfect_of_iso {A : Type u} [CommRing A]
    {X Y : DerivedCategory (ModuleCat.{max v u} A)} (e : X ≅ Y) (hX : IsPerfect X) :
    IsPerfect Y := by
  obtain ⟨P, l, r, h₁, h₂, h₃, h₄, ⟨eP⟩⟩ := hX
  exact ⟨P, l, r, h₁, h₂, h₃, h₄, ⟨e.symm ≪≫ eP⟩⟩

-- The proof threads six total derived extension-of-scalars data through three successive
-- localizations, and the resulting dependent instance goals exceed the default budget.
set_option backward.isDefEq.respectTransparency false in
/-- The general form of [stacks 0BYP], for arbitrary total derived extension-of-scalars data: let
`R` be a commutative ring, `p` a prime of `R` and `K` a pseudo-coherent object of `D(R)` which is
bounded below. Set `dᵢ = dim_{κ(p)} Hⁱ(Dk.functor.obj K)`. If `dᵢ = 0` for all `i < a`, then there
is an `f ∈ R` outside `p` such that `Df.functor.obj K` is perfect, for every datum `Df` along
`R → R_f`, and is represented by a complex over `R_f` concentrated in degrees `[a, b]` whose term
in degree `i` is free of rank exactly `dᵢ`.

The hypothesis `hD` asks for a datum along every homomorphism of rings in the ambient universe,
which the proof needs for rings produced only during the argument. The source statement, for the
canonical data, is
`StacksDraft.Perfect.exists_away_bounded_free_complex_representing_of_fibre_vanishing_below`. -/
theorem exists_away_bounded_free_complex_representing_of_fibre_vanishing_below_of_datum
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (Dk : TotalDerivedExtensionScalars.{u, v, u} (algebraMap R p.ResidueField))
    (hD : ∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B),
      Nonempty (TotalDerivedExtensionScalars.{u, v, u} φ))
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hbounded : ∃ c : ℤ, K.IsGE c) (a : ℤ) :
    let k := p.ResidueField
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj (Dk.functor.obj K)
    (∀ i : ℤ, i < a → IsZero (H i)) →
      ∃ f : R, f ∉ p ∧
        ∀ Df : TotalDerivedExtensionScalars.{u, v, u}
            (algebraMap R (Localization.Away f)),
          IsPerfect (Df.functor.obj K) ∧
            ∃ (P : CochainComplex (ModuleCat.{max v u} (Localization.Away f)) ℤ) (b : ℤ),
              P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
                (∀ i : ℤ, Nonempty (P.X i ≅ ModuleCat.of (Localization.Away f)
                  (ULift.{v} (Fin (Module.finrank k (H i)) → Localization.Away f)))) ∧
                Nonempty (DerivedCategory.Q.obj P ≅ Df.functor.obj K) := by
  classical
  intro k H hvanish
  have hrankzero : ∀ i : ℤ, i < a → Module.finrank k (H i) = 0 := by
    intro i hi
    exact finrank_eq_zero_of_isZero.{u, v} (hvanish i hi)
  have hfv : ∀ i : ℤ, i < a → FibreCohomologyVanishes.{u, v} p K i := fun i hi =>
    fibreCohomologyVanishes_of_isZero_homology.{u, v} p Dk hK i (hvanish i hi)
  obtain ⟨f₀, hf₀, hperf₀⟩ :=
    exists_away_isPerfect_of_fibre_vanishing.{u, v} p K hK hbounded a hfv
  let Rf := Localization.Away f₀
  let Df₀ := (hD R Rf (algebraMap R Rf)).some
  have hKf : IsPerfect (Df₀.functor.obj K) :=
    isPerfect_of_iso.{u, v} ((localizationAwayFunctorIsoTotalDerived.{u, v} f₀ Df₀).app K)
      hperf₀
  have hdisj : Disjoint (Submonoid.powers f₀ : Set R) p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f₀).2 hf₀
  let q : Ideal Rf := p.map (algebraMap R Rf)
  have hqprime : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) Rf p ‹_› hdisj
  let := hqprime
  have hcomap : p = q.comap (algebraMap R Rf) :=
    (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f₀) Rf ‹_› hdisj).symm
  let φ : p.ResidueField →+* q.ResidueField :=
    Ideal.ResidueField.map p q (algebraMap R Rf) hcomap
  have hφ : φ.comp (algebraMap R p.ResidueField) =
      (algebraMap Rf q.ResidueField).comp (algebraMap R Rf) := by
    ext r
    simp [φ]
  let Dq := (hD Rf q.ResidueField (algebraMap Rf q.ResidueField)).some
  let Dχ := (hD R q.ResidueField
    ((algebraMap Rf q.ResidueField).comp (algebraMap R Rf))).some
  have hrankeq : ∀ i : ℤ, Module.finrank q.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} q.ResidueField) i).obj
        (Dq.functor.obj (Df₀.functor.obj K))) = Module.finrank k (H i) := by
    intro i
    obtain ⟨ec⟩ := totalDerived_comp_of_isPseudoCoherent.{u, v} Df₀ Dq Dχ hK
    rw [((DerivedCategory.homologyFunctor (ModuleCat.{max v u} q.ResidueField) i).mapIso
      ec).toLinearEquiv.finrank_eq]
    exact finrank_homology_totalDerived_comp.{u, v} hφ Dk Dχ hK i
  obtain ⟨_, _, g, hg, hcont⟩ :=
    exists_away_bounded_free_complex_representing_of_datum.{u, v} q Dq
      (hD Rf (Localization.AtPrime q) (algebraMap Rf (Localization.AtPrime q))).some
      (hD (Localization.AtPrime q) (IsLocalRing.ResidueField (Localization.AtPrime q))
        (IsLocalRing.residue (Localization.AtPrime q))).some
      (Df₀.functor.obj K) hKf
  obtain ⟨h, hh, hloc⟩ := exists_principal_refinement p f₀ hf₀ g hg
  refine ⟨h, hh, fun Dh => ?_⟩
  let Lg := Localization.Away g
  let Lh := Localization.Away h
  let := hloc
  let e : Lg ≃ₐ[R] Lh := IsLocalization.algEquiv (Submonoid.powers h) Lg Lh
  let Dg := (hD Rf Lg (algebraMap Rf Lg)).some
  let Dgc := (hD R Lg ((algebraMap Rf Lg).comp (algebraMap R Rf))).some
  let De := (hD Lg Lh e.toRingEquiv.toRingHom).some
  obtain ⟨P, a', b', hPge, hPle, hPX, ⟨hPK⟩⟩ := hcont Dg
  obtain ⟨eg⟩ := totalDerived_comp_of_isPseudoCoherent.{u, v} Df₀ Dg Dgc hK
  let Φ := ModuleCat.extendScalars.{u, u, max v u} e.toRingEquiv.toRingHom
  let P' := (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hP'X : ∀ i : ℤ, Nonempty (P'.X i ≅
      ModuleCat.of Lh (ULift.{v} (Fin (Module.finrank k (H i)) → Lh))) := by
    intro i
    obtain ⟨ei⟩ := hPX i
    rw [hrankeq i] at ei
    exact ⟨Φ.mapIso ei ≪≫
      (extendScalars_standard_free_iso.{u, v} e.toRingEquiv.toRingHom _).some⟩
  have hP'ge : CochainComplex.IsStrictlyGE P' a :=
    strictLowerBound_of_rank_zero.{u, v} P' (fun i => Module.finrank k (H i)) a hP'X hrankzero
  have hP'le : CochainComplex.IsStrictlyLE P' b' := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    let := hPle
    exact Φ.map_isZero (P.isZero_of_isStrictlyLE b' i hi)
  have hP'fin : ∀ i : ℤ, Module.Finite Lh (P'.X i) := fun i =>
    Module.Finite.equiv (hP'X i).some.toLinearEquiv.symm
  have hP'proj : ∀ i : ℤ, Module.Projective Lh (P'.X i) := fun i =>
    Module.Projective.of_equiv (hP'X i).some.toLinearEquiv.symm
  have hproj (i : ℤ) : Projective (P.X i) := by
    let := (hPX i).some
    exact Projective.of_iso (hPX i).some.symm
      (ModuleCat.projective_of_free (Module.Free.chooseBasis Lg _))
  let := hproj
  let := hPle
  have hcomp : e.toRingEquiv.toRingHom.comp ((algebraMap Rf Lg).comp (algebraMap R Rf)) =
      algebraMap R Lh := by
    ext r
    change e ((algebraMap Rf Lg) ((algebraMap R Rf) r)) = algebraMap R Lh r
    rw [← IsScalarTower.algebraMap_apply R Rf Lg]
    exact e.commutes r
  have hDeIso : IsIso (De.comparison.app P) := De.comparison_isIso_of_projective P b'
  obtain ⟨eh⟩ := totalDerived_comp_of_isPseudoCoherent_of_eq.{u, v} hcomp Dgc De Dh hK
  have eFinal : DerivedCategory.Q.obj P' ≅ Dh.functor.obj K :=
    (Iso.refl _ : DerivedCategory.Q.obj P' ≅
        (extensionOfScalarsComplexGeneral.{u, v, u}
          e.toRingEquiv.toRingHom).obj P).symm ≪≫
      (@asIso _ _ _ _ (De.comparison.app P) hDeIso).symm ≪≫
      De.functor.mapIso (hPK ≪≫ eg) ≪≫ eh
  exact ⟨⟨P', a, b', hP'ge, hP'le, hP'fin, hP'proj, ⟨eFinal.symm⟩⟩,
    P', b', hP'ge, hP'le, hP'X, ⟨eFinal⟩⟩

/-- **Stacks 0BYP.** Let `R` be a commutative ring, `p` a prime of `R` and `K` a pseudo-coherent
object of `D(R)` which is bounded below. Set `dᵢ = dim_{κ(p)} Hⁱ(K ⊗ᴸ_R κ(p))`. If `dᵢ = 0` for
all `i < a`, then there is an `f ∈ R` outside `p` such that `K ⊗ᴸ_R R_f` is perfect and is
represented by a complex over `R_f` concentrated in degrees `[a, b]` whose term in degree `i` is
free of rank exactly `dᵢ`. -/
@[stacks 0BYP]
theorem exists_away_bounded_free_complex_representing_of_fibre_vanishing_below
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hbounded : ∃ c : ℤ, K.IsGE c) (a : ℤ) :
    let k := p.ResidueField
    let H := fun i : ℤ =>
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} k) i).obj
        ((totalDerivedExtensionScalars.{u, u, v} (algebraMap R k)).functor.obj K)
    (∀ i : ℤ, i < a → IsZero (H i)) →
      ∃ f : R, f ∉ p ∧
        let Kf := (totalDerivedExtensionScalars.{u, u, v}
          (algebraMap R (Localization.Away f))).functor.obj K
        IsPerfect Kf ∧
          ∃ (P : CochainComplex (ModuleCat.{max v u} (Localization.Away f)) ℤ) (b : ℤ),
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
              (∀ i : ℤ, Nonempty (P.X i ≅ ModuleCat.of (Localization.Away f)
                (ULift.{v} (Fin (Module.finrank k (H i)) → Localization.Away f)))) ∧
              Nonempty (DerivedCategory.Q.obj P ≅ Kf) := by
  intro k H hvanish
  obtain ⟨f, hf, hcont⟩ :=
    exists_away_bounded_free_complex_representing_of_fibre_vanishing_below_of_datum.{u, v} p
      (totalDerivedExtensionScalars.{u, u, v} (algebraMap R p.ResidueField))
      (fun A B _ _ φ => totalDerivedExtensionScalars_exists.{u, u, v} φ)
      K hK hbounded a hvanish
  exact ⟨f, hf, hcont (totalDerivedExtensionScalars.{u, u, v}
    (algebraMap R (Localization.Away f)))⟩

end StacksDraft.Perfect
