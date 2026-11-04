module

public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeChase
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeDiagonalRepresentation
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorChain
public import StacksFrontier.RingTheory.Flat.DegreewiseChaseCycles

/-!
# The "moreover" clause of [stacks 0E2F] from the residue-field vanishing

Let `R → A` be flat of finite presentation with `B = A ⊗[R] A` Noetherian, and let `K` be a
relative dualizing complex for `R → A`.  Suppose that at every prime `𝔭` of `R` the cohomology of
`RHom_{B_𝔭}(A_𝔭, K_𝔭 ⊗ᴸ_{A_𝔭} B_𝔭)` vanishes outside degree zero, the subscript denoting base
change to the residue field `κ(𝔭)`.  This is the hypothesis under which
`Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldVanishing` proves clause (2), and
this file proves the "moreover" clause under it: for every `R → R'` the derived base change of a
generator of `Hom_{D(B)}(A, K ⊗ᴸ_A B)` generates `Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B')`.

The proof is the source's: [stacks 0E1U] represents `RHom_B(A, K ⊗ᴸ_A B)` by the Hom complex
`E^• = Hom^•_B(P^•, F^•)`, compatibly with base change; the degreewise chase makes the degree-zero
cycles of `E^•` commute with base change
(`StacksDraft.DegreewiseChase.isIso_cyclesComparison_includeLeft`), which "gives the final
assertion of the lemma"; and `Dualizing.isPostcompGenerator_derivedExtension_map` reads that on
the derived category.

## Main results

* `Dualizing.envelopingBaseChangeRingHom_eq` — the ring map along which the clause base changes
  `ξ` is the map of diagonals `Dualizing.diagonalBaseChangeMap`.
* `Dualizing.isGeneratorPreservingAt_of_residueFieldVanishing` — **the clause, from the
  residue-field vanishing.**

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars StacksDraft.DegreewiseChase

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

noncomputable section

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']

/-- The ring map `A ⊗[R] A → A' ⊗[R'] A'` along which the "moreover" clause base changes the
generator is the map of diagonals. -/
theorem envelopingBaseChangeRingHom_eq :
    envelopingBaseChangeRingHom R A R' = diagonalBaseChangeMap R A R' := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a₁ a₂ =>
      rw [diagonalBaseChangeMap_tmul]
      show ((a₁ ⊗ₜ[R] (1 : R')) ⊗ₜ[R'] (1 : A ⊗[R] R')) *
          ((1 : A ⊗[R] R') ⊗ₜ[R'] (a₂ ⊗ₜ[R] (1 : R'))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable [Module.Flat R A] [Algebra.FinitePresentation R A]

/-- **The "moreover" clause of [stacks 0E2F], from the residue-field vanishing.**  Let `R → A` be
flat of finite presentation with `A ⊗[R] A` Noetherian, and let `K` be a relative dualizing
complex for `R → A` such that at every prime `𝔭` of `R` the derived Hom from the diagonal into the
base change of `K` to `κ(𝔭)` has no cohomology outside degree zero.  Then for every `R → R'`,
derived base change along `A ⊗[R] A → A' ⊗[R'] A'` carries every generator of
`Hom_{D(A ⊗[R] A)}(A, K ⊗ᴸ_A (A ⊗[R] A))` to a generator.

The residue-field vanishing is the hypothesis `hres` of
`Dualizing.isRelativeDualizingComplex_baseChange_of_residueFieldVanishing`, and nothing else is
assumed: the representatives come from [stacks 0E1U]
(`Dualizing.exists_diagonalHomComplexRepresentation_canonical`), the base change of the
degree-zero cycles from the degreewise chase, and the rest from
`Dualizing.isPostcompGenerator_derivedExtension_map`. -/
theorem isGeneratorPreservingAt_of_residueFieldVanishing [IsNoetherianRing (A ⊗[R] A)]
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hres : ∀ (p : Ideal R) [p.IsPrime] (j : ℤ), j ≠ 0 → Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] ResidueFieldAt R p)) j).obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul' (ResidueFieldAt R p) :
              (A ⊗[R] ResidueFieldAt R p) ⊗[ResidueFieldAt R p]
                (A ⊗[R] ResidueFieldAt R p) →ₐ[ResidueFieldAt R p]
                (A ⊗[R] ResidueFieldAt R p)).toRingHom).obj
          (diagonalBaseChangeTarget R A (ResidueFieldAt R p) K)))) :
    IsGeneratorPreservingAt R A R' K := by
  obtain ⟨P, F, dP, d, hPLE, hPproj, hPkflat, ⟨eP⟩, hFLE, hFflat, ⟨eF⟩, hbc, hEflat, hEfin⟩ :=
    exists_diagonalHomComplexRepresentation_canonical R A K hK
  have := hPLE
  have := hPproj
  have := hFLE
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P dP
  let E := CochainComplex.HomComplexR (A ⊗[R] A) P F
  have hE : ∀ (S' : Type u) [CommRing S'] [Algebra R S'],
      Nonempty ((diagonalIncludeLeftExtend R A S').obj E ≅
        CochainComplex.HomComplexR ((A ⊗[R] A) ⊗[R] S')
          ((diagonalIncludeLeftExtend R A S').obj P)
          ((diagonalIncludeLeftExtend R A S').obj F)) :=
    fun S' _ _ => ⟨(hbc S').choose⟩
  let ι : (A ⊗[R] A) →+* (A ⊗[R] A) ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
  -- the degree-zero cycles of `E^•` base change: the degreewise chase
  have hcyc : IsIso (StacksDraft.HomologyBaseChange.cyclesComparison ι E 0) := by
    have := hEfin (0 + 1)
    refine isIso_cyclesComparison_includeLeft R (A ⊗[R] A) R' E 0 hEflat (fun p _ => ?_)
    have h := exact_rTensor_residueField_of_isZero_homology R A K P dP hPkflat eP F d hFflat eF E
      hE p 1 (hres p 1 one_ne_zero)
    rw [show (1 : ℤ) - 1 = 0 from by ring, show (1 : ℤ) + 1 = 2 from by ring] at h
    rw [show (0 : ℤ) + 1 = 1 from by ring, show (0 : ℤ) + 2 = 2 from by ring]
    exact h
  -- the endomorphisms of the diagonal are scalars
  have hscal : ∀ a : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj P,
      ∃ s : A ⊗[R] A, a = s • 𝟙 _ := by
    intro a
    obtain ⟨b, hb⟩ := diagonal_endomorphism_eq_smul_id R A (eP.inv ≫ a ≫ eP.hom)
    refine ⟨b, ?_⟩
    have : a = eP.hom ≫ (eP.inv ≫ a ≫ eP.hom) ≫ eP.inv := by simp
    rw [this, hb, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.hom_inv_id]
  -- a generator, represented by a chain map
  obtain ⟨ξ, hξ⟩ := exists_isPostcompGenerator hK
  have hξ' : IsPostcompGenerator (eP.hom ≫ ξ ≫ eF.inv) := hξ.conj eP.symm eF.symm
  obtain ⟨f₀, hf₀⟩ := Q_map_surjective_of_isKProjective P F (eP.hom ≫ ξ ≫ eF.inv)
  rw [← hf₀] at hξ'
  -- the comparisons at the two representatives
  let D := totalDerivedExtensionScalars.{u, u, u} ι
  have hPcmp : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hPkflat
  have hFcmp : IsIso (D.comparison.app F) := by
    have : Module.Flat R (A ⊗[R] A) := Module.Flat.trans R A (A ⊗[R] A)
    have : CochainComplex.IsStrictlyLE (((ModuleCat.restrictScalars
        (algebraMap R (A ⊗[R] A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) d :=
      (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff F
        (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))) d).2 inferInstance
    have : ∀ n : ℤ, Module.Flat R ((((ModuleCat.restrictScalars
        (algebraMap R (A ⊗[R] A))).mapHomologicalComplex (ComplexShape.up ℤ)).obj F).X n) :=
      hFflat
    exact RingTheory.TorIndependence.isIso_comparison_of_kFlat_restrictScalars
      (R := R) (A := A ⊗[R] A) (B := R') (T := (A ⊗[R] A) ⊗[R] R')
      RingTheory.TorIndependence.torIndependent_of_flat_left F
      (CochainComplex.KFlat.kFlat_of_flat _ d)
  obtain ⟨e, he⟩ := hbc R'
  have hD : IsPostcompGenerator (D.functor.map (DerivedCategory.Q.map f₀)) :=
    isPostcompGenerator_derivedExtension_map ι P F dP hPcmp hFcmp e he hcyc hscal f₀ hξ'
  -- from the left coprojection `B → B ⊗[R] R'` to the map of diagonals `B → B'`
  let eC : ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) ≃+* ((A ⊗[R] A) ⊗[R] R') :=
    (diagonalBaseChangeEquiv R A R').toRingEquiv.symm
  let h : (A ⊗[R] A) →+* ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')) :=
    eC.symm.toRingHom.comp (ι.comp (RingEquiv.refl (A ⊗[R] A)).toRingHom)
  have hh : h = envelopingBaseChangeRingHom R A R' := by
    rw [envelopingBaseChangeRingHom_eq]
    rfl
  let G := totalDerivedExtensionScalars.{u, u, u} h
  have : D.functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ D.functor ⟶
        (ModuleCat.extendScalars.{u, u, u} ι).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from D.comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{u} (A ⊗[R] A)) (ComplexShape.up ℤ)) :=
    D.isLeftDerived
  have : G.functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ G.functor ⟶
        (ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from G.comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{u} (A ⊗[R] A)) (ComplexShape.up ℤ)) :=
    G.isLeftDerived
  have eG := StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight.{u}
    eC ι D.functor D.comparison G.functor G.comparison
  have hG : IsPostcompGenerator
      ((totalDerivedExtensionScalars.{u, u, u} h).functor.map (DerivedCategory.Q.map f₀)) :=
    IsPostcompGenerator.map_natIso eG.symm (hD.map _)
  rw [hh] at hG
  let eP' : DerivedCategory.Q.obj P ≅ diagonalSingle R A := eP
  refine isGeneratorPreservingAt_of_exists ⟨eP'.inv ≫ DerivedCategory.Q.map f₀ ≫ eF.hom,
    hξ'.conj eP' eF, ?_⟩
  refine (hG.conj
    ((totalDerivedExtensionScalars.{u, u, u} (envelopingBaseChangeRingHom R A R')).functor.mapIso
      eP')
    ((totalDerivedExtensionScalars.{u, u, u} (envelopingBaseChangeRingHom R A R')).functor.mapIso
      eF)).of_conj (Iso.refl _) (Iso.refl _) ?_
  simp only [Functor.mapIso_inv, Functor.mapIso_hom, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id]
  rw [Functor.map_comp, Functor.map_comp]

end

end Dualizing

end
