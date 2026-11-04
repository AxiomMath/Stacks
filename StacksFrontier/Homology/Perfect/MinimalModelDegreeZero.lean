module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Perfect.ConeDegreeZeroLift
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsChainModel
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsAdjunctionComp

/-!
# A model of a pseudo-coherent complex over a local ring, minimal in degree zero

Let `R` be a local ring with residue field `κ` and let `K` be a bounded above complex of flat
`R`-modules whose image in `D(R)` is pseudo-coherent and whose fibre `K ⊗_R κ` has no
cohomology in degree `-1`. `StacksDraft.MinimalModel.exists_minimal_model` produces a complex
`P` together with a quasi-isomorphism `u : P ⟶ K` such that `P⁻¹ = 0`, `P⁰` is finite free, and
`P` is *minimal in degree zero*: the differential `P⁰ → P¹` vanishes modulo the maximal ideal,
and an element of `P⁰` whose image in `K ⊗ κ` is a coboundary vanishes modulo the maximal ideal.

`P` is the minimal free representative of
[Stacks, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC),
whose term in degree `i` has rank `dim_κ Hⁱ(K ⊗ᴸ κ)`; that `u` can be taken to be a map of
complexes is K-projectivity of `P`. Minimality in degree zero is a dimension count: `P ⊗ κ`
computes `H⁰(K ⊗ κ)`, which has the dimension of `P⁰ ⊗ κ`, so the differential out of degree
zero of `P ⊗ κ` vanishes.

These are exactly the hypotheses `hmin₁` and `hmin₂` of
`StacksDraft.ConeLift.exists_cocycle_lift`.

## Main results

* `StacksDraft.MinimalModel.exists_minimal_model`: the model described above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open StacksDraft.ConeLift (bcObj bcMap bcUnit)

universe u

namespace StacksDraft.MinimalModel

attribute [local instance 10000] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- The degree-zero cohomology of a complex vanishing in degree `-1` is the kernel of its
differential out of degree zero. -/
noncomputable def homologyZeroEquivKer {S : Type u} [Ring S]
    (X : CochainComplex (ModuleCat.{u} S) ℤ) (hX : IsZero (X.X (-1))) :
    X.homology 0 ≃ₗ[S] LinearMap.ker (X.d 0 1).hom :=
  ((X.isoHomologyπ (-1) 0 (by simp) (hX.eq_of_src _ _)).symm ≪≫
    ShortComplex.cyclesMapIso (X.isoSc' (-1) 0 1 (by simp) (by simp)) ≪≫
    ShortComplex.moduleCatCyclesIso _).toLinearEquiv

/-- The universe lift of the coordinate space `Fin n → k` over a field `k` has dimension `n`. -/
theorem finrank_ulift_fin_fun {k : Type u} [Field k] (n : ℕ) :
    Module.finrank k (ULift.{u} (Fin n → k)) = n := by
  rw [ULift.moduleEquiv.finrank_eq, Module.finrank_fin_fun]

/-- **A model, minimal in degree zero, of a pseudo-coherent complex over a local ring.** See
the module documentation. -/
theorem exists_minimal_model [IsLocalRing R] (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, Module.Flat R (K.X i)]
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj K))
    (hneg : IsZero ((((ModuleCat.extendScalars.{u, u, u}
        (IsLocalRing.residue R)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology (-1))) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (u : P ⟶ K), QuasiIso u ∧ IsZero (P.X (-1)) ∧
      Module.Free R (P.X 0) ∧ Module.Finite R (P.X 0) ∧
      (∀ q : P.X 0, (bcUnit (IsLocalRing.residue R) (P.X 1)).hom ((P.d 0 1).hom q) = 0) ∧
      (∀ q : P.X 0, (∃ w : bcObj (IsLocalRing.residue R) (K.X (-1)),
          (bcMap (IsLocalRing.residue R) (K.d (-1) 0)).hom w =
            (bcUnit (IsLocalRing.residue R) _).hom ((u.f 0).hom q)) →
        (bcUnit (IsLocalRing.residue R) (P.X 0)).hom q = 0) := by
  classical
  set ρ := IsLocalRing.residue R
  let k := IsLocalRing.ResidueField R
  obtain ⟨hfin, b', -, P, hPle, ⟨hPX, ⟨eP⟩⟩, -⟩ :=
    StacksDraft.Perfect.exists_unique_boundedAbove_free_complex_representing.{u, u}
      (DerivedCategory.Q.obj K) hK
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} ρ
  let Kκ := ((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let Pκ := ((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have hcomp : IsIso (D.comparison.app K) :=
    CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison_isIso_of_flat
      D K b
  let eH : ∀ i : ℤ, (DerivedCategory.homologyFunctor (ModuleCat.{u} k) i).obj
      (D.functor.obj (DerivedCategory.Q.obj K)) ≅ Kκ.homology i := fun i =>
    (DerivedCategory.homologyFunctor _ i).mapIso
      (@asIso _ _ _ _ (D.comparison.app K) hcomp ≪≫
        (Iso.refl _ : (CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral.{u,
          u, u} ρ).obj K ≅ DerivedCategory.Q.obj Kκ)) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app _
  have hPm : IsZero (P.X (-1)) := by
    obtain ⟨e⟩ := hPX (-1)
    have h0 : Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (-1)).obj
        (D.functor.obj (DerivedCategory.Q.obj K))) = 0 := by
      have := ModuleCat.subsingleton_of_isZero (hneg.of_iso (eH (-1)))
      exact Module.finrank_zero_of_subsingleton
    refine IsZero.of_iso ?_ e
    rw [h0]
    exact ModuleCat.isZero_of_subsingleton _
  have hfree : ∀ i, Module.Free R (P.X i) := fun i =>
    Module.Free.of_equiv (hPX i).some.toLinearEquiv.symm
  have hfinite : ∀ i, Module.Finite R (P.X i) := fun i =>
    Module.Finite.equiv (hPX i).some.toLinearEquiv.symm
  have hproj : ∀ i, Projective (P.X i) := fun i =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (P.X i))
  have hflatP : ∀ i, Module.Flat R (P.X i) := fun _ => inferInstance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b'
  obtain ⟨u, hu⟩ := StacksDraft.Perfect.map_surjective_of_isKProjective P K eP.hom
  have hQu : QuasiIso u :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 (by rw [hu]; infer_instance)
  have huκ : QuasiIso (((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u) :=
    StacksDraft.PseudoCoherence.quasiIso_extendScalars_map_of_flat ρ b' b u
  have hPκm : IsZero (Pκ.X (-1)) := (ModuleCat.extendScalars.{u, u, u} ρ).map_isZero hPm
  have hdiff : ∀ x : Pκ.X 0, (Pκ.d 0 1).hom x = 0 := by
    obtain ⟨e0⟩ := hPX 0
    obtain ⟨e0'⟩ := StacksDraft.Perfect.extendScalars_standard_free_iso.{u, u} ρ
      (Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
        (D.functor.obj (DerivedCategory.Q.obj K))))
    let eX : Pκ.X 0 ≅ _ := (ModuleCat.extendScalars.{u, u, u} ρ).mapIso e0 ≪≫ e0'
    have hdimX : Module.finrank k (Pκ.X 0) = Module.finrank k
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
          (D.functor.obj (DerivedCategory.Q.obj K))) := by
      rw [eX.toLinearEquiv.finrank_eq, finrank_ulift_fin_fun]
    have : Module.Finite k (Pκ.X 0) := Module.Finite.equiv eX.toLinearEquiv.symm
    have hH : IsIso (HomologicalComplex.homologyMap
        (((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map u) 0) := by
      rw [← quasiIsoAt_iff_isIso_homologyMap]
      infer_instance
    have hdimK : Module.finrank k (LinearMap.ker (Pκ.d 0 1).hom) = Module.finrank k
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
          (D.functor.obj (DerivedCategory.Q.obj K))) := by
      rw [← (homologyZeroEquivKer Pκ hPκm).finrank_eq,
        (@asIso _ _ _ _ _ hH ≪≫ (eH 0).symm).toLinearEquiv.finrank_eq]
    exact LinearMap.congr_fun (LinearMap.ker_eq_top.1
      (Submodule.eq_top_of_finrank_eq (hdimK.trans hdimX.symm)))
  refine ⟨P, u, hQu, hPm, hfree 0, hfinite 0, fun q => hdiff ((bcUnit ρ (P.X 0)).hom q), ?_⟩
  rintro q ⟨w, hw⟩
  obtain ⟨v, hv⟩ := StacksDraft.QuasiIsoDegreeZero.exists_eq_d_of_quasiIso
    (((ModuleCat.extendScalars.{u, u, u} ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map u)
    ((bcUnit ρ (P.X 0)).hom q) (hdiff _) w hw.symm
  have hv0 : v = 0 := (ModuleCat.isZero_iff_subsingleton.1 hPκm).elim _ _
  rw [hv, hv0, map_zero]
  rfl

end StacksDraft.MinimalModel

end
