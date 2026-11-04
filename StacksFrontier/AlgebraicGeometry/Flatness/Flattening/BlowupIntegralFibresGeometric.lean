module

public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupChartGeometric
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormulaGeneral
public import StacksFrontier.AlgebraicGeometry.QcohPushforwardOpen.Basic
public import StacksFrontier.RingTheory.Flat.BlowupFlattening
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibreLocusSchemeBridge

/-!
# The geometric reading of Stacks 0810

[Stacks, Tag 0810] produces, from a flat finitely presented ring map `R → S` with geometrically
integral fibres and a finite `S`-module `M` which is finitely presented and generically free of
rank `r` away from `f ∈ R`, a finitely generated ideal `I ⊆ R` with `V(f) = V(I)` such that on
every affine chart `R[I/a]` of the blowup the strict transform of `M` is free of rank `r` on a
principal neighbourhood of each extended prime.

This file states and proves the same lemma for schemes: with `S` affine, `X ⟶ S` affine, flat and
of finite presentation with geometrically integral fibres and `F` a quasi-coherent `𝒪_X`-module
of finite type which is of finite presentation over `D(s)` and free of rank `r` at the generic
point of every fibre over `D(s)`, there is a finite-type quasi-coherent sheaf of ideals `ℐ` on
`S` with `V(ℐ) = V(s)` such that over every point of the blowup `Bl_ℐ(S)` the strict transform of
`F` is free of rank `r` on an open of `X ×_S Bl_ℐ(S)` meeting the fibre there.

## Main results

* `AlgebraicGeometry.exists_free_open_of_chart_at`: the conclusion of the ring-level
  [Stacks, Tag 0810] on a single affine blowup chart, read on the strict transform of a
  quasi-coherent module.
* `AlgebraicGeometry.nonempty_free_localizedModule_of_stalk_rank`: hypothesis (5) of the source,
  read on the sections — freeness of rank `r` of the stalk at the generic point of a fibre is
  freeness of rank `r` of `Γ(F, ⊤)` localized at the extended prime.
* `AlgebraicGeometry.exists_idealSheafData_forall_blowUp_exists_free_of_rank`:
  **[Stacks, Tag 0810]**, geometric form.

## Implementation notes

The hypotheses of the source are the geometric ones, and each is turned into its ring-level
counterpart on global sections: flatness and finite presentation by
`AlgebraicGeometry.Scheme.Hom.flat_appTop` and
`AlgebraicGeometry.Scheme.Hom.finitePresentation_appTop`, geometric integrality of the fibres by
`AlgebraicGeometry.geometricallyIntegral_fiberToSpecResidueField_iff` after moving `f` to
`Spec` of its global-section map, finiteness of `F` by
`Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`, finite presentation over `D(s)` by
`Stacks.AlgebraicGeometry.FinitePresentationLocal.finitePresentation_sections_of_restrict`
followed by model-independence of finite presentation for a localized module, and freeness at
the generic point of a fibre by
`Stacks.ModuleStalkSpecialization.nonempty_linearEquiv_pi_of_basis_stalk`.

The generic point of the fibre over a prime `p` of `Γ(S, ⊤)` is the point whose prime is the
extension `p·Γ(X, ⊤)`; that this point is generic in its fibre is read off from
`AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`, which says that the prime of the image
of a point is the contraction of the prime of the point.

The conclusion is transported chart by chart. Every point of the blowup lies on an affine chart
(`Stacks.Blowup.iSup_opensRange_blowUpAffineChart`, the second assertion of [Stacks, Tag 0804]),
the sections of the strict transform over the base change of that chart are the module the
ring-level statement concludes about
(`Stacks.Blowup.nonempty_free_sections_chartBaseChange`), and the point of the base change over
the given point of the blowup is the extension of its prime, which is prime because the fibres of
the base change are domains
(`Ideal.isPrime_map_comap_includeRight`).

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### The conclusion on a single chart -/

/-- **The conclusion of the ring-level [Stacks, Tag 0810] on one affine blowup chart, read on the
strict transform.** Let `S` be a scheme, `f : X ⟶ S` with `X` affine, `F` a quasi-coherent
`𝒪_X`-module, `ℐ` a quasi-coherent sheaf of ideals on `S`, `U` an affine open of `S` whose
preimage is all of `X` and `a ∈ ℐ(U)`. If, for every prime `p'` of the affine blowup algebra
`Γ(S, U)[ℐ(U)/a]`, the module of [Stacks, Tag 0810] becomes free of rank `r` after inverting
some `g` outside `p'`, then every point `z` of the chart of `Bl_ℐ(S)` at `a` has a point of
`X ×_S Bl_ℐ(S)` above it with an open neighbourhood on which the strict transform of `F` is
free of rank `r`. -/
theorem exists_free_open_of_chart_at
    {S X : Scheme.{u}} [IsAffine X] (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (ℐ : S.IdealSheafData) (r : ℕ)
    (U : S.affineOpens) {a : Γ(S, U.1)} [haF : Fact (a ∈ ℐ.ideal U)]
    (hUX : (⊤ : X.Opens) ≤ f ⁻¹ᵁ U.1)
    (z : Stacks.Blowup.blowUp ℐ) (hzO : z ∈ Stacks.Blowup.blowUpChartImage ℐ U (a := a))
    (I : Ideal Γ(S, U.1)) (hI : ℐ.ideal U = I) :
    letI : Algebra Γ(S, U.1) Γ(X, ⊤) := (f.appLE U.1 (⊤ : X.Opens) hUX).hom.toAlgebra
    Module.Flat Γ(S, U.1) Γ(X, ⊤) →
    (∀ (p : Ideal Γ(S, U.1)) (hp : p.IsPrime), letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber Γ(X, ⊤))) →
    letI : Fact (a ∈ I) := ⟨hI ▸ haF.out⟩
    (∀ (p' : Ideal (Blowup I a)), p'.IsPrime →
        ∃ g : Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup I a,
          g ∉ Ideal.map Algebra.TensorProduct.includeRight p' ∧
          Nonempty (LocalizedModule (Submonoid.powers g)
            (((Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup I a) ⊗[Γ(X, ⊤)] Γ(F, ⊤)) ⧸
              Submodule.torsion' (Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup I a)
                ((Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup I a) ⊗[Γ(X, ⊤)] Γ(F, ⊤))
                (Submonoid.powers (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup I a)
                  (algebraMap Γ(S, U.1) Γ(X, ⊤) a))))
            ≃ₗ[Localization.Away g] (Fin r → Localization.Away g))) →
      ∃ (W : (Limits.pullback f (Stacks.Blowup.blowUpToBase ℐ)).Opens)
        (x : ↥(Limits.pullback f (Stacks.Blowup.blowUpToBase ℐ))),
        x ∈ W ∧ (pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).base x = z ∧
        Nonempty ((Stacks.StrictTransform.sheaf f (Stacks.Blowup.blowUpToBase ℐ)
          (Stacks.Blowup.exceptionalIdeal ℐ) F).restrict W.ι ≅
            SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  subst hI
  let : Algebra Γ(S, U.1) Γ(X, ⊤) := (f.appLE U.1 (⊤ : X.Opens) hUX).hom.toAlgebra
  intro hflat hfibre hchart
  have hOaff : IsAffineOpen (Stacks.Blowup.blowUpChartImage ℐ U (a := a)) :=
    Stacks.Blowup.isAffineOpen_blowUpChartImage ℐ U
  have hVaff : IsAffineOpen
      (Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens)) :=
    Stacks.Blowup.isAffineOpen_chartBaseChangeOpen f ℐ U (isAffineOpen_top X) hUX
  let : Algebra Γ(X, ⊤) Γ(Limits.pullback f (Stacks.Blowup.blowUpToBase ℐ),
      Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens)) :=
    ((pullback.fst f (Stacks.Blowup.blowUpToBase ℐ)).appLE (⊤ : X.Opens)
      (Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
      (Stacks.Blowup.chartBaseChangeOpen_le_preimage_fst f ℐ U (a := a)
        (UX := (⊤ : X.Opens)))).hom.toAlgebra
  have hc1 := Stacks.Blowup.chartBaseChangeSectionAlgEquiv_includeRight f ℐ U (a := a)
    (isAffineOpen_top X) hUX
  let : Algebra (Blowup (ℐ.ideal U) a) (Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup (ℐ.ideal U) a) :=
    Algebra.TensorProduct.rightAlgebra
  have := hflat
  have hp₀prime : ((hOaff.primeIdealOf ⟨z, hzO⟩).asIdeal).IsPrime :=
    (hOaff.primeIdealOf ⟨z, hzO⟩).isPrime
  have hp'prime : (Ideal.comap (Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).inv.hom
      (hOaff.primeIdealOf ⟨z, hzO⟩).asIdeal).IsPrime := hp₀prime.comap _
  obtain ⟨g, hgq, hfree⟩ := hchart _ hp'prime
  clear hchart
  obtain ⟨hqBprime, hqBcomap⟩ := Ideal.isPrime_map_comap_includeRight (R := Γ(S, U.1))
    (A := Γ(X, ⊤)) hfibre (Blowup (ℐ.ideal U) a)
    (Ideal.comap (Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).inv.hom
      (hOaff.primeIdealOf ⟨z, hzO⟩).asIdeal)
  -- the two mutually inverse maps between the chart ring and the affine blowup algebra
  have hικ : ∀ ss, (Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).inv.hom
      ((Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).hom.hom ss) = ss :=
    fun ss ↦ (Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).hom_inv_id_apply ss
  -- the comparison of the two routes into the section ring of the base change
  have hcomp : ∀ ss,
      (Stacks.Blowup.chartBaseChangeSectionAlgEquiv f ℐ U (a := a) (isAffineOpen_top X) hUX).symm
        (((pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).appLE
          (Stacks.Blowup.blowUpChartImage ℐ U (a := a))
          (Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
          (Stacks.Blowup.chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a)
            (UX := (⊤ : X.Opens)))).hom ss)
      = Algebra.TensorProduct.includeRight
        ((Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).hom.hom ss) := by
    intro ss
    have h := hc1 ((Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).hom.hom ss)
    have h2 := congrArg ((pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).appLE
      (Stacks.Blowup.blowUpChartImage ℐ U (a := a))
      (Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
      (Stacks.Blowup.chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a)
        (UX := (⊤ : X.Opens)))).hom (hικ ss)
    exact (Stacks.Blowup.chartBaseChangeSectionAlgEquiv f ℐ U (a := a)
      (isAffineOpen_top X) hUX).symm_apply_eq.mpr (h.trans h2).symm
  clear hc1 hflat hfibre
  obtain ⟨q, hqprime, hgq', hqcomap⟩ := exists_prime_comap_of_ringEquiv
    (Stacks.Blowup.chartBaseChangeSectionAlgEquiv f ℐ U (a := a) (isAffineOpen_top X)
      hUX).toRingEquiv
    ((pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).appLE
      (Stacks.Blowup.blowUpChartImage ℐ U (a := a))
      (Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
      (Stacks.Blowup.chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a)
        (UX := (⊤ : X.Opens)))).hom
    (Algebra.TensorProduct.includeRight :
      Blowup (ℐ.ideal U) a →ₐ[Γ(S, U.1)] Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup (ℐ.ideal U) a)
    (Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).hom.hom
    (Stacks.Blowup.chartSectionRingIsoBlowup ℐ U (a := a)).inv.hom
    hcomp hικ (hOaff.primeIdealOf ⟨z, hzO⟩).asIdeal hqBcomap hqBprime g hgq
  -- the point of the base change lying over `z`
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec
    (pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)) hOaff hVaff
    (Stacks.Blowup.chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a) (UX := (⊤ : X.Opens)))
  have hy2 : (Spec.map ((pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).appLE
      (Stacks.Blowup.blowUpChartImage ℐ U (a := a))
      (Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
      (Stacks.Blowup.chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a)
        (UX := (⊤ : X.Opens))))).base ⟨q, hqprime⟩ = hOaff.primeIdealOf ⟨z, hzO⟩ :=
    PrimeSpectrum.ext hqcomap
  have hsnd : (pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).base
      (hVaff.fromSpec.base ⟨q, hqprime⟩) = z := by
    have h : hOaff.fromSpec.base ((Spec.map
          ((pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).appLE
            (Stacks.Blowup.blowUpChartImage ℐ U (a := a))
            (Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
            (Stacks.Blowup.chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a)
              (UX := (⊤ : X.Opens))))).base ⟨q, hqprime⟩)
        = (pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).base
          (hVaff.fromSpec.base ⟨q, hqprime⟩) :=
      congrArg (fun m : Spec Γ(Limits.pullback f (Stacks.Blowup.blowUpToBase ℐ),
        Stacks.Blowup.chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens)) ⟶
        Stacks.Blowup.blowUp ℐ ↦ m.base ⟨q, hqprime⟩) hsq
    rw [← h, hy2, hOaff.fromSpec_primeIdealOf ⟨z, hzO⟩]
  have hfreeQ := Stacks.Blowup.nonempty_free_sections_chartBaseChange f F ℐ U hUX r g hfree
  obtain ⟨W, hxW, hiso⟩ := exists_restrict_iso_free_of_basis_away
    (Stacks.StrictTransform.sheaf f (Stacks.Blowup.blowUpToBase ℐ)
      (Stacks.Blowup.exceptionalIdeal ℐ) F) hVaff
    ((Stacks.Blowup.chartBaseChangeSectionAlgEquiv f ℐ U (a := a) (isAffineOpen_top X) hUX) g) r
    ⟨q, hqprime⟩ hgq' hfreeQ
  exact ⟨W, hVaff.fromSpec.base ⟨q, hqprime⟩, hxW, hsnd, hiso⟩

/-! ### The rank hypothesis, read on the sections -/

/-- **Freeness of rank `r` at the generic point of a fibre, read on the sections.** For an affine
`f : X ⟶ S` with `S` affine and `f` flat, the generic point of the fibre over a prime `p` of
`Γ(S, ⊤)` is the point whose prime is the extension `p·Γ(X, ⊤)`, so freeness of rank `r` of the
stalk of `F` there is freeness of rank `r` of `Γ(F, ⊤)` localized at that extension. -/
theorem nonempty_free_localizedModule_of_stalk_rank
    {S X : Scheme.{u}} [IsAffine S] [IsAffine X] (f : X ⟶ S) [Flat f]
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(S, ⊤)) (r : ℕ) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) :=
      (f.appLE (⊤ : S.Opens) (⊤ : X.Opens) le_top).hom.toAlgebra
    (∀ x : X, f.base x ∈ S.basicOpen s → f.base ⁻¹' {f.base x} ⊆ closure {x} →
      letI := Stacks.ModuleStalkSpecialization.stalkModule F x
      Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x))) →
    Module.Flat Γ(S, ⊤) Γ(X, ⊤) →
    ∀ (p : Ideal Γ(S, ⊤)) (hp : p.IsPrime), s ∉ p →
      letI := hp
      ∀ hq : (Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p).IsPrime,
        letI := hq
        Nonempty (LocalizedModule
          (Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p).primeCompl Γ(F, ⊤)
          ≃ₗ[Localization (Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p).primeCompl]
          (Fin r → Localization (Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p).primeCompl)) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) :=
    (f.appLE (⊤ : S.Opens) (⊤ : X.Opens) le_top).hom.toAlgebra
  intro hrank hflat p hp hs hq
  have := hp
  have := hq
  have := hflat
  -- the generic point of the fibre over `p`
  set x : X := (isAffineOpen_top X).fromSpec.base
    ⟨Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p, hq⟩ with hxdef
  have hpx : (isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩
      = ⟨Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p, hq⟩ :=
    primeIdealOf_fromSpec (isAffineOpen_top X) _
  -- its image is the point of `p`
  have hbase : ∀ x' : X, ((isAffineOpen_top X).primeIdealOf ⟨x', trivial⟩).asIdeal.comap
      (algebraMap Γ(S, ⊤) Γ(X, ⊤))
      = ((isAffineOpen_top S).primeIdealOf ⟨f.base x', trivial⟩).asIdeal := fun x' ↦
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE
      (⊤ : S.Opens) (isAffineOpen_top S) (⊤ : X.Opens) (isAffineOpen_top X) le_top trivial)
  have hfx : ((isAffineOpen_top S).primeIdealOf ⟨f.base x, trivial⟩).asIdeal = p := by
    rw [← hbase x, hpx]
    exact comap_map_eq_of_flat_isPrime (algebraMap Γ(S, ⊤) Γ(X, ⊤))
      (RingHom.flat_algebraMap_iff.mpr hflat) p hq
  have hmemU : f.base x ∈ S.basicOpen s := by
    refine (mem_basicOpen_iff_notMem_primeIdealOf (isAffineOpen_top S) s
      ⟨f.base x, trivial⟩).mpr ?_
    rw [hfx]
    exact hs
  have hgen : f.base ⁻¹' {f.base x} ⊆ closure {x} := by
    intro x' hx'
    have hfx' : ((isAffineOpen_top S).primeIdealOf ⟨f.base x', trivial⟩).asIdeal = p := by
      rw [show f.base x' = f.base x from hx']
      exact hfx
    have hle : Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p
        ≤ ((isAffineOpen_top X).primeIdealOf ⟨x', trivial⟩).asIdeal := by
      refine Ideal.map_le_iff_le_comap.mpr ?_
      rw [hbase x', hfx']
    have hspec : (⟨Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) p, hq⟩ : PrimeSpectrum Γ(X, ⊤)) ⤳
        (isAffineOpen_top X).primeIdealOf ⟨x', trivial⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have hspec2 := hspec.map (isAffineOpen_top X).fromSpec.base.hom.continuous
    rw [show (isAffineOpen_top X).fromSpec.base
      ((isAffineOpen_top X).primeIdealOf ⟨x', trivial⟩) = x' from
        (isAffineOpen_top X).fromSpec_primeIdealOf ⟨x', trivial⟩] at hspec2
    exact specializes_iff_mem_closure.mp hspec2
  have hbasis := hrank x hmemU hgen
  have := Stacks.ModuleStalkSpecialization.nonempty_linearEquiv_pi_of_basis_stalk F
    (isAffineOpen_top X) (x := x) trivial r hbasis
  rw [hpx] at this
  exact this

/-! ### The geometric form of Stacks 0810 -/

/-- **Stacks Project, Tag 0810.** Let `S` be an affine scheme, `s : Γ(S, ⊤)`, `r ≥ 0` an integer,
`f : X ⟶ S` an affine morphism and `F` a quasi-coherent `𝒪_X`-module. Assume

1. `f` is of finite presentation and flat with geometrically integral fibres;
2. `F` is of finite type;
3. `F` restricted to `f⁻¹(D(s))` is of finite presentation;
4. for every point `x` of `X` which is generic in its fibre and whose image lies in `D(s)`, the
   stalk `F_x` is free of rank `r` over `𝒪_{X,x}`.

Then there is a quasi-coherent sheaf of ideals `ℐ` on `S` whose ideal of global sections is
finitely generated and whose support is `V(s)`, such that over every point `z` of the blowup
`Bl_ℐ(S)` there is a point of `X ×_S Bl_ℐ(S)` above `z` with an open neighbourhood on which the
strict transform of `F` is free of rank `r`.

This is the geometric reading of the ring-level
`AlgebraicGeometry.exists_fg_ideal_forall_blowup_chart_exists_away_basis`: hypotheses (1)–(4) are
converted into its hypotheses on `Γ(S, ⊤) → Γ(X, ⊤)` and `Γ(F, ⊤)`, and its conclusion — the
`a`-power-torsion quotient of the base change becomes free of rank `r` after inverting one
element per prime of each affine blowup chart — is carried onto the sheaf-level strict transform
by `AlgebraicGeometry.exists_free_open_of_chart_at`. -/
@[stacks 0810 "the scheme-level form"]
public theorem exists_idealSheafData_forall_blowUp_exists_free_of_rank
    {S X : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsAffineHom f] [Flat f]
    [GeometricallyIntegral f] (hf : AlgebraicGeometry.FinitePresentation f)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : Γ(S, ⊤)) (r : ℕ)
    (hFU : (F.restrict (f ⁻¹ᵁ S.basicOpen s).ι).IsFinitePresentation)
    (hrank : ∀ x : X, f.base x ∈ S.basicOpen s → f.base ⁻¹' {f.base x} ⊆ closure {x} →
      letI := Stacks.ModuleStalkSpecialization.stalkModule F x
      Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x))) :
    ∃ ℐ : S.IdealSheafData,
      (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩).FG ∧
      (ℐ.support : Set S) = (↑(S.basicOpen s))ᶜ ∧
      ∀ z : Stacks.Blowup.blowUp ℐ,
        ∃ (W : (Limits.pullback f (Stacks.Blowup.blowUpToBase ℐ)).Opens)
          (x : ↥(Limits.pullback f (Stacks.Blowup.blowUpToBase ℐ))),
          x ∈ W ∧ (pullback.snd f (Stacks.Blowup.blowUpToBase ℐ)).base x = z ∧
          Nonempty ((Stacks.StrictTransform.sheaf f (Stacks.Blowup.blowUpToBase ℐ)
            (Stacks.Blowup.exceptionalIdeal ℐ) F).restrict W.ι ≅
              SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) :=
    (f.appLE (⊤ : S.Opens) (⊤ : X.Opens) le_top).hom.toAlgebra
  have happ : f.appLE (⊤ : S.Opens) (⊤ : X.Opens) le_top = f.appTop :=
    Scheme.Hom.appLE_eq_app f
  have hmap : algebraMap Γ(S, ⊤) Γ(X, ⊤) = f.appTop.hom := congrArg (·.hom) happ
  have hflat : Module.Flat Γ(S, ⊤) Γ(X, ⊤) := by
    exact RingHom.flat_algebraMap_iff.mp (hmap ▸ f.flat_appTop)
  have := hf.1
  have : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) := by
    exact RingHom.finitePresentation_algebraMap.mp (hmap ▸ f.finitePresentation_appTop)
  have hfibre : ∀ (p : Ideal Γ(S, ⊤)) (hp : p.IsPrime),
      let := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber Γ(X, ⊤)) := by
    intro p hp
    have := hp
    have harrow : Arrow.mk f ≅ Arrow.mk (Spec.map f.appTop) :=
      Arrow.isoMk X.isoSpec S.isoSpec (by simpa using Scheme.isoSpec_hom_naturality f)
    have : MorphismProperty.RespectsIso (@GeometricallyIntegral) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have h3 : GeometricallyIntegral (Spec.map f.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff (P := @GeometricallyIntegral) harrow).mp ‹_›
    refine (geometricallyIntegral_fiberToSpecResidueField_iff Γ(S, ⊤) Γ(X, ⊤) ⟨p, hp⟩).mp ?_
    rw [hmap, CommRingCat.ofHom_hom]
    exact (GeometricallyIntegral.iff_geometricallyIntegral_fiber
      (Spec.map f.appTop)).mp h3 ⟨p, hp⟩
  have : Module.Finite Γ(X, ⊤) Γ(F, ⊤) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F (isAffineOpen_top X)
  let : Module Γ(S, ⊤) Γ(F, ⊤) := Module.compHom _ (algebraMap Γ(S, ⊤) Γ(X, ⊤))
  have : IsScalarTower Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hpre : f ⁻¹ᵁ S.basicOpen s = X.basicOpen (algebraMap Γ(S, ⊤) Γ(X, ⊤) s) := by
    rw [Scheme.preimage_basicOpen_top f s, hmap]
  have hFU2 : (F.restrict (X.basicOpen (algebraMap Γ(S, ⊤) Γ(X, ⊤) s)).ι).IsFinitePresentation := by
    rw [← hpre]
    exact hFU
  have : Module.FinitePresentation Γ(X, X.basicOpen (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))
      Γ(F, X.basicOpen (algebraMap Γ(S, ⊤) Γ(X, ⊤) s)) :=
    Stacks.AlgebraicGeometry.FinitePresentationLocal.finitePresentation_sections_of_restrict F
      ((isAffineOpen_top X).basicOpen _) hFU2
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE F
    (X.basicOpen_le (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))
  have : IsScalarTower Γ(X, ⊤) Γ(X, X.basicOpen (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))
      Γ(F, X.basicOpen (algebraMap Γ(S, ⊤) Γ(X, ⊤) s)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsLocalizedModule.Away (algebraMap Γ(S, ⊤) Γ(X, ⊤) s)
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ F
        (X.basicOpen_le (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))) :=
    Stacks.AlgebraicGeometry.QcohPushforwardOpen.isLocalizedModule_restrictₗ_of_eq F
      isCompact_univ (isQuasiSeparated_univ (α := X)) _ rfl
      (X.basicOpen_le (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))
  have hfpM : Module.FinitePresentation
      (Localization.Away (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))
      (LocalizedModule (Submonoid.powers (algebraMap Γ(S, ⊤) Γ(X, ⊤) s)) Γ(F, ⊤)) :=
    Module.FinitePresentation.of_isLocalizedModule_of_isLocalization
      (Submonoid.powers (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))
      (A₁ := Γ(X, X.basicOpen (algebraMap Γ(S, ⊤) Γ(X, ⊤) s)))
      (A₂ := Localization.Away (algebraMap Γ(S, ⊤) Γ(X, ⊤) s))
      (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ F
        (X.basicOpen_le (algebraMap Γ(S, ⊤) Γ(X, ⊤) s)))
      (LocalizedModule.mkLinearMap _ Γ(F, ⊤))
  obtain ⟨J, hJfg, hJsupp, hchart⟩ := exists_fg_ideal_forall_blowup_chart_exists_away_basis
    Γ(S, ⊤) Γ(X, ⊤) Γ(F, ⊤) s r hfibre hfpM
    (nonempty_free_localizedModule_of_stalk_rank f F s r hrank hflat)
  refine ⟨Scheme.IdealSheafData.ofIdealTop J, ?_, ?_, ?_⟩
  · rw [Stacks.Coherent.ofIdealTop_ideal_top]
    exact hJfg
  · refine Set.ext fun x ↦ ?_
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Scheme.mem_zeroLocus_iff]
    have hiff : ∀ t : Γ(S, ⊤), x ∈ S.basicOpen t ↔
        t ∉ ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal := fun t ↦
      mem_basicOpen_iff_notMem_primeIdealOf (isAffineOpen_top S) t ⟨x, trivial⟩
    have hprime := ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).isPrime
    have hle : (∀ t ∈ (J : Set Γ(S, ⊤)), x ∉ S.basicOpen t) ↔
        J ≤ ((isAffineOpen_top S).primeIdealOf ⟨x, trivial⟩).asIdeal := by
      refine ⟨fun h t ht ↦ ?_, fun h t ht hxt ↦ (hiff t).mp hxt (h ht)⟩
      by_contra hc
      exact h t ht ((hiff t).mpr hc)
    rw [hle, ← hJsupp _ hprime]
    simp [Set.mem_compl_iff, hiff s]
  · intro z
    obtain ⟨a', hza⟩ : ∃ t : (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top S⟩,
        z ∈ (Stacks.Blowup.blowUpAffineChart (Scheme.IdealSheafData.ofIdealTop J)
          ⟨⊤, isAffineOpen_top S⟩ t.2).opensRange := by
      refine TopologicalSpace.Opens.mem_iSup.mp ?_
      rw [Stacks.Blowup.iSup_opensRange_blowUpAffineChart
        (Scheme.IdealSheafData.ofIdealTop J) ⟨⊤, isAffineOpen_top S⟩]
      exact trivial
    have haF : Fact ((a' : Γ(S, ⊤)) ∈ (Scheme.IdealSheafData.ofIdealTop J).ideal
      ⟨⊤, isAffineOpen_top S⟩) := ⟨a'.2⟩
    obtain ⟨w, hw⟩ := hza
    have ha' : (a' : Γ(S, ⊤)) ∈ J :=
      (Stacks.Coherent.ofIdealTop_ideal_top S J).le a'.2
    exact exists_free_open_of_chart_at f F _ r ⟨⊤, isAffineOpen_top S⟩ le_top z
      ⟨w, trivial, hw⟩ J (Stacks.Coherent.ofIdealTop_ideal_top S J) hflat hfibre
      (hchart (a' : Γ(S, ⊤)) ha')

end AlgebraicGeometry

end
