module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.LocalizedModule.FreeRankModelIndependence
public import StacksFrontier.RingTheory.Blowup.StrictTransformBaseChange
public import StacksFrontier.RingTheory.Flat.BlowupGeometricallyIntegralFibres
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformChartRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pieces for the geometric reading of Stacks 0810
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

universe u

/-! ### The chart generator of the base change -/

namespace Stacks.Blowup

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData) (U : S.affineOpens)
  {a : Γ(S, U.1)} [ha : Fact (a ∈ ℐ.ideal U)] {UX : X.Opens}

/-- **The section ring of the base change of a chart is the chart ring's own base change, as a
module over the chart ring.** The isomorphism
`Stacks.Blowup.chartBaseChangeSectionAlgEquiv` carries `1 ⊗ t` to the image of `t` under the
projection to the blowup, so it is an isomorphism of algebras over the chart ring as well as
over `Γ(X, U_X)`. -/
theorem chartBaseChangeSectionAlgEquiv_includeRight (hUXaff : IsAffineOpen UX)
    (hUX : UX ≤ f ⁻¹ᵁ U.1) (t : Blowup (ℐ.ideal U) a) :
    letI : Algebra Γ(S, U.1) Γ(X, UX) := (f.appLE U.1 UX hUX).hom.toAlgebra
    letI : Algebra Γ(X, UX) Γ(Limits.pullback f (blowUpToBase ℐ),
        chartBaseChangeOpen f ℐ U (a := a) UX) :=
      ((pullback.fst f (blowUpToBase ℐ)).appLE UX (chartBaseChangeOpen f ℐ U (a := a) UX)
        (chartBaseChangeOpen_le_preimage_fst f ℐ U (a := a) (UX := UX))).hom.toAlgebra
    chartBaseChangeSectionAlgEquiv f ℐ U hUXaff hUX (Algebra.TensorProduct.includeRight t)
      = ((pullback.snd f (blowUpToBase ℐ)).appLE (blowUpChartImage ℐ U (a := a))
          (chartBaseChangeOpen f ℐ U (a := a) UX)
          (chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a) (UX := UX))).hom
        ((chartSectionRingIsoBlowup ℐ U (a := a)).inv.hom t) := by
  let : Algebra Γ(S, U.1) Γ(X, UX) := (f.appLE U.1 UX hUX).hom.toAlgebra
  let : Algebra Γ(S, U.1) Γ(blowUp ℐ, blowUpChartImage ℐ U (a := a)) :=
    ((blowUpToBase ℐ).appLE U.1 (blowUpChartImage ℐ U (a := a))
      (blowUpChartImage_le_preimage ℐ U (a := a))).hom.toAlgebra
  let : Algebra Γ(X, UX) Γ(Limits.pullback f (blowUpToBase ℐ),
      chartBaseChangeOpen f ℐ U (a := a) UX) :=
    ((pullback.fst f (blowUpToBase ℐ)).appLE UX (chartBaseChangeOpen f ℐ U (a := a) UX)
      (chartBaseChangeOpen_le_preimage_fst f ℐ U (a := a) (UX := UX))).hom.toAlgebra
  let : Algebra Γ(blowUp ℐ, blowUpChartImage ℐ U (a := a))
      Γ(Limits.pullback f (blowUpToBase ℐ), chartBaseChangeOpen f ℐ U (a := a) UX) :=
    ((pullback.snd f (blowUpToBase ℐ)).appLE (blowUpChartImage ℐ U (a := a))
      (chartBaseChangeOpen f ℐ U (a := a) UX)
      (chartBaseChangeOpen_le_preimage_snd f ℐ U (a := a) (UX := UX))).hom.toAlgebra
  simp only [chartBaseChangeSectionAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  rfl

end Stacks.Blowup

/-! ### Transporting a trivialisation along an open immersion -/

namespace AlgebraicGeometry

/-- **A trivialisation of `F` on an open of the source of an open immersion is a trivialisation
on an open of the target.** This is the pointwise form of
`Stacks.Modules.exists_restrict_iso_free_of_isOpenImmersion`, taking the trivialising open and
the isomorphism as data rather than reading them off a finite-local-freeness hypothesis. -/
theorem exists_restrict_iso_free_of_mem {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (F : X.Modules) (J : Type u) (y : Y) (W : Y.Opens) (hyW : y ∈ W)
    (e : (F.restrict g).restrict W.ι ≅ SheafOfModules.free.{u} J) :
    ∃ V : X.Opens, g.base y ∈ V ∧
      Nonempty (F.restrict V.ι ≅ SheafOfModules.free.{u} J) := by
  let e₀ := g.isoImage W
  let iso₂ : Scheme.Modules.restrictFunctor e₀.hom ⋙ Scheme.Modules.restrictFunctor e₀.inv ≅
      𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp e₀.inv e₀.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e₀.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId
  exact ⟨g ''ᵁ W, ⟨y, hyW, rfl⟩, ⟨(iso₂.app (F.restrict (g ''ᵁ W).ι)).symm ≪≫
    (Scheme.Modules.restrictFunctor e₀.inv).mapIso
      ((Stacks.Modules.restrictImageIso g W F).symm ≪≫ e) ≪≫
    (Stacks.Modules.freeRestrictIso e₀.inv J).symm⟩⟩

end AlgebraicGeometry

/-! ### Freeness of the stalk, read on the sections -/

namespace Stacks.ModuleStalkSpecialization

/-- **Freeness of rank `r` of the stalk of a quasi-coherent module is freeness of rank `r` of the
localization of its sections.** The stalk of a quasi-coherent module at a point of an affine open
is a localization of the sections there (`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`
and `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`), and freeness of a fixed rank does not
depend on the model of a localization. -/
theorem nonempty_linearEquiv_pi_of_basis_stalk {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (r : ℕ)
    (h : letI := stalkModule F x
      Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x))) :
    Nonempty (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U)
      ≃ₗ[Localization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl]
      (Fin r → Localization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)) := by
  let := stalkModule F x
  let := sectionsStalkModule F hx
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have : IsLocalizedModule.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal (germₗ F hx) :=
    isLocalizedModule_germₗ F hU hx
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    isScalarTower_sectionsStalk F hx
  exact Module.nonempty_linearEquiv_pi_of_isLocalizedModule_of_isLocalization
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (germₗ F hx)
    (LocalizedModule.mkLinearMap _ Γ(F, U)) r ⟨h.some.equivFun⟩

end Stacks.ModuleStalkSpecialization

/-! ### Primes of a base change with geometrically integral fibres -/

/-- **The extension of a prime along a base change with geometrically integral fibres is prime,
and contracts back to it.** For a flat `R`-algebra `A` all of whose fibres are geometrically
integral and any `R`-algebra `T`, the fibres of `T → A ⊗[R] T` are domains, so a prime of `T`
extends to a prime of `A ⊗[R] T`. -/
@[ega "0 6.5.1" "special case"]
public theorem Ideal.isPrime_map_comap_includeRight {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A]
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber A))
    (T : Type u) [CommRing T] [Algebra R T] (p' : Ideal T) [p'.IsPrime] :
    (Ideal.map (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) p').IsPrime ∧
      (Ideal.map (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) p').comap
        (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) = p' := by
  let : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have hmapI : ∀ J : Ideal T,
      Ideal.map (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) J
        = Ideal.map (algebraMap T (A ⊗[R] T)) J := fun _ ↦ rfl
  have hcomapI : ∀ J : Ideal (A ⊗[R] T),
      Ideal.comap (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) J
        = Ideal.comap (algebraMap T (A ⊗[R] T)) J := fun _ ↦ rfl
  rw [hmapI, hcomapI]
  have hflat : Module.Flat T (A ⊗[R] T) :=
    have : Module.Flat T (T ⊗[R] A) := Module.Flat.baseChange R T A
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.commRight R T A).symm.toLinearEquiv
  have hprime : (Ideal.map (algebraMap T (A ⊗[R] T)) p').IsPrime :=
    Ideal.isPrime_map_of_flat_of_isDomain_fiber' p' (isDomain_fiber_baseChange hfibre p')
  exact ⟨hprime, comap_map_eq_of_flat_isPrime (algebraMap T (A ⊗[R] T))
    (RingHom.flat_algebraMap_iff.mpr hflat) p' hprime⟩

/-! ### Transporting freeness of a torsion quotient -/

/-- **Transporting rank-`r` freeness of a torsion quotient of a base change along an isomorphism
of the algebra being changed to.** -/
public theorem nonempty_free_quotient_torsion_of_algEquiv
    {A : Type u} [CommRing A] {B B₀ : Type u} [CommRing B] [CommRing B₀]
    [Algebra A B] [Algebra A B₀]
    (M : Type u) [AddCommGroup M] [Module A M]
    (eB : B ≃ₐ[A] B₀) (c : A) (r : ℕ) (g : B)
    (h : Nonempty (LocalizedModule (Submonoid.powers g)
        ((B ⊗[A] M) ⧸ Submodule.torsion' B (B ⊗[A] M)
          (Submonoid.powers (algebraMap A B c)))
        ≃ₗ[Localization.Away g] (Fin r → Localization.Away g))) :
    Nonempty (LocalizedModule (Submonoid.powers (eB g))
        ((B₀ ⊗[A] M) ⧸ Submodule.torsion' B₀ (B₀ ⊗[A] M)
          (Submonoid.powers (algebraMap A B₀ c)))
        ≃ₗ[Localization.Away (eB g)] (Fin r → Localization.Away (eB g))) := by
  let : Algebra B B₀ := (eB : B →+* B₀).toAlgebra
  have halg : ∀ x : A, algebraMap B B₀ (algebraMap A B x) = algebraMap A B₀ x :=
    eB.commutes
  have : IsScalarTower A B B₀ := IsScalarTower.of_algebraMap_eq fun x ↦ (halg x).symm
  let ψ : (B ⊗[A] M) ≃ₗ[A] (B₀ ⊗[A] M) :=
    TensorProduct.congr eB.toLinearEquiv (LinearEquiv.refl A M)
  have hψ : ∀ (b : B) (w : B ⊗[A] M), ψ (b • w) = b • ψ w := fun b w ↦ by
    induction w using TensorProduct.inductionOn with
    | tmul cc m =>
      rw [TensorProduct.smul_tmul']
      change (eB (b * cc)) ⊗ₜ[A] m = (b • eB cc) ⊗ₜ[A] m
      rw [Algebra.smul_def, map_mul]
      rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  let ψB : (B ⊗[A] M) ≃ₗ[B] (B₀ ⊗[A] M) := { ψ with map_smul' := hψ }
  have hsub : Submodule.map ψB.toLinearMap
        (Submodule.torsion' B (B ⊗[A] M) (Submonoid.powers (algebraMap A B c)))
      = (Submodule.torsion' B₀ (B₀ ⊗[A] M)
          (Submonoid.powers (algebraMap A B₀ c))).restrictScalars B := by
    rw [Submodule.map_torsion'_powers (algebraMap A B c) ψB, ← halg c,
      Submodule.restrictScalars_torsion'_powers_algebraMap B (algebraMap A B c)]
  let θ : ((B ⊗[A] M) ⧸ Submodule.torsion' B (B ⊗[A] M)
        (Submonoid.powers (algebraMap A B c)))
      ≃ₗ[B] ((B₀ ⊗[A] M) ⧸ Submodule.torsion' B₀ (B₀ ⊗[A] M)
        (Submonoid.powers (algebraMap A B₀ c))) :=
    (Submodule.Quotient.equiv _ _ ψB hsub).trans
      (Submodule.Quotient.restrictScalarsEquiv B
        (Submodule.torsion' B₀ (B₀ ⊗[A] M) (Submonoid.powers (algebraMap A B₀ c))))
  exact Module.nonempty_linearEquiv_pi_localizedModule_away_of_bijective
    (B := B) (C := B₀) eB.bijective θ g r h

/-! ### Freeness on a basic open from freeness of a localized section module -/

/-- **A rank-`r` basis of the localization of the sections over an affine open gives a free
restriction on an open around the corresponding point.** -/
public theorem exists_restrict_iso_free_of_basis_away {Z : Scheme.{u}} (G : Z.Modules)
    [G.IsQuasicoherent] {V : Z.Opens} (hV : IsAffineOpen V) (g : Γ(Z, V)) (r : ℕ)
    (y : Spec Γ(Z, V)) (hy : g ∉ y.asIdeal)
    (hfree : Nonempty (LocalizedModule (Submonoid.powers g) Γ(G, V)
      ≃ₗ[Localization.Away g] (Fin r → Localization.Away g))) :
    ∃ W : Z.Opens, hV.fromSpec.base y ∈ W ∧
      Nonempty (G.restrict W.ι ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  have := hV.isOpenImmersion_fromSpec
  have hiso : Nonempty ((AlgebraicGeometry.tilde (R := Γ(Z, V))
      (ModuleCat.of Γ(Z, V) Γ(G, V))).restrict (specBasicOpen Γ(Z, V) g).ι ≅
      SheafOfModules.free.{u} (ULift.{u} (Fin r))) :=
    (tilde_restrict_basicOpen_rank_iff Γ(Z, V) Γ(G, V) g r).mpr
      ⟨Module.Basis.ofEquivFun hfree.some⟩
  exact exists_restrict_iso_free_of_mem hV.fromSpec G (ULift.{u} (Fin r)) y
    (specBasicOpen Γ(Z, V) g) hy
    ((Scheme.Modules.restrictFunctor (specBasicOpen Γ(Z, V) g).ι).mapIso
      (Stacks.Modules.tildeIsoRestrictFromSpec G hV).symm ≪≫ hiso.some)

/-! ### The point of a base change over a point of the chart -/

/-- **The extended prime, read through an isomorphism of the ambient ring.** Given a ring
isomorphism `e : B ≃+* B₀`, a prime `p₀` of `C`, maps `κ : C → T` and `ι : T → C` with
`ι ∘ κ = id`, and a map `ψ : T → B` whose extension of `p₀.comap ι` is prime and contracts
back, the ideal of `B₀` corresponding to that extension is a prime which contracts to `p₀`
along any `φ : C → B₀` with `e⁻¹ ∘ φ = ψ ∘ κ`, and which avoids the image of anything avoiding
the extension. -/
public theorem exists_prime_comap_of_ringEquiv {B B₀ C T : Type u} [CommRing B] [CommRing B₀]
    [CommRing C] [CommRing T] {FT : Type*} [FunLike FT T B] [RingHomClass FT T B]
    (e : B ≃+* B₀) (φ : C →+* B₀) (ψ : FT) (κ : C →+* T)
    (ι : T →+* C) (hφ : ∀ x, e.symm (φ x) = ψ (κ x)) (hικ : ∀ x, ι (κ x) = x)
    (p₀ : Ideal C)
    (hcomap : (Ideal.map ψ (Ideal.comap ι p₀)).comap ψ = Ideal.comap ι p₀)
    (hqB : (Ideal.map ψ (Ideal.comap ι p₀)).IsPrime) (g : B)
    (hg : g ∉ Ideal.map ψ (Ideal.comap ι p₀)) :
    ∃ q : Ideal B₀, q.IsPrime ∧ e g ∉ q ∧ Ideal.comap φ q = p₀ := by
  refine ⟨Ideal.comap (e.symm : B₀ →+* B) (Ideal.map ψ (Ideal.comap ι p₀)), hqB.comap _, ?_, ?_⟩
  · simpa [Ideal.mem_comap] using hg
  · refine Ideal.ext fun x ↦ ?_
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change e.symm (φ x) ∈ _ ↔ _
    rw [hφ x, ← Ideal.mem_comap, hcomap, Ideal.mem_comap, hικ x]

/-! ### The sections of the strict transform on the base change of a chart -/

namespace Stacks.Blowup

/-- **The module of [Stacks, Tag 0810] is the sections of the strict transform.** If the module
`M'` that the ring-level Tag 0810 concludes about becomes free of rank `r` after inverting
`g`, then the sections of the sheaf-level strict transform over the base change of the chart
become free of rank `r` after inverting the image of `g`. -/
public theorem nonempty_free_sections_chartBaseChange {S X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (ℐ : S.IdealSheafData)
    (U : S.affineOpens) {a : Γ(S, U.1)} [Fact (a ∈ ℐ.ideal U)]
    (hUX : (⊤ : X.Opens) ≤ f ⁻¹ᵁ U.1) (r : ℕ) :
    letI : Algebra Γ(S, U.1) Γ(X, ⊤) := (f.appLE U.1 (⊤ : X.Opens) hUX).hom.toAlgebra
    ∀ g : Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup (ℐ.ideal U) a,
      Nonempty (LocalizedModule (Submonoid.powers g)
          (((Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup (ℐ.ideal U) a) ⊗[Γ(X, ⊤)] Γ(F, ⊤)) ⧸
            Submodule.torsion' (Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup (ℐ.ideal U) a)
              ((Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup (ℐ.ideal U) a) ⊗[Γ(X, ⊤)] Γ(F, ⊤))
              (Submonoid.powers (algebraMap Γ(X, ⊤)
                (Γ(X, ⊤) ⊗[Γ(S, U.1)] Blowup (ℐ.ideal U) a)
                (algebraMap Γ(S, U.1) Γ(X, ⊤) a))))
          ≃ₗ[Localization.Away g] (Fin r → Localization.Away g)) →
      Nonempty (LocalizedModule (Submonoid.powers
            (chartBaseChangeSectionAlgEquiv f ℐ U (isAffineOpen_top X) hUX g))
          Γ(Stacks.StrictTransform.sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F,
            chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
          ≃ₗ[Localization.Away (chartBaseChangeSectionAlgEquiv f ℐ U (isAffineOpen_top X) hUX g)]
          (Fin r → Localization.Away
            (chartBaseChangeSectionAlgEquiv f ℐ U (isAffineOpen_top X) hUX g))) := by
  let : Algebra Γ(S, U.1) Γ(X, ⊤) := (f.appLE U.1 (⊤ : X.Opens) hUX).hom.toAlgebra
  intro g hfree
  let : Algebra Γ(X, ⊤) Γ(Limits.pullback f (blowUpToBase ℐ),
      chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens)) :=
    ((Limits.pullback.fst f (blowUpToBase ℐ)).appLE (⊤ : X.Opens)
      (chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
      (chartBaseChangeOpen_le_preimage_fst f ℐ U (a := a)
        (UX := (⊤ : X.Opens)))).hom.toAlgebra
  have hbridge : ((Γ(Limits.pullback f (blowUpToBase ℐ),
        chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens)) ⊗[Γ(X, ⊤)] Γ(F, ⊤)) ⧸
      Submodule.torsion' Γ(Limits.pullback f (blowUpToBase ℐ),
          chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
        (Γ(Limits.pullback f (blowUpToBase ℐ),
          chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens)) ⊗[Γ(X, ⊤)] Γ(F, ⊤))
        (Submonoid.powers (algebraMap Γ(X, ⊤)
          Γ(Limits.pullback f (blowUpToBase ℐ),
            chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
          (algebraMap Γ(S, U.1) Γ(X, ⊤) a))))
      ≃ₗ[Γ(Limits.pullback f (blowUpToBase ℐ),
        chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))]
      Γ(Stacks.StrictTransform.sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F,
        chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens)) :=
    Stacks.StrictTransform.sectionsSheafEquivQuotientTorsionBaseChange f
      (blowUpToBase ℐ) (exceptionalIdeal ℐ) F (isAffineOpen_top X)
      ⟨chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens),
        isAffineOpen_chartBaseChangeOpen f ℐ U (isAffineOpen_top X) hUX⟩
      (chartBaseChangeOpen_le_preimage_fst f ℐ U (a := a) (UX := (⊤ : X.Opens)))
      (algebraMap Γ(X, ⊤) Γ(Limits.pullback f (blowUpToBase ℐ),
        chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
        (algebraMap Γ(S, U.1) Γ(X, ⊤) a))
      (ideal_comap_exceptionalIdeal_chartBaseChangeOpen f ℐ U (isAffineOpen_top X) hUX)
  have hbij : Function.Bijective (algebraMap
      Γ(Limits.pullback f (blowUpToBase ℐ),
        chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))
      Γ(Limits.pullback f (blowUpToBase ℐ),
        chartBaseChangeOpen f ℐ U (a := a) (⊤ : X.Opens))) := Function.bijective_id
  exact Module.nonempty_linearEquiv_pi_localizedModule_away_of_bijective hbij hbridge
    (chartBaseChangeSectionAlgEquiv f ℐ U (isAffineOpen_top X) hUX g) r
    (nonempty_free_quotient_torsion_of_algEquiv Γ(F, ⊤)
      (chartBaseChangeSectionAlgEquiv f ℐ U (isAffineOpen_top X) hUX)
      (algebraMap Γ(S, U.1) Γ(X, ⊤) a) r g hfree)

end Stacks.Blowup

end
