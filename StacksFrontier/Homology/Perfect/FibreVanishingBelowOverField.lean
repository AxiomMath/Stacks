module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.Homology.Perfect.SingleDegreeFibreOverField
public import StacksFrontier.Homology.ExtendScalars.IndependentUniverses

/-!
# A bounded complex of projectives with no fibre cohomology below `a` over a field

Let `R` be a commutative ring, `L` a bounded complex of finite projective `R`-modules and
`φ : R → k` a ring map to a field. If the cohomology of `L ⊗_R k` vanishes in all degrees `< a`,
then on a principal neighbourhood `D(g)` of the point `ker φ` the complex `L` is homotopy
equivalent to a bounded complex of finite free modules concentrated in degrees `≥ a`.

This is [stacks 0BYP] at the prime `ker φ`, with the derived fibre computed degreewise and
compared with the fibre over the extension `κ(ker φ) → k`.

## Main results

* `StacksDraft.Perfect.exists_away_homotopyEquiv_free_of_isZero_homology_lt`: the principal
  neighbourhood and the homotopy equivalence.
* `StacksDraft.Perfect.exists_homotopyEquiv_free_of_isUnit`: its base change to every algebra
  in which `g` becomes a unit.
* `StacksDraft.Perfect.exists_homotopyEquiv_free_of_isZero_homology_lt`: the two combined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

variable {R : Type u} [CommRing R]

/-- **A bounded complex of finite projectives which, after base change to a field, has no
cohomology below degree `a`, is homotopy equivalent on a principal open `D(g)` containing the
point to a bounded complex of finite free modules concentrated in degrees `≥ a`.** -/
theorem exists_away_homotopyEquiv_free_of_isZero_homology_lt {k : Type u} [Field k]
    (φ : R →+* k) (L : CochainComplex (ModuleCat.{max v u} R) ℤ) (a₀ b₀ : ℤ) [L.IsStrictlyGE a₀]
    [L.IsStrictlyLE b₀] (hfin : ∀ j, Module.Finite R (L.X j))
    (hproj : ∀ j, Module.Projective R (L.X j)) (a : ℤ)
    (hvan : ∀ j, j < a → IsZero ((((ModuleCat.extendScalars.{u, u, max v u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).homology j)) :
    ∃ g : R, φ g ≠ 0 ∧ ∃ (d : ℤ → ℕ) (b : ℤ)
      (P : CochainComplex (ModuleCat.{max v u} (Localization.Away g)) ℤ),
      P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Nonempty (P.X i ≅ ModuleCat.of (Localization.Away g)
        (ULift.{v} (Fin (d i) → Localization.Away g)))) ∧
      Nonempty (HomotopyEquiv
        (((ModuleCat.extendScalars.{u, u, max v u}
          (algebraMap R (Localization.Away g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
        P) := by
  classical
  let p := RingHom.ker φ
  have : p.IsPrime := RingHom.ker_isPrime φ
  have hLproj : ∀ j, Projective (L.X j) := fun j => (L.X j).projective_of_categoryTheory_projective
  let K := (DerivedCategory.Q).obj L
  have hK : IsPerfect K := ⟨L, a₀, b₀, inferInstance, inferInstance, hfin, hproj, ⟨Iso.refl _⟩⟩
  -- the lift `κ(p) → k`
  have hunit : p.primeCompl ≤ (IsUnit.submonoid k).comap φ :=
    fun x hx => isUnit_iff_ne_zero.2 fun h => hx (RingHom.mem_ker.2 h)
  let ι : p.ResidueField →+* k := Ideal.ResidueField.lift p φ le_rfl hunit
  have hι : ι.comp (algebraMap R p.ResidueField) = φ := by
    ext r
    exact Ideal.ResidueField.lift_algebraMap p φ le_rfl hunit r
  have hGl : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} ι) := by
    let : Algebra p.ResidueField k := ι.toAlgebra
    refine extendScalars_preservesFiniteLimits_of_flat'.{u, v} ι ?_
    rw [← ι.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
    infer_instance
  have hGc : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, max v u} ι) :=
    ModuleCat.extendScalars_preservesFiniteColimits ι
  -- the derived fibre at `p` has no cohomology below `a`
  have hzero : ∀ j, j < a → IsZero (derivedFibreHomology.{u, v} p K j) := by
    intro j hj
    obtain ⟨e0⟩ := nonempty_totalDerivedExtensionScalars_obj_Q_iso.{u, v}
      (algebraMap R p.ResidueField) L b₀
    let C0 := ((ModuleCat.extendScalars.{u, u, max v u}
      (algebraMap R p.ResidueField)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
    let H0 : derivedFibreHomology.{u, v} p K j ≅ C0.homology j :=
      (DerivedCategory.homologyFunctor _ j).mapIso e0 ≪≫
        (DerivedCategory.homologyFunctorFactors _ j).app C0
    obtain ⟨hfinH, -, -⟩ := exists_away_bounded_free_complex_representing.{u, v} p K hK
    have : Module.Finite p.ResidueField (derivedFibreHomology.{u, v} p K j) := hfinH j
    have : Module.Finite p.ResidueField (C0.homology j) := Module.Finite.equiv H0.toLinearEquiv
    let G := ModuleCat.extendScalars.{u, u, max v u} ι
    let Hk : (((ModuleCat.extendScalars.{u, u, max v u}
        (ι.comp (algebraMap R p.ResidueField))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).homology j ≅ G.obj (C0.homology j) :=
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).mapIso
        ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, max v u}
          (algebraMap R p.ResidueField) ι) (ComplexShape.up ℤ)).app L) ≪≫
        (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso G
          (ComplexShape.up ℤ) j).app C0
    have hz := hvan j hj
    rw [← hι] at hz
    have h0 : Module.finrank k (G.obj (C0.homology j)) = 0 := by
      have := ModuleCat.subsingleton_of_isZero (hz.of_iso Hk.symm)
      exact Module.finrank_zero_of_subsingleton
    rw [finrank_extendScalars_of_field.{u, v} ι] at h0
    have : Subsingleton (C0.homology j) := Module.finrank_zero_iff.mp h0
    exact (ModuleCat.isZero_of_subsingleton _).of_iso H0
  obtain ⟨g, hg, -, P, b, hPa, hPb, hPX, ⟨eP⟩⟩ :=
    exists_away_bounded_free_complex_representing_of_fibre_vanishing_below.{u, v} p K
      (isPseudoCoherent_of_isPerfect K hK) ⟨a₀, inferInstance⟩ a hzero
  refine ⟨g, fun h => hg (RingHom.mem_ker.2 h), _, b, P, hPa, hPb, hPX, ?_⟩
  obtain ⟨eg⟩ := nonempty_totalDerivedExtensionScalars_obj_Q_iso.{u, v}
    (algebraMap R (Localization.Away g)) L b₀
  let Lg := ((ModuleCat.extendScalars.{u, u, max v u}
    (algebraMap R (Localization.Away g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have : CochainComplex.IsStrictlyLE Lg b₀ := by dsimp only [Lg]; infer_instance
  have : ∀ j, Projective (Lg.X j) := fun j =>
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R (Localization.Away g))).map_projective _
      (hLproj j)
  have : CochainComplex.IsKProjective Lg := CochainComplex.isKProjective_of_projective Lg b₀
  have : ∀ j, Projective (P.X j) := fun j =>
    Projective.of_iso (hPX j).some.symm
      (ModuleCat.of (Localization.Away g)
        (ULift.{v} (Fin _ → Localization.Away g))).projective_of_categoryTheory_projective
  have : CochainComplex.IsKProjective P := CochainComplex.isKProjective_of_projective P b
  exact nonempty_homotopyEquiv_of_Q_iso Lg P (eg.symm ≪≫ eP.symm)

/-- A homotopy equivalence over `R_g` between `L ⊗ R_g` and a bounded complex of finite free
modules concentrated in degrees `[a, b]` gives one over every `R`-algebra in which `g` becomes a
unit. -/
theorem exists_homotopyEquiv_free_of_isUnit (L : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (g : R) (a b : ℤ) (d : ℤ → ℕ)
    (P : CochainComplex (ModuleCat.{max v u} (Localization.Away g)) ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hPX : ∀ i, Nonempty (P.X i ≅ ModuleCat.of (Localization.Away g)
      (ULift.{v} (Fin (d i) → Localization.Away g))))
    (e : HomotopyEquiv
      (((ModuleCat.extendScalars.{u, u, max v u}
        (algebraMap R (Localization.Away g))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) P)
    {R'' : Type u} [CommRing R''] (θ : R →+* R'') (hθ : IsUnit (θ g)) :
    ∃ P'' : CochainComplex (ModuleCat.{max v u} R'') ℤ, P''.IsStrictlyGE a ∧ P''.IsStrictlyLE b ∧
      (∀ i, Nonempty (P''.X i ≅ ModuleCat.of R'' (ULift.{v} (Fin (d i) → R'')))) ∧
      Nonempty (HomotopyEquiv
        (((ModuleCat.extendScalars.{u, u, max v u} θ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) P'') := by
  let θ' : Localization.Away g →+* R'' := IsLocalization.Away.lift g hθ
  have hθ' : θ'.comp (algebraMap R (Localization.Away g)) = θ := IsLocalization.Away.lift_comp g hθ
  let G := ModuleCat.extendScalars.{u, u, max v u} θ'
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, ?_, ?_, fun i => ?_, ?_⟩
  · exact (CochainComplex.isStrictlyGE_iff _ a).2
      fun j hj => G.map_isZero (P.isZero_of_isStrictlyGE a j hj)
  · exact (CochainComplex.isStrictlyLE_iff _ b).2
      fun j hj => G.map_isZero (P.isZero_of_isStrictlyLE b j hj)
  · exact ⟨G.mapIso (hPX i).some ≪≫ (extendScalars_standard_free_iso.{u, v} θ' (d i)).some⟩
  · have e₁ : HomotopyEquiv
        (((ModuleCat.extendScalars.{u, u, max v u} θ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{u, u, max v u}
            (algebraMap R (Localization.Away g))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)) := by
      rw [← hθ']
      exact HomotopyEquiv.ofIso ((NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp.{u, max v u} (algebraMap R (Localization.Away g)) θ')
        (ComplexShape.up ℤ)).app L)
    exact ⟨e₁.trans (G.mapHomotopyEquiv e)⟩

/-- **A bounded complex of finite projectives which, after base change to a field, has no
cohomology below degree `a`, is homotopy equivalent to a bounded complex of finite free modules
concentrated in degrees `≥ a` after base change to every algebra in which some `g` with
`φ g ≠ 0` becomes a unit.** -/
theorem exists_homotopyEquiv_free_of_isZero_homology_lt {k : Type u} [Field k]
    (φ : R →+* k) (L : CochainComplex (ModuleCat.{max v u} R) ℤ) (a₀ b₀ : ℤ) [L.IsStrictlyGE a₀]
    [L.IsStrictlyLE b₀] (hfin : ∀ j, Module.Finite R (L.X j))
    (hproj : ∀ j, Module.Projective R (L.X j)) (a : ℤ)
    (hvan : ∀ j, j < a → IsZero ((((ModuleCat.extendScalars.{u, u, max v u} φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).homology j)) :
    ∃ g : R, φ g ≠ 0 ∧ ∃ (d : ℤ → ℕ) (b : ℤ), ∀ {R'' : Type u} [CommRing R''] (θ : R →+* R''),
      IsUnit (θ g) → ∃ P'' : CochainComplex (ModuleCat.{max v u} R'') ℤ,
        P''.IsStrictlyGE a ∧ P''.IsStrictlyLE b ∧
        (∀ i, Nonempty (P''.X i ≅ ModuleCat.of R'' (ULift.{v} (Fin (d i) → R'')))) ∧
        Nonempty (HomotopyEquiv
          (((ModuleCat.extendScalars.{u, u, max v u} θ).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L) P'') := by
  obtain ⟨g, hg, d, b, P, hPa, hPb, hPX, ⟨e⟩⟩ :=
    exists_away_homotopyEquiv_free_of_isZero_homology_lt.{u, v} φ L a₀ b₀ hfin hproj a hvan
  exact ⟨g, hg, d, b, fun θ hθ => exists_homotopyEquiv_free_of_isUnit.{u, v} L g a b d P hPX e θ hθ⟩

end StacksDraft.Perfect

end
