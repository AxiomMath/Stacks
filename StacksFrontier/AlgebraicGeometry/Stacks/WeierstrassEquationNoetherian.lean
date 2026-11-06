module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroSectionsComp
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSectionsRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSectionsZero
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationFromIso
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationGeneration
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassEquationSections

/-!
# Local Weierstrass equations over Noetherian bases

Let `E` be a family over the spectrum of a Noetherian ring `A`, proper and smooth of relative
dimension one, with a section. Over `A_h` let `X` and `Y` be sections of `O(2·0)` and `O(3·0)`
satisfying the Weierstrass equation of a Weierstrass curve `C` in degree six, and let the sections
`zX, Y, z³` of `O(3·0)` have no common zero. They give a morphism to the plane cubic of `C`
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.cubicHomOfSections`), carrying the zero
section to the point at infinity. If it is an isomorphism on the fibre at a point `y` at which the
discriminant of `C` does not vanish, then it is an isomorphism near `y` (Stacks Tag 0G0Q), and `E`
is near the image of `y` a restriction of the Weierstrass family.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.hasLocalComparison_of_cubicSections`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.TensorPowers (natTensorPow)
open Stacks.ProjectiveFromSections
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

open Stacks.Cech (sectionsModule)

variable {A : Type u} [CommRing A] (E : PointedFamily (Spec (.of A))) [IsProper E.map]
  [SmoothOfRelativeDimension 1 E.map]

/-- **Divisibility by the canonical section is not created by extending the residue field.** If
the restriction of a section of `O(0)^{⊗ (1 + m)}` to the fibre at `p` is not a multiple of the
canonical section, then neither is its restriction to the fibre at any field-valued point with
kernel `p`, provided the higher cohomology of `O(0)^{⊗ m}` and `O(0)^{⊗ (1 + m)}` vanishes on the
fibre at `p`. A functional on the fibre at `p` separating the restriction from the multiples of
the canonical section extends, by cohomology and base change, to one over the field. -/
theorem restrictSection_notMem_range_of_ker_eq [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (m : ℕ)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf m) i))
    (hvan' : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf (1 + m)) i))
    (x : Γ(natTensorPow E.zeroSheaf (1 + m), ⊤))
    (hx : E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) (1 + m) x ∉
      Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := m) (E.fibreFamily p).zeroSection))
    {K : Type u} [Field K] (φ : A →+* K) (hφ : RingHom.ker φ = p) :
    E.restrictSection (Spec.map (CommRingCat.ofHom φ)) (1 + m) x ∉
      Set.range (mulSections (E.baseChange φ).zeroSheaf (m := m) (E.baseChange φ).zeroSection) := by
  rintro ⟨w, hw⟩
  obtain ⟨g, hg, m₁, H⟩ := E.exists_isBaseChange_restrictSection_of_isUnit p m hvan
  obtain ⟨g', hg', m₂, H'⟩ := E.exists_isBaseChange_restrictSection_of_isUnit p (1 + m) hvan'
  have hunit : ∀ a : A, a ∉ p → IsUnit (φ a) := fun a ha =>
    IsUnit.mk0 _ fun h => ha (hφ ▸ RingHom.mem_ker.2 h)
  have hunitκ : ∀ a : A, a ∉ p → IsUnit (algebraMap A p.ResidueField a) := fun a ha =>
    IsUnit.mk0 _ (by rwa [Ne, Ideal.algebraMap_residueField_eq_zero])
  obtain ⟨⟨ρ, hρ, hbc⟩, -⟩ := H φ (hunit g hg)
  obtain ⟨⟨ρ', hρ', hbc'⟩, -⟩ := H' φ (hunit g' hg')
  obtain ⟨⟨ρκ', hρκ', -⟩, -⟩ := H' (algebraMap A p.ResidueField) (hunitκ g' hg')
  let : Algebra A K := φ.toAlgebra
  let := sectionsModule E.map (natTensorPow E.zeroSheaf m) ⊤
  let := sectionsModule E.map (natTensorPow E.zeroSheaf (1 + m)) ⊤
  let := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf m) ⊤
  let := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf (1 + m)) ⊤
  let : Module A Γ(natTensorPow (E.baseChange φ).zeroSheaf (1 + m), ⊤) := Module.compHom _ φ
  let : IsScalarTower A K Γ(natTensorPow (E.baseChange φ).zeroSheaf (1 + m), ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module A Γ(natTensorPow (E.baseChange φ).zeroSheaf m, ⊤) := Module.compHom _ φ
  let : IsScalarTower A K Γ(natTensorPow (E.baseChange φ).zeroSheaf m, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Algebra A p.ResidueField := (algebraMap A p.ResidueField).toAlgebra
  let := sectionsModule (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf m) ⊤
  let := sectionsModule (E.fibreFamily p).map
    (natTensorPow (E.fibreFamily p).zeroSheaf (1 + m)) ⊤
  let : Module A Γ(natTensorPow (E.fibreFamily p).zeroSheaf (1 + m), ⊤) :=
    Module.compHom _ (algebraMap A p.ResidueField)
  let : IsScalarTower A p.ResidueField
      Γ(natTensorPow (E.fibreFamily p).zeroSheaf (1 + m), ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Stacks.Ample.IsInvertibleModule (E.fibreFamily p).total (E.fibreFamily p).zeroSheaf :=
    isInvertibleModule_zeroSheaf _
  have : Stacks.Ample.IsInvertibleModule (E.baseChange φ).total (E.baseChange φ).zeroSheaf :=
    isInvertibleModule_zeroSheaf _
  -- a functional on the fibre at `p` separating the restriction of `x` from the multiples of `s`
  let fκ := mulSectionsLinear (E.fibreFamily p).map (E.fibreFamily p).zeroSheaf
    (E.fibreFamily p).zeroSection m
  have hxκ : ρκ' x ∉ LinearMap.range fκ := by
    rintro ⟨v, hv⟩
    exact hx ⟨v, hv.trans (congrFun hρκ' x)⟩
  obtain ⟨l, hlx, hl⟩ := Submodule.exists_le_ker_of_notMem hxκ
  -- the residue field embeds into `K`
  let ι : p.ResidueField →+* K := Ideal.ResidueField.lift p φ (hφ ▸ le_rfl)
    fun a ha => hunit a ha
  have hι : ∀ a : A, ι (algebraMap A p.ResidueField a) = φ a :=
    Ideal.ResidueField.lift_algebraMap p φ _ _
  -- the functional, read on sections over `A` and extended over `K`
  let G : Γ(natTensorPow E.zeroSheaf (1 + m), ⊤) →ₗ[A] K :=
    { toFun := fun v => ι (l (ρκ' v))
      map_add' := fun a b => by rw [map_add, map_add, map_add]
      map_smul' := fun a v => by
        rw [map_smul, RingHom.id_apply]
        show ι (l ((algebraMap A p.ResidueField a) • ρκ' v)) = φ a * ι (l (ρκ' v))
        rw [map_smul, smul_eq_mul, map_mul, hι] }
  let Λ := hbc'.lift G
  have hΛ : ∀ v, Λ (ρ' v) = G v := hbc'.lift_eq G
  have hmul : ∀ v : Γ(natTensorPow E.zeroSheaf m, ⊤),
      ρ' (mulSections E.zeroSheaf E.zeroSection v) =
        mulSections (E.baseChange φ).zeroSheaf (E.baseChange φ).zeroSection (ρ v) := by
    intro v
    rw [hρ', hρ, restrictSection_mulSections, restrictSection_zeroSection]
  have hmulκ : ∀ v : Γ(natTensorPow E.zeroSheaf m, ⊤),
      ρκ' (mulSections E.zeroSheaf E.zeroSection v) ∈ LinearMap.range fκ := by
    intro v
    refine ⟨E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) m v,
      ?_⟩
    show mulSections _ _ _ = _
    rw [hρκ', restrictSection_mulSections, restrictSection_zeroSection]
  let fK := mulSectionsLinear (E.baseChange φ).map (E.baseChange φ).zeroSheaf
    (E.baseChange φ).zeroSection m
  have hker : ∀ w' : Γ(natTensorPow (E.baseChange φ).zeroSheaf m, ⊤), Λ (fK w') = 0 := by
    intro w'
    induction w' using hbc.inductionOn with
    | tmul v =>
      refine (congrArg Λ (hmul v).symm).trans ?_
      rw [hΛ]
      show ι (l (ρκ' _)) = 0
      rw [hl (hmulκ v), map_zero]
    | smul a v hv => rw [map_smul, map_smul, hv, smul_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  have h0 : Λ (mulSections _ _ w) = 0 := hker w
  rw [hw, ← congrFun hρ' x, hΛ] at h0
  exact hlx (ι.injective (h0.trans (map_zero ι).symm))

/-- **The fibre facts over a localization, at any field-valued point with kernel `p`.** A unit
multiple of the restriction to `A_h` of a section as in
`PointedFamily.restrictSection_notMem_range_of_ker_eq` restricts, at a field-valued point of
`Spec A_h` over `p`, to a section which is not a multiple of the canonical section. -/
theorem restrictSection_localization_notMem_range [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (m : ℕ)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf m) i))
    (hvan' : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf (1 + m)) i))
    (x : Γ(natTensorPow E.zeroSheaf (1 + m), ⊤))
    (hx : E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) (1 + m) x ∉
      Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := m) (E.fibreFamily p).zeroSection))
    {B : Type u} [CommRing B] (φ : A →+* B) (u : Bˣ) {K : Type u} [Field K] (ψ : B →+* K)
    (hψ : RingHom.ker (ψ.comp φ) = p) :
    letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf (1 + m)) ⊤
    (E.baseChange φ).restrictSection (Spec.map (CommRingCat.ofHom ψ)) (1 + m)
        ((u : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) (1 + m) x) ∉
      Set.range (mulSections ((E.baseChange φ).baseChange ψ).zeroSheaf (m := m)
        ((E.baseChange φ).baseChange ψ).zeroSection) := by
  have : SmoothOfRelativeDimension 1 (E.baseChange φ).map :=
    smoothOfRelativeDimension_pullback_map E _
  have : SmoothOfRelativeDimension 1 ((E.baseChange φ).baseChange ψ).map :=
    smoothOfRelativeDimension_pullback_map _ _
  let := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf (1 + m)) ⊤
  let := sectionsModule ((E.baseChange φ).baseChange ψ).map
    (natTensorPow ((E.baseChange φ).baseChange ψ).zeroSheaf m) ⊤
  let := sectionsModule ((E.baseChange φ).baseChange ψ).map
    (natTensorPow ((E.baseChange φ).baseChange ψ).zeroSheaf (1 + m)) ⊤
  have : Stacks.Ample.IsInvertibleModule ((E.baseChange φ).baseChange ψ).total
      ((E.baseChange φ).baseChange ψ).zeroSheaf :=
    isInvertibleModule_zeroSheaf _
  have hcomp : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (ψ.comp φ)) := by
    rw [← Spec.map_comp]
    rfl
  have hF := (E.restrictSection_comp_notMem_range (Spec.map (CommRingCat.ofHom φ))
    (Spec.map (CommRingCat.ofHom ψ)) _ hcomp x).1
    (E.restrictSection_notMem_range_of_ker_eq p m hvan hvan' x hx (ψ.comp φ) hψ)
  rw [(E.baseChange φ).restrictSection_smul ψ]
  rintro ⟨w, hw⟩
  refine hF ⟨(ψ ((u⁻¹ : Bˣ) : B)) • w, ?_⟩
  show mulSectionsLinear ((E.baseChange φ).baseChange ψ).map _ _ m _ = _
  rw [map_smul]
  show ψ ((u⁻¹ : Bˣ) : B) • mulSections _ _ w = _
  rw [hw, smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul]

/-- `PointedFamily.restrictSection_localization_notMem_range` at the residue field of a point of
`Spec B` with kernel `p`, in the spelling of the fibre `E ×_{Spec B} Spec κ(y)`. -/
theorem restrictSection_residueField_notMem_range [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (m : ℕ)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf m) i))
    (hvan' : ∀ i : ℕ, 0 < i → Subsingleton (cohomologyOverField p.ResidueField
      (E.fibreFamily p).map (natTensorPow (E.fibreFamily p).zeroSheaf (1 + m)) i))
    (x : Γ(natTensorPow E.zeroSheaf (1 + m), ⊤))
    (hx : E.restrictSection (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) (1 + m) x ∉
      Set.range (mulSections (E.fibreFamily p).zeroSheaf (m := m) (E.fibreFamily p).zeroSection))
    {B : Type u} [CommRing B] (φ : A →+* B) (u : Bˣ) (y : Spec (.of B))
    (hker : RingHom.ker ((Weierstrass.residueMapOf y).comp φ) = p) :
    letI := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf (1 + m)) ⊤
    (E.baseChange φ).restrictSection ((Spec (.of B)).fromSpecResidueField y) (1 + m)
        ((u : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) (1 + m) x) ∉
      Set.range (mulSections ((E.baseChange φ).pullback
        ((Spec (.of B)).fromSpecResidueField y)).zeroSheaf (m := m)
        ((E.baseChange φ).pullback ((Spec (.of B)).fromSpecResidueField y)).zeroSection) := by
  let := sectionsModule (E.baseChange φ).map (natTensorPow (E.baseChange φ).zeroSheaf (1 + m)) ⊤
  have h' : (E.baseChange φ).restrictSection
        (Spec.map (CommRingCat.ofHom (Weierstrass.residueMapOf y))) (1 + m)
        ((u : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) (1 + m) x) ∉
      Set.range (mulSections ((E.baseChange φ).pullback
        (Spec.map (CommRingCat.ofHom (Weierstrass.residueMapOf y)))).zeroSheaf (m := m)
        ((E.baseChange φ).pullback
          (Spec.map (CommRingCat.ofHom (Weierstrass.residueMapOf y)))).zeroSection) :=
    E.restrictSection_localization_notMem_range p m hvan hvan' x hx φ u
      (Weierstrass.residueMapOf y) hker
  rwa [Weierstrass.SpecMap_residueMapOf] at h'

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

/-- The pullback of a proper family along any morphism is proper. -/
private theorem isProper_pullback_map {S T : Scheme.{u}} (E : PointedFamily S) [IsProper E.map]
    (t : T ⟶ S) : IsProper (E.pullback t).map :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback E.map t)
    inferInstance

/-- **The genus-one conditions at a point of `Spec A`, read on the fibre over
`Ideal.ResidueField`.** The fibre over the residue field `κ(x)` of the scheme `Spec A` is the base
change of the fibre over `x.asIdeal.ResidueField` along the canonical isomorphism of the two
fields. -/
theorem _root_.AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.isGenusOneAt_iff_residueField
    {A : Type u} [CommRing A] (E : PointedFamily (Spec (.of A))) [IsProper E.map]
    (p : Ideal A) [p.IsPrime] :
    E.IsGenusOneAt (show Spec (.of A) from ⟨p, ‹_›⟩) ↔
      Module.finrank p.ResidueField (structureSheafCohomology
          (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).map 0) = 1 ∧
        genus (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))).map =
          1 := by
  set x : Spec (.of A) := ⟨p, ‹_›⟩
  let t : Spec (.of p.ResidueField) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))
  let i : CommRingCat.of p.ResidueField ⟶ (Spec (.of A)).residueField x :=
    (Scheme.Spec.residueFieldIso (.of A) x).inv
  let : Algebra p.ResidueField ((Spec (.of A)).residueField x) := i.hom.toAlgebra
  have hb : (Spec (.of A)).fromSpecResidueField x = Spec.map i ≫ t :=
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of A) x).symm
  have hpb : IsPullback (E.pullbackMap (Spec.map i) hb)
      (E.map.fiberToSpecResidueField x) (E.pullback t).map
      (Spec.map (CommRingCat.ofHom (algebraMap p.ResidueField
        ((Spec (.of A)).residueField x)))) :=
    E.isPullback_pullbackMap (Spec.map i) hb
  have := isProper_pullback_map E t
  have h₀ := finrank_structureSheafCohomology_baseChange p.ResidueField
    ((Spec (.of A)).residueField x) _ _ _ hpb 0
  have h₁ := genus_baseChange p.ResidueField ((Spec (.of A)).residueField x) _ _ _ hpb
  exact ⟨fun h => ⟨h₀.symm.trans h.1, h₁.symm.trans h.2⟩,
    fun h => ⟨h₀.trans h.1, h₁.trans h.2⟩⟩

variable {B : Type u} [CommRing B] (F : PointedFamily (Spec (.of B))) [IsProper F.map]
  [SmoothOfRelativeDimension 1 F.map] (C : WeierstrassCurve B)
  (X : Γ(natTensorPow F.zeroSheaf 2, ⊤)) (Y : Γ(natTensorPow F.zeroSheaf 3, ⊤))

/-- **A local Weierstrass equation from sections of `O(2·0)` and `O(3·0)`.** Sections `X`, `Y`
satisfying the Weierstrass equation of `C` in degree six, with `zX, Y, z³` generating and the zero
section in the chart of `Y` at the point `(0 : 1 : 0)`, give a local Weierstrass equation at every
point `y` at which the morphism to the plane cubic is an isomorphism on the fibre and the
discriminant of `C` does not vanish. -/
theorem hasLocalComparison_of_cubicSections [IsNoetherianRing B]
    (hrel : SatisfiesCubic C F.map (weierstrassSections F.zeroSheaf F.zeroSection X Y))
    (hcov : TopologicalSpace.IsOpenCover
      (nvCover (weierstrassSections F.zeroSheaf F.zeroSection X Y)))
    (σ₁ : Spec (.of B) ⟶
      (nvCover (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1).toScheme)
    (hσ₁ : σ₁ ≫ (nvCover (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1).ι = F.zero)
    (h₀ : σ₁.appTop (chartRatio (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1 0) = 0)
    (h₂ : σ₁.appTop (chartRatio (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1 2) = 0)
    (y : Spec (.of B))
    [Stacks.Ample.IsInvertibleModule
      (Limits.pullback F.map ((Spec (.of B)).fromSpecResidueField y))
      ((Scheme.Modules.pullback (Limits.pullback.fst F.map
        ((Spec (.of B)).fromSpecResidueField y))).obj (natTensorPow F.zeroSheaf 3))]
    (hiso : IsIso (cubicHomOfSections
      (satisfiesCubic_map (residueMapOf y) (Limits.pullback.snd F.map
          ((Spec (.of B)).fromSpecResidueField y))
        ((SpecMap_residueMapOf y) ▸ Limits.pullback.condition.symm)
        (satisfiesCubic_pullbackFamily (g := Limits.pullback.fst F.map
          ((Spec (.of B)).fromSpecResidueField y)) hrel))
      (isOpenCover_pullbackFamily (g := Limits.pullback.fst F.map
        ((Spec (.of B)).fromSpecResidueField y)) hcov)))
    (hΔ : C.Δ ∉ y.asIdeal) :
    HasLocalComparison family.{u} F y := by
  have : Smooth F.map := SmoothOfRelativeDimension.smooth 1 F.map
  obtain ⟨U, hyU, hU⟩ := exists_isIso_overPullback_cubicHomOfSections hrel hcov y hiso
  exact hasLocalComparison_of_isIso_overPullback F C (cubicHomOfSections hrel hcov)
    (cubicHomOfSections_projectionOf hrel hcov)
    (comp_cubicHomOfSections_eq_zeroOf hrel hcov F.zero F.zero_map σ₁ hσ₁ h₀ h₂) U hU y hyU hΔ

/-- **A local Weierstrass equation from sections whose fibre is a curve of genus one.** The
morphism to the plane cubic is an isomorphism on the fibre at `y`, with a unit discriminant there,
when the fibre has genus one and `X`, `Y` restrict to sections not divisible by the canonical
section. -/
theorem hasLocalComparison_of_isGenusOneAt [IsNoetherianRing B]
    (hrel : SatisfiesCubic C F.map (weierstrassSections F.zeroSheaf F.zeroSection X Y))
    (hcov : TopologicalSpace.IsOpenCover
      (nvCover (weierstrassSections F.zeroSheaf F.zeroSection X Y)))
    (σ₁ : Spec (.of B) ⟶
      (nvCover (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1).toScheme)
    (hσ₁ : σ₁ ≫ (nvCover (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1).ι = F.zero)
    (h₀ : σ₁.appTop (chartRatio (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1 0) = 0)
    (h₂ : σ₁.appTop (chartRatio (weierstrassSections F.zeroSheaf F.zeroSection X Y) 1 2) = 0)
    (y : Spec (.of B)) (hgy : F.IsGenusOneAt y)
    (hX : F.restrictSection ((Spec (.of B)).fromSpecResidueField y) 2 X ∉
      Set.range (mulSections (F.pullback ((Spec (.of B)).fromSpecResidueField y)).zeroSheaf
        (m := 1) (F.pullback ((Spec (.of B)).fromSpecResidueField y)).zeroSection))
    (hY : F.restrictSection ((Spec (.of B)).fromSpecResidueField y) 3 Y ∉
      Set.range (mulSections (F.pullback ((Spec (.of B)).fromSpecResidueField y)).zeroSheaf
        (m := 2) (F.pullback ((Spec (.of B)).fromSpecResidueField y)).zeroSection)) :
    HasLocalComparison family.{u} F y := by
  have := isProper_pullback_map F ((Spec (.of B)).fromSpecResidueField y)
  have hfib := @PointedFamily.isIso_cubicHomOfSections _ _
    (F.pullback ((Spec (.of B)).fromSpecResidueField y)) this
    (PointedFamily.smoothOfRelativeDimension_pullback_map F _) hgy.1 hgy.2 _ hX _ hY
    (C.map (residueMapOf y)) (satisfiesCubic_fibre y hrel) (isOpenCover_fibre y hcov)
  have hΔ : C.Δ ∉ y.asIdeal := (isUnit_residueMapOf_iff y C.Δ).1 (by
    rw [← WeierstrassCurve.map_Δ]
    exact hfib.2)
  exact hasLocalComparison_of_cubicSections F C X Y hrel hcov σ₁ hσ₁ h₀ h₂ y
    (isIso_of_isIso_fibre y hrel hcov hfib.1) hΔ

/-- **A point of `Spec A_f` over a point of `D(f)`**, whose residue map has kernel the point. -/
theorem exists_localization_point {A : Type u} [CommRing A] (x : Spec (.of A)) {f : A}
    (hf : f ∉ x.asIdeal) :
    ∃ y : Spec (.of (Localization.Away f)),
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) y = x ∧
        RingHom.ker ((residueMapOf y).comp (algebraMap A (Localization.Away f))) = x.asIdeal := by
  obtain ⟨y, hy⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hf
  let y' : Spec (.of (Localization.Away f)) := y
  refine ⟨y', hy, ?_⟩
  ext a
  have h := isUnit_residueMapOf_iff y' (algebraMap A (Localization.Away f) a)
  rw [isUnit_iff_ne_zero] at h
  rw [RingHom.mem_ker, RingHom.comp_apply, ← not_iff_not, ← ne_eq, h, ← hy]
  rfl

/-- **A local Weierstrass equation at a point of genus one over a Noetherian ring.** Near a point
`x` of `Spec A` at which the fibre is a curve of genus one, sections `X`, `Y` of `O(2·0)`,
`O(3·0)` over some `A_f` with `f ∉ x` satisfy a Weierstrass equation in degree six, the sections
`zX, Y, z³` generate, and the zero section lies in the chart of `Y` at `(0 : 1 : 0)`; on the fibre
the morphism to the plane cubic is an isomorphism and the discriminant is a unit. -/
theorem localWeierstrassAt_of_isGenusOneAt {A : Type u} [CommRing A] [IsNoetherianRing A]
    (E : PointedFamily (Spec (.of A))) [IsProper E.map] [SmoothOfRelativeDimension 1 E.map]
    (x : Spec (.of A)) (hx : E.IsGenusOneAt x) : LocalWeierstrassAt E x := by
  have : x.asIdeal.IsPrime := x.isPrime
  have hg := (E.isGenusOneAt_iff_residueField x.asIdeal).1 hx
  obtain ⟨h, hh, x₀, y₀, hx₀, hy₀, Hrel⟩ :=
    E.exists_weierstrassEquation_sections x.asIdeal hg.1 hg.2
  obtain ⟨r, hr, Hcov⟩ := E.exists_isOpenCover_nvCover x.asIdeal hg.1 hg.2 x₀ hy₀
  obtain ⟨r', hr', Hzero⟩ := E.exists_zero_lift_nvCover x.asIdeal hg.1 hg.2 x₀ hy₀
  have hf : h * r * r' ∉ x.asIdeal := fun hm =>
    (Ideal.IsPrime.mem_or_mem inferInstance hm).elim
      (fun hm' => (Ideal.IsPrime.mem_or_mem inferInstance hm').elim hh hr) hr'
  set B := Localization.Away (h * r * r')
  set φ := algebraMap A B
  have hunit : IsUnit (φ (h * r * r')) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, map_mul] at hunit
  have hu_h : IsUnit (φ h) := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hunit)
  have hu_r : IsUnit (φ r) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hunit)
  have hu_r' : IsUnit (φ r') := isUnit_of_mul_isUnit_right hunit
  obtain ⟨u, C, hC⟩ := Hrel φ hu_h
  set F := E.baseChange φ
  let := Stacks.Cech.sectionsModule F.map (natTensorPow F.zeroSheaf 2) ⊤
  let := Stacks.Cech.sectionsModule F.map (natTensorPow F.zeroSheaf 3) ⊤
  set X := (u : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 2 x₀
  set Y := (u : B) • E.restrictSection (Spec.map (CommRingCat.ofHom φ)) 3 y₀
  have hrel : SatisfiesCubic C F.map (weierstrassSections F.zeroSheaf F.zeroSection X Y) :=
    satisfiesCubic_weierstrassSections C F.map F.zeroSheaf F.zeroSection X Y hC
  have hcov : TopologicalSpace.IsOpenCover
      (nvCover (weierstrassSections F.zeroSheaf F.zeroSection X Y)) := Hcov φ hu_r u
  obtain ⟨σ₁, hσ₁, h₀, h₂⟩ := Hzero φ hu_r' u
  obtain ⟨y, hy, hker⟩ := exists_localization_point x hf
  -- the fibre at `y`
  have hpb := IsPullback.of_hasPullback E.map (Spec.map (CommRingCat.ofHom φ))
  have : IsProper F.map := isProper_pullback_map E _
  have hgy : F.IsGenusOneAt y := (PointedFamily.isGenusOneAt_iff_of_isPullback
    (Spec.map (CommRingCat.ofHom φ)) (Limits.pullback.fst E.map _) hpb y).2 (hy ▸ hx)
  have hvan : ∀ n, 1 ≤ n → ∀ i : ℕ, 0 < i → Subsingleton
      (cohomologyOverField x.asIdeal.ResidueField (E.fibreFamily x.asIdeal).map
        (natTensorPow (E.fibreFamily x.asIdeal).zeroSheaf n) i) :=
    fun n hn i hi =>
      (E.fibreFamily x.asIdeal).subsingleton_cohomologyOverField_zeroSheaf hg.1 hg.2 hn hi
  have hX := E.restrictSection_residueField_notMem_range x.asIdeal 1 (hvan 1 le_rfl)
    (hvan (1 + 1) (by omega)) x₀ hx₀ φ u y hker
  have hY := E.restrictSection_residueField_notMem_range x.asIdeal 2 (hvan 2 (by omega))
    (hvan (1 + 2) (by omega)) y₀ hy₀ φ u y hker
  rw [← hy]
  exact HasLocalComparison.of_isOpenImmersion _ y
    (hasLocalComparison_of_isGenusOneAt F C X Y hrel hcov σ₁ hσ₁ h₀ h₂ y hgy hX hY)

/-- **The local Weierstrass equation over Noetherian affine bases**: a family over a Noetherian
affine scheme, proper and smooth of relative dimension one with a section, is near every point of
genus one a restriction of the Weierstrass family. -/
theorem localWeierstrassNoetherian : LocalWeierstrassNoetherian.{u} :=
  localWeierstrassNoetherian_of_spec fun _ _ _ E _ _ x hx =>
    localWeierstrassAt_of_isGenusOneAt E x hx

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
