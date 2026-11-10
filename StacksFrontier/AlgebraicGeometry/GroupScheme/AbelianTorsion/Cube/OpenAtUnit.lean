module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.CubeSetup
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.FormalLift
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.LevelZero
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.Transport
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.Thickening.FaceSections
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.Thickening.FlatSections
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.Thickening.OpenTransport
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.Thickening.PointBaseChange
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.Assembly
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.Faces
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections

/-!
# Openness at the unit for the theorem of the cube

Let `A` be an abelian variety over an algebraically closed field `k`, and let `N` be an invertible
module on `A × A × A` which is trivial on the three faces `e × A × A`, `A × e × A` and
`A × A × e`. Then there is an open neighbourhood `U` of the unit `e` of the third factor such
that `N` is trivial over `A × A × U`.

## Main results

* `Stacks.Groupoids.openAtUnitStatement`: `OpenAtUnitStatement A`, the statement above.
* `Stacks.Groupoids.exists_isTrivial_pullback_cubeProj₃_of_isTrivial_faces`: the same, spelled
  out.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
  CartesianMonoidalCategory Opposite
open RingedSpaceModuleAdjunction Stacks.CubeOpenAtUnit
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] [IsAlgClosed k] (A : Over (Spec (.of k))) [GrpObj A]
  [AlgebraicGeometry.IsAbelianVariety k A]

omit [IsAlgClosed k] in
/-- The closed point of `Spec k` maps, along `Spec k ⟶ Spec R`, into `V(ker(R ⟶ k))`. -/
theorem mem_range_truncationBase_ker {R : Type u} [CommRing R]
    (φ₀ : CommRingCat.of R ⟶ CommRingCat.of k) :
    (Spec.map φ₀).base (IsLocalRing.closedPoint k) ∈
      Set.range (Stacks.FormalNeighbourhood.truncationBase (RingHom.ker φ₀.hom) 0).base := by
  have : (RingHom.ker φ₀.hom).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨(Ideal.comap φ₀.hom ⊥).map (Ideal.Quotient.mk _), ?_⟩, ?_⟩
  · rw [← RingHom.ker_eq_comap_bot]
    refine Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, pow_one]
  · apply PrimeSpectrum.ext
    change Ideal.comap (Ideal.Quotient.mk _) (Ideal.map (Ideal.Quotient.mk _) _) =
      Ideal.comap φ₀.hom (IsLocalRing.maximalIdeal k)
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    refine sup_eq_left.2 fun a ha => ?_
    rwa [Ideal.mem_comap, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_one] at ha

/-- **Openness at the unit.** An invertible module on `A × A × A` trivial on the three faces is
trivial over `A × A × U` for an open neighbourhood `U` of the unit of the third factor. -/
theorem openAtUnitStatement : OpenAtUnitStatement A := by
  intro N hN h₁ h₂ h₃
  have : IsSeparated A.hom := inferInstance
  have hAΓ : IsIso A.hom.appTop := by
    have h := isIso_globalSections_of_geometricallyIntegral k A.hom
    exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv A.hom.appTop
  set e := unitPt A
  obtain ⟨U, hU, heU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := e.base (IsLocalRing.closedPoint k)) (U := ⊤) trivial
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsNoetherianRing Γ(A.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let σ : Spec (.of Γ(A.left, U)) ⟶ A.left := hU.fromSpec
  have : IsOpenImmersion σ := hU.isOpenImmersion_fromSpec
  have hrange : Set.range e.base ⊆ Set.range σ.base := by
    rintro _ ⟨y, rfl⟩
    have hy : y = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
    subst hy
    change _ ∈ Set.range hU.fromSpec.base
    rwa [hU.range_fromSpec]
  let e' : Spec (.of k) ⟶ Spec (.of Γ(A.left, U)) := IsOpenImmersion.lift σ e hrange
  have he' : e' ≫ σ = unitPt A := IsOpenImmersion.lift_fac σ e hrange
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective e'
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (σ ≫ A.hom)
  have hψφ : ψ ≫ φ₀ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ₀, hψ, ← Category.assoc, he', unitPt_hom, Spec.map_id]
  have hsurj : Function.Surjective φ₀.hom := fun y =>
    ⟨ψ.hom y, by rw [← CommRingCat.comp_apply, hψφ]; rfl⟩
  have hφ : Spec.map (CommRingCat.ofHom φ₀.hom) = e' := hφ₀
  set m := RingHom.ker φ₀.hom
  have : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  set ρ := cubeFst A σ
  set f := cubeBase A σ
  have := hN
  set NP : (cubeT A σ).Modules := (Scheme.Modules.pullback ρ).obj N
  have hNP : Stacks.SheafOfModules.IsInvertible (cubeT A σ).presheaf
      (cubeT A σ).ringCatSheaf.property NP :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj ρ N
  have : Stacks.SheafOfModules.IsInvertible (cubeT A σ).sheaf.obj
      (cubeT A σ).ringCatSheaf.property NP := hNP
  have : NP.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible NP
  set s := cubeSection A σ he'
  obtain ⟨hsci, hsker⟩ := ker_eq_baseIdealSheaf_of_isPullback φ₀.hom hsurj f s _
    (by rw [hφ]; exact isPullback_cubeSection A σ he')
  obtain ⟨τ⟩ := nonempty_pullback_pullback_iso_unit ρ N s (𝟙 _) (cubeFace₃ A).left
    (by rw [Category.id_comp]; exact cubeSection_fst A σ he') h₃
  set j := cubeFace A σ
  set s' := faceSection A σ he'
  obtain ⟨hs'ci, hs'ker⟩ := ker_eq_baseIdealSheaf_of_isPullback φ₀.hom hsurj (faceBase A σ) s' _
    (by rw [hφ]; exact isPullback_faceSection A σ he')
  have hs'ker' : ∀ i, s'.ker = baseIdealSheaf _ m (j i ≫ f) ^ 1 := fun i => by
    rw [cubeFace_base]
    exact hs'ker
  have hK : ∀ c : (H (A ⊗ A).left 1).obj (SheafOfModules.unit (A ⊗ A).left.ringCatSheaf),
      (∀ i, ((H (A ⊗ A).left 1).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (faceToW A i).left).unit.app
          (SheafOfModules.unit (A ⊗ A).left.ringCatSheaf))).hom c = 0) → c = 0 := by
    intro c hc
    have hinjK := Stacks.KunnethLowDegree.injective_H1_faces k A.hom A.hom e (unitPt_hom A) e
      (unitPt_hom A)
    refine hinjK (a₂ := 0) ?_
    have h0 := hc 0
    have h1 := hc 1
    simp only [faceToW, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext (h1.trans (LinearMap.map_zero _).symm) (h0.trans (LinearMap.map_zero _).symm)
  have hinj := jointlyInjective_quoMap_one f m NP s hsker (fun i => j i) (fun _ => s')
    hs'ker' (fun i => (faceToW A i).left) (fun i => faceToW_cubeSection A σ he' i) τ hK
  have hflat : ∀ U : (cubeT A σ).affineOpens,
      (Stacks.Coherent.baseSectionHom _ f U.1).Flat ∧
        Module.Flat Γ(cubeT A σ, U.1) Γ(NP, U.1) := fun U =>
    ⟨flat_baseSectionHom f U, flat_sections_of_isInvertible NP U⟩
  let faces := fun i => Face.ofClosedImmersion NP (j i)
  have hflatF : ∀ i, ∀ U : (faces i).F.affineOpens,
      (Stacks.Coherent.baseSectionHom _ ((faces i).j ≫ f) U.1).Flat ∧
        Module.Flat Γ((faces i).F, U.1) Γ((faces i).G', U.1) := fun i U => by
    have : Flat ((faces i).j ≫ f) := by
      change Flat (j i ≫ f)
      rw [cubeFace_base]
      infer_instance
    exact ⟨flat_baseSectionHom _ U, flat_sections_of_isInvertible
      ((Scheme.Modules.pullback (j i)).obj NP) U⟩
  have hface : ∀ i, Nonempty ((Scheme.Modules.pullback (j i)).obj NP ≅
      SheafOfModules.unit (faceT A σ).ringCatSheaf) := fun i =>
    nonempty_pullback_pullback_iso_unit ρ N (j i) (pullback.fst _ _) (faceOf A i).left
      (cubeFace_fst A σ i) (by fin_cases i; exacts [h₁, h₂])
  have hsurjF : ∀ n i, Function.Surjective
      ((quoDrop ((faces i).j ≫ f) m (faces i).G' (n + 1)).app ⊤) := fun n i =>
    surjective_quoDrop_app_top_of_iso_unit A.hom (σ ≫ A.hom)
      (pullback.fst _ _ ≫ pullback.fst A.hom A.hom) ((faces i).j ≫ f)
      (by change IsPullback _ (j i ≫ f) _ _; rw [cubeFace_base]; exact isPullback_faceT A σ) m
      (faces i).G' (hface i).some n
  let α := Stacks.Algebraization.idealQuotientPushforwardIso (baseIdealSheaf _ m f) 1 NP s hsker
  let t₀ : Γ(quo f m NP 1, ⊤) := α.inv.app ⊤ (τ.inv.app ⊤ (1 : Γ((A ⊗ A).left, ⊤)))
  have ht₀ : ∀ y, y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback s).obj NP)
      (α.hom.app ⊤ t₀) := by
    intro y
    have h1 : α.hom.app ⊤ t₀ = τ.inv.app ⊤ (1 : Γ((A ⊗ A).left, ⊤)) := by
      change (α.inv ≫ α.hom).app ⊤ _ = _
      rw [Iso.inv_hom_id]
      rfl
    have h2 := Stacks.Ample.nonvanishingLocus_congr τ.symm
      (show Γ(SheafOfModules.unit (A ⊗ A).left.ringCatSheaf, ⊤) from (1 : Γ((A ⊗ A).left, ⊤)))
    have h3 : Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback s).obj NP)
        (τ.inv.app ⊤ (1 : Γ((A ⊗ A).left, ⊤))) = Set.univ :=
      h2.trans (Stacks.Models.nonvanishingLocus_unit_one _)
    rw [h1, h3]
    trivial
  have hlift := exists_lift_of_faces f m NP hflat faces hflatF hsurjF hinj t₀
  set x := e'.base (IsLocalRing.closedPoint k)
  have hx : x ∈ Set.range (Stacks.FormalNeighbourhood.truncationBase m 0).base := by
    rw [show x = (Spec.map φ₀).base (IsLocalRing.closedPoint k) by rw [hφ₀]]
    exact mem_range_truncationBase_ker φ₀
  obtain ⟨U', hxU', htriv⟩ := exists_isTrivial_of_lifts f m NP s hsker t₀ ht₀ hlift x hx
  refine ⟨σ ''ᵁ U', ⟨x, hxU', ?_⟩, isTrivial_pullback_fst_image (cubeProj₃ A).left σ N U' ?_⟩
  · change (e' ≫ σ).base _ = _
    rw [he']
  · exact nonempty_modulePullback_comp_iso_unit ρ N (pullback.fst f U'.ι) htriv

/-- **Openness at the unit**, spelled out: an invertible `N` on `A × A × A` trivial on the three
faces is trivial over `A × A × U` for an open neighbourhood `U` of the unit of the third factor. -/
theorem exists_isTrivial_pullback_cubeProj₃_of_isTrivial_faces
    (N : SheafOfModules.{u} (structureSheafRing (cubeObj A).left.toRingedSpace))
    (hN : Stacks.SheafOfModules.IsInvertible (cubeObj A).left.presheaf
      (cubeObj A).left.ringCatIsSheaf N)
    (h₁ : Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
      (pullbackOver (cubeFace₁ A) N))
    (h₂ : Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
      (pullbackOver (cubeFace₂ A) N))
    (h₃ : Stacks.SheafOfModules.IsTrivial (A ⊗ A).left.presheaf (A ⊗ A).left.ringCatIsSheaf
      (pullbackOver (cubeFace₃ A) N)) :
    ∃ U : A.left.Opens, η[A].left (IsLocalRing.closedPoint k) ∈ U ∧
      Stacks.SheafOfModules.IsTrivial (pullback (cubeProj₃ A).left U.ι).presheaf
        (pullback (cubeProj₃ A).left U.ι).ringCatIsSheaf
        ((modulePullback (pullback.fst (cubeProj₃ A).left U.ι).toLRSHom.toShHom).obj N) :=
  openAtUnitStatement A N hN h₁ h₂ h₃

end Stacks.Groupoids

end
