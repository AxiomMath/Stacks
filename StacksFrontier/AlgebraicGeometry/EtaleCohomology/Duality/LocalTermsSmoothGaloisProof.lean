module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsSmoothGalois
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryPointLocalRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.GaloisModuleLevelStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.GaloisModuleInertiaTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SepClosureGaloisFixingSubgroup
public import StacksFrontier.RingTheory.Invariant.StrictHenselizationInertiaEmbedding
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SourceAutGaloisElement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Stalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedImmersionTwistCompat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PuncturedDiscreteValuationSpectrum
public import StacksFrontier.AlgebraicGeometry.FieldToResidue

/-!
# The Galois modules at the points at infinity of a smooth compactification

This file proves `Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryGaloisInput`.

Let `x` be a point of `X̄_k̄` outside `V_k̄` and `y` its image in `X̄`. Then `X̄` is a smooth
proper curve over `k` (`Stacks.EtaleCohomology.isCurve_and_smooth_of_fieldBaseChange`), so
`A = 𝒪_{X̄,y}` is a discrete valuation ring with fraction field `K = κ(η_V)` and finite residue
field, and some function on `V` is not in `A` (`X̄` is separated and `y ∉ V`). For a place `P` of
the separable closure `L` of `K` over `A`, the inertia group `I = I_P` is a boundary inertia group.

For a geometric point `s̄` over `x`, the projection `X̄_k̄ ⟶ X̄` is weakly étale, so it induces
an isomorphism of strict henselizations `𝒪^{sh}_{X̄,s̄} ≅ H = 𝒪^{sh}_{X̄_k̄,s̄}` (Stacks 094Z);
thus `H` is a strict henselization of `A`, `H ≅ (B_P)^{I}` (Stacks 08HT), and the fraction field
`K^{sh}` of `H` embeds into `L` with image the inertia field `L^{I}`. Through `L ⊆ Ω` this gives a
geometric point `t̄` of `Spec K^{sh}` over the geometric generic point of `V`, and the absolute
Galois group of `K^{sh}` at `t̄` is identified with `I` as a topological group
(`Stacks.EtaleCohomology.sepClosureAutHomeomorphFixingSubgroup`). The Galois module of `Gₙ` at
`t̄` is `(ℤ/ℓⁿ⁺¹)^r` with `σ` acting through `ρ₀` of its image in `I`
(`Stacks.EtaleCohomology.exists_levelPullbackGaloisModule_addEquiv`), so the bounds on the
invariants and cocycles of `I` transfer
(`Stacks.EtaleCohomology.galoisInvariants_and_cocycles_killed_of_inertia`).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.smoothBoundaryGaloisInput`.
* `Stacks.EtaleCohomology.LAdicSheaf.localTermsSmoothBoundaryStalkInput` — the input of
  `Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_smooth`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.Scheme IsLocalRing Stacks.Frobenius
open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

-- Hom types must resolve `Quiver Scheme` through the category structure.
attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] GeometricPoint.residueFieldAlgebra

/-- **The Galois modules at the points at infinity of a smooth compactification are governed by
inertia groups** (Weil II 1.8, the boundary part of Stacks 03VH). -/
theorem LAdicSheaf.smoothBoundaryGaloisInput : LAdicSheaf.SmoothBoundaryGaloisInput.{u} := by
  intro B V ℓ _ _ _ _ _ _ iIrr _ k _ _ f _ _ _ _ j kbar _ _ _ iYc iYs p _ _ hℓp L Ω _ _ _ _ _ _ _
    _ _ r ρ₀ hρ₀ x hx
  classical
  have : Fintype k := Fintype.ofFinite k
  -- `X̄` is a smooth proper curve over `k`
  let Xb : Scheme.{u} := j.obj.right.left
  let fb : Xb ⟶ Spec (.of k) := j.obj.right.hom
  have : IsProper fb := j.property.2
  have : IsCurve kbar (pullback.snd fb (specAlgebraMap k kbar)) := iYc
  have : Smooth (pullback.snd fb (specAlgebraMap k kbar)) := iYs
  obtain ⟨hXc, hXs⟩ := isCurve_and_smooth_of_fieldBaseChange kbar fb
  have : IsIntegral Xb := hXc.toIsVariety.toIsIntegral
  have hdim : topologicalKrullDim Xb = 1 := hXc.topologicalKrullDim_eq_one
  let jV : V.1 ⟶ Xb := j.obj.hom.left
  have : IsOpenImmersion jV := j.property.1
  let pr := fieldBaseChangeProj j.obj.right kbar
  -- the point `y` of `X̄` under `x`
  let y : Xb := pr.base x
  have hyV : y ∉ Set.range jV.base := fun hy =>
    hx (by rwa [range_fieldBaseChangeMap j.obj.hom kbar])
  have hgen : jV.base (genericPoint V.1) = genericPoint Xb := genericPoint_eq_of_isOpenImmersion jV
  have hy : jV.base (genericPoint V.1) ⤳ y :=
    hgen ▸ (genericPoint_spec Xb).specializes (Set.mem_univ y)
  have hyg : y ≠ genericPoint Xb := fun h => hyV ⟨genericPoint V.1, hgen.trans h.symm⟩
  -- the local ring `A = 𝒪_{X̄,y}`
  let K := V.1.residueField (genericPoint V.1)
  let A : Type u := Xb.presheaf.stalk y
  let iAK : Algebra A K := (curveLocalRingToFunctionField jV hy).hom.toAlgebra
  have : IsFractionRing A K := isFractionRing_curveLocalRingToFunctionField jV hy
  have : IsDiscreteValuationRing A := IsCurve.isDiscreteValuationRing_stalk k fb hyg
  have hfin : Finite (ResidueField A) := finite_residueField fb y
    (Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint Xb hdim hyg)
  have hchar : ℓ ≠ ringChar (ResidueField A) := by
    have : CharP (ResidueField A) p :=
      charP_of_injective_ringHom (fieldToResidue fb y).hom.injective p
    rwa [ringChar.eq (ResidueField A) p]
  have hsep : ∃ a : Γ(V.1, ⊤), (V.1.evaluation ⊤ (genericPoint V.1) trivial).hom a ∉
      Set.range (algebraMap A K) := by
    by_contra hc
    push Not at hc
    exact hyV (mem_range_of_forall_mem_range_curveLocalRing jV hy fb
      (IsFractionRing.injective A K) hc)
  -- the place `P` and the inertia group
  let iAL : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (integralClosure A L)
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  refine ⟨P.inertia Gal(L / K), ⟨A, inferInstance, inferInstance, inferInstance, iAK,
    inferInstance, iAL, inferInstance, P, hP, hfin, hchar, hsep, rfl⟩, ?_⟩
  intro e he n s hs
  -- the big étale site and `X̄_k̄ ⊇ V_k̄`
  let Y : Scheme.{u} := fieldBaseChange j.obj.right kbar
  let Vk : Scheme.{u} := fieldBaseChange (Over.mk f) kbar
  let j' : Vk ⟶ Y := fieldBaseChangeMap j.obj.hom kbar
  let prV : Vk ⟶ V.1 := fieldBaseChangeProj (Over.mk f) kbar
  have : Small.{u} ({Y, Xb, Vk} : Set Scheme.{u}) := inferInstance
  let B' : BigEtaleSite.{u} := BigEtaleSite.ofSet ({Y, Xb, Vk} : Set Scheme.{u})
  have hY : B'.Contains Y := BigEtaleSite.contains_ofSet _ (by simp)
  have hXb : B'.Contains Xb := BigEtaleSite.contains_ofSet _ (by simp)
  have : IsOpenImmersion j' :=
    have : MorphismProperty.IsStableUnderComposition @IsOpenImmersion.{u} :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (inferInstanceAs (IsOpenImmersion j.obj.hom.left))
      (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w j.obj.hom).symm (Category.id_comp _).symm
  have : Nonempty Vk := by
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (Over.mk f).hom)
      (g := specAlgebraMap k kbar) (genericPoint V.1) (default : Spec (.of kbar))
      (Subsingleton.elim _ _)
    exact ⟨z⟩
  let fY : Y ⟶ Spec (.of kbar) := pullback.snd fb (specAlgebraMap k kbar)
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have hs' : s.hom.base default ∉ Set.range j'.base := hs ▸ hx
  obtain ⟨hHdom, hHdvr, ϖ, hϖ, eK, heK⟩ :=
    exists_strictHenselizationBaseChange_iso_of_isCurve fY j' B' hY s hs'
  -- the strict henselization `H = 𝒪^{sh}_{X̄_k̄,s̄}` and its fraction field `K^{sh}`
  let H := etaleLocalRing B' Y hY s
  let Ksh := Localization.Away ϖ
  have hfr : IsFractionRing H Ksh := isFractionRing_localizationAway_of_irreducible H hϖ
  let : Field Ksh := IsFractionRing.toField H
  have : Small.{u} ({Spec (.of Ksh)} : Set Scheme.{u}) := inferInstance
  let B'' : BigEtaleSite.{u} := BigEtaleSite.ofSet ({Spec (.of Ksh)} : Set Scheme.{u})
  have hK : B''.Contains (Spec (.of Ksh)) := BigEtaleSite.contains_ofSet _ (by simp)
  -- `X̄_k̄ ⟶ X̄` is weakly étale, so `𝒪^{sh}_{X̄,s̄} ≅ H` (Stacks 094Z)
  let x0 : Y := s.hom.base (closedPoint s.residueField)
  have hW : WeaklyEtale pr := by
    have := weaklyEtale_specAlgebraMap k kbar
    exact inferInstanceAs (WeaklyEtale (pullback.fst fb (specAlgebraMap k kbar)))
  let HX := etaleLocalRing B' Xb hXb (s.map pr)
  let g : HX →+* H := etaleLocalRingHom B' hY hXb pr s
  let iXH : Algebra (Xb.presheaf.stalk (pr x0)) HX := etaleLocalRingAlgebra B' Xb hXb (s.map pr)
  have : IsLocalHom (algebraMap (Xb.presheaf.stalk (pr x0)) HX) :=
    isLocalHom_algebraMap_etaleLocalRing B' Xb hXb (s.map pr)
  have hsc : IsSepClosure (ResidueField (Xb.presheaf.stalk (pr x0))) (ResidueField HX) :=
    isSepClosure_residueField_etaleLocalRing B' Xb hXb (s.map pr)
  have hbij : Function.Bijective g := by
    have : IsHenselization (Xb.presheaf.stalk (pr x0)) (ResidueField HX) HX :=
      isHenselization_etaleLocalRing B' Xb hXb (s.map pr)
    exact (weaklyEtale_iff_strictHenselizationMap_bijective pr).mp hW x0 HX H (ResidueField.map g)
      g inferInstance (etaleLocalRingHom_comp_fromLocalRing B' hY hXb pr s)
      (RingHom.ext fun a => (ResidueField.map_residue g a).symm)
  let gE : HX ≃+* H := RingEquiv.ofBijective g hbij
  -- `H` as a strict henselization of `A`
  have hy0 : y = pr x0 := by
    show pr x = pr (s.hom.base (closedPoint s.residueField))
    rw [← hs]
    exact congrArg (fun z => pr (s.hom.base z)) (Subsingleton.elim _ _)
  let eAc : A ≃+* Xb.presheaf.stalk (pr x0) :=
    (Xb.presheaf.stalkCongr (Inseparable.of_eq hy0)).commRingCatIsoToRingEquiv
  let iAH : Algebra A H :=
    ((structureSheafStalkFromLocalRing B' Y hY s).comp
      ((pr.stalkMap x0).hom.comp eAc.toRingHom)).toAlgebra
  have halgH : ∀ a : A, algebraMap A H a = g (algebraMap _ HX (eAc a)) := fun a =>
    (RingHom.congr_fun (etaleLocalRingHom_comp_fromLocalRing B' hY hXb pr s) (eAc a)).symm
  have : IsLocalHom (algebraMap A H) := ⟨fun a ha => by
    rw [halgH] at ha
    exact (isUnit_map_iff eAc a).mp (isUnit_of_map_unit _ _ (isUnit_of_map_unit g _ ha))⟩
  have hInd : StacksDraft.IndEtale A H :=
    StacksDraft.indEtale_of_equiv eAc.symm gE
      (fun a => by rw [halgH, RingEquiv.apply_symm_apply]; rfl)
      (indEtale_etaleLocalRing B' Xb hXb (s.map pr))
  have : IsSepClosure (ResidueField A) (ResidueField H) := by
    have he1 : (algebraMap (ResidueField A) (ResidueField H)).comp
        ((ResidueField.mapEquiv eAc).symm : ResidueField (Xb.presheaf.stalk (pr x0)) →+*
          ResidueField A) =
        ((ResidueField.mapEquiv gE : ResidueField HX ≃+* ResidueField H) :
          ResidueField HX →+* ResidueField H).comp
          (algebraMap (ResidueField (Xb.presheaf.stalk (pr x0))) (ResidueField HX)) := by
      refine RingHom.ext fun z => ?_
      obtain ⟨a, rfl⟩ := residue_surjective z
      have h1 : (ResidueField.mapEquiv eAc).symm (residue _ a) = residue A (eAc.symm a) :=
        ResidueField.map_residue _ _
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ResidueField.algebraMap_residue,
        halgH, RingEquiv.apply_symm_apply]
      exact (ResidueField.map_residue _ _).symm
    have := hsc.sep_closed
    exact ⟨IsSepClosed.of_ringEquiv (ResidueField.mapEquiv gE).symm,
      @Algebra.IsSeparable.of_equiv_equiv _ _ _ _ _ _ _ _ _ _
        (ResidueField.mapEquiv eAc).symm (ResidueField.mapEquiv gE) he1 hsc.separable⟩
  -- `H ≅ (B_P)^I` and the embedding `ι : K^{sh} → L` onto the inertia field
  have : IsSepClosed L := IsSepClosure.sep_closed K
  have hGal : IsGalois K L := IsSepClosure.isGalois
  have : P.LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  let Φ : H ≃ₐ[A] IsIntegralClosure.inertiaInvariants A K L P :=
    Classical.choice
      (IsIntegralClosure.nonempty_algEquiv_inertiaInvariants_of_indEtale A K L P H hInd)
  obtain ⟨ι, hιH, hιrange⟩ :=
    IsIntegralClosure.exists_ringHom_fractionRing_range_eq_inertiaFixedField A K L P H Φ Ksh
  -- the embedding `ι' : K^{sh} → L → Ω` and the geometric point `t̄`
  let ι' : Ksh →+* Ω := (algebraMap L Ω).comp ι
  have hΦA : ∀ a : A, ((Φ (algebraMap A H a) : IsIntegralClosure.localizedSubring P) : L) =
      algebraMap A L a := fun a => by
    rw [Φ.commutes]
    exact IsIntegralClosure.coe_algebraMap_inertiaInvariants A K L P a
  have hι'A : ∀ a : A, ι' (algebraMap H Ksh (algebraMap A H a)) =
      algebraMap K Ω (algebraMap A K a) := fun a => by
    simp only [ι', RingHom.comp_apply, hιH, hΦA]
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L Ω]
  let gA : A →+* Ksh := (algebraMap H Ksh).comp (algebraMap A H)
  have hgA : Function.Injective gA := by
    intro a b hab
    have h := congrArg ι' hab
    simp only [gA, RingHom.comp_apply, hι'A] at h
    exact IsFractionRing.injective A K ((algebraMap K Ω).injective h)
  let γ : K →+* Ksh := IsFractionRing.lift (A := A) hgA
  have hγ : ι'.comp γ = algebraMap K Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, γ, IsFractionRing.lift_algebraMap, gA]
    exact hι'A a
  have halg : letI := ι'.toAlgebra; Algebra.IsAlgebraic Ksh Ω := by
    let : Algebra Ksh Ω := ι'.toAlgebra
    let : Algebra K Ksh := γ.toAlgebra
    have : IsScalarTower K Ksh Ω :=
      IsScalarTower.of_algebraMap_eq fun z => (RingHom.congr_fun hγ z).symm
    exact Algebra.IsAlgebraic.tower_top (K := K) (L := Ksh)
  let t : GeometricPoint (Spec (.of Ksh)) := ⟨Ω, Spec.map (CommRingCat.ofHom ι')⟩
  have ht : t.IsAlgebraic := isAlgebraic_specMap_geometricPoint ι' halg
  -- `t̄` lies over the geometric generic point of `V`
  let hK0 : Spec (.of Ksh) ⟶ Vk := eK.inv ≫ strictHenselizationBaseChangeToSource B' hY j' s
  have hcongr : ∀ {a b : Xb} (h : a = b),
      Spec.map (Xb.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Xb.fromSpecStalk a =
        Xb.fromSpecStalk b := by
    intro a b h
    subst h
    rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Spec.map_id,
      Category.id_comp]
  have h4 : t.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap H Ksh)) ≫
      strictHenselizationToBase B' Y hY s ≫ pr =
      Spec.map (curveLocalRingToFunctionField jV hy ≫ CommRingCat.ofHom (algebraMap K Ω)) ≫
        Xb.fromSpecStalk y := by
    rw [strictHenselizationToBase, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← hcongr hy0]
    simp only [t, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact hι'A a
  have hxg : (t.hom ≫ hK0) ≫ prV = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
      V.1.fromSpecResidueField (genericPoint V.1) := by
    rw [← cancel_mono jV]
    have h1 : eK.inv ≫ pullback.snd j' (strictHenselizationToBase B' Y hY s) =
        Spec.map (CommRingCat.ofHom (algebraMap H Ksh)) := by
      rw [← heK, Iso.inv_hom_id_assoc]
    have h2 : prV ≫ jV = j' ≫ pr := (fieldBaseChangeMap_comp_fst j.obj.hom kbar).symm
    simp only [hK0, Category.assoc]
    rw [h2, pullback.condition_assoc, ← Category.assoc eK.inv, h1,
      ← specMap_curveLocalRingToFunctionField_comp_fromSpecStalk jV hy]
    refine h4.trans ?_
    rw [Spec.map_comp (curveLocalRingToFunctionField jV hy) (CommRingCat.ofHom (algebraMap K Ω)),
      Category.assoc]
    exact rfl
  -- the residue field at the point of `Spec K^{sh}` is `K^{sh}`
  let κt := (Spec (.of Ksh)).residueField (t.hom default)
  let iκΩ : Algebra κt Ω := GeometricPoint.residueFieldAlgebra t
  let ψ0 := (Spec (.of Ksh)).fromSpecResidueField (t.hom default)
  let ζ : Ksh →+* κt := (Spec.preimage ψ0).hom
  have hζ : (GeometricPoint.residueFieldHom t).comp ζ = ι' := by
    have h := GeometricPoint.specMap_residueFieldHom_comp_fromSpecResidueField t
    have h' : Spec.map (CommRingCat.ofHom ζ ≫ CommRingCat.ofHom (GeometricPoint.residueFieldHom t))
        = Spec.map (CommRingCat.ofHom ι') := by
      rw [Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]
      exact h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h')
  have hζs : Function.Surjective ζ := by
    have := isIso_fromSpecResidueField_of_field Ksh (t.hom default)
    have : IsIso (Spec.preimage ψ0) :=
      ⟨Spec.preimage (inv ψ0), Spec.map_injective (by simp [Spec.map_comp]),
        Spec.map_injective (by simp [Spec.map_comp])⟩
    exact (ConcreteCategory.bijective_of_isIso (Spec.preimage ψ0)).2
  -- the absolute Galois group at `t̄` is the inertia group
  let E := IsIntegralClosure.inertiaFixedField A K L P
  have hE : ∀ z : Ω, z ∈ Set.range (algebraMap κt Ω) ↔ ∃ e ∈ E, algebraMap L Ω e = z := by
    intro z
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨w, rfl⟩ := hζs c
      have hw : ι w ∈ (E : Set L) := hιrange ▸ ⟨w, rfl⟩
      exact ⟨ι w, hw, (RingHom.congr_fun hζ w).symm⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨w, rfl⟩ : e ∈ Set.range ι := hιrange ▸ he
      exact ⟨ζ w, RingHom.congr_fun hζ w⟩
  let ψ : GeometricPoint.absoluteGaloisGroup t ≃ₜ P.inertia Gal(L / K) :=
    (sepClosureAutHomeomorphFixingSubgroup E hE).trans
      (Homeomorph.setCongr (congrArg (fun G : Subgroup Gal(L / K) => (G : Set Gal(L / K)))
        (IsIntegralClosure.fixingSubgroup_inertiaFixedField A K L P)))
  have hψv : ∀ σ, (ψ σ : Gal(L / K)) = sepClosureAutToGal E hE σ := fun _ => rfl
  have hψ : ∀ g g', ψ (g * g') = ψ g * ψ g' := fun g g' =>
    Subtype.ext ((hψv _).trans ((sepClosureAutToGal E hE).map_mul g g'))
  -- the Galois module of the level and the action through `ρ₀`
  let xbar := (algebraicClosureGeometricPoint K Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
  let pth : finiteEtaleFiberFunctor ((t.map hK0).map prV) ≅ finiteEtaleFiberFunctor xbar :=
    eqToIso (congrArg (fun f => finiteEtaleFiberFunctor (⟨Ω, f⟩ : GeometricPoint V.1)) hxg)
  obtain ⟨Θ, hΘ⟩ := exists_levelPullbackGaloisModule_addEquiv B V xbar ρ₀ hρ₀ prV hK0 B'' hK t n pth
  have hΘ' : ∀ (σ : GeometricPoint.absoluteGaloisGroup t) v,
      Θ (((levelPullbackGaloisModule B V xbar ρ₀ hρ₀ prV hK0 B'' hK t n).obj.obj.ρ σ).asHom v) =
        (PadicInt.toZModPow (n + 1)).mapMatrix
          ((ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) (ψ σ : Gal(L / K)) :
            Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ Θ v := by
    intro σ v
    have : IsAlgClosure κt Ω := ht
    have : Normal κt Ω := IsAlgClosure.normal _ _
    let τ : Ω ≃ₐ[κt] Ω := AlgEquiv.liftNormal σ Ω
    have hτσ : ∀ a : GeometricPoint.separableClosure t, (σ a : Ω) = τ (a : Ω) := fun a =>
      (AlgEquiv.liftNormal_commutes σ Ω a).symm
    let α : t.source ≅ t.source :=
      Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τ.toRingEquiv).op
    have hα : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom) := rfl
    have hτι : ∀ w, τ (ι' w) = ι' w := fun w => by
      rw [← RingHom.congr_fun hζ w]
      exact τ.commutes (ζ w)
    have hαt : α.hom ≫ t.hom = t.hom := by
      rw [hα]
      show Spec.map _ ≫ Spec.map (CommRingCat.ofHom ι') = Spec.map (CommRingCat.ofHom ι')
      rw [← Spec.map_comp]
      congr 1
      ext w
      exact hτι w
    let τK : Ω ≃ₐ[K] Ω :=
      { τ.toRingEquiv with
        commutes' := fun c => by
          show τ (algebraMap K Ω c) = algebraMap K Ω c
          rw [← RingHom.congr_fun hγ c, RingHom.comp_apply, hτι] }
    have hspec : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τK.toRingEquiv).op).hom =
        α.hom := rfl
    have hαx : (Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso τK.toRingEquiv).op).hom ≫
        xbar.hom = xbar.hom := by
      show _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫
        V.1.fromSpecResidueField (genericPoint V.1)) = _
      rw [hspec, ← hxg, ← Category.assoc, ← Category.assoc, hαt]
      exact hxg
    have hσ : etaleFundamentalGroupMulEquiv pth
        (GeometricPoint.sourceAutElement (S := V.1) ((t.map hK0).map prV) α
          (comp_map_map_hom_eq prV hK0 t hαt)) =
        galoisToFundamentalGroup V.1 L Ω (τK.restrictNormal L) := by
      rw [galoisToFundamentalGroup_restrictNormal_eq_sourceAutElement V.1 L Ω τK hαx]
      refine (etaleFundamentalGroupMulEquiv_eqToIso_sourceAutElement (S := V.1) hxg α _).trans ?_
      exact GeometricPoint.sourceAutElement_congr (S := V.1) xbar hspec.symm _
    have hψσ : (ψ σ : Gal(L / K)) = τK.restrictNormal L := by
      ext l
      apply (algebraMap L Ω).injective
      rw [AlgEquiv.restrictNormal_commutes, hψv, algebraMap_sepClosureAutToGal]
      exact hτσ _
    exact (hΘ σ τ hτσ α hα hαt v).trans
      ((congrArg (fun γ => levelRepresentation ρ₀ (n + 1) γ (Θ v))
        (hσ.trans (congrArg (galoisToFundamentalGroup V.1 L Ω) hψσ.symm))).trans
        (levelRepresentation_apply ρ₀ (n + 1) _ _))
  exact ⟨B', hY, Ksh, inferInstance, eK, B'', hK, t, galoisInvariants_and_cocycles_killed_of_inertia
    (levelPullbackGaloisModule B V xbar ρ₀ hρ₀ prV hK0 B'' hK t n) (P.inertia Gal(L / K)) ψ hψ
    (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) n e Θ hΘ' he⟩

/-- **The boundary stalks of the levels of `ℱ_ρ` are bounded for a smooth compactification**: the
input `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsSmoothBoundaryStalkInput` of
`Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_smooth`, from the Galois modules
at the points at infinity (`Stacks.EtaleCohomology.LAdicSheaf.smoothBoundaryGaloisInput`). -/
theorem LAdicSheaf.localTermsSmoothBoundaryStalkInput :
    LAdicSheaf.LocalTermsSmoothBoundaryStalkInput.{u} :=
  LAdicSheaf.localTermsSmoothBoundaryStalkInput_of_smoothBoundaryPointInput
    (LAdicSheaf.smoothBoundaryPointInput_of_smoothBoundaryGaloisInput
      LAdicSheaf.smoothBoundaryGaloisInput)

end Stacks.EtaleCohomology

end
