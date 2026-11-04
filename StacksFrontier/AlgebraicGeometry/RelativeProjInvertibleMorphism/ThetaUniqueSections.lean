module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUniqueClauseOne
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistBasicOpenDecompositionPos
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.SectionPullRestrict

/-!
# The relative `θ` of Stacks Tag 01O9 is determined on sections, by positive degrees

A family of maps on local sections `Γ(O, 𝒪(n)) ⟶ Γ(r_{ℒ,ψ}^{-1}(O), ℒ^{⊗ n})`, natural in `O`,
multiplicative, and carrying the section `ψ(a)` of `𝒪(d)` attached to a homogeneous `a` of
*positive* degree `d` over an affine open of the base to `ψ(a)`, is the pushforward form of `θ` of
[Stacks, Tag 01O9]. Two families of maps `r^* 𝒪(n) ⟶ ℒ^{⊗ n}` out of the inverse image along a
morphism `r` agreeing with `r_{ℒ,ψ}`, multiplicative and reading `ψ` in positive degrees, agree.

## Main results

* `GradedPowerMap.exists_psiU_mul_eq_pos`: every section of `𝒪(n)` over the image of a standard
  open `D₊(g)` of a chart is `x / g ^ j` with `j ≥ 1` and `deg x > 0`.
* `GradedPowerMap.eq_thetaPush_app_of_laws`: a natural multiplicative family of maps on sections
  reading `ψ` in positive degrees is `thetaPush`.
* `GradedPowerMap.eq_of_unitApp_laws`: two multiplicative families of maps on twists out of the
  inverse image along `r`, reading `ψ` in positive degrees, agree.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01MM](https://stacks.math.columbia.edu/tag/01MM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u w



open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ModuleHomGlue

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedPowerMap

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- **Every section of `𝒪(n)` over a standard open of a chart is `x / g ^ j` with `j ≥ 1` and `x`
of positive degree**, read in the relative twists. -/
theorem exists_psiU_mul_eq_pos (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) (n : ℤ)
    (t : Γ(Otw A n, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) :
    ∃ (j N : ℕ) (x : A.grading V N) (_ : 0 < j) (_ : 0 < N) (_ : ((j * e : ℕ) : ℤ) + n = (N : ℤ)),
      HEq (((twD A).algebra.mul ((j * e : ℕ) : ℤ) n).app
          (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
          ((Otw A (j * e : ℕ)).presheaf.map (homOfLE (chart_image_le V hV
            (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))).op
            (psiU A (j * e) V (A.componentEquiv V (j * e)
              ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩))) t)
        ((Otw A N).presheaf.map (homOfLE (chart_image_le V hV
            (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))).op
          (psiU A N V (A.componentEquiv V N x))) := by
  obtain ⟨j, N, x, hj, hNp, hN, hH⟩ :=
    Stacks.AlgebraicGeometry.ProjTwistBasicOpenDecomposition.exists_pow_mul_eq_degreeSection_pos
      (A.grading V) hg he n (((twD A).chartData.chartIso V hV n).hom.app
        (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) t)
  refine ⟨j, N, x, hj, hNp, hN, ?_⟩
  have ht : ((twD A).chartData.chartIso V hV n).inv.app
      (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
      (((twD A).chartData.chartIso V hV n).hom.app
        (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) t) = t :=
    (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ
      (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
      ((twD A).chartData.chartIso V hV n).hom_inv_id) t).trans rfl
  have h1 := heq_family (F := fun k => ↑((AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
      (A.grading V) k).val.obj (op (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))))
    (G := fun k => ↑Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
    (fun k => ((twD A).chartData.chartIso V hV k).inv.app
      (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) hN hH
  have h2 := chartIso_inv_mul V hV ((j * e : ℕ) : ℤ) n
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V)
        ((j * e : ℕ) : ℤ)).val.map
      (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen (A.grading V) g ≤ ⊤)).op
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading V) (j * e)
        ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩))
    (((twD A).chartData.chartIso V hV n).hom.app
        (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) t)
  have h3 := chartIso_inv_degreeSection V hV (j * e)
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
    ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩
  have h4 := chartIso_inv_degreeSection V hV N
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) x
  refine (heq_of_eq (h2.trans (congrArg₂ (fun a b => ((twD A).algebra.mul ((j * e : ℕ) : ℤ) n).app
    (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) a b)
    h3 ht))).symm.trans (h1.trans (heq_of_eq h4))

/-- **A multiplicative family reading `ψ` in positive degrees is the local datum** on the image of
a standard open of the chart over `V`. -/
theorem eq_localApp_of_laws_pos (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ}
    {g : A.sectionRing V} (hg : g ∈ A.grading V e) (he : 0 < e)
    (F : ∀ k : ℤ, Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading V) g) →
      Γ(tensorPowerModule T P.L k,
        P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (hM : ∀ (i j : ℤ) (s t), F (i + j) (((twD A).algebra.mul i j).app
        (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
          s t) = Stacks.TensorPowerDivision.localMul P.L (F i s) (F j t))
    (hP : ∀ (d : ℕ) (_ : 0 < d) (p : A.grading V d),
      F d ((Otw A d).presheaf.map (homOfLE (chart_image_le V hV
          (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))).op
        (psiU A d V (A.componentEquiv V d p))) =
          P.psiVal V hV d (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) p)
    (n : ℤ) (t : Γ(Otw A n, (relativeProj A).chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) :
    F n t = localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV n) rfl t := by
  have hO : (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g ≤
      (relativeProj A).toBase ⁻¹ᵁ V := chart_image_le V hV _
  obtain ⟨j, N, x, hj, hNp, hN, hH⟩ := exists_psiU_mul_eq_pos V hV hg he n t
  have fam := heq_family
    (F := fun k => ↑Γ(Otw A k, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
    (G := fun k => ↑Γ(tensorPowerModule T P.L k,
      P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
  have k₁ := fam (fun k => localApp ((relativeProj A).chart V hV) (P.thetaLoc V hV k) rfl) hN hH
  have k₂ := fam F hN hH
  simp only at k₁ k₂
  rw [P.localApp_thetaLoc_mul V hV _ _ rfl] at k₁
  rw [P.localApp_thetaLoc_psiU V hV _ rfl hO (P.targetOpen_le V hV _),
    P.localApp_thetaLoc_psiU V hV _ rfl hO (P.targetOpen_le V hV _)] at k₁
  have hje : 0 < j * e := Nat.mul_pos hj he
  have k₃ := (heq_of_eq ((hM _ _ _ t).trans
    (congrArg (fun z => Stacks.TensorPowerDivision.localMul P.L z (F n t))
      (hP _ hje _)))).symm.trans (k₂.trans (heq_of_eq (hP _ hNp _)))
  exact P.psiVal_cancel V hV hg he j n _ _ (eq_of_heq (k₃.trans k₁.symm))

/-- **A natural multiplicative family of maps on sections, reading `ψ` in positive degrees over the
affine opens of the base, is `thetaPush`**: the pushforward form of `θ` of [Stacks, Tag 01O9] is
determined, on sections, by these three properties. -/
theorem eq_thetaPush_app_of_laws
    (F : ∀ (n : ℤ) (O : (relativeProj A).scheme.Opens), Γ(Otw A n, O) → Γ(P.pushK n, O))
    (hnat : ∀ (n : ℤ) (O O' : (relativeProj A).scheme.Opens) (h : O' ≤ O) (s : Γ(Otw A n, O)),
      F n O' ((Otw A n).presheaf.map (homOfLE h).op s) =
        (P.pushK n).presheaf.map (homOfLE h).op (F n O s))
    (hM : ∀ (i j : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A i, O))
      (t : Γ(Otw A j, O)),
      F (i + j) O (((twD A).algebra.mul i j).app (op O) s t) =
        Stacks.TensorPowerDivision.localMul P.L (F i O s) (F j O t))
    (hP : ∀ (V : S.Opens) (_ : IsAffineOpen V) (d : ℕ) (_ : 0 < d) (a : Γ(A.piece (d : ℤ), V)),
      F d ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a) =
        (tensorPowerModule T P.L d).presheaf.map (homOfLE (P.image_preimage_preimage_le V)).op
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
            (P.value d V a)))
    (n : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A n, O)) :
    F n O s = (P.thetaPush n).app O s := by
  let ι := {k : (V : S.affineOpens) ×
      Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.Idx (A.grading V.1) //
    (relativeProj A).chart k.1.1 k.1.2 ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading k.1.1) (k.2.1.2 : A.sectionRing k.1.1) ≤ O}
  let U : ι → (relativeProj A).scheme.Opens := fun k =>
    (relativeProj A).chart k.1.1.1 k.1.1.2 ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading k.1.1.1) (k.1.2.1.2 : A.sectionRing k.1.1.1)
  have hUO : ∀ k, U k ≤ O := fun k => k.2
  have hcov : O ≤ ⨆ k, U k := by
    intro z hz
    obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
      (Opens.mem_top ((relativeProj A).toBase.base z))
    have hzr : z ∈ ((relativeProj A).chart V hV).opensRange := by
      rw [Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.opensRange_chart]; exact hzV
    obtain ⟨w, rfl⟩ := hzr
    have hw : w ∈ (relativeProj A).chart V hV ⁻¹ᵁ O := hz
    obtain ⟨d, g, hd, hg, hwg, hgW⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le (A.grading V) hw
    have hle : (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g
        ≤ O :=
      le_trans (Scheme.Hom.image_mono ((relativeProj A).chart V hV) hgW)
        (((relativeProj A).chart V hV).image_preimage_le O)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨V, hV⟩, ⟨⟨d, ⟨g, hg⟩⟩, hd⟩⟩, hle⟩,
      ⟨w, hwg, rfl⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (P.pushK n).isSheaf U hUO hcov
    fun k => ?_
  refine (hnat n O (U k) (hUO k) s).symm.trans ?_
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.ModuleLimits.Hom_app_presheaf_map
    (P.thetaPush n) (hUO k) s).symm
  refine Eq.trans ?_ (P.thetaPush_app_eq_localApp k.1.1.1 k.1.1.2 n rfl _).symm
  refine P.eq_localApp_of_laws_pos k.1.1.1 k.1.1.2 k.1.2.1.2.2 k.1.2.2 (fun m => F m (U k))
    (fun i j s t => hM i j (U k) s t) (fun d hd p => ?_) n _
  have hle : U k ≤ (relativeProj A).toBase ⁻¹ᵁ k.1.1.1 := chart_image_le k.1.1.1 k.1.1.2 _
  refine (hnat d _ _ hle _).trans ?_
  refine (congrArg ((P.pushK d).presheaf.map (homOfLE hle).op)
    (hP k.1.1.1 k.1.1.2 d hd _)).trans ?_
  refine (pushforward_restrict_map P.coveringOpen.ι (P.globalMorphism (relativeProj A))
    (tensorPowerModule T P.L d) (homOfLE hle) _).trans ?_
  exact map_map _ _ _ _ _

/-- `thetaPush` is multiplicative on sections, the product of the target being that of the tensor
powers. -/
theorem thetaPush_app_mul (i j : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A i, O))
    (t : Γ(Otw A j, O)) :
    (P.thetaPush (i + j)).app O (((twD A).algebra.mul i j).app (op O) s t) =
      Stacks.TensorPowerDivision.localMul P.L ((P.thetaPush i).app O s) ((P.thetaPush j).app O t) :=
  P.thetaPush_mul i j (op O) s t

omit P in
/-- **A morphism out of an inverse image is determined by its values on the inverse images of
sections.** -/
theorem hom_ext_unitApp {X Y : Scheme.{u}} (r : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (φ ψ : (Scheme.Modules.pullback r).obj M ⟶ N)
    (h : ∀ (O : Y.Opens) (s : Γ(M, O)),
      φ.app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r M O s) =
        ψ.app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r M O s)) :
    φ = ψ := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction r).homEquiv M N).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun O => ConcreteCategory.hom_ext _ _ fun s => ?_
  exact h O s

/-- A morphism `r` with `U(ψ).ι ≫ r = r_{ℒ,ψ}` lying over the base lies over
`f^{-1}(V)` over `V`. -/
theorem preimage_toBase_le_of_comp {r : T ⟶ (relativeProj A).scheme}
    (hrf : r ≫ (relativeProj A).toBase = f) (V : S.Opens) :
    r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ≤ f ⁻¹ᵁ V := by
  rw [← hrf, Scheme.Hom.comp_preimage]

/-- **[Stacks, Tag 01O9]: the maps on twists out of the inverse image along a morphism `r` agreeing
with `r_{ℒ,ψ}`, multiplicative and reading `ψ` in positive degrees, are unique.** Let `ψ` generate
everywhere (`U(ψ) = X`) and let `r : X ⟶ Proj_S(𝒜)` over `S` restrict to `r_{ℒ,ψ}`. Two families
`Φ_n : r^* 𝒪(n) ⟶ ℒ^{⊗ n}` which are multiplicative on the inverse images of sections and carry the
inverse image of `ψ(a)`, for `a` homogeneous of positive degree over an affine open of the base,
to `ψ(a)`, agree. -/
theorem eq_of_unitApp_laws (hcov : P.coveringOpen = ⊤) (r : T ⟶ (relativeProj A).scheme)
    (hr : P.coveringOpen.ι ≫ r = P.globalMorphism (relativeProj A))
    (hrf : r ≫ (relativeProj A).toBase = f)
    (Φ₁ Φ₂ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (Otw A n) ⟶ tensorPowerModule T P.L n)
    (hM₁ : ∀ (i j : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A i, O))
      (t : Γ(Otw A j, O)),
      (Φ₁ (i + j)).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
          (Otw A (i + j)) O (((twD A).algebra.mul i j).app (op O) s t)) =
        Stacks.TensorPowerDivision.localMul P.L
          ((Φ₁ i).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
            (Otw A i) O s))
          ((Φ₁ j).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
            (Otw A j) O t)))
    (hM₂ : ∀ (i j : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A i, O))
      (t : Γ(Otw A j, O)),
      (Φ₂ (i + j)).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
          (Otw A (i + j)) O (((twD A).algebra.mul i j).app (op O) s t)) =
        Stacks.TensorPowerDivision.localMul P.L
          ((Φ₂ i).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
            (Otw A i) O s))
          ((Φ₂ j).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
            (Otw A j) O t)))
    (hP₁ : ∀ (V : S.Opens) (_ : IsAffineOpen V) (d : ℕ) (_ : 0 < d) (a : Γ(A.piece (d : ℤ), V)),
      (Φ₁ d).app (r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
          (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r (Otw A d)
            ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
        (tensorPowerModule T P.L d).presheaf.map
          (homOfLE (preimage_toBase_le_of_comp hrf V)).op
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
            (P.value d V a)))
    (hP₂ : ∀ (V : S.Opens) (_ : IsAffineOpen V) (d : ℕ) (_ : 0 < d) (a : Γ(A.piece (d : ℤ), V)),
      (Φ₂ d).app (r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
          (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r (Otw A d)
            ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
        (tensorPowerModule T P.L d).presheaf.map
          (homOfLE (preimage_toBase_le_of_comp hrf V)).op
          ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
            (P.value d V a)))
    (n : ℤ) : Φ₁ n = Φ₂ n := by
  have hle : ∀ O : (relativeProj A).scheme.Opens,
      P.coveringOpen.ι ''ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ O) ≤ r ⁻¹ᵁ O := by
    intro O
    rw [← hr, Scheme.Hom.comp_preimage]
    exact P.coveringOpen.ι.image_preimage_le (r ⁻¹ᵁ O)
  have heq : ∀ O : (relativeProj A).scheme.Opens,
      r ⁻¹ᵁ O = P.coveringOpen.ι ''ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ O) := by
    intro O
    rw [← hr, Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, hcov, top_inf_eq]
  have key : ∀ (Φ : ∀ n : ℤ, (Scheme.Modules.pullback r).obj (Otw A n) ⟶
      tensorPowerModule T P.L n)
      (_ : ∀ (i j : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A i, O))
        (t : Γ(Otw A j, O)),
        (Φ (i + j)).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
            (Otw A (i + j)) O (((twD A).algebra.mul i j).app (op O) s t)) =
          Stacks.TensorPowerDivision.localMul P.L
            ((Φ i).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
              (Otw A i) O s))
            ((Φ j).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
              (Otw A j) O t)))
      (_ : ∀ (V : S.Opens) (_ : IsAffineOpen V) (d : ℕ) (_ : 0 < d)
        (a : Γ(A.piece (d : ℤ), V)),
        (Φ d).app (r ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))
            (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r (Otw A d)
              ((relativeProj A).toBase ⁻¹ᵁ V) (psiU A d V a)) =
          (tensorPowerModule T P.L d).presheaf.map
            (homOfLE (preimage_toBase_le_of_comp hrf V)).op
            ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
              (P.value d V a)))
      (n : ℤ) (O : (relativeProj A).scheme.Opens) (s : Γ(Otw A n, O)),
      (tensorPowerModule T P.L n).presheaf.map (homOfLE (hle O)).op
          ((Φ n).app (r ⁻¹ᵁ O) (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r
            (Otw A n) O s)) = (P.thetaPush n).app O s := by
    intro Φ hM hP n O s
    refine P.eq_thetaPush_app_of_laws (fun n O s => (tensorPowerModule T P.L n).presheaf.map
        (homOfLE (hle O)).op ((Φ n).app (r ⁻¹ᵁ O)
          (Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp r (Otw A n) O s)))
      (fun n O O' h s => ?_) (fun i j O s t => ?_) (fun V hV d hd a => ?_) n O s
    · show _ = (tensorPowerModule T P.L n).presheaf.map
        (homOfLE (P.coveringOpen.ι.image_mono
          ((P.globalMorphism (relativeProj A)).preimage_mono h))).op _
      rw [Stacks.AlgebraicGeometry.SectionRingBaseChange.unitApp_map,
        Stacks.AlgebraicGeometry.SectionRingBaseChange.hom_app_map,
        Stacks.AlgebraicGeometry.SectionRingBaseChange.map_map_homOfLE _ (hle O')
          (r.preimage_mono h) ((hle O').trans (r.preimage_mono h)),
        Stacks.AlgebraicGeometry.SectionRingBaseChange.map_map_homOfLE _
          (P.coveringOpen.ι.image_mono ((P.globalMorphism (relativeProj A)).preimage_mono h))
          (hle O) ((P.coveringOpen.ι.image_mono
            ((P.globalMorphism (relativeProj A)).preimage_mono h)).trans (hle O))]
    · show (tensorPowerModule T P.L (i + j)).presheaf.map (homOfLE (hle O)).op _ = _
      rw [hM i j O s t, Stacks.TensorPowerDivision.map_localMul]
      rfl
    · refine (congrArg ((tensorPowerModule T P.L d).presheaf.map
        (homOfLE (hle ((relativeProj A).toBase ⁻¹ᵁ V))).op) (hP V hV d hd a)).trans ?_
      exact Stacks.AlgebraicGeometry.SectionRingBaseChange.map_map_homOfLE _ _ _ _ _
  refine hom_ext_unitApp r (Φ₁ n) (Φ₂ n) fun O s => ?_
  refine (map_bijective_of_eq (tensorPowerModule T P.L n) (hle O) (heq O)).1 ?_
  exact (key Φ₁ hM₁ hP₁ n O s).trans (key Φ₂ hM₂ hP₂ n O s).symm

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
