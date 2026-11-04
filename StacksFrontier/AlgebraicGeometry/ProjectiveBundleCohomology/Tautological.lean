module

import all StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyRelativelyAmple
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.LocalModel
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.TwistStalk
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.DegreeOnePiece
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistDegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.TwistStalkModule

/-!
# The tautological surjection on a projective bundle

Let `π : 𝐏(E) ⟶ S` be the projective bundle of an `𝒪_S`-module `E`, with twists given by a
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`. The degree-one generator
`E ≅ Sym¹(E)` followed by the canonical map `Sym¹(E) ⟶ π_* 𝒪_{𝐏(E)}(1)` of Tag 01NR is, by
adjunction, a morphism `π^* E ⟶ 𝒪_{𝐏(E)}(1)`. It is an epimorphism: at a point of `𝐏(E)` over an
affine open of `S`, the twist `𝒪(1)` is generated at that point by the image of a degree-one
section of `Sym(E)` which does not vanish there.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.tautologicalMap`: `π^* E ⟶ 𝒪_{𝐏(E)}(1)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.span_germ_degreeSection_eq_top`: on
  `Proj 𝒮`, the germ at `x` of the canonical section of a degree-one element `f` not vanishing at
  `x` generates the stalk of `𝒪(1)`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.epi_tautologicalMap`: **the tautological
  map is an epimorphism.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistGrading degreeSection)
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Absolute

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **A degree-one element not vanishing at `x` generates `𝒪(1)` at `x`.** Every germ at `x` of
`𝒪_{Proj 𝒮}(1)` is a multiple of the germ of the canonical section of `f`. -/
public theorem exists_smul_germ_degreeSection {f : S} (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal)
    (z : Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalk 𝒮
      (twistGrading (S := S) 𝒮 ((1 : ℕ) : ℤ)) x) :
    ∃ c : (ProjectiveSpectrum.Proj.structureSheaf 𝒮).presheaf.stalk x,
      z = c • Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafGerm 𝒮
        (twistGrading (S := S) 𝒮 ((1 : ℕ) : ℤ)) x ⊤ trivial (degreeSection 𝒮 1 ⟨f, hf⟩) := by
  set e := Stacks.AlgebraicGeometry.ProjKoszulComplex.twistingSheafStalkEquiv 𝒮 hf hx
    ((1 : ℕ) : ℤ)
  set g := Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafGerm 𝒮
    (twistGrading (S := S) 𝒮 ((1 : ℕ) : ℤ)) x ⊤ trivial (degreeSection 𝒮 1 ⟨f, hf⟩)
  have hg : e g = 1 := by
    refine (Proj.stalkIso' 𝒮 x).injective ?_
    refine HomogeneousLocalization.val_injective _ ?_
    rw [map_one, HomogeneousLocalization.val_one]
    refine (Stacks.AlgebraicGeometry.ProjKoszulComplex.val_twistingSheafStalkEquiv_germ 𝒮 hf hx
      ((1 : ℕ) : ℤ) ⊤ trivial (degreeSection 𝒮 1 ⟨f, hf⟩) (m := f) (s := 1)
      (degreeSection_apply 𝒮 1 ⟨f, hf⟩ ⟨x, trivial⟩)).trans ?_
    rw [show (-((1 : ℕ) : ℤ)) = -((1 : ℕ) : ℤ) from rfl,
      Stacks.AlgebraicGeometry.ProjKoszulComplex.zpowFiber_neg_natCast]
    have h := Stacks.AlgebraicGeometry.ProjStalkGlobalSections.powFiberInv_mul_powFiber 𝒮 1 hx
    rwa [Stacks.AlgebraicGeometry.ProjStalkGlobalSections.powFiber, pow_one] at h
  refine ⟨e z, ?_⟩
  refine e.injective ?_
  rw [map_smul, hg, smul_eq_mul, mul_one]

/-- `exists_smul_germ_degreeSection` for the action of the `RingCat`-valued stalk of the
structure sheaf, which is the action the stalk functor of sheaves of modules uses. -/
public theorem exists_ringCat_smul_germ_degreeSection {f : S} (hf : f ∈ 𝒮 1)
    {x : ProjectiveSpectrum.top 𝒮} (hx : f ∉ x.asHomogeneousIdeal)
    (z : Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalk 𝒮
      (twistGrading (S := S) 𝒮 ((1 : ℕ) : ℤ)) x) :
    ∃ c : TopCat.Presheaf.stalk (C := RingCat.{u})
        ((ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj ⋙
          forget₂ CommRingCat.{u} RingCat.{u}) x,
      z = haveI :=
          (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalkRingCatModule
            𝒮 (twistGrading (S := S) 𝒮 ((1 : ℕ) : ℤ)) x)
        c • Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafGerm 𝒮
          (twistGrading (S := S) 𝒮 ((1 : ℕ) : ℤ)) x ⊤ trivial
          (degreeSection 𝒮 1 ⟨f, hf⟩) := by
  obtain ⟨c, hc⟩ := exists_smul_germ_degreeSection 𝒮 hf hx z
  refine ⟨(SemilinearStalk.commStalkRingEquiv
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj x).symm c, ?_⟩
  rw [← Stacks.AlgebraicGeometry.ProjStalkGlobalSections.associatedModuleSheafStalk_ringCat_smul,
    RingEquiv.apply_symm_apply]
  exact hc

end Absolute

section Bundle

variable {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))

/-- **The tautological map `π^* E ⟶ 𝒪_{𝐏(E)}(1)`**: the adjoint transpose of the degree-one
generator `E ≅ Sym¹(E)` followed by the canonical map `Sym¹(E) ⟶ π_* 𝒪(1)` of Tag 01NR. -/
public def tautologicalMap :
    (Scheme.Modules.pullback
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).obj E ⟶
      D.algebra.piece ((1 : ℕ) : ℤ) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).homEquiv E
      (D.algebra.piece ((1 : ℕ) : ℤ))).symm
    ((Scheme.Modules.symmetricAlgebraGenIso S E).hom ≫ D.ψ 1)

/-- The germ of a section transported along an equality of opens is the germ of the section. -/
public theorem germ_eqRec {X : Scheme.{u}} (G : X.Modules) {W W' : X.Opens} (h : W = W')
    (s : Γ(G, W)) (y : X) (hy : y ∈ W) (hy' : y ∈ W') :
    (TopCat.Presheaf.germ G.presheaf W' y hy').hom (h ▸ s) =
      (TopCat.Presheaf.germ G.presheaf W y hy).hom s := by
  subst h
  rfl

/-- **The tautological map is an epimorphism.** -/
public theorem epi_tautologicalMap : Epi (tautologicalMap E hqc D) := by
  refine AlgebraicGeometry.epi_of_stalk_surjective _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase.base x ∈
      (⊤ : S.Opens) from trivial)
  have hVa : IsAffineOpen V := hV
  let := D.chartData.chart_isOpenImmersion V hVa
  have hx : x ∈ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hVa ''ᵁ
      ⊤ := by
    rw [D.chartData.chart_range V hVa]; exact hxV
  obtain ⟨x', -, rfl⟩ := hx
  have hgen := Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra E hqc V hVa
  have hcov := Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) hgen
  have hx'top : x' ∈ (⊤ : (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).Opens) := trivial
  rw [← hcov] at hx'top
  obtain ⟨z, hz⟩ := Opens.mem_iSup.mp hx'top
  obtain ⟨b, hb⟩ :=
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).mem_grading_iff V z.1).mp z.2
  refine AlgebraicGeometry.surjective_stalk_of_restrict _ x' _ ?_
  have hrange := @AlgebraicGeometry.mem_range_stalk_pushforward _ _
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase _ _ _
    (Scheme.Modules.symmetricAlgebraGenIso S E).hom
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) (D.ψ 1) V b _ hxV
  let s'' : Γ(D.algebra.piece ((1 : ℕ) : ℤ),
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hVa ''ᵁ ⊤) :=
    (D.chartData.chart_range V hVa).symm ▸ ((D.ψ 1).app V b)
  let s' : Γ((Scheme.Modules.restrictFunctor
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hVa)).obj
        (D.algebra.piece ((1 : ℕ) : ℤ)), ⊤) := s''
  have hs' := AlgebraicGeometry.mem_range_restrict_germ _ x' (tautologicalMap E hqc D) ⊤ trivial s'
    (by
      have := germ_eqRec (D.algebra.piece ((1 : ℕ) : ℤ)) (D.chartData.chart_range V hVa).symm
        ((D.ψ 1).app V b) _ hxV (by simp)
      exact this ▸ hrange)
  obtain ⟨t₀, ht₀⟩ := hs'
  have hchart : (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ)).hom.val.app (op ⊤) s' =
      degreeSection ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) 1 z := by
    have h2 : s' = (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ)).inv.val.app (op ⊤)
        (degreeSection ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) 1
          ⟨DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V) 1 b,
            (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).of_mem_grading V b⟩) :=
      (D.ψ_chart V hVa 1 b).symm
    have hz' : (⟨DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces V)
        1 b, (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).of_mem_grading V b⟩ :
        (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V 1) = z := Subtype.ext hb
    rw [h2, hz']
    have := congrArg (fun φ => (φ.val.app (op ⊤)).hom
      (degreeSection ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) 1 z))
      (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ)).inv_hom_id
    exact this
  have hzx : z.1 ∉ x'.asHomogeneousIdeal := hz
  have hbij := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.stalkFunctor _ x').mapIso (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ))).hom
  intro y
  obtain ⟨r, hr⟩ := exists_ringCat_smul_germ_degreeSection
    ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) z.2 hzx
    (((SheafOfModules.stalkFunctor _ x').map (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ)).hom).hom y)
  have hg := AlgebraicGeometry.stalk_map_germ (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ)).hom x' ⊤
    trivial s'
  let r' : TopCat.Presheaf.stalk (C := RingCat.{u}) (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).ringCatSheaf.obj x' := r
  refine ⟨r' • t₀, hbij.1 ?_⟩
  have e1 := map_smul ((SheafOfModules.stalkFunctor _ x').map
    ((Scheme.Modules.restrictFunctor
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hVa)).map
        (tautologicalMap E hqc D))).hom r' t₀
  have e2 := map_smul ((SheafOfModules.stalkFunctor _ x').map
    (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ)).hom).hom r'
    ((TopCat.Presheaf.germ ((Scheme.Modules.restrictFunctor
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).chart V hVa)).obj
        (D.algebra.piece ((1 : ℕ) : ℤ))).val.presheaf ⊤ x' trivial).hom s')
  refine (congrArg _ e1).trans ?_
  refine (congrArg (fun w => ((SheafOfModules.stalkFunctor _ x').map
    (D.chartData.chartIso V hVa ((1 : ℕ) : ℤ)).hom).hom (r' • w)) ht₀).trans ?_
  refine e2.trans ?_
  refine (congrArg (fun w => r' • w) hg).trans ?_
  refine (congrArg (fun w : ↑((SheafOfModules.stalkFunctor (AlgebraicGeometry.Proj
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)).ringCatSheaf x').obj
        (twistingSheaf ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V)
          ((1 : ℕ) : ℤ))) => r' • w)
    (congrArg (fun t => (TopCat.Presheaf.germ (twistingSheaf
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading V) ((1 : ℕ) : ℤ)).val.presheaf
        ⊤ x' trivial).hom t) hchart)).trans ?_
  exact hr.symm

end Bundle

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
