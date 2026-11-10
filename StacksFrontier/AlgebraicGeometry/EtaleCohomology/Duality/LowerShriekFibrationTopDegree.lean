module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekTraceEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LowerShriekFibrationTransfer
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.HomologicalDualityAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperLocallyConstantDuality

/-!
# The top-degree trace of an elementary fibration on compactly supported cohomology

Let `f : U → S` be an elementary fibration over `S` affine and smooth of dimension `d` over an
algebraically closed field `k`, `ℓ` a prime, `Λ = ℤ/ℓ`, and `K = Rf_!(f⁻¹ Λ_S)`, which lives in
degrees `[0, 2]`. The top-degree trace `θ : K ⟶ Λ_S[-2]`
(`Stacks.EtaleCohomology.lowerShriekTopTraceTheta`) is the truncation `K → τ_{≥ 2} K` followed by
an isomorphism `τ_{≥ 2} K ≅ Λ_S[-2]` (`Stacks.EtaleCohomology.exists_lowerShriekTopTraceTheta_eq`).
When moreover `R⁰f_! Λ = 0`, the fibre `τ_{≤ 1} K` of the truncation is `R¹f_! Λ[-1]`, whose
compactly supported cohomology vanishes in the degrees `2d + 1` and `2d + 2`
([Tag 095U](https://stacks.math.columbia.edu/tag/095U) on a compactification of `S` of dimension
`≤ d`). So `θ` induces an isomorphism on top-degree compactly supported cohomology,
`H^{2d+2}_c(U, Λ) ≅ H^{2d}_c(S, Λ)`, read as the transfer map of
`Stacks.HomologicalDuality.transferHom`
(`Stacks.EtaleCohomology.bijective_transferHom_lowerShriekTopTrace`). This is how a trace on
`H^{2d+2}_c(U)` comes from a trace on `H^{2d}_c(S)`, in the fibration step of Poincaré duality in
the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume `Rf_!`, defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.HomologicalDuality.bijective_map_mor₂_shift`.
* `Stacks.EtaleCohomology.exists_lowerShriekTopTraceTheta_eq`.
* `Stacks.EtaleCohomology.bijective_transferHom_lowerShriekTopTrace`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated
  AlgebraicGeometry Opposite

universe w v v' u₁ u₂ u

namespace Stacks.HomologicalDuality

variable {C : Type u₁} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : C ⥤ AddCommGrpCat.{w}} [H.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C)

include hT in
/-- **A homological functor is bijective on `M₂[n] → M₃[n]`** for a distinguished triangle
`M₁ → M₂ → M₃ → M₁[1]` with `H(M₁[n]) = H(M₁[n + 1]) = 0`. -/
theorem bijective_map_mor₂_shift (n : ℤ) (h₁ : Subsingleton (H.obj (T.obj₁⟦n⟧)))
    (h₂ : Subsingleton (H.obj (T.obj₁⟦n + 1⟧))) :
    Function.Bijective (H.map (T.mor₂⟦n⟧')).hom := by
  refine ⟨?_, fun y => exact₃_homology T hT n y (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x₁, rfl⟩ := exact₂_homology T hT n x hx
  rw [Subsingleton.elim x₁ 0, map_zero]

/-- Bijectivity of a morphism of abelian groups is unchanged by composing with isomorphisms. -/
theorem bijective_hom_comp_iff {A B B' A' : AddCommGrpCat.{w}} (i : A ≅ B) (g : B ⟶ B')
    (j : B' ≅ A') : Function.Bijective (i.hom ≫ g ≫ j.hom).hom ↔ Function.Bijective g.hom := by
  have hi : Function.Bijective i.hom.hom := i.addCommGroupIsoToAddEquiv.bijective
  have hj : Function.Bijective j.hom.hom := j.addCommGroupIsoToAddEquiv.bijective
  rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_comp, Function.Bijective.of_comp_iff _ hi, Function.Bijective.of_comp_iff' hj]

end Stacks.HomologicalDuality

namespace Stacks.HomologicalDuality

section Transfer

variable {C : Type u₁} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  {C' : Type u₂} [Category.{v'} C'] [Preadditive C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (F : C ⥤ C') [F.CommShift ℤ] [F.Additive]
  {H : C ⥤ AddCommGrpCat.{w}} [H.Additive] {H' : C' ⥤ AddCommGrpCat.{w}} [H'.Additive]
  (e : H ≅ F ⋙ H') {D : C} {D' : C'} {c : ℤ} (θ : F.obj D ⟶ D'⟦c⟧) {N N' : ℤ}
  (hN : N + c = N')

omit [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Preadditive C']
  [∀ n : ℤ, (shiftFunctor C' n).Additive] [F.Additive] [H.Additive] [H'.Additive] in
/-- **The transfer map `H(D[N]) ⟶ H'(D'[N'])` is bijective exactly when `H'(θ[N])` is.** -/
theorem bijective_transferHom_iff :
    Function.Bijective (transferHom F e θ hN).hom ↔ Function.Bijective (H'.map (θ⟦N⟧')).hom := by
  rw [transferHom, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    ← Category.assoc]
  exact bijective_hom_comp_iff (e.app (D⟦N⟧) ≪≫ H'.mapIso ((F.commShiftIso N).app D)) _
    (H'.mapIso ((shiftFunctorAdd' C' c N N' (by omega)).app D').symm)

end Transfer

end Stacks.HomologicalDuality

namespace Stacks.EtaleCohomology

open ExtensionTorsor HomologicalDuality Stacks.TopTruncationExt DerivedCategory.TStructure

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] {U S : Scheme.{u}}
  (f : U ⟶ S) (jf : CompactificationOf (Over.mk f))
  (hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ 1)
  (ν : etaleModuleInverseImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
    derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
      𝟭 (EtaleModules.{u, 0} (ZMod ℓ) S))

/-- **The top-degree trace is the truncation onto `τ_{≥ 2}`, up to isomorphism**:
`θ : Rf_!(f⁻¹ Λ_S[0]) ⟶ Λ_S[0][-2]` is `K → τ_{≥ 2} K` followed by an isomorphism
`τ_{≥ 2} K ≅ Λ_S[0][-2]`. -/
theorem exists_lowerShriekTopTraceTheta_eq :
    ∃ γ : plusTruncGE ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))) 1 ≅
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧,
      lowerShriekTopTraceTheta ℓ f jf hf ν =
        (plusTriangleLTGE ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))) 1).mor₂ ≫
          γ.hom := by
  let K := (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))
  let Kι := DerivedCategory.Plus.ι.obj K
  let L := DerivedCategory.Plus.ι.obj (plusTruncGE K 1)
  have hK : Kι.IsLE 2 := isLE_derivedLowerShriek_inverseImage_single f jf ℓ hf _
  let u : Kι ⟶ L := (t.truncGEπ (1 + 1)).app Kι
  have hL : L.IsLE 2 := isLE_truncGE Kι (1 + 1) 2 (by norm_num)
  have : L.IsGE 2 := (inferInstance : ((t.truncGE (1 + 1)).obj Kι).IsGE (1 + 1))
  have : IsIso (topProj L 2 hL) := isIso_topProj_of_isGE L 2 hL
  have : IsIso ((DerivedCategory.homologyFunctor _ 2).map u) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ (1 + 1) 2 (by norm_num) Kι
  let X := ((DerivedCategory.singleFunctor _ 0).map
    ((DerivedCategory.homologyFunctor _ 2).map u))⟦(-2 : ℤ)⟧'
  have key : topProj Kι 2 hK = u ≫ topProj L 2 hL ≫ inv X := by
    rw [← Category.assoc, comp_topProj 2 hK hL u, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  let γι : L ≅ ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧ :=
    asIso (topProj L 2 hL) ≪≫ (asIso X).symm ≪≫
      (shiftFunctor _ (-2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        (ν.app (unitSheaf (X := S) ℓ)))
  have htr : lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ) = u ≫ γι.hom := by
    change topProj Kι 2 hK ≫ _ = _
    rw [key]
    simp only [Category.assoc]
    rfl
  let cs : ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧ ≅
      DerivedCategory.Plus.ι.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))⟦(-2 : ℤ)⟧) :=
    ((DerivedCategory.Plus.ι.commShiftIso (-2 : ℤ)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ))).symm
  refine ⟨DerivedCategory.Plus.ι.preimageIso (γι ≪≫ cs), ?_⟩
  apply DerivedCategory.Plus.ι.map_injective
  have e₁ : DerivedCategory.Plus.ι.map (lowerShriekTopTraceTheta ℓ f jf hf ν) =
      lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ) ≫ cs.hom :=
    CategoryTheory.Functor.map_preimage _ _
  have hmor : DerivedCategory.Plus.ι.map (plusTriangleLTGE K 1).mor₂ = u :=
    t.plus.fullyFaithfulι.map_preimage _
  have e₂ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.ι.preimageIso (γι ≪≫ cs)).hom = γι.hom ≫ cs.hom :=
    CategoryTheory.Functor.map_preimage _ _
  exact e₁.trans ((congrArg (· ≫ cs.hom) htr).trans ((Category.assoc _ _ _).trans
    ((congrArg (u ≫ ·) e₂.symm).trans ((congrArg (· ≫ _) hmor.symm).trans
      (CategoryTheory.Functor.map_comp _ _ _).symm))))

/-- **`Rf_!(f⁻¹ Λ_S)` lives in degrees `≥ 1` when `R⁰f_! Λ = 0`**, `Rf_!` of a sheaf living in
degrees `≥ 0`. -/
theorem isGE_one_lowerShriek_inverseImage_single
    (hR0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))))) :
    (DerivedCategory.Plus.ι.obj ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))).IsGE 1 := by
  have := isGE_derivedLowerShriek_obj (ZMod ℓ) f jf ((DerivedCategory.Plus.singleFunctor _ 0).obj
    ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))) 0
  rw [DerivedCategory.isGE_iff]
  intro i hi
  rcases lt_or_eq_of_le (show i ≤ 0 by omega) with h | rfl
  · exact DerivedCategory.isZero_of_isGE _ 0 i h
  · exact hR0

/-- **The compactly supported cohomology of `τ_{≤ 1} Rf_! Λ = R¹f_! Λ[-1]` vanishes above
`2d + 1`**, for a compactification of `S` of dimension at most `d`
([Tag 095U](https://stacks.math.columbia.edu/tag/095U)). -/
theorem subsingleton_lowerShriek_plusTruncLT (q : S ⟶ Spec (.of k))
    (jS : CompactificationOf (Over.mk q)) (d : ℕ)
    (hdimS : topologicalKrullDim jS.space ≤ d)
    (hR0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))))
    (n : ℤ) (m : ℕ) (hm : -1 + n = m) (hmd : 2 * d < m) :
    Subsingleton ((derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)))).obj
      ((plusTruncLT ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))) 1)⟦n⟧)) := by
  let K := (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))
  have := isGE_one_lowerShriek_inverseImage_single ℓ f jf hR0
  let eT : (plusTruncLT K 1)⟦n⟧ ≅ ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((DerivedCategory.Plus.homologyFunctor _ 1).obj K))⟦(m : ℤ)⟧ :=
    (shiftFunctor _ n).mapIso (plusTruncLTIso K 1) ≪≫
      ((shiftFunctorAdd' _ (-1) n m hm).app _).symm
  have := subsingleton_lowerShriek_shift q jS ℓ ((DerivedCategory.Plus.homologyFunctor _ 1).obj K) m
    (subsingleton_ext_unitSheaf_of_proper jS.toBase d hdimS _ m hmd)
  exact ((derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
    (op ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (unitSheaf (X := Spec (.of k)) ℓ)))).mapIso eT).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

section TopDegree

variable (q : S ⟶ Spec (.of k)) [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace S]
  [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated q]
  [LocallyOfFiniteType q] (jS : CompactificationOf (Over.mk q))
  (jU : CompactificationOf (Over.mk (f ≫ q)))

/-- **The top-degree trace is an isomorphism on top-degree compactly supported cohomology**: for
an elementary fibration `f : U → S` with `R⁰f_! Λ = 0`, a compactification of `S` of dimension at
most `d` and `N = 2d + 2`, the transfer map `H^N_c(U, Λ) ⟶ H^{N-2}_c(S, Λ)` induced by
`θ : Rf_!(f⁻¹ Λ_S) ⟶ Λ_S[-2]` is bijective. -/
theorem bijective_transferHom_lowerShriekTopTrace (d : ℕ)
    (hdimS : topologicalKrullDim jS.space ≤ d)
    (hR0 : IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))))
    {N N' : ℤ} (hN : N + -2 = N') (hNd : N = 2 * (d : ℤ) + 2) :
    Function.Bijective (transferHom (derivedLowerShriek.{u, 0} f jf (ZMod ℓ))
      (lowerShriekCoyonedaCompIso ℓ f q jf jS jU) (lowerShriekTopTraceTheta ℓ f jf hf ν)
      hN).hom := by
  let K := (derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))
  obtain ⟨γ, hγ⟩ := exists_lowerShriekTopTraceTheta_eq ℓ f jf hf ν
  have hb := bijective_map_mor₂_shift (H := derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙
      preadditiveCoyoneda.obj
        (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ))))
    (plusTriangleLTGE K 1) (plusTriangleLTGE_distinguished K 1) N
    (subsingleton_lowerShriek_plusTruncLT ℓ f jf q jS d hdimS hR0 N (2 * d + 1)
      (by push_cast; omega) (by omega))
    (subsingleton_lowerShriek_plusTruncLT ℓ f jf q jS d hdimS hR0 (N + 1) (2 * d + 2)
      (by push_cast; omega) (by omega))
  let Hs := derivedLowerShriek.{u, 0} q jS (ZMod ℓ) ⋙ preadditiveCoyoneda.obj
    (op ((DerivedCategory.Plus.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)))
  rw [bijective_transferHom_iff, hγ]
  have hmap : Hs.map (((plusTriangleLTGE K 1).mor₂ ≫ γ.hom)⟦N⟧') =
      Hs.map ((plusTriangleLTGE K 1).mor₂⟦N⟧') ≫ Hs.map (γ.hom⟦N⟧') :=
    (congrArg Hs.map ((shiftFunctor _ N).map_comp _ _)).trans (Hs.map_comp _ _)
  refine (congrArg (fun φ => Function.Bijective (AddCommGrpCat.Hom.hom φ)) hmap).mpr ?_
  exact ((Hs.mapIso ((shiftFunctor _ N).mapIso γ)).addCommGroupIsoToAddEquiv.bijective).comp hb

end TopDegree

end Stacks.EtaleCohomology

end
