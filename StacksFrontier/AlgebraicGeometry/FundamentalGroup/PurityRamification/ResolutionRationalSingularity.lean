module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.InvertiblePiece
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.InvertibleOfStalkRankOne
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.CohenMacaulayNeighbourhood
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.RationalOfDualizingSection
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionDualizingModule
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.VanishingSectionNakayama
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeCurveDimension
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular

/-!
# The rational singularity step of Tag 0EA3

In the situation of [Stacks, Tag 0EA3], with `X` affine and Cohen–Macaulay, `𝒪_{X, x}` defines a
rational singularity.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Duality Opposite
open RingedSpaceModuleAdjunction (modulePullback)

universe u

namespace Stacks.PurityRamification

/-- An immersion into a smooth proper scheme for a morphism `b ≫ h` with `b` H-projective and
the source of `h` quasi-affine. -/
theorem exists_immersion_smooth_proper_of_isProjectiveMorphism {X' U S : Scheme.{u}}
    (b : X' ⟶ U) (hb : IsProjectiveMorphism b) (h : U ⟶ S) [U.IsQuasiAffine]
    [LocallyOfFiniteType h] :
    ∃ (P : Scheme.{u}) (ι : X' ⟶ P) (g : P ⟶ S), IsImmersion ι ∧ Smooth g ∧ IsProper g ∧
      ι ≫ g = b ≫ h := by
  obtain ⟨P₀, ι₀, g₀, hι₀, hg₀, hgp₀, hfac₀⟩ := exists_immersion_smooth_proper h
  obtain ⟨N, i₀, hi₀, hi₀f⟩ := hb
  have := hι₀
  have := hg₀
  have := hgp₀
  have := hi₀
  have hsq := isPullback_projectiveSpaceOverMap N ι₀
  have : IsImmersion (projectiveSpaceOverMap N ι₀) :=
    MorphismProperty.of_isPullback hsq.flip inferInstance
  have : IsProper (projectiveSpaceOver N P₀ ↘ P₀) := isProper_projectiveSpaceOver N P₀
  refine ⟨projectiveSpaceOver N P₀, i₀ ≫ projectiveSpaceOverMap N ι₀,
    (projectiveSpaceOver N P₀ ↘ P₀) ≫ g₀, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [← hi₀f, ← hfac₀]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact projectiveSpaceOverMap_fst N ι₀

/-- A point of `Spec 𝒪_{X, x}` other than the closed point maps outside `closure {x}`: its image
is a generization of `x`, and a generization of `x` lying in `closure {x}` is `x` itself, the
image of the closed point. -/
theorem fromSpecStalk_notMem_closure {X : Scheme.{u}} (x : X) (p : Spec (X.presheaf.stalk x))
    (hp : p ≠ IsLocalRing.closedPoint (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∉ closure ({x} : Set X) := by
  intro hmem
  have h1 : X.fromSpecStalk x p ⤳ x := by
    have := (IsLocalRing.specializes_closedPoint p).map (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  have h2 : x ⤳ X.fromSpecStalk x p := specializes_iff_mem_closure.mpr hmem
  have h3 : X.fromSpecStalk x p = X.fromSpecStalk x (IsLocalRing.closedPoint _) := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact (h1.antisymm h2).eq
  exact hp ((X.fromSpecStalk x).isEmbedding.injective h3)

/-- **Étaleness of the model over the complement of `closure {x}`.** If `f` is étale outside
`closure {x}` and `b : Z' ⟶ U` is an isomorphism over `U ∖ closure {x}`, then `b ≫ f|_U` is étale
at every point of `Z'` mapping outside `closure {x}`. -/
theorem etaleAt_comp_of_isIso_pullback_snd {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) (Uo : X.Opens) {Z' : Scheme.{u}}
    (b : Z' ⟶ Uo.toScheme)
    (hiso : IsIso (pullback.snd b (Scheme.Opens.ι (X := X) Uo ⁻¹ᵁ
      ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩).ι))
    (z' : Z') (hz' : Uo.ι (b z') ∉ closure ({x} : Set X)) : EtaleAt (b ≫ Uo.ι ≫ f) z' := by
  let Vo : Uo.toScheme.Opens := Uo.ι ⁻¹ᵁ ⟨(closure {x})ᶜ, isClosed_closure.isOpen_compl⟩
  have heq : b ∣_ Vo = (pullbackRestrictIsoRestrict b Vo).inv ≫ pullback.snd b Vo.ι := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict, Iso.inv_hom_id_assoc]
  have : IsIso (b ∣_ Vo) := by
    rw [heq]
    infer_instance
  exact etaleAt_comp b (Uo.ι ≫ f) (x := z') (etaleAt_of_isIso_restrict b Vo z' hz')
    (etaleAt_comp_of_etale Uo.ι f (b z') (het _ hz'))

open Stacks.SheafOfModules.TensorStalkRingedSpace in
/-- **A map `𝒪_X ⟶ L` bijective on the stalk at `x` gives a section not vanishing at `x`.** If
the germ of `ψ(1)` were in `𝔪_x L_x`, so would be the whole image of the stalk map
(`Stacks.SheafOfModules.stalkMapL_unitHomEquiv_symm_mem_maximalSmul`), which is `L_x`; by
Nakayama `L_x = 0`, contradicting injectivity on the nonzero stalk of `𝒪_X`. -/
theorem mem_nonvanishingLocus_of_bijective_stalkMapL {X : RingedSpace.{u, u}}
    [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    (ψ : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ L) (x : X.carrier)
    (hbij : Function.Bijective
      (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val ψ.val x))
    (hfin : Module.Finite (ringStalk X x) (grpStalk X L.val x))
    (hnt : Nontrivial (grpStalk X (_root_.SheafOfModules.unit (structureSheafRing X)).val x)) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus L (L.unitHomEquiv ψ) := by
  by_contra hx
  have hrange := Stacks.SheafOfModules.stalkMapL_unitHomEquiv_symm_mem_maximalSmul L
    (L.unitHomEquiv ψ) hx
  rw [Equiv.symm_apply_apply] at hrange
  have h0 := Stacks.SheafOfModules.eq_zero_of_surjective_stalkMapL_of_mem_maximalSmul ψ hfin
    hbij.2 hrange
  obtain ⟨u, hu⟩ := exists_ne (0 : grpStalk X (_root_.SheafOfModules.unit
    (structureSheafRing X)).val x)
  exact hu (hbij.1 ((h0 _).trans (map_zero _).symm))

/-- **`𝒪_{X, x}` defines a rational singularity** in the situation of [Stacks, Tag 0EA3], once
`X` has been shrunk to be affine and Cohen–Macaulay. -/
theorem definesRationalSingularity_stalk_of_isCohenMacaulay {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [IsAffine X] (hCM : AlgebraicGeometry.IsCohenMacaulay X) (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)] [IsNormalDomain (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) :
    DefinesRationalSingularity (X.presheaf.stalk x) := by
  classical
  have : IsNoetherianRing A := hA.1.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hBloc : IsLocalRing (X.presheaf.stalk x) := inferInstance
  obtain ⟨W, g, hres, hproj, j, Zm, hfp, hprop, hZproj, hreg, hiso, ⟨eW⟩⟩ :=
    exists_spreadOut_resolution_stalk hA f x hdim
  have hx2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := hdim.ge
  have hG := isGorensteinLocalRing_stalk_of_isCohenMacaulay f hCM x hx2 het
  -- the affine neighbourhood `U` of the model
  let Uo : X.Opens := j.obj.1
  have : IsAffine Uo.toScheme := isAffineOpen_affineOpenNhds X x j
  let h : Uo.toScheme ⟶ Spec (.of A) := Uo.ι ≫ f
  have hCMU : AlgebraicGeometry.IsCohenMacaulay Uo.toScheme := hCM.restrict Uo
  have hetU : ∀ z : Uo.toScheme, ringKrullDim (Uo.toScheme.presheaf.stalk z) ≤ 1 →
      EtaleAt h z := by
    intro z hz
    have hz' : ringKrullDim (X.presheaf.stalk z.1) ≤ 1 := by
      rwa [← ringKrullDim_eq_of_ringEquiv (Uo.stalkIso z).commRingCatIsoToRingEquiv]
    exact etaleAt_comp_of_etale Uo.ι f z (etaleAt_of_ringKrullDim_le_one f x hx2 het z.1 hz')
  -- the model `b : X' ⟶ U` and the cartesian square over `π : Spec 𝒪_{X, x} ⟶ U`
  let π : Spec (X.presheaf.stalk x) ⟶ Uo.toScheme := (specStalkCone X x).π.app j
  let b : Zm.left ⟶ Uo.toScheme := Zm.hom
  have : IsProper b := hprop
  let ε : W ≅ pullback b π := (Over.forget _).mapIso eW
  let π' : W ⟶ Zm.left := ε.hom ≫ pullback.fst b π
  have hw₂ : ε.hom ≫ pullback.snd b π = g := Over.w eW.hom
  have sq : IsPullback π' g b π :=
    IsPullback.of_iso_pullback ⟨by rw [← hw₂, Category.assoc, Category.assoc,
      pullback.condition]⟩ ε rfl hw₂
  have : IsIntegral W := hres.1.2.2
  have : IsProper g := hres.1.2.1
  have hdimW : topologicalKrullDim W = 2 := by
    have : IsLocallyNoetherian (Spec (X.presheaf.stalk x)) :=
      isLocallyNoetherian_Spec.mpr inferInstance
    rw [IsBirational.topologicalKrullDim_eq_of_isClosedMap hres.1.1 g.isClosedMap]
    show topologicalKrullDim (PrimeSpectrum (X.presheaf.stalk x)) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  -- an immersion of the model into a smooth proper scheme, and a compactification
  obtain ⟨P, ι, gP, hι, hgP, hgpP, hfac⟩ :=
    exists_immersion_smooth_proper_of_isProjectiveMorphism b hZproj h
  have : @IsImmersion (FTS.mk (b ≫ h)).left P ι := hι
  have : @Smooth P (FTS.mk (𝟙 (Spec (.of A)))).left gP := hgP
  have : @IsProper P (FTS.mk (𝟙 (Spec (.of A)))).left gP := hgpP
  obtain ⟨c', -⟩ : ∃ c : CompactificationOf (Over.mk (b ≫ h)), True := by
    have := hι
    have := hgpP
    have : QuasiCompact (ι ≫ gP) := by
      rw [hfac]
      infer_instance
    have : QuasiCompact ι := QuasiCompact.of_comp ι gP
    obtain ⟨c, -⟩ := exists_quasiCompact_compactificationOf_of_isImmersion_isProper ι gP
    exact ⟨hfac ▸ c, trivial⟩
  -- `X'` regular over the regular `Spec A`: a local complete intersection morphism (0E9K)
  have hregA : IsRegular (Spec (.of A)) :=
    (isRegular_spec_iff A).mpr (((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp ‹_›)
  have hlci : IsLocalCompleteIntersectionMorphism (b ≫ h) :=
    isLocalCompleteIntersectionMorphism_of_isRegular (b ≫ h) hreg hregA
  let F' := ftsHomToBase (b ≫ h)
  -- a point of `W` over the punctured spectrum
  have hgen : g (genericPoint W) ≠ IsLocalRing.closedPoint (X.presheaf.stalk x) := by
    rw [IsBirational.genericPoint_eq g hres.1.1]
    intro he
    have he' := congrArg PrimeSpectrum.asIdeal he
    rw [genericPoint_eq_bot_of_affine] at he'
    have := ringKrullDim_eq_zero_of_isField
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr he'.symm)
    rw [hdim] at this
    exact absurd this (by decide)
  let x₀ := π' (genericPoint W)
  obtain ⟨O, r, hx₀, hclosed, hnt, hstalk, φ, hφ⟩ :=
    ClosedOpenProperFactorization.exists_piece_fundamentalClass F' ι gP hfac hlci c' x₀
  -- `W` maps into the piece `V`, being connected
  let V : Zm.left.Opens := ι ⁻¹ᵁ O
  have hWV : ∀ w : W, π' w ∈ V := by
    have hcl : IsClopen (π' ⁻¹' (V : Set Zm.left)) :=
      ⟨hclosed.preimage π'.continuous, V.isOpen.preimage π'.continuous⟩
    exact fun w => Set.eq_univ_iff_forall.mp (hcl.eq_univ ⟨genericPoint W, hx₀⟩) w
  let π'' : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι π' (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWV w)
  have hπ'' : π'' ≫ V.ι = π' := IsOpenImmersion.lift_fac _ _ _
  -- the model is étale at the points over the punctured spectrum
  have hπU : π ≫ Uo.ι = X.fromSpecStalk x := Scheme.Opens.fromSpecStalkOfMem_ι _ _ _
  have hetW : ∀ w : W, g w ≠ IsLocalRing.closedPoint (X.presheaf.stalk x) →
      EtaleAt (b ≫ h) (π' w) := by
    intro w hw
    refine etaleAt_comp_of_isIso_pullback_snd f x het Uo b hiso (π' w) ?_
    have h1 : Uo.ι (b (π' w)) = X.fromSpecStalk x (g w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Category.assoc, sq.w,
        Category.assoc, hπU, Scheme.Hom.comp_apply]
    rw [h1]
    exact fromSpecStalk_notMem_closure x (g w) hw
  -- the piece as a morphism of `FTS (Spec A)`
  let pH := ClosedOpenProperFactorization.pieceHom (X := FTS.mk (b ≫ h)) ι O
  let PF := ClosedOpenProperFactorization.pieceFTS (X := FTS.mk (b ≫ h)) ι O
  let fV := pH ≫ F'
  let ιV : V.toScheme ⟶ (Over.mk (b ≫ h)).left := V.ι
  have : IsOpenImmersion ιV := inferInstanceAs (IsOpenImmersion V.ι)
  let cV : CompactificationOf (Over.mk fV.left) := c'.precompOpen ιV
  let fVs : V.toScheme ⟶ Spec (.of A) := V.ι ≫ (b ≫ h)
  -- `r = 0`: at the étale point `x₀`, `H⁰(f_V^!𝒪)` has a nonzero stalk
  have hetV : ∀ w : W, g w ≠ IsLocalRing.closedPoint (X.presheaf.stalk x) →
      EtaleAt fVs (π'' w) := by
    intro w hw
    have hVw : V.ι (π'' w) = π' w := by rw [← Scheme.Hom.comp_apply, hπ'']
    exact etaleAt_comp_of_etale V.ι (b ≫ h) (π'' w) (hVw ▸ hetW w hw)
  let y₀ : V.toScheme := π'' (genericPoint W)
  have hy₀ : EtaleAt fVs y₀ := hetV _ hgen
  obtain ⟨Q, hyQ, hQ⟩ := (etaleAt_iff_exists_open fVs y₀).mp hy₀
  obtain ⟨U₁, hU₁, hyU₁, hU₁Q⟩ : ∃ U₁ : V.toScheme.Opens, IsAffineOpen U₁ ∧ y₀ ∈ U₁ ∧ U₁ ≤ Q := by
    obtain ⟨-, ⟨U₁, hU₁, rfl⟩, hyU₁, hle⟩ :=
      V.toScheme.isBasis_affineOpens.exists_subset_of_mem_open hyQ Q.isOpen
    exact ⟨U₁, hU₁, hyU₁, hle⟩
  have : IsAffine U₁.toScheme := hU₁
  let h₁ : U₁.toScheme ⟶ Spec (.of A) := U₁.ι ≫ fVs
  have hE₁ : Etale h₁ := by
    have := MorphismProperty.comp_mem @Etale _ _
      (inferInstance : Etale (V.toScheme.homOfLE hU₁Q)) hQ
    rwa [← Category.assoc, Scheme.homOfLE_ι] at this
  have : LocallyOfFiniteType h₁ := inferInstance
  have hCM₁ : AlgebraicGeometry.IsCohenMacaulay U₁.toScheme :=
    AlgebraicGeometry.isCohenMacaulay_of_isRegular ((hreg.restrict V).restrict U₁)
  have het₁ : ∀ z : U₁.toScheme, ringKrullDim (U₁.toScheme.presheaf.stalk z) ≤ 1 →
      EtaleAt h₁ z := fun z _ => (etale_iff_forall_etaleAt h₁).mp hE₁ z
  have : IsNoetherian ((Functor.fromPUnit (Spec (.of A))).obj PF.right) :=
    inferInstanceAs (IsNoetherian (Spec (.of A)))
  have : LocallyOfFiniteType (U₁.ι ≫ PF.hom) := inferInstanceAs (LocallyOfFiniteType h₁)
  have : QuasiCompact (U₁.ι ≫ PF.hom) := inferInstanceAs (QuasiCompact h₁)
  have : IsSeparated (U₁.ι ≫ PF.hom) := inferInstanceAs (IsSeparated h₁)
  let j₁ : FTS.mk (U₁.ι ≫ PF.hom) ⟶ PF := MorphismProperty.Over.homMk U₁.ι rfl
  have : IsOpenImmersion j₁.left := inferInstanceAs (IsOpenImmersion U₁.ι)
  obtain ⟨e₁⟩ := nonempty_upperShriek_derivedStructureSheaf_iso h₁ hCM₁ het₁
    (cV.precompOpen j₁.left)
  have hnt₁ : Nontrivial ↑((ClosedOpenProperFactorization.upperShriekHomology (j₁ ≫ fV)
      (cV.precompOpen j₁.left) 0).presheaf.stalk (⟨y₀, hyU₁⟩ : U₁.toScheme)) := by
    let eG : ClosedOpenProperFactorization.upperShriekHomology (j₁ ≫ fV)
        (cV.precompOpen j₁.left) 0 ≅ Stacks.Ample.unitModule U₁.toScheme :=
      (DerivedCategory.homologyFunctor _ 0).mapIso ((ObjectProperty.ι _).mapIso e₁) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _
    have : Nontrivial ↑(U₁.toScheme.presheaf.stalk (⟨y₀, hyU₁⟩ : U₁.toScheme)) :=
      (U₁.toScheme.toLocallyRingedSpace.isLocalRing _).toNontrivial
    exact ((Stacks.Ample.unitStalkEquiv U₁.toScheme _).symm.trans
      (AlgebraicGeometry.schemeStalkLinearEquiv eG.symm _)).toEquiv.symm.nontrivial
  have hntV := (ClosedOpenProperFactorization.nontrivial_stalk_upperShriekHomology_comp_iff j₁ fV
    cV 0 ⟨y₀, hyU₁⟩).mp hnt₁
  obtain rfl : r = 0 := by
    have := (hnt y₀ 0).mp hntV
    omega
  -- `ω_V = H⁰(f_V^!𝒪)` is invertible: coherent with stalks free of rank one
  let ωV : V.toScheme.Modules := ClosedOpenProperFactorization.upperShriekHomology fV cV (-0)
  have : IsLocallyNoetherian V.toScheme := LocallyOfFiniteType.isLocallyNoetherian fVs
  have hKV := isDualizingComplex_upperShriek_obj fV cV _
    (isDualizingComplex_derivedStructureSheaf_spec A)
  have hcohV : _root_.SheafOfModules.IsCoherent ωV :=
    isCoherent_homology_of_isDualizingComplex hKV (-0)
  have hinvV : Stacks.Ample.IsInvertibleModule V.toScheme ωV :=
    Scheme.Modules.isInvertibleModule_of_forall_stalk_linearEquiv ωV hcohV hstalk
  -- the section `ψ₀(1)` of `ω_V`, nonvanishing where `f_V` is smooth
  let ψ₀ : _root_.SheafOfModules.unit V.toScheme.ringCatSheaf ⟶ ωV :=
    (VectorBundleKZero.exteriorPowerZeroIsoUnit V.toScheme _).inv ≫ φ
  let sV : ωV.sections := ωV.unitHomEquiv ψ₀
  -- its pullback to `W`
  let πL : W.toLocallyRingedSpace ⟶ V.toScheme.toLocallyRingedSpace := π''.toLRSHom
  let L : W.Modules := (modulePullback πL.toShHom).obj ωV
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible W.sheaf.obj
      W.ringCatSheaf.property L := by
    have : AlgebraicGeometry.SheafOfModules.IsInvertible V.toScheme.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          V.toScheme.IsSheaf) ωV := hinvV
    exact Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback πL.toShHom ωV
  let s : L.sections := Stacks.SheafOfModules.modulePullbackSection πL ωV sV
  have hgenW : ∀ w : W, g w ≠ IsLocalRing.closedPoint (X.presheaf.stalk x) →
      w ∈ Stacks.SheafOfModules.nonvanishingLocus (X := W.toRingedSpace) L s := by
    intro w hw
    have hsm := ((etaleAt_iff_smoothAt_and_unramifiedAt fVs (π'' w)).mp (hetV w hw)).1
    have hφw := (hφ (π'' w)).mpr hsm
    have hφz : IsIso ((Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).map φ) :=
      (ClosedOpenProperFactorization.isIso_stalkMap_iff_isIso_stalkAb (Z := V.toScheme)
        (π'' w) φ).mp hφw
    have hψz : IsIso ((Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).map ψ₀) := by
      have h3 : IsIso ((Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).map
          (VectorBundleKZero.exteriorPowerZeroIsoUnit V.toScheme _).inv ≫
          (Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).map φ) :=
        (((Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).mapIso
          (VectorBundleKZero.exteriorPowerZeroIsoUnit V.toScheme _).symm) ≪≫
            @asIso _ _ _ _ ((Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).map φ)
              hφz).isIso_hom
      convert h3 using 2
      all_goals first
        | rfl
        | exact heq_of_eq ((Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).map_comp _ _)
    have hbij : Function.Bijective
        ((Stacks.ConormalSequenceRight.stalkAb V.toScheme (π'' w)).map ψ₀) :=
      ConcreteCategory.bijective_of_isIso _
    let eU := Stacks.SheafOfModules.unitStalkLinearEquiv (X := V.toScheme.toRingedSpace) (π'' w)
    have hπw := mem_nonvanishingLocus_of_bijective_stalkMapL (X := V.toScheme.toRingedSpace)
      ωV ψ₀ (π'' w) hbij (Module.Finite.of_surjective
        ((Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL V.toScheme.toRingedSpace _ _
          ψ₀.val (π'' w)).comp eU.toLinearMap) (hbij.2.comp eU.surjective))
      eU.symm.toEquiv.nontrivial
    exact (Set.ext_iff.mp (Stacks.SheafOfModules.preimage_nonvanishingLocus πL ωV sV) w).mp hπw
  have hs : s.eval (op ⊤) ≠ 0 := by
    intro h0
    apply hgenW (genericPoint W) hgen
    show _ ∈ _
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  -- `ω_W ≅ L`
  obtain ⟨e₀⟩ := @nonempty_relativeDualizingModule_iso_pullback_upperShriekHomology A _ _ _ _ h _
    hCMU hetU (X.presheaf.stalk x) _ hBloc _ π (flat_specStalkCone_π_app X x j) _ b _ _ g π' sq
    hdimW c'
  have : IsOpenImmersion pH.left :=
    ClosedOpenProperFactorization.isOpenImmersion_pieceHom_left (X := FTS.mk (b ≫ h)) ι O
  let eL := e₀ ≪≫ (Scheme.Modules.pullbackCongr hπ''.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp π'' V.ι).app _).symm ≪≫
      (Scheme.Modules.pullback π'').mapIso
        (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm ≪≫
          (ClosedOpenProperFactorization.upperShriekHomologyRestrictIso pH F' c' 0).symm)
  exact definesRationalSingularity_of_relativeDualizingModule_section (X.presheaf.stalk x) hdim
    (isNagataRing_of_isQuasiExcellent
      (isExcellent_stalk_of_isExcellent_of_locallyOfFiniteType hA f x).1)
    (ModuleCat.of _ (X.presheaf.stalk x))
    ⟨inferInstance, 0, hG⟩ g hres L ⟨eL⟩ s hs hgenW

end Stacks.PurityRamification

end
