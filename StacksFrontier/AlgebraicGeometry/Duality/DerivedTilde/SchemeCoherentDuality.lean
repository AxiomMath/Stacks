module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeBiduality
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeOpenComplexModel
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeIsoModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexBoundedBelow

/-!
# Coherent duality on a locally Noetherian scheme: preservation and bounds

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` and `D = R𝓗om(-, K)`.
For `L` in `D_Coh(𝒪_X)`, `D(L)` lies in `D_Coh(𝒪_X)`; if `X` is quasi-compact, `D` carries
`D^+_Coh` into `D^-_Coh` and `D^-_Coh` into `D^+_Coh` ([Stacks, Tag 0A89]). Over an affine open
`V` the restrictions of `L` and `K` are associated to complexes `M`, `ω` over `Γ(X, V)` and
`D(L)|_V` is associated to `R𝓗om(M̃, ω̃)` on `Spec Γ(X, V)`, where the cohomology sheaves are
those of `R𝓗om(τ_{≤ n} M, ω)~` for `n` large ([Stacks, Tag 0A6H]) and the bounds come from the
injective amplitude of `ω`.

## Main results

* `Stacks.Duality.isCoherent_homology_derivedSheafHom_of_isDualizingComplex`: `D` preserves
  `D_Coh(𝒪_X)`.
* `Stacks.Duality.isBoundedAbove_derivedSheafHom_of_isDualizingComplex` and
  `Stacks.Duality.isBoundedBelow_derivedSheafHom_of_isDualizingComplex`: on a quasi-compact `X`,
  `D` carries `D^+_Coh` into `D^-` and `D^-_Coh` into `D^+`.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite TopologicalSpace
  AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor
  Stacks.DerivedQCoh.preservesFiniteLimits_restrictFunctor

namespace Stacks.Duality

open Stacks.SheafOfModules

/-! ### On `Spec R` -/

section Affine

variable (R : CommRingCat.{u}) [IsNoetherianRing R]
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-- **Duality preserves coherence on `Spec R`.** For `ω` a dualizing complex and `M` with finite
cohomology modules, the cohomology sheaves of `R𝓗om(M̃, ω̃)` are coherent: in degree `i` they are
those of `R𝓗om(τ_{≤ n} M, ω)~` for `n ≥ b - i`, `[a, b]` an injective amplitude of `ω`. -/
theorem isCoherent_homology_derivedSheafHom_derivedTilde
    (ω M : DerivedCategory (ModuleCat.{u} R)) (hω : Dualizing.IsDualizingComplex ω)
    (hM : ∀ i : ℤ, Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj M))
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      (((derivedSheafHom (Spec R).sheaf).obj (op ((tilde.functor R).mapDerivedCategory.obj M))).obj
        ((tilde.functor R).mapDerivedCategory.obj ω))).IsCoherent := by
  let t : Triangulated.TStructure (DerivedCategory (ModuleCat.{u} R)) :=
    DerivedCategory.TStructure.t
  let tl := (tilde.functor R).mapDerivedCategory
  let K := tl.obj ω
  let Dh := (derivedSheafHom (Spec R).sheaf).flip.obj K
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  have hωge : ω.IsGE a := StacksDraft.InjectiveDimension.isGE_of_hasInjectiveAmplitude ω a b hamp
  let n := b - i
  let TL := (t.triangleLEGE n (n + 1) rfl).obj M
  obtain ⟨δ, hD⟩ := exists_distinguished_derivedSheafHom_first (Spec R).sheaf K _
    (tl.map_distinguished TL (t.triangleLEGE_distinguished n (n + 1) rfl M))
  have hB : TL.obj₃.IsGE (n + 1) :=
    inferInstanceAs (t.IsGE ((t.truncGE (n + 1)).obj M) (n + 1))
  have hDB : (Dh.obj (op (tl.obj TL.obj₃))).IsLE (b - (n + 1)) :=
    isLE_derivedSheafHom_derivedTilde_of_injectiveAmplitude R _ ω (n + 1) a b hB hamp
  have h1 : IsIso ((DerivedCategory.homologyFunctor (StructureSheafModules (Spec R).sheaf) i).map
      (Dh.map (tl.map TL.mor₁).op)) :=
    isIso_homology_mor₂ _ hD i
      (DerivedCategory.isZero_of_isLE _ (b - (n + 1)) i (by omega) (hX := hDB))
      (DerivedCategory.isZero_of_isLE _ (b - (n + 1)) (i + 1) (by omega) (hX := hDB))
  have hAle : TL.obj₁.IsLE n := inferInstanceAs (t.IsLE ((t.truncLE n).obj M) n)
  have hAf := StacksDraft.DerivedHomFiniteness.finite_homology_truncLE M hM n
  have hApc : StacksDraft.PseudoCoherence.IsPseudoCoherent TL.obj₁ :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      TL.obj₁ 0 (R : Type u)).2.1).2
        ⟨⟨n, fun j hj => DerivedCategory.isZero_of_isLE TL.obj₁ n j hj⟩, hAf⟩
  exact isCoherent_of_modulesIso
    ((asIso ((DerivedCategory.homologyFunctor (StructureSheafModules (Spec R).sheaf) i).map
      (Dh.map (tl.map TL.mor₁).op))) ≪≫
      (DerivedCategory.homologyFunctor (StructureSheafModules (Spec R).sheaf) i).mapIso
        (affinePseudoCoherentDerivedSheafHomIso R TL.obj₁ ω hApc ⟨a, hωge⟩)).symm
    (CoherentAbelian.isCoherent_of_stacksIsCoherent (isCoherent_homology_tildeDerived R _ i
      (StacksDraft.DerivedHom.finite_homology_derivedHom
        (StacksDraft.DerivedHom.derivedHomAdjunction (R := (R : Type u))) TL.obj₁ ω n a hAle hωge
        hAf hω.finiteCohomology i)))

end Affine

/-! ### On a locally Noetherian scheme -/

section Scheme

variable {X : Scheme.{u}}

/-- **The derived internal Hom over an affine open, read on `Spec Γ(X, V)`.** If the restrictions
of `L` and `K` to the affine open `V` are, along `V ≅ Spec Γ(X, V)`, the complexes associated to
`M` and `ω`, then the restriction of `R𝓗om(L, K)` is that of `R𝓗om(M̃, ω̃)` ([Stacks, Tag 08DL]).
-/
def restrictDerivedSheafHomIsoOfModels (V : X.Opens) (hV : IsAffineOpen V)
    {L K : DerivedCategory X.Modules} {M ω : DerivedCategory (ModuleCat.{u} Γ(X, V))}
    (iL : (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj L ≅
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
        ((tilde.functor Γ(X, V)).mapDerivedCategory.obj M))
    (iK : (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K ≅
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
        ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω)) :
    (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj
        (((derivedSheafHom X.sheaf).obj (op L)).obj K) ≅
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
        (((derivedSheafHom (Spec Γ(X, V)).sheaf).obj
          (op ((tilde.functor Γ(X, V)).mapDerivedCategory.obj M))).obj
            ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω)) :=
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := X.ringCatSheaf) V
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := X.ringCatSheaf) V
  derivedSheafHomSchemeRestrictionIso V L K ≪≫
    ((RingedSite.derivedSheafHomBifunctor (ringedSite V.toScheme.sheaf)).mapIso iL.symm.op).app _ ≪≫
    ((RingedSite.derivedSheafHomBifunctor (ringedSite V.toScheme.sheaf)).obj _).mapIso iK ≪≫
    (derivedSheafHomSchemeIsoIso hV.isoSpec.hom _ _).symm

/-- Over an affine open, vanishing of a restricted cohomology sheaf is read on a model on
`Spec Γ(X, V)`. -/
theorem isZero_restrict_homology_iff (V : X.Opens) (hV : IsAffineOpen V)
    {L : DerivedCategory X.Modules} {E : DerivedCategory (Spec Γ(X, V)).Modules}
    (iL : (Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj L ≅
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj E) (i : ℤ) :
    IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj L)) ↔
      IsZero ((DerivedCategory.homologyFunctor (Spec Γ(X, V)).Modules i).obj E) := by
  let e := Stacks.AlgebraicGeometry.CoherentOfFiniteType.restrictEquivOfIso hV.isoSpec.symm
  let c : (Scheme.Modules.restrictFunctor V.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj L) ≅
      e.functor.obj ((DerivedCategory.homologyFunctor (Spec Γ(X, V)).Modules i).obj E) :=
    ((DerivedCategoryB.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor V.ι) i).app L).symm ≪≫
      (DerivedCategory.homologyFunctor V.toScheme.Modules i).mapIso iL ≪≫
      (DerivedCategoryB.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor hV.isoSpec.hom) i).app E
  refine ⟨fun h => ?_, fun h => (e.functor.map_isZero h).of_iso c⟩
  exact (e.inverse.map_isZero (h.of_iso c.symm)).of_iso (e.unitIso.app _)

/-- On a quasi-compact scheme, choosing for each affine open a bound gives finitely many opens
covering the scheme, each with its chosen bound. -/
private theorem exists_finset_cover_of_forall_isAffineOpen [CompactSpace X]
    (p : X.Opens → ℤ → Prop) (h : ∀ U : X.Opens, IsAffineOpen U → ∃ c, p U c) :
    ∃ (t : Finset X) (U : X → X.Opens) (c : X → ℤ), (∀ x, p (U x) (c x)) ∧
      ∀ y : X, ∃ x ∈ t, y ∈ (U x : Set X) := by
  have hpt : ∀ x : X, ∃ (U : X.Opens) (_ : IsAffineOpen U), x ∈ U := fun x => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hU hxU using hpt
  choose c hc using fun x => h (U x) (hU x)
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
    (fun x : X => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  exact ⟨t, U, c, hc, fun y => by simpa using ht (Set.mem_univ y)⟩

variable [IsLocallyNoetherian X]

/-- A dualizing model over an affine open, read along `V ≅ Spec Γ(X, V)`. -/
theorem exists_isDualizingComplex_iso_restrictFunctor (V : X.Opens) (hV : IsAffineOpen V)
    {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K) :
    letI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, V)), Dualizing.IsDualizingComplex ω ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).mapDerivedCategory.obj K ≅
        (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapDerivedCategory.obj
          ((tilde.functor Γ(X, V)).mapDerivedCategory.obj ω)) := by
  obtain ⟨ω, hω, ⟨e⟩⟩ := hK V hV
  exact ⟨ω, hω, ⟨e ≪≫ (Dualizing.mapDerivedCategoryComp (tilde.functor Γ(X, V))
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom)).app ω⟩⟩

/-- **Duality preserves `D_Coh`** ([Stacks, Tag 0A89]). For a dualizing complex `K` on a locally
Noetherian scheme and `L` with coherent cohomology sheaves, `R𝓗om(L, K)` has coherent cohomology
sheaves. -/
theorem isCoherent_homology_derivedSheafHom_of_isDualizingComplex
    {K L : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (((derivedSheafHom X.sheaf).obj (op L)).obj K)).IsCoherent := by
  refine AlgebraicGeometry.Modules.isCoherent_of_restrict _
    (fun U : X.affineOpens => (U : X.Opens)) (iSup_affineOpens_eq_top X) fun U => ?_
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hM := exists_finite_iso_restrictFunctor_of_isCoherent (U : X.Opens) U.2 L hL
  have hω := exists_isDualizingComplex_iso_restrictFunctor (U : X.Opens) U.2 hK
  exact isCoherent_of_modulesIso
    (((DerivedCategoryB.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor (U : X.Opens).ι) i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (U : X.Opens).toScheme.Modules i).mapIso
        (restrictDerivedSheafHomIsoOfModels (U : X.Opens) U.2 hM.choose_spec.2.some
          hω.choose_spec.2.some) ≪≫
      (DerivedCategoryB.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor (U.2.isoSpec).hom) i).app _).symm
    (isCoherent_restrict_of_isOpenImmersion _ _
      (isCoherent_homology_derivedSheafHom_derivedTilde Γ(X, U) hω.choose hM.choose
        hω.choose_spec.1 hM.choose_spec.1 i))

omit [IsLocallyNoetherian X] in
/-- On a quasi-compact scheme, an object whose cohomology sheaves vanish above a bound after
restriction to each affine open is bounded above. -/
theorem isBoundedAbove_of_forall_isAffineOpen [CompactSpace X] (F : DerivedCategory X.Modules)
    (h : ∀ U : X.Opens, IsAffineOpen U → ∃ c : ℤ, ∀ i : ℤ, c < i →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj F))) :
    DerivedCategoryB.IsBoundedAbove F := by
  obtain ⟨t, U, c, hc, ht⟩ := exists_finset_cover_of_forall_isAffineOpen _ h
  refine ⟨∑ x ∈ t, |c x|, fun i hi => ?_⟩
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  obtain ⟨x, hxt, hyx⟩ := ht y
  have hcx : c x ≤ ∑ x ∈ t, |c x| := by
    have := Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hxt
    have := le_abs_self (c x)
    omega
  exact Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict _ _ y hyx
    (hc x i (by omega))

omit [IsLocallyNoetherian X] in
/-- On a quasi-compact scheme, an object whose cohomology sheaves vanish below a bound after
restriction to each affine open is bounded below. -/
theorem isBoundedBelow_of_forall_isAffineOpen [CompactSpace X] (F : DerivedCategory X.Modules)
    (h : ∀ U : X.Opens, IsAffineOpen U → ∃ c : ℤ, ∀ i : ℤ, i < c →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor X.Modules i).obj F))) :
    DerivedCategoryB.IsBoundedBelow F := by
  obtain ⟨t, U, c, hc, ht⟩ := exists_finset_cover_of_forall_isAffineOpen _ h
  refine ⟨-∑ x ∈ t, |c x|, fun i hi => ?_⟩
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  obtain ⟨x, hxt, hyx⟩ := ht y
  have hcx : -∑ x ∈ t, |c x| ≤ c x := by
    have := Finset.single_le_sum (f := fun x => |c x|) (fun _ _ => abs_nonneg _) hxt
    have := neg_abs_le (c x)
    omega
  exact Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict _ _ y hyx
    (hc x i (by omega))

/-- **On a quasi-compact scheme duality carries `D^+_Coh` into `D^-`** ([Stacks, Tag 0A89]). -/
theorem isBoundedAbove_derivedSheafHom_of_isDualizingComplex [CompactSpace X]
    {K L : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (hLb : DerivedCategoryB.IsBoundedBelow L) :
    DerivedCategoryB.IsBoundedAbove (((derivedSheafHom X.sheaf).obj (op L)).obj K) := by
  refine isBoundedAbove_of_forall_isAffineOpen _ fun U hU => ?_
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hM := exists_finite_iso_restrictFunctor_of_isCoherent U hU L hL
  have hω := exists_isDualizingComplex_iso_restrictFunctor U hU hK
  obtain ⟨a, b, hamp⟩ := hω.choose_spec.1.finiteInjectiveDimension
  obtain ⟨n₀, hn₀⟩ := hLb
  have hMge : hM.choose.IsGE n₀ := (DerivedCategory.isGE_iff _ n₀).2 fun i hi =>
    (StandardModel.isZero_homology_mapDerivedCategory_obj_iff Γ(X, U) _ i).1
      ((isZero_restrict_homology_iff U hU hM.choose_spec.2.some i).1
        (Functor.map_isZero _ (hn₀ i hi)))
  have hle := isLE_derivedSheafHom_derivedTilde_of_injectiveAmplitude Γ(X, U) _ _ n₀ a b hMge hamp
  refine ⟨b - n₀, fun i hi => ?_⟩
  exact (isZero_restrict_homology_iff U hU (restrictDerivedSheafHomIsoOfModels U hU
    hM.choose_spec.2.some hω.choose_spec.2.some) i).2
      (DerivedCategory.isZero_of_isLE _ (b - n₀) i hi (hX := hle))

/-- **On a quasi-compact scheme duality carries `D^-_Coh` into `D^+`** ([Stacks, Tag 0A89]). -/
theorem isBoundedBelow_derivedSheafHom_of_isDualizingComplex [CompactSpace X]
    {K L : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hL : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (hLb : DerivedCategoryB.IsBoundedAbove L) :
    DerivedCategoryB.IsBoundedBelow (((derivedSheafHom X.sheaf).obj (op L)).obj K) := by
  refine isBoundedBelow_of_forall_isAffineOpen _ fun U hU => ?_
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hM := exists_finite_iso_restrictFunctor_of_isCoherent U hU L hL
  have hω := exists_isDualizingComplex_iso_restrictFunctor U hU hK
  obtain ⟨a, b, hamp⟩ := hω.choose_spec.1.finiteInjectiveDimension
  have hωge : hω.choose.IsGE a :=
    StacksDraft.InjectiveDimension.isGE_of_hasInjectiveAmplitude _ a b hamp
  obtain ⟨n₀, hn₀⟩ := hLb
  have hMle : hM.choose.IsLE n₀ := (DerivedCategory.isLE_iff _ n₀).2 fun i hi =>
    (StandardModel.isZero_homology_mapDerivedCategory_obj_iff Γ(X, U) _ i).1
      ((isZero_restrict_homology_iff U hU hM.choose_spec.2.some i).1
        (Functor.map_isZero _ (hn₀ i hi)))
  have hge := isGE_derivedSheafHom (Spec Γ(X, U)).sheaf _ _ n₀ a
    (@Stacks.Homology.isLE_mapDerivedCategory_obj _ _ _ _ _ _ _ _ (tilde.functor Γ(X, U)) _ _ _
      hM.choose n₀ hMle)
    (@Stacks.Sites.FibredCategory.isGE_mapDerivedCategory_obj _ _ _ _ _ _ _ _
      (tilde.functor Γ(X, U)) _ _ _ hω.choose a hωge)
  refine ⟨a - n₀, fun i hi => ?_⟩
  exact (isZero_restrict_homology_iff U hU (restrictDerivedSheafHomIsoOfModels U hU
    hM.choose_spec.2.some hω.choose_spec.2.some) i).2
      (DerivedCategory.isZero_of_isGE _ (a - n₀) i hi (hX := hge))

end Scheme

end Stacks.Duality

end
