module

public import StacksFrontier.AlgebraicGeometry.ProEtale.BoundedLocallyConstantReduction
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedInverseImage
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedInverseImageComplete
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteComparison
public import
  StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Localization
public import
  StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.ClosedImmersionPushforwardExact
public import
  StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.ClosedImmersionPushforwardExactSupplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageFiniteLocallyConstant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafIsoDescent
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Linear
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TopDegree
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# The pieces of a clopen decomposition in the base case of Stacks 09C3

Let `X` be an affine weakly contractible scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal.
The base case of the induction proving Stacks 09C3 concerns a sheaf `F` of `Λ`-modules on
`X_proét` such that `F[-a]` has bounded locally constant reduction in `[a, a]`
(`AlgebraicGeometry.ProEtale.HasBoundedLocallyConstantReduction`): `F` is derived complete, the
reduction `F ⊗_Λ^L \underline{Λ/I}` has Tor amplitude in degree `0`, and
`F ⊗_Λ \underline{Λ/I}` is locally constant of finite type. The proof begins: "since `X` is
weakly contractible, there exists a finite disjoint open covering `X = ∐ U_i` such that
`F ⊗ Λ/I` restricts to a constant sheaf on each `U_i`". This file supplies that step and checks,
on each piece `j : U ⟶ X`, the hypotheses under which `j⁻¹F` is a completed constant sheaf:

* `j⁻¹F` is derived complete, read in degree `0`;
* `H⁻¹(j⁻¹F ⊗_Λ^L \underline{N}) = 0` for every `Λ`-module `N` killed by `I`;
* `j⁻¹F ⊗_Λ \underline{Λ/I}` is the restriction of `F ⊗_Λ \underline{Λ/I}`, hence constant, with
  a finitely generated value killed by `I`;
* `j⁻¹F → j⁻¹F ⊗_Λ \underline{Λ/I}` is surjective on global sections, because the ring of
  global sections of a clopen subscheme of `X` is again w-contractible.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.isZero_sheaf_of_isEmpty`: every sheaf of modules on the small
  pro-étale site of an empty scheme is zero.
* `AlgebraicGeometry.ProEtale.constantSheafIsoProetaleModuleInverseImageOfOverPullback`: if the
  restriction of a sheaf `G` on `X_proét` to the slice over `j : U ⟶ X` is the constant sheaf
  `\underline{M}`, then `j⁻¹G ≅ \underline{M}` on `U_proét`.
* `exists_opens_isConstantFGOver_of_isFiniteTypeLocallyConstantModuleSheaf`, in the namespace
  `AlgebraicGeometry.ProEtale`: a sheaf locally constant of finite type on `X_proét` is constant
  of finite type on the members of a finite decomposition of `X` into disjoint clopen opens.
* In the namespace `AlgebraicGeometry.ProEtale`,
  `HasBoundedLocallyConstantReduction.isDerivedComplete_proetaleModuleInverseImage`,
  `HasBoundedLocallyConstantReduction.isZero_homology_tensor_proetaleModuleInverseImage`
  and `nonempty_proetaleModuleInverseImage_tensor_iso`: the hypotheses above, on a piece.

## References

* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w w'

namespace AlgebraicGeometry

/-- **Sheaves on the small pro-étale site of an empty scheme vanish**: every object of the site
has empty underlying scheme, so it is covered by the empty sieve and every sheaf has zero
sections over it. -/
theorem Scheme.ProEt.isZero_sheaf_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] {R : Type*} [Ring R]
    (F : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{w'} R)) : IsZero F := by
  have h (Z : Y.ProEt) : IsZero (F.obj.obj (op Z)) := by
    have : IsEmpty Z.left := ⟨fun z => (IsEmpty.false : Y → False) (Z.hom z)⟩
    exact (F.isTerminalOfBotCover Z (Scheme.ProEt.bot_mem_topology_of_isEmpty Z this)).isZero
  refine (IsZero.iff_id_eq_zero _).2 ?_
  ext Z : 3
  exact (h Z.unop).eq_of_src _ _

namespace ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.ModuleSheaf.derivedMonoidal Stacks.ModuleSheaf.derivedSymmetric

variable {X : Scheme.{u}} {Λ : Type (max (u + 1) w)} [CommRing Λ]

/-- Sheafification of presheaves of modules on the slices of the small pro-étale site. -/
local instance hasSheafify_proEt_over_moduleCat_of_clopenPieces (R : Type (max (u + 1) w))
    [CommRing R] {Y : Scheme.{u}} (V : Y.ProEt) :
    HasSheafify ((Scheme.ProEt.topology Y).over V) (ModuleCat.{max (u + 1) w} R) :=
  hasSheafify_moduleCat.{u + 1, u, max (u + 1) w, max (u + 1) w} _ _

section Bridge

attribute [local instance] proetalePostcompose_isContinuous

/-- **Restriction along a weakly étale morphism and the slice site.** Let `j : U ⟶ X` be weakly
étale and `G` a sheaf of `Λ`-modules on `X_proét` whose restriction to the slice site over the
object `j` of `X_proét` is the constant sheaf `\underline{M}`. Then the inverse image `j⁻¹G` is
the constant sheaf `\underline{M}` on `U_proét`.

The slice site over `j` is equivalent to `U_proét`
(`AlgebraicGeometry.ProEtale.localizationEquivalence`, compatibly with the topologies), and
transporting along this equivalence carries the restriction of `G` to the slice to the
restriction of `G` along composition with `j`, which is `j⁻¹G`
(`AlgebraicGeometry.ProEtale.proetaleModuleInverseImageIsoRestriction`). Transport along an
equivalence of sites carries constant sheaves to constant sheaves, both being left adjoint to
sections over a final object (`Stacks.ConstantSheaf.constantSheafIsoOfPushforward`). -/
def constantSheafIsoProetaleModuleInverseImageOfOverPullback {U : Scheme.{u}} (j : U ⟶ X)
    [WeaklyEtale j] (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (M : ModuleCat.{max (u + 1) w} Λ)
    (c : (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk j))
        (ModuleCat.{max (u + 1) w} Λ)).obj M ≅
      ((Scheme.ProEt.topology X).overPullback (ModuleCat.{max (u + 1) w} Λ)
        (Scheme.ProEt.mk j)).obj G) :
    (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj M ≅
      (proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ).obj G := by
  let W := Scheme.ProEt.mk j
  let e := localizationEquivalence W
  let JW := Scheme.ProEt.topology W.left
  let JO := (Scheme.ProEt.topology X).over W
  have : e.functor.IsDenseSubsite JW JO := by
    change e.functor.IsDenseSubsite (Scheme.ProEt.topology W.left) _
    rw [localizationEquivalence_inducedTopology]
    infer_instance
  have : e.symm.inverse.IsDenseSubsite JW JO := this
  have : e.inverse.IsDenseSubsite JO JW := by
    change e.symm.functor.IsDenseSubsite _ (Scheme.ProEt.topology W.left)
    rw [localizationEquivalence_inducedTopology]
    exact (inferInstance : e.symm.functor.IsDenseSubsite JO (e.symm.inverse.inducedTopology JO))
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  let E := e.symm.sheafCongr JO JW (ModuleCat.{max (u + 1) w} Λ)
  have hT : IsTerminal (Scheme.ProEt.mk (𝟙 W.left)) := MorphismProperty.Over.mkIdTerminal _ _
  let i := Stacks.ConstantSheaf.constantSheafIsoOfPushforward JO JW (ModuleCat.{max (u + 1) w} Λ)
    e.inverse E.toAdjunction (Iso.refl _)
    Over.mkIdTerminal hT ((Over.mkIdTerminal.isTerminalObj e.inverse).uniqueUpToIso hT)
  exact (i.app M).symm ≪≫ E.functor.mapIso c ≪≫ Iso.refl _ ≪≫
    ((proetaleModuleInverseImageIsoRestriction.{u, max (u + 1) w, w} Λ j).app G).symm

/-- **Restriction of a sheaf constant of finite type over a weakly étale `j`.** If the
restriction of `G` to the slice site over the object `j : U ⟶ X` of `X_proét` is the constant
sheaf on a finitely generated module, then so is `j⁻¹G` on `U_proét`, with the same value. -/
theorem exists_constantSheaf_iso_proetaleModuleInverseImage_of_isConstantFGOver
    {U : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    {G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)}
    (hG : Stacks.ConstantSheaf.IsConstantFGOver (Scheme.ProEt.topology X) Λ
      (Scheme.ProEt.mk j) G) :
    ∃ M : ModuleCat.{max (u + 1) w} Λ, Module.Finite Λ M ∧
      Nonempty ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj M ≅
        (proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ).obj G) := by
  obtain ⟨M, hM, ⟨c⟩⟩ := hG
  exact ⟨M, (ModuleCat.isFG_iff _).mp hM,
    ⟨constantSheafIsoProetaleModuleInverseImageOfOverPullback j G M c⟩⟩

end Bridge

section Decomposition

open ProetaleWContractible

variable (X Λ) in
/-- **A sheaf locally constant of finite type is constant of finite type on a clopen
decomposition.** Let `X` be an affine weakly contractible scheme and `G` a sheaf of `Λ`-modules
on `X_proét` which is locally constant of finite type. Then `X` is a finite disjoint union of
clopen opens `U i` such that the restriction of `G` to the slice over each `U i ⟶ X` is the
constant sheaf on a finitely generated module.

A trivializing covering of the final object of `X_proét` is refined by a clopen decomposition
of `X` (Stacks 098H,
`AlgebraicGeometry.Scheme.ProEt.exists_clopenDecomposition_of_isWContractible`),
and the images of its members are the opens. -/
theorem exists_opens_isConstantFGOver_of_isFiniteTypeLocallyConstantModuleSheaf [IsAffine X]
    (hX : IsWeaklyContractibleObj X)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
      max (u + 1) w, max (u + 1) w} (Scheme.ProEt.topology X) Λ G) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ⨆ i, U i = ⊤ ∧ (∀ i, IsClopen (U i : Set X)) ∧
      ∀ i, Stacks.ConstantSheaf.IsConstantFGOver (Scheme.ProEt.topology X) Λ
        (Scheme.ProEt.mk (U i).ι) G := by
  let W := Scheme.ProEt.mk (𝟙 X)
  have : IsAffine W.left := inferInstanceAs (IsAffine X)
  obtain ⟨ι, V, f, hf, hV⟩ := hG W
  obtain ⟨n, Us, g, hdec, hg, hR⟩ := Scheme.ProEt.exists_clopenDecomposition_of_isWContractible W
    (isWContractible_of_isWeaklyContractible X hX) _ hf
  refine ⟨n, fun i => let := hdec.openImmersion i; (g i).opensRange, fun i k hik => ?_, ?_,
    fun i => hdec.clopen i, fun i => ?_⟩
  · have := hdec.openImmersion i
    have := hdec.openImmersion k
    change Disjoint (g i).opensRange (g k).opensRange
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact hdec.disjoint i k hik
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x ∈ ⋃ i, Set.range (g i).base := hdec.cover ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · have hi := hdec.openImmersion i
    obtain ⟨k, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp (hR i)
    let q : Scheme.ProEt.mk (g i).opensRange.ι ⟶ Scheme.ProEt.clopenDecompositionObj W g hg i :=
      MorphismProperty.Over.homMk (IsOpenImmersion.lift (H := hi) (g i) (g i).opensRange.ι
        (by rintro _ ⟨y, rfl⟩; exact y.2)) (by
          change IsOpenImmersion.lift (H := hi) _ _ _ ≫ g i ≫ 𝟙 X = _
          exact (congrArg (IsOpenImmersion.lift (H := hi) _ _ _ ≫ ·) (Category.comp_id (g i))).trans
            (IsOpenImmersion.lift_fac _ _ _))
    exact (Stacks.ConstantSheaf.IsConstantFGOver.restrict h (hV k)).restrict q

end Decomposition

section Pieces

variable (I : Ideal Λ) [IsNoetherianRing Λ]

/-- **Restriction to a locally closed subscheme preserves derived completeness, read in degree
`0`.** If `F[-a]` is derived complete on `X_proét` along `I·\underline{Λ}`, then for an
immersion `j : U ⟶ X` the sheaf `j⁻¹F`, placed in degree `0`, is derived complete on `U_proét`
along `I·\underline{Λ}`: derived completeness is invariant under shifts, and restriction along an
immersion preserves it
(`AlgebraicGeometry.ProEtale.isDerivedComplete_mapDerivedCategory_proetaleModuleInverseImage`). -/
theorem isDerivedComplete_singleFunctor_zero_proetaleModuleInverseImage
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)} {a : ℤ}
    (hF : RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj
        ((DerivedCategory.singleFunctor _ a).obj F)))
    {U : Scheme.{u}} (j : U ⟶ X) [IsImmersion j] :
    RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} U Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} U Λ I)
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantCoefficientModuleEquiv.{u, max (u + 1) w, w} U Λ).functor.obj
          ((proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ).obj F))) := by
  let eU := derivedModuleEquiv.{u, max (u + 1) w, w} U Λ
  let EU := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} U Λ
  let jΛ := proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ
  have : EU.functor.Additive := Functor.additive_of_preserves_binary_products _
  have h₁ : IsDerivedComplete I ((DerivedCategory.singleFunctor _ a).obj F) :=
    DerivedCompleteRecurrence.isDerivedComplete_of_iso
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).unitIso.app _).symm
      (isDerivedComplete_derivedModuleEquiv_inverse_obj X I hF)
  have h₂ : IsDerivedComplete I ((DerivedCategory.singleFunctor _ a).obj (jΛ.obj F)) :=
    DerivedCompleteRecurrence.isDerivedComplete_of_iso
      ((jΛ.mapDerivedCategorySingleFunctor a).app F)
      (isDerivedComplete_mapDerivedCategory_proetaleModuleInverseImage j I h₁)
  have h₃ : IsDerivedComplete I ((DerivedCategory.singleFunctor _ 0).obj (jΛ.obj F)) :=
    DerivedCompleteRecurrence.isDerivedComplete_of_iso
      (((DerivedCategory.singleFunctors _).shiftIso a 0 a (by omega)).app _)
      (fun l hl => isDerivedCompleteAt_map (shiftFunctor _ a) _ l (h₂ l hl))
  exact isDerivedComplete_of_isDerivedComplete_derivedModuleEquiv_inverse_obj U I
    (DerivedCompleteRecurrence.isDerivedComplete_of_iso
      ((eU.unitIso.app _) ≪≫ eU.inverse.mapIso
        ((EU.functor.mapDerivedCategorySingleFunctor 0).app (jΛ.obj F))) h₃)

omit [IsNoetherianRing Λ] in
/-- A constant sheaf on a module killed by `I` is killed by `I`. -/
theorem smul_id_constantSheaf_eq_zero {Y : Scheme.{u}} {N : ModuleCat.{max (u + 1) w} Λ}
    (hN : ∀ x ∈ I, ∀ n : N, x • n = 0) {x : Λ} (hx : x ∈ I) :
    x • 𝟙 ((constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) w} Λ)).obj N) =
      0 := by
  have h : x • 𝟙 N = 0 := by
    ext n
    exact hN x hx n
  rw [← (constantSheaf (Scheme.ProEt.topology Y) (ModuleCat.{max (u + 1) w} Λ)).map_id]
  refine (Stacks.ModuleSheaf.constantSheaf_map_smul (J := Scheme.ProEt.topology Y) x
    (𝟙 N)).symm.trans ?_
  rw [h, CategoryTheory.Functor.map_zero]

omit [IsNoetherianRing Λ] in
/-- **The Tor condition on a piece.** If `F[-a]` has bounded locally constant reduction in
`[a, a]`, then for every morphism `j : U ⟶ X` and every `Λ`-module `N` killed by `I`,
`H⁻¹(j⁻¹F ⊗_Λ^L \underline{N}) = 0`: it is
`H^{a-1}(j⁻¹F[-a] ⊗_Λ^L \underline{N}) ≅ j⁻¹H^{a-1}(F[-a] ⊗_Λ^L \underline{N})`
(`nonempty_homology_tensor_constantSheaf_proetaleModuleInverseImage_iso`). -/
theorem HasBoundedLocallyConstantReduction.isZero_homology_tensor_proetaleModuleInverseImage
    {F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)} {a : ℤ}
    (hF : HasBoundedLocallyConstantReduction X Λ I ((DerivedCategory.singleFunctor _ a).obj F) a a)
    {U : Scheme.{u}} (j : U ⟶ X) (N : ModuleCat.{max (u + 1) w} Λ)
    (hN : ∀ x ∈ I, ∀ n : N, x • n = 0) :
    IsZero ((DerivedCategory.homologyFunctor _ (-1)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
          ((proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ).obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj N))) := by
  let jΛ := proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ
  have h₀ := hF.2.2.1 ((constantSheaf (Scheme.ProEt.topology X) _).obj N)
    (fun x hx => smul_id_constantSheaf_eq_zero I hN hx) (a - 1) (by simp)
  obtain ⟨c⟩ := nonempty_homology_tensor_constantSheaf_proetaleModuleInverseImage_iso j
    ((DerivedCategory.singleFunctor _ a).obj F) N (a - 1)
  obtain ⟨s⟩ := Stacks.ModuleSheaf.nonempty_homology_singleFunctor_tensor_iso (jΛ.obj F)
    ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj N)) a (a - 1)
  have h₁ : IsZero ((DerivedCategory.homologyFunctor _ (a - 1 - a)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (jΛ.obj F) ⊗
        (DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj N))) :=
    (jΛ.map_isZero h₀).of_iso (s.symm ≪≫ (DerivedCategory.homologyFunctor _ (a - 1)).mapIso
      (whiskerRightIso ((jΛ.mapDerivedCategorySingleFunctor a).app F).symm _) ≪≫ c.symm)
  rwa [show a - 1 - a = -1 by omega] at h₁

omit [IsNoetherianRing Λ] in
/-- **The reduction of a restriction is the restriction of the reduction.** For a morphism
`j : U ⟶ X` and a sheaf `F` of `Λ`-modules on `X_proét`,
`j⁻¹F ⊗_Λ \underline{Λ/I} ≅ j⁻¹Hᵃ(F[-a] ⊗_Λ^L \underline{Λ/I})`: both are the top cohomology
sheaf of a derived tensor product
(`Stacks.ModuleSheaf.nonempty_homology_tensor_single_iso_of_isLE`),
and inverse image commutes with the cohomology of derived tensor products with constant sheaves. -/
theorem nonempty_proetaleModuleInverseImage_tensor_iso
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) {U : Scheme.{u}}
    (j : U ⟶ X) (a : ℤ) :
    Nonempty ((proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ).obj F ⊗
        quotientConstantSheaf U Λ I ≅
      (proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ).obj
        ((DerivedCategory.homologyFunctor _ a).obj
          ((DerivedCategory.singleFunctor _ a).obj F ⊗
            (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I)))) := by
  let jΛ := proetaleModuleInverseImage.{u, max (u + 1) w, w} j Λ
  obtain ⟨c⟩ := nonempty_homology_tensor_constantSheaf_proetaleModuleInverseImage_iso j
    ((DerivedCategory.singleFunctor _ a).obj F)
    ((ModuleCat.restrictScalars.{max (u + 1) w} (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I))) a
  obtain ⟨t⟩ := Stacks.ModuleSheaf.nonempty_homology_tensor_single_iso_of_isLE
    ((DerivedCategory.singleFunctor _ a).obj (jΛ.obj F)) a (quotientConstantSheaf U Λ I)
  exact ⟨whiskerRightIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ a).app
      (jΛ.obj F)).symm _ ≪≫ t.symm ≪≫ (DerivedCategory.homologyFunctor _ a).mapIso
      (whiskerRightIso ((jΛ.mapDerivedCategorySingleFunctor a).app F).symm _) ≪≫ c.symm⟩

omit [IsNoetherianRing Λ] in
/-- The constant sheaf `\underline{Λ/I}` is killed by `I`. -/
theorem smul_id_quotientConstantSheaf_eq_zero (Y : Scheme.{u}) {x : Λ} (hx : x ∈ I) :
    x • 𝟙 (quotientConstantSheaf Y Λ I) = 0 :=
  smul_id_constantSheaf_eq_zero I (fun y hy q => by
    change Ideal.Quotient.mk I y • (show Λ ⧸ I from q) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy, zero_smul]) hx

omit [IsNoetherianRing Λ] in
/-- **The value of a constant reduction is killed by `I`.** On a nonempty scheme `U`, if
`F ⊗_Λ \underline{Λ/I}` is the constant sheaf `\underline{M}`, then `I` kills `M`: the constant
sheaf functor is faithful over a nonempty site
(`Stacks.ConstantSheaf.eq_of_constantSheaf_map_app_eq`). -/
theorem smul_eq_zero_of_tensor_quotientConstantSheaf_iso {U : Scheme.{u}} [Nonempty U]
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ))
    (M : ModuleCat.{max (u + 1) w} Λ)
    (e : F ⊗ quotientConstantSheaf U Λ I ≅
      (constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj M) :
    ∀ x ∈ I, ∀ m : M, x • m = 0 := by
  intro x hx m
  obtain ⟨y⟩ := ‹Nonempty U›
  have hT : x • 𝟙 (F ⊗ quotientConstantSheaf U Λ I) = 0 := by
    refine (Stacks.ModuleSheaf.whiskerLeft_smul_id (J := Scheme.ProEt.topology U) x F
      (quotientConstantSheaf U Λ I)).symm.trans ?_
    rw [smul_id_quotientConstantSheaf_eq_zero I U hx, MonoidalPreadditive.whiskerLeft_zero]
  have h : x • 𝟙 M = 0 := by
    refine Stacks.ConstantSheaf.eq_of_constantSheaf_map_app_eq (Scheme.ProEt.topology U) _ _
      (U := Scheme.ProEt.mk (𝟙 U))
      (Scheme.ProEt.bot_notMem_topology_of_nonempty (X := U) (V := Scheme.ProEt.mk (𝟙 U)) y)
      ?_
    refine congrArg (fun φ => φ.hom.app (op (Scheme.ProEt.mk (𝟙 U))))
      ((Stacks.ModuleSheaf.constantSheaf_map_smul (J := Scheme.ProEt.topology U) x (𝟙 M)).trans ?_)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    have : x • 𝟙 ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).obj M) =
        e.inv ≫ (x • 𝟙 (F ⊗ quotientConstantSheaf U Λ I)) ≫ e.hom := by
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.inv_hom_id]
    rw [this, hT, zero_comp, comp_zero]
  exact congrArg (fun φ : M ⟶ M => φ.hom m) h

attribute [local instance] Stacks.ModuleSheaf.monoidalClosed in
omit [IsNoetherianRing Λ] in
/-- **Global sections of the reduction over a piece are surjective.** Let `U` be an affine scheme
whose ring of global sections is w-contractible. For every sheaf `F` of `Λ`-modules on
`U_proét`, the reduction `F → F ⊗_Λ \underline{Λ/I}` is surjective on global sections: it is an
epimorphism, as the tensor product is right exact and `\underline{Λ} → \underline{Λ/I}` is an
epimorphism, and sections over `U` are exact
(`AlgebraicGeometry.Scheme.ProEt.surjective_app_of_isWContractible_of_concrete`). -/
theorem surjective_app_mk_id_reduction_of_isWContractible {U : Scheme.{u}} [IsAffine U]
    (hU : ProetaleWContractible.IsWContractible.{u, u} Γ(U, ⊤))
    (F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)) :
    Function.Surjective (((ρ_ F).inv ≫ F ◁ (constantSheaf (Scheme.ProEt.topology U)
        (ModuleCat.{max (u + 1) w} Λ)).map (ModuleCat.ofHom
          ((Ideal.Quotient.mkₐ Λ I).toLinearMap))).hom.app (op (Scheme.ProEt.mk (𝟙 U)))) := by
  have : IsAffine (Scheme.ProEt.mk (𝟙 U)).left := inferInstanceAs (IsAffine U)
  have h₁ : Epi (ModuleCat.ofHom.{max (u + 1) w} (Ideal.Quotient.mkₐ Λ I).toLinearMap) :=
    (ModuleCat.epi_iff_surjective _).2 Ideal.Quotient.mk_surjective
  have _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  have h₂ : Epi ((constantSheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)).map
      (ModuleCat.ofHom (Ideal.Quotient.mkₐ Λ I).toLinearMap)) := by
    have := (constantSheafAdj (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ)
      (MorphismProperty.Over.mkIdTerminal _ _)).isLeftAdjoint
    infer_instance
  have h₃ : Epi ((MonoidalCategory.tensorLeft F).map ((constantSheaf (Scheme.ProEt.topology U)
      (ModuleCat.{max (u + 1) w} Λ)).map (ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ Λ I).toLinearMap)))) := inferInstance
  have h₄ : Epi ((ρ_ F).inv ≫ F ◁ (constantSheaf (Scheme.ProEt.topology U)
      (ModuleCat.{max (u + 1) w} Λ)).map (ModuleCat.ofHom
        ((Ideal.Quotient.mkₐ Λ I).toLinearMap))) := @epi_comp _ _ _ _ _ _ inferInstance _ h₃
  exact Scheme.ProEt.surjective_app_of_isWContractible_of_concrete (Scheme.ProEt.mk (𝟙 U)) hU _
    ((Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max (u + 1) w} Λ) _).2 h₄)

/-- **A clopen open of an affine scheme with w-contractible global sections** is an affine scheme
with w-contractible global sections: its inclusion is a closed immersion whose open complement,
closed in the quasi-compact space `X`, is quasi-compact
(`AlgebraicGeometry.ProEtale.isWContractible_of_isClosedImmersion_of_isCompact_compl_range`). -/
theorem isAffine_and_isWContractible_of_isClopen [IsAffine X]
    (hX : ProetaleWContractible.IsWContractible.{u, u} Γ(X, ⊤)) (V : X.Opens)
    (hV : IsClopen (V : Set X)) :
    IsAffine V.toScheme ∧ ProetaleWContractible.IsWContractible.{u, u} Γ(V.toScheme, ⊤) := by
  have hr : Set.range V.ι.base = (V : Set X) := V.range_ι
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (hr ▸ hV.isClosed)
  exact ⟨isAffine_of_isAffineHom V.ι,
    isWContractible_of_isClosedImmersion_of_isCompact_compl_range V.ι hX
      (hr ▸ hV.isOpen.isClosed_compl.isCompact)⟩

end Pieces

end ProEtale

end AlgebraicGeometry
