module

public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.Covering
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexAffinePerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackUnitComp

/-!
# Relative dualizing complexes detected after an étale surjective base change

Let `f : X ⟶ Y` be proper, flat and of finite presentation, `g : V ⟶ Y` étale and surjective
with `V` a disjoint union of affines, and `f' : U ⟶ V` the base change of `f`. A pair `(ω, τ)` on
`X/Y` whose base change to `U/V` is isomorphic, as a pair, to a relative dualizing complex is a
relative dualizing complex. This is the last step of the proof of Stacks 0E61 (by Stacks 0E60).

## Main results

* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_isPullback`: `Y`-perfectness of
  `ω` from that of `L(g')^* ω` over `V`.
* `AlgebraicGeometry.Space.RelativeDualizingPair.isAffineBaseChangePair_of_baseChange_iso`: the
  base change condition of `(ω, τ)` from an isomorphism of its base change with a relative
  dualizing complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  sheafTensor_additive_inverseImageRingedSite_over
  sheafTensor_obj_additive_inverseImageRingedSite_over
  hasMapBifunctor_sheafTensor_inverseImageRingedSite_over

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y U V : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : V ⟶ Y} {f' : U ⟶ V} {g' : U ⟶ X}

/-- **`Y`-perfectness is detected after an étale surjective base change**: for a cartesian
square `g' ≫ f = f' ≫ g` with `g` étale and surjective and `f` flat and locally of finite
presentation, `ω ∈ D(𝒪_X)` is `Y`-perfect as soon as `L(g')^* ω` is `V`-perfect. -/
theorem isPerfectRelativeToCanonical_of_isPullback (sq : IsPullback g' f' f g)
    (hg : IsEtale B S hS g.hom) (hgs : IsSurjective B S hS g.hom) (hfl : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (ω : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (h : IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f'
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hlfp)
      ((smallEtaleDerivedModulePullback B S hS g').obj ω)) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp ω :=
  isPerfectRelativeToCanonical_of_forall_isEtale (f := f) (hfl := hfl) (hlfp := hlfp)
    (ι := Unit) (fun _ => g') (fun _ => f') (fun _ => g)
    (fun _ => (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
    (fun _ => (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hlfp)
    (fun _ => isEtale_of_isPullback B S hS _ _ _ _ sq.flip hg)
    (fun x => ⟨(), isSurjective_of_isPullback B S hS sq.flip hgs x⟩) (fun _ => hg)
    (fun _ => sq.w) ω (fun _ => h)
variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A pair which is a relative dualizing complex after an étale surjective base change is one**
(the last step of the proof of Stacks 0E61). Let `(ω, τ)` be a pair on `X/Y`, `g : V ⟶ Y` étale
and surjective with `V` the disjoint union of affines `Y_i`, and `f' : U ⟶ V` the base change of
`f`. If the base change of `(ω, τ)` to `U/V` is isomorphic, as a pair, to a relative dualizing
complex `D`, then the base change of `(ω, τ)` to every affine `Y'` is `(a'(𝒪_{Y'}), Tr)`: this
holds over the `Y_i ⟶ V ⟶ Y`, which form an étale covering of `Y`, and Stacks 0E60 applies. -/
theorem RelativeDualizingPair.isAffineBaseChangePair_of_baseChange_iso {hfl : IsFlat B S hS f.hom}
    {hfp : IsFinitePresentation B S hS f.hom} (P : RelativeDualizingPair f hfl hfp)
    (hf : IsProper B S hS f.hom) (sq : IsPullback g' f' f g) (hg : IsEtale B S hS g.hom)
    (hgs : IsSurjective B S hS g.hom)
    (D : RelativeDualizingComplex hZ f'
      ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf)
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hfl)
      ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sq hfp))
    (ε : (P.baseChange sq).ω ≅ D.ω)
    (hε : (derivedModulePushforward B S hS f').map ε.hom ≫ D.τ = (P.baseChange sq).τ)
    {ι : Type u} {Yi : ι → AlgebraicSpaces B S hS} {j : ∀ i, Yi i ⟶ V}
    (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj V)
      fun i => (algebraicSpacesToSheaf B S hS).map (j i)))
    (hYi : ∀ i, IsAffineSpace B S hS (Yi i).1)
    ⦃X' Y' : AlgebraicSpaces B S hS⦄ (f'' : X' ⟶ Y') (h : Y' ⟶ Y) (h' : X' ⟶ X)
    (sq' : IsPullback h' f'' f h) (hY' : IsAffineSpace B S hS Y'.1) :
    IsAffineBaseChangePair hZ sq' hfp hY' P.ω P.τ := by
  have sqi : ∀ i, IsPullback (pullback.snd (j i) f') (pullback.fst (j i) f') f' (j i) :=
    fun i => (IsPullback.of_hasPullback (j i) f').flip
  have hi : ∀ i, IsAffineBaseChangePair hZ ((sqi i).paste_horiz sq) hfp (hYi i) P.ω P.τ :=
    fun i => P.isAffineBaseChangePair_paste sq (sqi i) (hYi i)
      (isAffineBaseChangePair_of_iso hZ _ (sqi i) (hYi i) ε hε
        (D.isAffineBaseChangePair _ _ _ (sqi i) (hYi i)))
  have hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (j i ≫ g).hom) :=
    ⟨Y.2, fun i => (Yi i).2,
      fun i => isEtale_comp B S hS (isEtale_cofanInj_of_isColimit hc i) hg,
      Set.eq_univ_of_forall fun y => by
        obtain ⟨v, rfl⟩ := hgs y
        obtain ⟨i, w, rfl⟩ := exists_pointsMap_cofanInj_eq_of_isColimit hc v
        exact Set.mem_iUnion.2 ⟨i, w, pointsMap_comp_apply B S hS _ _ w⟩⟩
  exact P.isAffineBaseChangePair_of_isEtaleCovering_of_isProper hf
    (fun i => (sqi i).paste_horiz sq) hYi hcov hi f'' h h' sq' hY'
section Chase

variable {𝒞 : Type*} [Category* 𝒞]

/-- The bookkeeping of `RelativeDualizingPair.compIso_inv_app_comp_map_comp_eq`, in an arbitrary
category. -/
theorem compIso_inv_app_comp_map_comp_eq_aux {P Q R W Z T₁ T₂ O₁ O₂ O₃ O₄ : 𝒞}
    (cP : Q ≅ P) (LBC : Q ⟶ R) (LRε : R ⟶ W) (Lτ : W ⟶ O₁) (Lu₀ : O₂ ≅ O₁) (cO : O₂ ≅ O₃)
    (uv : O₁ ≅ O₄) (uvb : O₃ ≅ O₄) (BC₁ : P ⟶ T₁) (cU : T₂ ≅ T₁) (BC' : R ⟶ T₂) (RLε : T₂ ⟶ Z)
    (BC'' : W ≅ Z) (hh : cP.inv ≫ LBC ≫ BC' ≫ cU.hom = BC₁) (hn : LRε ≫ BC''.hom = BC' ≫ RLε)
    (hu : cO.hom ≫ uvb.hom = Lu₀.hom ≫ uv.hom) :
    cP.inv ≫ (LBC ≫ LRε ≫ Lτ ≫ Lu₀.inv) ≫ cO.hom =
      BC₁ ≫ (cU.inv ≫ RLε) ≫ (BC''.inv ≫ Lτ ≫ uv.hom) ≫ uvb.inv := by
  have hu' : Lu₀.inv ≫ cO.hom = uv.hom ≫ uvb.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hn' : LRε = BC' ≫ RLε ≫ BC''.inv := by
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh' : cP.inv ≫ LBC ≫ BC' = BC₁ ≫ cU.inv := by
    rw [← hh]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Category.assoc, hu', hn']
  rw [reassoc_of% hh']

end Chase

/-- **The transport along a further cartesian square of `BC ≫ Rf₀_* ε ≫ τ₀ ≫ u⁻¹`**: for
cartesian squares `a₀ ≫ f = f₀ ≫ b₀` and `u ≫ f₀ = f₁ ≫ v`, with `a₁ = u ≫ a₀`, `b₁ = v ≫ b₀` and a
pair `(ω₀, τ₀)` on `f₀` with `ε : L a₀^* ω ≅ ω₀`, the map
`L b₀^* Rf_* ω ⟶ L b₀^* 𝒪_Y` induced by `τ₀`, pulled back along `v` and read through
`L v^* L b₀^* ≅ L b₁^*`, is the map induced by the base change of `τ₀` to `f₁`. -/
theorem RelativeDualizingPair.compIso_inv_app_comp_map_comp_eq
    {U₀ V₀ U₁ V₁ : AlgebraicSpaces B S hS}
    {f₀ : U₀ ⟶ V₀} {a₀ : U₀ ⟶ X} {b₀ : V₀ ⟶ Y} {f₁ : U₁ ⟶ V₁} {u : U₁ ⟶ U₀} {v : V₁ ⟶ V₀}
    {a₁ : U₁ ⟶ X} {b₁ : V₁ ⟶ Y} {hfl₀ : IsFlat B S hS f₀.hom}
    {hfp₀ : IsFinitePresentation B S hS f₀.hom} (P₀ : RelativeDualizingPair f₀ hfl₀ hfp₀)
    (sq₀ : IsPullback a₀ f₀ f b₀) (sq' : IsPullback u f₁ f₀ v) (sq₁ : IsPullback a₁ f₁ f b₁)
    (ha : u ≫ a₀ = a₁) (hb : v ≫ b₀ = b₁)
    (ω : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (ε : (smallEtaleDerivedModulePullback B S hS a₀).obj ω ≅ P₀.ω) :
    (smallEtaleDerivedModulePullbackCompIso B S hS v b₀ ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS hb).inv.app
          ((derivedModulePushforward B S hS f).obj ω) ≫
      (smallEtaleDerivedModulePullback B S hS v).map
        (smallEtaleDerivedModuleBaseChangeMap B S hS f b₀ f₀ a₀ sq₀.w ω ≫
          (derivedModulePushforward B S hS f₀).map ε.hom ≫ P₀.τ ≫
          (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) b₀).inv) ≫
      (smallEtaleDerivedModulePullbackCompIso B S hS v b₀ ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS hb).hom.app
          (derivedStructureSheaf B S hS Y.1 Y.2).obj =
    smallEtaleDerivedModuleBaseChangeMap B S hS f b₁ f₁ a₁ sq₁.w ω ≫
      (derivedModulePushforward B S hS f₁).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS u a₀ ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS ha).inv.app ω ≫
          (smallEtaleDerivedModulePullback B S hS u).map ε.hom) ≫
      P₀.baseChangeTrace sq' ≫
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) b₁).inv := by
  subst ha hb
  have key := compIso_inv_app_comp_map_comp_eq_aux
    ((smallEtaleDerivedModulePullbackCompIso B S hS v b₀).app
      ((derivedModulePushforward B S hS f).obj ω))
    ((smallEtaleDerivedModulePullback B S hS v).map
      (smallEtaleDerivedModuleBaseChangeMap B S hS f b₀ f₀ a₀ sq₀.w ω))
    ((smallEtaleDerivedModulePullback B S hS v).map
      ((derivedModulePushforward B S hS f₀).map ε.hom))
    ((smallEtaleDerivedModulePullback B S hS v).map P₀.τ)
    ((smallEtaleDerivedModulePullback B S hS v).mapIso
      (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) b₀))
    ((smallEtaleDerivedModulePullbackCompIso B S hS v b₀).app
      (derivedStructureSheaf B S hS Y.1 Y.2).obj)
    (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) v)
    (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) (v ≫ b₀))
    (smallEtaleDerivedModuleBaseChangeMap B S hS f (v ≫ b₀) f₁ (u ≫ a₀) sq₁.w ω)
    ((derivedModulePushforward B S hS f₁).mapIso
      ((smallEtaleDerivedModulePullbackCompIso B S hS u a₀).app ω))
    (smallEtaleDerivedModuleBaseChangeMap B S hS f₀ v f₁ u sq'.w
      ((smallEtaleDerivedModulePullback B S hS a₀).obj ω))
    ((derivedModulePushforward B S hS f₁).map
      ((smallEtaleDerivedModulePullback B S hS u).map ε.hom))
    (@asIso _ _ _ _ (smallEtaleDerivedModuleBaseChangeMap B S hS f₀ v f₁ u sq'.w P₀.ω)
      (P₀.isIso_smallEtaleDerivedBaseChangeMap sq'))
    (smallEtaleDerivedBaseChangeMap_horizontal B S hS f f₀ f₁ a₀ u b₀ v sq₀.w sq'.w ω)
    (smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f₀ v f₁ u sq'.w ε.hom)
    (smallEtaleDerivedModulePullbackCompIso_hom_app_unit_comp v b₀)
  have e₁ : (smallEtaleDerivedModulePullback B S hS v).map
        (smallEtaleDerivedModuleBaseChangeMap B S hS f b₀ f₀ a₀ sq₀.w ω ≫
          (derivedModulePushforward B S hS f₀).map ε.hom ≫ P₀.τ ≫
          (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) b₀).inv) =
      (smallEtaleDerivedModulePullback B S hS v).map
          (smallEtaleDerivedModuleBaseChangeMap B S hS f b₀ f₀ a₀ sq₀.w ω) ≫
        (smallEtaleDerivedModulePullback B S hS v).map
          ((derivedModulePushforward B S hS f₀).map ε.hom) ≫
        (smallEtaleDerivedModulePullback B S hS v).map P₀.τ ≫
        (smallEtaleDerivedModulePullback B S hS v).map
          (smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) b₀).inv :=
    (Functor.map_comp _ _ _).trans (congrArg _ ((Functor.map_comp _ _ _).trans
      (congrArg _ (Functor.map_comp _ _ _))))
  have e₂ : (derivedModulePushforward B S hS f₁).map
        ((smallEtaleDerivedModulePullbackCompIso B S hS u a₀).inv.app ω ≫
          (smallEtaleDerivedModulePullback B S hS u).map ε.hom) =
      (derivedModulePushforward B S hS f₁).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS u a₀).inv.app ω) ≫
        (derivedModulePushforward B S hS f₁).map
          ((smallEtaleDerivedModulePullback B S hS u).map ε.hom) :=
    Functor.map_comp _ _ _
  simp only [smallEtaleDerivedModulePullbackCongr, eqToIso_refl, Iso.trans_refl]
  rw [e₁, e₂]
  exact key

end AlgebraicGeometry.Space

end
