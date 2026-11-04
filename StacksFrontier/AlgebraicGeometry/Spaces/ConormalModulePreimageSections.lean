module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleRangeSections

/-!
# The sections `1 ⊗ a` of the conormal module of `g⁻¹(Z) ⊆ W`

For a flat morphism `g : W ⟶ T'` to an affine object of the site and a closed subspace `Z` of
`T'` with ideal `I ⊆ R' = Γ(T', 𝒪_{T'})`, the conormal module of `g⁻¹(Z) ⊆ W` is
`𝒪_{g⁻¹(Z)} ⊗_{R'} I` (`AlgebraicGeometry.Space.conormalModulePreimageIso`). This file computes
that identification on the sections `1 ⊗ a`: they are the classes of the sections `g^♯a` of the
ideal of `g⁻¹(Z)`. It is a step of the identification, in the body of the proof of
[Stacks Project, Tag 0D3X], of the map `φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` with the canonical map
of [Stacks Project, Tag 0D3F].

## Main results

* `AlgebraicGeometry.Space.baseRingTensorSection_comp_pullbackCompIso_inv`: `1 ⊗ m` along
  `i^*(𝒪_W ⊗_R M) ≅ 𝒪_Z ⊗_R M`.
* `AlgebraicGeometry.Space.baseRingTensorSection_conormalModulePreimageIso_inv`.
* `AlgebraicGeometry.Space.baseRingTensorSection_conormalModulePreimageRangeIso_inv`,
  `AlgebraicGeometry.Space.baseRingTensorSection_conormalModulePreimageSquareZeroIso_inv`: the same
  for `𝒪_{g⁻¹(T)} ⊗_{R₁} N` and `𝒪_{g⁻¹(T)} ⊗_{R₁} I`, `T ⟶ T'` a closed immersion.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory

/-- **A section read through the inverse of `F' ⋙ H ≅ F''`**, the composite of
`F ⋙ G ≅ F'` (whiskered by `H`), `G ⋙ H ≅ G'` and `F ⋙ G' ≅ F''`, computed one isomorphism at
a time. Stated for abstract functors so that it is checked without unfolding concrete ones. -/
theorem comp_isoWhiskerRight_trans_inv_app_eq {𝒜 𝒞 𝒟 ℰ : Type*} [Category 𝒜] [Category 𝒞]
    [Category 𝒟] [Category ℰ] {F : 𝒜 ⥤ 𝒞} {G : 𝒞 ⥤ 𝒟} {H : 𝒟 ⥤ ℰ} {F' : 𝒜 ⥤ 𝒟}
    {G' : 𝒞 ⥤ ℰ} {F'' : 𝒜 ⥤ ℰ} (b : F ⋙ G ≅ F') (c : G ⋙ H ≅ G') (d : F ⋙ G' ≅ F'') (M : 𝒜)
    {U : ℰ} (σ : U ⟶ F''.obj M) (x : U ⟶ G'.obj (F.obj M)) (y : U ⟶ H.obj (G.obj (F.obj M)))
    (z : U ⟶ H.obj (F'.obj M)) (h₁ : σ ≫ d.inv.app M = x) (h₂ : x ≫ c.inv.app (F.obj M) = y)
    (h₃ : y ≫ H.map (b.hom.app M) = z) (e : F' ⋙ H ≅ F'')
    (he : e = Functor.isoWhiskerRight b.symm H ≪≫ Functor.associator F G H ≪≫
        Functor.isoWhiskerLeft F c ≪≫ d) :
    σ ≫ e.inv.app M = z := by
  subst h₁ h₂ h₃ he
  simp

/-- **A section read through the inverse of `H(B) ≅ H(F'(N)) ≅ L(N)`**, the first isomorphism
the image under `H` of the inverse of `D : F'(N) ≅ B`, the second a component of
`c : F' ⋙ H ≅ L`. Stated for abstract functors so that it is checked without unfolding concrete
ones. -/
theorem comp_mapIso_symm_trans_app_inv_eq {𝒜 𝒟 ℰ : Type*} [Category 𝒜] [Category 𝒟]
    [Category ℰ] {F' : 𝒜 ⥤ 𝒟} {H : 𝒟 ⥤ ℰ} {L : 𝒜 ⥤ ℰ} (N : 𝒜) {B : 𝒟} (D : F'.obj N ≅ B)
    (c : F' ⋙ H ≅ L) {U : ℰ} (σ : U ⟶ L.obj N) (y : U ⟶ H.obj (F'.obj N)) (z : U ⟶ H.obj B)
    (h₁ : σ ≫ c.inv.app N = y) (h₂ : y ≫ H.map D.hom = z) (e : H.obj B ≅ L.obj N)
    (he : e = H.mapIso D.symm ≪≫ c.app N) :
    σ ≫ e.inv = z := by
  subst h₁ h₂ he
  simp

/-- **A section read through the inverse of `C ≅ G_{φ₀}(I) ≅ G_{φ₀}(F(N)) = G_φ(F(N)) ≅ G₁(N)`**
for a family of functors `G_φ` and an equality `φ₀ = φ`, the second isomorphism the image of
the inverse of `e₂ : F(N) ≅ I` and the last a component of `e₄ : F ⋙ G_φ ≅ G₁`, computed one
isomorphism at a time. Stated for an abstract family of functors, with the sections `y φ` given as
a family, so that the transport along `φ₀ = φ` is checked without unfolding concrete functors. -/
theorem comp_trans_mapIso_symm_trans_eqToIso_trans_app_inv_eq {𝒜 𝒜' ℰ Φ : Type*} [Category 𝒜]
    [Category 𝒜'] [Category ℰ] (G : Φ → 𝒜' ⥤ ℰ) {φ₀ φ : Φ} (hφ : φ₀ = φ) {F : 𝒜 ⥤ 𝒜'}
    {G₁ : 𝒜 ⥤ ℰ} {N : 𝒜} {I : 𝒜'} {C : ℰ} (e₁ : C ≅ (G φ₀).obj I) (e₂ : F.obj N ≅ I)
    (e₄ : F ⋙ G φ ≅ G₁) {U : ℰ} (σ : U ⟶ G₁.obj N) (y : ∀ φ, U ⟶ (G φ).obj (F.obj N))
    (w : U ⟶ (G φ₀).obj I) (z : U ⟶ C)
    (h₁ : y φ ≫ e₄.hom.app N = σ) (h₃ : y φ₀ ≫ (G φ₀).map e₂.hom = w)
    (h₄ : w ≫ e₁.inv = z) (e : C ≅ G₁.obj N)
    (he : e = e₁ ≪≫ (G φ₀).mapIso e₂.symm ≪≫
      eqToIso (congrArg (fun φ => (G φ).obj (F.obj N)) hφ) ≪≫ e₄.app N) :
    σ ≫ e.inv = z := by
  subst hφ h₁ h₃ h₄ he
  simp

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Pullback

variable {Z W : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS} (i : Z ⟶ W)
  (g : W ⟶ schemeSpace T)

/-- **The section `1 ⊗ m` of `𝒪_Z ⊗_R M`, read on `i^*(𝒪_W ⊗_R M)`, is the pullback of the
section `1 ⊗ m` of `𝒪_W ⊗_R M`.** -/
theorem baseRingTensorSection_comp_pullbackCompIso_inv (M : ModuleCat.{u} (baseRing B S hS T))
    (m : M) :
    baseRingTensorSection B S hS Z (baseRingHomOfMap (i ≫ g)) M m ≫
        (baseRingTensorModulePullbackCompIso B S hS i g).inv.app M =
      modulePullbackGlobalSection B S hS i
        (baseRingTensorSection B S hS W (baseRingHomOfMap g) M m) := by
  have h₃ : modulePullbackGlobalSection B S hS i (modulePullbackGlobalSection B S hS g
        (baseRingTensorSection B S hS (schemeSpace T) (baseRingHomOfMap (𝟙 (schemeSpace T)))
          M m)) ≫
        (modulePullback B S hS i).map ((baseRingTensorModulePullbackIso B S hS g).hom.app M) =
      modulePullbackGlobalSection B S hS i
        (baseRingTensorSection B S hS W (baseRingHomOfMap g) M m) :=
    (modulePullbackGlobalSection_comp B S hS i _ _).symm.trans
      (congrArg (modulePullbackGlobalSection B S hS i)
        (modulePullbackGlobalSection_baseRingTensorSection B S hS g M m))
  exact CategoryTheory.comp_isoWhiskerRight_trans_inv_app_eq
    (baseRingTensorModulePullbackIso B S hS g) (modulePullbackCompIso B S hS i g)
    (baseRingTensorModulePullbackIso B S hS (i ≫ g)) M _ _ _ _
    (baseRingTensorSection_comp_pullbackIso_inv B S hS (i ≫ g) M m)
    (modulePullbackGlobalSection_comp_modulePullbackCompIso_inv B S hS i g _) h₃
    (baseRingTensorModulePullbackCompIso B S hS i g)
    (baseRingTensorModulePullbackCompIso.eq_1 B S hS i g)

end Pullback

section Conormal

variable {W : AlgebraicSpaces B S hS} {T' : BigFppfOver B S hS} (g : W ⟶ schemeSpace T')
  (Z : ClosedSubspaces B S hS (schemeSpace T').1)

/-- **The section `1 ⊗ a` of `𝒪_{g⁻¹(Z)} ⊗_{R'} I` is the class of `g^♯a`** in the conormal
module of `g⁻¹(Z) ⊆ W`: through `AlgebraicGeometry.Space.conormalModulePreimageIso` it is the
pullback to `g⁻¹(Z)` of the section `g^♯a` of the ideal of `g⁻¹(Z)`. -/
theorem baseRingTensorSection_conormalModulePreimageIso_inv (hg : IsFlat B S hS g.hom)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (a : closedSubspaceBaseIdeal B S hS Z) :
    baseRingTensorSection B S hS _
        (baseRingHomOfMap (subspaceInclusion B S hS W (preimageSubspace B S hS g Z) ≫ g))
        (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS Z)) a ≫
        (conormalModulePreimageIso B S hS g Z hg hT').inv =
      modulePullbackGlobalSection B S hS
        (subspaceInclusion B S hS W (preimageSubspace B S hS g Z))
        (preimageIdealSection B S hS g Z a) := by
  have h₁ := baseRingTensorSection_comp_pullbackCompIso_inv B S hS
    (subspaceInclusion B S hS W (preimageSubspace B S hS g Z)) g
    (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS Z)) a
  have h₂ : baseRingTensorSection B S hS W (baseRingHomOfMap g)
        (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS Z)) a ≫
        (definingIdealSheafPreimageIso B S hS g Z hg hT').hom =
      preimageIdealSection B S hS g Z a :=
    (congrArg (_ ≫ ·) (definingIdealSheafPreimageIso_hom B S hS g Z hg hT')).trans
      (baseRingTensorSection_baseRingTensorPreimageIdealHom B S hS g Z a)
  exact CategoryTheory.comp_mapIso_symm_trans_app_inv_eq
    (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS Z))
    (definingIdealSheafPreimageIso B S hS g Z hg hT')
    (baseRingTensorModulePullbackCompIso B S hS
      (subspaceInclusion B S hS W (preimageSubspace B S hS g Z)) g) _ _ _ h₁
    ((modulePullbackGlobalSection_comp B S hS _ _ _).symm.trans
      (congrArg (modulePullbackGlobalSection B S hS
        (subspaceInclusion B S hS W (preimageSubspace B S hS g Z))) h₂))
    (conormalModulePreimageIso B S hS g Z hg hT') (conormalModulePreimageIso.eq_1 B S hS g Z hg hT')

/-- **The section `1 ⊗ n` of `𝒪_{g⁻¹(Z)} ⊗_{R₁} N` is the class of `g^♯(e(n))`**, through any
isomorphism `E` equal to the composite of `AlgebraicGeometry.Space.conormalModulePreimageIso`, the
image of `e⁻¹ : I ≅ ψ^*N`, the transport along `φ₀ = φ₁ ∘ ψ` and
`AlgebraicGeometry.Space.baseRingTensorModuleRestrictScalarsIso`, for a surjection
`ψ : R' ⟶ R₁` and an `R₁`-module `N` whose restriction to `R'` is the ideal `I` of `Z`. The ring
map `ψ` and the isomorphism `E` are variables, so that a concrete instance is checked through the
equation `hE` rather than by unfolding. -/
theorem baseRingTensorSection_comp_inv_of_eq_conormalModulePreimageIso_trans
    (hg : IsFlat B S hS g.hom) (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {R₁ : Type u} [CommRing R₁] (ψ : baseRing B S hS T' →+* R₁) (hψ : Function.Surjective ψ)
    (φ₁ : R₁ →+* modelGlobalFunctions B S hS
      ⟨(preimageSubspace B S hS g Z).1.toFunctor, (preimageSubspace B S hS g Z).2.1⟩)
    (hdat : baseRingHomOfMap (subspaceInclusion B S hS W (preimageSubspace B S hS g Z) ≫ g) =
      φ₁.comp ψ)
    (N : ModuleCat.{u} R₁)
    (e : (ModuleCat.restrictScalars.{u} ψ).obj N ≅
      ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS Z)) (n : N)
    (E : conormalModule B S hS W (preimageSubspace B S hS g Z) ≅
      (baseRingTensorModule B S hS _ φ₁).obj N)
    (hE : E = conormalModulePreimageIso B S hS g _ hg hT' ≪≫
      (baseRingTensorModule B S hS _ _).mapIso e.symm ≪≫
      eqToIso (congrArg (fun φ => (baseRingTensorModule B S hS _ φ).obj
        ((ModuleCat.restrictScalars.{u} ψ).obj N)) hdat) ≪≫
      (baseRingTensorModuleRestrictScalarsIso B S hS _ ψ φ₁ hψ).app N) :
    baseRingTensorSection B S hS _ φ₁ N n ≫ E.inv =
      modulePullbackGlobalSection B S hS
        (subspaceInclusion B S hS W (preimageSubspace B S hS g Z))
        (preimageIdealSection B S hS g Z (e.hom.hom n)) :=
  CategoryTheory.comp_trans_mapIso_symm_trans_eqToIso_trans_app_inv_eq
    (fun φ => baseRingTensorModule B S hS _ φ) hdat
    (conormalModulePreimageIso B S hS g Z hg hT') e
    (baseRingTensorModuleRestrictScalarsIso B S hS _ ψ φ₁ hψ)
    (baseRingTensorSection B S hS _ φ₁ N n)
    (fun φ => baseRingTensorSection B S hS _ φ ((ModuleCat.restrictScalars.{u} ψ).obj N) n)
    (baseRingTensorSection B S hS _
      (baseRingHomOfMap (subspaceInclusion B S hS W (preimageSubspace B S hS g Z) ≫ g))
      (ModuleCat.of (baseRing B S hS T') (closedSubspaceBaseIdeal B S hS Z)) (e.hom.hom n))
    _ (baseRingTensorSection_restrictScalarsIso_hom B S hS _ φ₁ hψ N n)
    (baseRingTensorSection_map B S hS _ _ e.hom n)
    (baseRingTensorSection_conormalModulePreimageIso_inv B S hS g Z hg hT' (e.hom.hom n)) E hE

variable {T : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))

/-- **The section `1 ⊗ n` of `𝒪_{g⁻¹(T)} ⊗_{R₁} N` is the class of `g^♯(e(n))`** in the conormal
module of `g⁻¹(T) ⊆ W`, through `AlgebraicGeometry.Space.conormalModulePreimageRangeIso`, where
`e` identifies `N`, read as an `R'`-module, with the ideal of `T` in `R'`. -/
theorem baseRingTensorSection_conormalModulePreimageRangeIso_inv (hg : IsFlat B S hS g.hom)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (N : ModuleCat.{u} (baseRing B S hS T))
    (e : (ModuleCat.restrictScalars.{u}
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).obj N ≅
      ModuleCat.of (baseRing B S hS T')
        (closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj))) (n : N) :
    baseRingTensorSection B S hS _ (baseRingHomOfMap (preimageRangeProjection B S hS g j hj)) N n ≫
        (conormalModulePreimageRangeIso B S hS g j hj hg hT' N e).inv =
      modulePullbackGlobalSection B S hS
        (subspaceInclusion B S hS W (preimageSubspace B S hS g (rangeSubspace B S hS j hj)))
        (preimageIdealSection B S hS g (rangeSubspace B S hS j hj) (e.hom.hom n)) :=
  baseRingTensorSection_comp_inv_of_eq_conormalModulePreimageIso_trans B S hS g _ hg hT' _
    (have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := hT'
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map j)).2)
    _ (by rw [← preimageRangeProjection_comp]; exact baseRingHomOfMap_comp B S hS _ j) N e n
    (conormalModulePreimageRangeIso B S hS g j hj hg hT' N e) rfl

/-- The transport of an element along an equality of ideals is the same element of the ring. -/
theorem coe_eqToIso_hom_moduleOf_ideal {R : Type u} [CommRing R] {I I' : Ideal R} (h : I = I')
    (x : I) :
    ((eqToIso (congrArg (fun I : Ideal R => ModuleCat.of R I) h)).hom.hom x : R) = x := by
  subst h
  rfl

/-- **The section `1 ⊗ a` of `𝒪_{g⁻¹(T)} ⊗_{R₁} I` is the class of `g^♯a`** in the conormal
module of `g⁻¹(T) ⊆ W`, through `AlgebraicGeometry.Space.conormalModulePreimageSquareZeroIso`, for
`a` in the square-zero ideal `I = Ker(Γ(T', 𝒪) → Γ(T, 𝒪))` read as a `Γ(T, 𝒪)`-module. -/
theorem baseRingTensorSection_conormalModulePreimageSquareZeroIso_inv (hg : IsFlat B S hS g.hom)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (hsq : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom ^ 2 = ⊥)
    (a : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom) :
    baseRingTensorSection B S hS _ (baseRingHomOfMap (preimageRangeProjection B S hS g j hj))
        (RingHom.squareZeroKer _
          (haveI := hT'
          (IsClosedImmersion.isAffine_surjective_of_isAffine
            ((BigFppfOver.toScheme B S hS).map j)).2) hsq) a ≫
        (conormalModulePreimageSquareZeroIso B S hS g j hj hg hT' hsq).inv =
      modulePullbackGlobalSection B S hS
        (subspaceInclusion B S hS W (preimageSubspace B S hS g (rangeSubspace B S hS j hj)))
        (preimageIdealSection B S hS g (rangeSubspace B S hS j hj)
          ⟨a.1, (closedSubspaceBaseIdeal_rangeSubspace B S hS j hj).symm ▸ a.2⟩) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T') := hT'
  have hψ : Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine ((BigFppfOver.toScheme B S hS).map j)).2
  let e := RingHom.restrictScalarsSquareZeroKerIso _ hψ hsq ≪≫
    eqToIso (congrArg (fun I : Ideal (baseRing B S hS T') => ModuleCat.of _ I)
      (closedSubspaceBaseIdeal_rangeSubspace B S hS j hj).symm)
  have hE : conormalModulePreimageSquareZeroIso B S hS g j hj hg hT' hsq =
      conormalModulePreimageRangeIso B S hS g j hj hg hT' (RingHom.squareZeroKer _ hψ hsq) e :=
    rfl
  rw [hE]
  refine (baseRingTensorSection_conormalModulePreimageRangeIso_inv B S hS g j hj hg hT'
    (RingHom.squareZeroKer _ hψ hsq) e a).trans ?_
  exact congrArg (fun x => modulePullbackGlobalSection B S hS
      (subspaceInclusion B S hS W (preimageSubspace B S hS g (rangeSubspace B S hS j hj)))
      (preimageIdealSection B S hS g (rangeSubspace B S hS j hj) x))
    (Subtype.ext (coe_eqToIso_hom_moduleOf_ideal
      (closedSubspaceBaseIdeal_rangeSubspace B S hS j hj).symm _))

end Conormal

end AlgebraicGeometry.Space

end
