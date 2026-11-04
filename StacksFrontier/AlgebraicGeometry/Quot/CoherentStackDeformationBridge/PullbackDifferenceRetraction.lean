module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackDifference
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare

/-!
# The kernel and quotient squares of the pullback unit, read through the retractions

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` and `h₂ : T ⟶ T'₂` split
first order thickenings with retractions `r`, `r₂`, and `g : T'₂ ⟶ T'` under `T` with
`r₂ = g ≫ r`. The unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` maps the extension attached to a lift to the
direct image of the one attached to its pullback
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_f_comp_pullbackUnit`,
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_g_comp_pullbackQuotientMap`).
This file records two ingredients of reading that map on `X_T` through the retractions:

* on the kernels, an abstract form of the chase: a map of square-zero ideals which, through
  identifications `Kₖ : Iₖ ≅ ιₖ Nₖ`, is `ι₁ λ` followed by `Ψ₀ ∘ ι₂ ≅ ι₁`, is `λ` on `X_T`
  (`AlgebraicGeometry.Space.CoherentSituation.retraction_map_comp_eq_of_comp_eq`);
* on the quotients, the associativity coherence of Stacks 03LU with `a_*M` written as restriction
  of scalars of the direct image to the thickened presentation, the spelling of the extensions
  attached to lifts
  (`AlgebraicGeometry.Space.thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso`).

## Implementation notes

The coherence of Stacks 03LU is stated by its source at `a_*M`; the extensions attached to lifts
are written at the restriction of scalars of `i_*M`. Comparing the component of
`c_*b_* ≅ (b ≫ c)_* ≅ c₂_*` (with its `eqToIso`) at the two spellings by unfolding costs
50 to 150 s of kernel time; here the `eqToIso` is removed first, at `c₂ = b ≫ c`, by
`AlgebraicGeometry.Space.CoherentSituation.trans_eqToIso_hom_app_of_eq_self` with an explicit
motive, the two spellings are then compared without it (cheap), and `c₂` is generalized by `subst`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe vX uX vY₁ uY₁ vY₂ uY₂ w u vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

namespace AlgebraicGeometry.Space.CoherentSituation

/-- An isomorphism followed by `eqToIso` of a self-equality has the same components. -/
theorem trans_eqToIso_hom_app_of_eq_self {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {F G : 𝒞 ⥤ 𝒟}
    (α : F ≅ G) (h : G = G) (X : 𝒞) : (α ≪≫ eqToIso h).hom.app X = α.hom.app X := by
  simp

/-- **The kernel square read through the retractions, abstractly.** For functors
`R₁ : 𝒜₁ ⥤ ℳ₁`, `R₂ : 𝒜₂ ⥤ ℳ₂` (restriction of scalars), `Ψ : 𝒜₂ ⥤ 𝒜₁`, `G : ℳ₂ ⥤ ℳ₁`
(direct images along a morphism of the thickened topoi), `C₁ : ℳ₁ ⥤ ℳ₀`, `C₂ : ℳ₂ ⥤ ℳ₀`
(direct images along the retractions), `ι₁ : ℳ₀ ⥤ 𝒜₁`, `ι₂ : ℳ₀ ⥤ 𝒜₂` (direct images along the
thickenings), with a natural `ρ : G R₂ ≅ R₁ Ψ`, `κ : C₁ G ≅ C₂`, `E : Ψ ι₂ ≅ ι₁` and
`rₖ : Cₖ Rₖ ιₖ ≅ 𝟭` satisfying the associativity coherence `hcoh` (stated for a map `q` given by
its value `hq`, so that `q` can be supplied in the spelling of its source): a map
`X₁ ≫ X₂ : I₁ ⟶ Ψ I₂`
which, through isomorphisms `Kₖ : Iₖ ≅ ιₖ Nₖ`, is `ι₁ λ` followed by `E⁻¹` (`hkey`), is read
through `C₁`, `ρ` and `κ` as `λ`, through `rₖ` and `Kₖ`. -/
theorem retraction_map_comp_eq_of_comp_eq {𝒜₁ 𝒜₂ ℳ₀ ℳ₁ ℳ₂ : Type*} [Category 𝒜₁]
    [Category 𝒜₂] [Category ℳ₀] [Category ℳ₁] [Category ℳ₂]
    (R₁ : 𝒜₁ ⥤ ℳ₁) (R₂ : 𝒜₂ ⥤ ℳ₂) (Ψ : 𝒜₂ ⥤ 𝒜₁) (G : ℳ₂ ⥤ ℳ₁) (C₁ : ℳ₁ ⥤ ℳ₀)
    (C₂ : ℳ₂ ⥤ ℳ₀) (ι₁ : ℳ₀ ⥤ 𝒜₁) (ι₂ : ℳ₀ ⥤ 𝒜₂)
    (ρ : ∀ M : 𝒜₂, G.obj (R₂.obj M) ≅ R₁.obj (Ψ.obj M))
    (hρ : ∀ {M N : 𝒜₂} (ψ : M ⟶ N),
      G.map (R₂.map ψ) ≫ (ρ N).hom = (ρ M).hom ≫ R₁.map (Ψ.map ψ))
    (κ : G ⋙ C₁ ≅ C₂) (E : ι₂ ⋙ Ψ ≅ ι₁)
    (r₁ : ι₁ ⋙ R₁ ⋙ C₁ ≅ 𝟭 ℳ₀) (r₂ : ι₂ ⋙ R₂ ⋙ C₂ ≅ 𝟭 ℳ₀)
    (q : ∀ M : ℳ₀, C₁.obj (R₁.obj (ι₁.obj M)) ⟶ C₂.obj (R₂.obj (ι₂.obj M)))
    (hq : ∀ M : ℳ₀, C₁.map (R₁.map (E.inv.app M) ≫ (ρ (ι₂.obj M)).inv) ≫
      κ.hom.app (R₂.obj (ι₂.obj M)) = q M)
    (hcoh : ∀ M : ℳ₀, q M ≫ r₂.hom.app M = r₁.hom.app M)
    {I₁ : 𝒜₁} {I₂ : 𝒜₂} {J : 𝒜₁} (X₁ : I₁ ⟶ J) (X₂ : J ⟶ Ψ.obj I₂) {N₁ N₂ : ℳ₀}
    (K₁ : I₁ ≅ ι₁.obj N₁) (K₂ : I₂ ≅ ι₂.obj N₂) (lam : N₁ ⟶ N₂)
    (hkey : K₁.hom ≫ ι₁.map lam = X₁ ≫ X₂ ≫ Ψ.map K₂.hom ≫ E.hom.app N₂)
    {N₁' N₂' : ℳ₀} (l₁ : N₁ ⟶ N₁') (l₂ : N₁' ⟶ N₂') (l₃ : N₂' ⟶ N₂)
    (hlam : lam = l₁ ≫ l₂ ≫ l₃) :
    C₁.map (R₁.map (X₁ ≫ X₂) ≫ (ρ I₂).inv) ≫ κ.hom.app (R₂.obj I₂) =
      (C₁.map (R₁.map K₁.hom) ≫ r₁.hom.app N₁ ≫ l₁) ≫ l₂ ≫
        ((l₃ ≫ r₂.inv.app N₂) ≫ C₂.map (R₂.map K₂.inv)) := by
  have hX : X₁ ≫ X₂ = K₁.hom ≫ ι₁.map lam ≫ E.inv.app N₂ ≫ Ψ.map K₂.inv := by
    rw [reassoc_of% hkey]
    simp
  have hρ' : R₁.map (Ψ.map K₂.inv) ≫ (ρ I₂).inv =
      (ρ (ι₂.obj N₂)).inv ≫ G.map (R₂.map K₂.inv) := by
    rw [Iso.comp_inv_eq, Category.assoc, hρ, Iso.inv_hom_id_assoc]
  have hmid : R₁.map (X₁ ≫ X₂) ≫ (ρ I₂).inv = R₁.map (K₁.hom ≫ ι₁.map lam) ≫
      (R₁.map (E.inv.app N₂) ≫ (ρ (ι₂.obj N₂)).inv) ≫ G.map (R₂.map K₂.inv) := by
    rw [hX]
    simp only [Functor.map_comp, Category.assoc]
    rw [hρ']
  have hκ : C₁.map (G.map (R₂.map K₂.inv)) ≫ κ.hom.app (R₂.obj I₂) =
      κ.hom.app (R₂.obj (ι₂.obj N₂)) ≫ C₂.map (R₂.map K₂.inv) :=
    κ.hom.naturality (R₂.map K₂.inv)
  have hr₁ : C₁.map (R₁.map (ι₁.map lam)) ≫ r₁.hom.app N₂ = r₁.hom.app N₁ ≫ lam :=
    r₁.hom.naturality lam
  have hc : C₁.map (R₁.map (E.inv.app N₂) ≫ (ρ (ι₂.obj N₂)).inv) ≫
      κ.hom.app (R₂.obj (ι₂.obj N₂)) = r₁.hom.app N₂ ≫ r₂.inv.app N₂ := by
    rw [hq, ← hcoh N₂]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id (q N₂)).symm
  calc _ = C₁.map (R₁.map (K₁.hom ≫ ι₁.map lam)) ≫ (C₁.map (R₁.map (E.inv.app N₂) ≫
          (ρ (ι₂.obj N₂)).inv) ≫ κ.hom.app (R₂.obj (ι₂.obj N₂))) ≫ C₂.map (R₂.map K₂.inv) := by
        rw [hmid, C₁.map_comp, C₁.map_comp, Category.assoc, Category.assoc, hκ]
        simp only [Category.assoc]
    _ = (C₁.map (R₁.map K₁.hom) ≫ C₁.map (R₁.map (ι₁.map lam)) ≫ r₁.hom.app N₂) ≫
          r₂.inv.app N₂ ≫ C₂.map (R₂.map K₂.inv) := by
        rw [hc, R₁.map_comp, C₁.map_comp]
        simp only [Category.assoc]
    _ = _ := by
        rw [hr₁, hlam]
        simp only [Category.assoc]

end AlgebraicGeometry.Space.CoherentSituation

namespace Deformation.ToposThickening.ThickeningTargetMorphism

open AlgebraicGeometry (RingedTopos RingedToposHom)

variable {X : RingedTopos.{vX, uX, w}} {Y₁ : RingedTopos.{vY₁, uY₁, w}}
  {Y₂ : RingedTopos.{vY₂, uY₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)
  (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)
  (E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁)
  (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
    (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
  (hE : ∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))).map
        (E.hom.app M) =
      θ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))

/-- The kernel identification `I ⊗ i_*F ≅ i_*J ⊗ i_*F ≅ i_*(J ⊗ F)` of a thickening from an
identification `e : i_*J ≅ I` (Stacks 08MQ and the projection formula). -/
abbrev kernelThickenedIso {i : RingedToposHom X Y₁} (hi : FirstOrderThickening i)
    (F J : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (e : (thickenedModulesFunctor i).obj J ≅ hi.I) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
        ((thickenedModulesFunctor i).obj F)).obj hi.I ≅
      (thickenedModulesFunctor i).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
      ((thickenedModulesFunctor i).obj F)).mapIso e).symm ≪≫ pushforwardModuleTensorIso hi F J

include hE in
/-- **The kernel square of a morphism of extensions along a morphism of thickenings, read
through retractions**
(`AlgebraicGeometry.Space.CoherentSituation.retraction_map_comp_eq_of_comp_eq` with the
compatibility of the actions `ThickeningTargetMorphism.hkey_of_idealMap`): for direct images
`C₁`, `C₂` to `X` with `j_* ⋙ C₁ ≅ C₂` and `Cₖ ∘ iₖ_* ≅ 𝟭` satisfying the associativity
coherence, and a map `λ : J₁ ⟶ J₂` compatible with the map of square-zero ideals under
`eₖ : iₖ_*Jₖ ≅ Iₖ`, the comparison `I₁ ⊗ i₁_*F ⟶ Ψ₀(I₂ ⊗ i₂_*F)` read on `X` is `λ ⊗ F`. -/
theorem retraction_map_idealTensorMap_comp_eq_of_idealMap
    (C₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (C₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (κ : D.j.pushforwardModules ⋙ C₁ ≅ C₂)
    (r₁ : thickenedModulesFunctor i₁ ⋙ structureRestrict i₁ ⋙ C₁ ≅ 𝟭 _)
    (r₂ : thickenedModulesFunctor i₂ ⋙ structureRestrict i₂ ⋙ C₂ ≅ 𝟭 _)
    (hcoh : ∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      C₁.map ((structureRestrict i₁).map (E.inv.app M) ≫
          (D.restrictIso ((thickenedModulesFunctor i₂).obj M)).inv) ≫
        κ.hom.app ((structureRestrict i₂).obj ((thickenedModulesFunctor i₂).obj M)) ≫
          r₂.hom.app M = r₁.hom.app M)
    (F J₁ J₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (lam : J₁ ⟶ J₂)
    (e₁ : (thickenedModulesFunctor i₁).obj J₁ ≅ hi₁.I)
    (e₂ : (thickenedModulesFunctor i₂).obj J₂ ≅ hi₂.I)
    (H : e₁.inv ≫ (thickenedModulesFunctor i₁).map lam =
      D.idealMap hi₁ hi₂ ≫ D.basePushforward.map e₂.inv ≫ E.hom.app J₂)
    {N₁' N₂' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (l₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J₁ ⟶ N₁')
    (l₂ : N₁' ⟶ N₂') (l₃ : N₂' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J₂)
    (hlam : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam = l₁ ≫ l₂ ≫ l₃) :
    C₁.map ((structureRestrict i₁).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map (E.inv.app F) ≫
            D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F)) ≫
        (D.restrictIso (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj
          ((thickenedModulesFunctor i₂).obj F)).obj hi₂.I)).inv) ≫
      κ.hom.app ((structureRestrict i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj
          ((thickenedModulesFunctor i₂).obj F)).obj hi₂.I)) =
      (C₁.map ((structureRestrict i₁).map (kernelThickenedIso hi₁ F J₁ e₁).hom) ≫
          r₁.hom.app _ ≫ l₁) ≫ l₂ ≫
        ((l₃ ≫ r₂.inv.app _) ≫ C₂.map ((structureRestrict i₂).map
          (kernelThickenedIso hi₂ F J₂ e₂).inv)) :=
  AlgebraicGeometry.Space.CoherentSituation.retraction_map_comp_eq_of_comp_eq
    (structureRestrict i₁) (structureRestrict i₂) D.basePushforward D.j.pushforwardModules C₁ C₂
    (thickenedModulesFunctor i₁) (thickenedModulesFunctor i₂) D.restrictIso
    D.restrictIso_hom_naturality κ E r₁ r₂
    (fun M => C₁.map ((structureRestrict i₁).map (E.inv.app M) ≫
        (D.restrictIso ((thickenedModulesFunctor i₂).obj M)).inv) ≫
      κ.hom.app ((structureRestrict i₂).obj ((thickenedModulesFunctor i₂).obj M)))
    (fun _ => rfl) (fun M => (Category.assoc _ _ _).trans (hcoh M))
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map (E.inv.app F))
    (D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F))
    (kernelThickenedIso hi₁ F J₁ e₁) (kernelThickenedIso hi₂ F J₂ e₂)
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam)
    ((Category.assoc _ _ _).trans (D.hkey_of_idealMap hi₁ hi₂ E θ hE F J₁ J₂ lam e₁ e₂ H))
    l₁ l₂ l₃ hlam


section IdealSquare

variable [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}]
  {S₁ : RingedTopos.{vS, uS, wS}} {S'₁ : RingedTopos.{vS', uS', wS'}}
  [S₁.J.HasSheafCompose (forget RingCat.{wS})] [S'₁.J.HasSheafCompose (forget RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'₁.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'₁.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify S₁.J AddCommGrpCat.{wS}] [S₁.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  {S₂ : RingedTopos.{vT, uT, wT}} {S'₂ : RingedTopos.{vT', uT', wT'}}
  [S₂.J.HasSheafCompose (forget RingCat.{wT})] [S'₂.J.HasSheafCompose (forget RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [S'₂.J.HasSheafCompose (forget₂ CommRingCat.{wT'} RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget AddCommGrpCat.{wT})]
  [S'₂.J.HasSheafCompose (forget AddCommGrpCat.{wT'})]
  [HasWeakSheafify S₂.J AddCommGrpCat.{wT}] [S₂.J.WEqualsLocallyBijective AddCommGrpCat.{wT}]
  (t₁ : RingedToposHom S₁ S'₁) (f₁ : RingedToposHom X S₁) (f'₁ : RingedToposHom Y₁ S'₁)
  (ht₁ : FirstOrderThickening t₁) (comm₁ : f'₁.comp i₁ = t₁.comp f₁) (hf'₁ : f'₁.IsFlat)
  (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁
    comm₁).IsStrict)
  (t₂ : RingedToposHom S₂ S'₂) (f₂ : RingedToposHom X S₂) (f'₂ : RingedToposHom Y₂ S'₂)
  (ht₂ : FirstOrderThickening t₂) (comm₂ : f'₂.comp i₂ = t₂.comp f₂) (hf'₂ : f'₂.IsFlat)
  (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings i₂ t₂ f₂ f'₂ hi₂ ht₂
    comm₂).IsStrict)

include hE in
/-- `ThickeningTargetMorphism.retraction_map_idealTensorMap_comp_eq_of_idealMap` for the
identifications `f^*𝒥ₖ = Iₖ` of strict squares of Situation 08VV, from the ideal-square
compatibility of `λ` (`ThickeningTargetMorphism.IdealSquareCompatible`). -/
theorem retraction_map_idealTensorMap_comp_eq_of_idealSquareCompatible
    (C₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (C₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (κ : D.j.pushforwardModules ⋙ C₁ ≅ C₂)
    (r₁ : thickenedModulesFunctor i₁ ⋙ structureRestrict i₁ ⋙ C₁ ≅ 𝟭 _)
    (r₂ : thickenedModulesFunctor i₂ ⋙ structureRestrict i₂ ⋙ C₂ ≅ 𝟭 _)
    (hcoh : ∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      C₁.map ((structureRestrict i₁).map (E.inv.app M) ≫
          (D.restrictIso ((thickenedModulesFunctor i₂).obj M)).inv) ≫
        κ.hom.app ((structureRestrict i₂).obj ((thickenedModulesFunctor i₂).obj M)) ≫
          r₂.hom.app M = r₁.hom.app M)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (H : D.IdealSquareCompatible hi₁ hi₂ t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂
      hf'₂ hstrict₂ E lam)
    {N₁' N₂' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (l₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj
      (basePullbackIdeal t₁ f₁ ht₁) ⟶ N₁')
    (l₂ : N₁' ⟶ N₂')
    (l₃ : N₂' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj
      (basePullbackIdeal t₂ f₂ ht₂))
    (hlam : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam = l₁ ≫ l₂ ≫ l₃) :
    type_of% (D.retraction_map_idealTensorMap_comp_eq_of_idealMap hi₁ hi₂ E θ hE C₁ C₂ κ r₁ r₂
      hcoh F
      (basePullbackIdeal t₁ f₁ ht₁) (basePullbackIdeal t₂ f₂ ht₂) lam
      (basePullbackIdealIsoIdeal i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁ hf'₁ hstrict₁)
      (basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂ hf'₂ hstrict₂) H.eq l₁ l₂ l₃ hlam) :=
  D.retraction_map_idealTensorMap_comp_eq_of_idealMap hi₁ hi₂ E θ hE C₁ C₂ κ r₁ r₂ hcoh F
      (basePullbackIdeal t₁ f₁ ht₁) (basePullbackIdeal t₂ f₂ ht₂) lam
      (basePullbackIdealIsoIdeal i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁ hf'₁ hstrict₁)
      (basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂ hf'₂ hstrict₂) H.eq l₁ l₂ l₃ hlam

end IdealSquare

end Deformation.ToposThickening.ThickeningTargetMorphism

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

-- Local priority 10000: these searches through `smallEtaleRingedTopos` are slow otherwise.
attribute [local instance 10000] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS} (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₀)
  {k : X₀ ⟶ X₁} {c₂ : X₂ ⟶ X₀} (e₁ : a ≫ b = k) (e₂ : b ≫ c = c₂) (h₁ : k ≫ c = 𝟙 X₀)
  (h₂ : a ≫ c₂ = 𝟙 X₀)
  {S₁ : RingedTopos.{vS, uS, wS}} {S'₁ : RingedTopos.{vS', uS', wS'}}
  [S₁.J.HasSheafCompose (forget RingCat.{wS})] [S'₁.J.HasSheafCompose (forget RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'₁.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'₁.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify S₁.J AddCommGrpCat.{wS}] [S₁.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  {S₂ : RingedTopos.{vT, uT, wT}} {S'₂ : RingedTopos.{vT', uT', wT'}}
  [S₂.J.HasSheafCompose (forget RingCat.{wT})] [S'₂.J.HasSheafCompose (forget RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [S'₂.J.HasSheafCompose (forget₂ CommRingCat.{wT'} RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget AddCommGrpCat.{wT})]
  [S'₂.J.HasSheafCompose (forget AddCommGrpCat.{wT'})]
  [HasWeakSheafify S₂.J AddCommGrpCat.{wT}] [S₂.J.WEqualsLocallyBijective AddCommGrpCat.{wT}]
  (hi₁ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS k))
  (hi₂ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a))
  (t₁ : RingedToposHom S₁ S'₁) (f₁ : RingedToposHom (smallEtaleRingedTopos B S hS X₀) S₁)
  (f'₁ : RingedToposHom (smallEtaleRingedTopos B S hS X₁) S'₁)
  (ht₁ : FirstOrderThickening t₁)
  (comm₁ : f'₁.comp (smallEtaleRingedToposHom B S hS k) = t₁.comp f₁) (hf'₁ : f'₁.IsFlat)
  (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings (smallEtaleRingedToposHom B S hS k)
    t₁ f₁ f'₁ hi₁ ht₁ comm₁).IsStrict)
  (t₂ : RingedToposHom S₂ S'₂) (f₂ : RingedToposHom (smallEtaleRingedTopos B S hS X₀) S₂)
  (f'₂ : RingedToposHom (smallEtaleRingedTopos B S hS X₂) S'₂)
  (ht₂ : FirstOrderThickening t₂)
  (comm₂ : f'₂.comp (smallEtaleRingedToposHom B S hS a) = t₂.comp f₂) (hf'₂ : f'₂.IsFlat)
  (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings (smallEtaleRingedToposHom B S hS a)
    t₂ f₂ f'₂ hi₂ ht₂ comm₂).IsStrict)
  (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS X₀).O))

/-- **The kernel identification `f^*𝒥 ⊗ i_*F ≅ I ⊗ i_*F ≅ i_*(f^*𝒥 ⊗ F)`** of a thickening `k`
in a strict square of Situation 08VV (Stacks 08MQ and the projection formula). -/
abbrev smallEtaleKernelThickenedIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (baseRing (smallEtaleRingedToposHom B S hS k))).flip.obj
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj F)).obj hi₁.I ≅
      (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS X₀).O).flip.obj F).obj (basePullbackIdeal t₁ f₁ ht₁)) :=
  (basePullbackIdealTensorIso (smallEtaleRingedToposHom B S hS k) t₁ f₁ f'₁ hi₁ ht₁ comm₁ hf'₁
      hstrict₁ ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj F)).symm ≪≫
    pushforwardModuleTensorIso hi₁ F (basePullbackIdeal t₁ f₁ ht₁)

/-- `c_* k_* ≅ 𝟭` for `k ≫ c = 𝟙`
(`AlgebraicGeometry.Space.CoherentSituation.pushforwardModulesRetractionIso`), with `k_*` written
as the direct image to the thickened presentation followed by restriction of scalars, the spelling
of `AlgebraicGeometry.Space.CoherentSituation.thickenedRetractionIso`. -/
abbrev thickenedPushforwardRetractionIso (k : X₀ ⟶ X₁) (c : X₁ ⟶ X₀) (h : k ≫ c = 𝟙 X₀) :
    thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k) ⋙
      structureRestrict (smallEtaleRingedToposHom B S hS k) ⋙
        (smallEtaleRingedToposHom B S hS c).pushforwardModules ≅ 𝟭 _ :=
  CoherentSituation.pushforwardModulesRetractionIso k c h

/-- Composing around the component of `α ≪≫ eqToIso h` for `h : G = G` is the same as around the
component of `α`. -/
private theorem comp_trans_eqToIso_hom_app_comp_of_eq_self {𝒞 𝒟 : Type*} [Category 𝒞]
    [Category 𝒟] {F G : 𝒞 ⥤ 𝒟} (α : F ≅ G) (h : G = G) (X : 𝒞) {A Z : 𝒟} (f : A ⟶ F.obj X)
    (w : G.obj X ⟶ Z) : f ≫ (α ≪≫ eqToIso h).hom.app X ≫ w = f ≫ α.hom.app X ≫ w := by
  rw [CoherentSituation.trans_eqToIso_hom_app_of_eq_self]

include h₁ in
/-- `AlgebraicGeometry.Space.pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso` for
`c₂ = b ≫ c`. -/
theorem pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso_comp_rfl
    (h₂' : a ≫ (b ≫ c) = 𝟙 X₀) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) (rfl : b ≫ c = b ≫ c))).hom.app
        ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
      (CoherentSituation.pushforwardModulesRetractionIso a (b ≫ c) h₂').hom.app M =
    (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M :=
  pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso a b c e₁ rfl h₁ h₂' M

include h₁ in
/-- `AlgebraicGeometry.Space.pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso` for
`c₂ = b ≫ c`, with the comparison `c_*b_* ≅ (b ≫ c)_*` itself. -/
theorem pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso_comp
    (h₂' : a ≫ (b ≫ c) = 𝟙 X₀) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (pushforwardModulesCompAt B S hS b c).hom.app
        ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
      (CoherentSituation.pushforwardModulesRetractionIso a (b ≫ c) h₂').hom.app M =
    (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M :=
  (comp_trans_eqToIso_hom_app_comp_of_eq_self (pushforwardModulesCompAt B S hS b c) _ _ _
    _).symm.trans
    (pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso_comp_rfl a b c e₁ h₁ h₂' M)

include h₁ in
/-- `AlgebraicGeometry.Space.pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso_comp`
with `a_*M` written as restriction of scalars of the direct image to the thickened presentation
and the identifications `AlgebraicGeometry.Space.thickenedPushforwardRetractionIso`. -/
theorem thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_comp
    (h₂' : a ≫ (b ≫ c) = 𝟙 X₀) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (pushforwardModulesCompAt B S hS b c).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) ≫
      (thickenedPushforwardRetractionIso a (b ≫ c) h₂').hom.app M =
    (thickenedPushforwardRetractionIso k c h₁).hom.app M :=
  pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso_comp a b c e₁ h₁ h₂' M

include h₁ in
/-- **The identifications `c_* k_* ≅ 𝟭` and `c₂_* a_* ≅ 𝟭` through `Ψ₀ ∘ a_* ≅ k_*`**
(`AlgebraicGeometry.Space.pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso`) with
`a_*M` written as restriction of scalars of the direct image to the thickened presentation, the
spelling of the extensions attached to lifts, and the identifications
`AlgebraicGeometry.Space.thickenedPushforwardRetractionIso`. Stated through `c₂ = b ≫ c`, where the
two spellings of `a_*M` are compared directly. -/
theorem thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) ≫
      (thickenedPushforwardRetractionIso a c₂ h₂).hom.app M =
    (thickenedPushforwardRetractionIso k c h₁).hom.app M := by
  subst e₂
  exact (comp_trans_eqToIso_hom_app_comp_of_eq_self (pushforwardModulesCompAt B S hS b c) _ _ _
    _).trans
    (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_comp a b c e₁ h₁ h₂ M)

include h₁ in
/-- `AlgebraicGeometry.Space.thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso`,
solved for the map `c_*k_*M ⟶ c₂_*a_*M`. -/
theorem thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_eq_comp_inv
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) =
      (thickenedPushforwardRetractionIso k c h₁).hom.app M ≫
        (thickenedPushforwardRetractionIso a c₂ h₂).inv.app M :=
  (Iso.eq_comp_inv ((thickenedPushforwardRetractionIso a c₂ h₂).app M)).2
    ((Category.assoc _ _ _).trans
      (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso a b c e₁ e₂ h₁ h₂ M))

-- Elaborating this instance of the abstract kernel square at the small étale ringed topoi
-- exceeds the default heartbeat budget.
include h₁ in
/-- **The kernel square of a morphism of extensions along `a ≫ b = k`, read through the
retractions** `c` of `k` and `b ≫ c` of `a`, for small étale ringed topoi: the instance of
`ThickeningTargetMorphism.retraction_map_idealTensorMap_comp_eq_of_idealSquareCompatible`
for `Ψ₀ ∘ a_* ≅ k_*`, given the ideal-square compatibility of `λ`. -/
theorem retraction_map_idealTensorMap_comp_eq_comp (h₂' : a ≫ (b ≫ c) = 𝟙 X₀)
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (H : (smallEtaleThickeningTargetOfEq a b k e₁).IdealSquareCompatible hi₁ hi₂ t₁ f₁ f'₁ ht₁
      comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂
      (smallEtaleThickenedModulesCompIso a b k e₁) lam)
    {N₁' N₂' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)}
    (l₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X₀).O).flip.obj F).obj (basePullbackIdeal t₁ f₁ ht₁) ⟶ N₁')
    (l₂ : N₁' ⟶ N₂')
    (l₃ : N₂' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X₀).O).flip.obj F).obj (basePullbackIdeal t₂ f₂ ht₂))
    (hlam : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X₀).O).flip.obj F).map lam = l₁ ≫ l₂ ≫ l₃) :
    type_of% ((smallEtaleThickeningTargetOfEq
        a b k e₁).retraction_map_idealTensorMap_comp_eq_of_idealSquareCompatible
      hi₁ hi₂ (smallEtaleThickenedModulesCompIso a b k e₁)
      (smallEtaleThickeningTargetPushforwardIso a b k e₁)
      (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app a b k e₁)
      t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂
      (smallEtaleRingedToposHom B S hS c).pushforwardModules
      (smallEtaleRingedToposHom B S hS (b ≫ c)).pushforwardModules
      (pushforwardModulesCompAt B S hS b c)
      (thickenedPushforwardRetractionIso k c h₁) (thickenedPushforwardRetractionIso a (b ≫ c) h₂')
      (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_comp a b c e₁ h₁ h₂')
      F lam H l₁ l₂ l₃ hlam) :=
  (smallEtaleThickeningTargetOfEq
    a b k e₁).retraction_map_idealTensorMap_comp_eq_of_idealSquareCompatible
      hi₁ hi₂ (smallEtaleThickenedModulesCompIso a b k e₁)
      (smallEtaleThickeningTargetPushforwardIso a b k e₁)
      (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app a b k e₁)
      t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂
      (smallEtaleRingedToposHom B S hS c).pushforwardModules
      (smallEtaleRingedToposHom B S hS (b ≫ c)).pushforwardModules
      (pushforwardModulesCompAt B S hS b c)
      (thickenedPushforwardRetractionIso k c h₁) (thickenedPushforwardRetractionIso a (b ≫ c) h₂')
      (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_comp a b c e₁ h₁ h₂')
      F lam H l₁ l₂ l₃ hlam

/-- `c_*b_* ≅ (b ≫ c)_* ≅ c₂_*` for `b ≫ c = c₂`, with `b_*` written as the direct image along
the morphism of thickened targets `Ψ₀ ∘ a_* ≅ k_*` of `a ≫ b = k`, the spelling of
`Deformation.ToposThickening.ThickeningTargetMorphism.restrictIso`. -/
abbrev smallEtaleRetractionCompIso :
    (smallEtaleThickeningTargetOfEq a b k e₁).j.pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS c).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS c₂).pushforwardModules :=
  pushforwardModulesCompAt B S hS b c ≪≫
    eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
      (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)

include h₁ in
/-- `AlgebraicGeometry.Space.thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso`
with `AlgebraicGeometry.Space.smallEtaleRetractionCompIso`. -/
theorem thickenedPushforwardRetractionIso_hom_app_smallEtaleRetractionCompIso
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (smallEtaleRetractionCompIso a b c e₁ e₂).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) ≫
      (thickenedPushforwardRetractionIso a c₂ h₂).hom.app M =
    (thickenedPushforwardRetractionIso k c h₁).hom.app M := by
  subst e₂
  exact (comp_trans_eqToIso_hom_app_comp_of_eq_self (pushforwardModulesCompAt B S hS b c) _ _ _
    _).trans
    (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_comp a b c e₁ h₁ h₂ M)

include h₁ in
/-- `thickenedPushforwardRetractionIso_hom_app_smallEtaleRetractionCompIso`, solved for the map
`c_*k_*M ⟶ c₂_*a_*M`. -/
theorem thickenedPushforwardRetractionIso_hom_app_smallEtaleRetractionCompIso_eq_comp_inv
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (smallEtaleRetractionCompIso a b c e₁ e₂).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) =
      (thickenedPushforwardRetractionIso k c h₁).hom.app M ≫
        (thickenedPushforwardRetractionIso a c₂ h₂).inv.app M :=
  (Iso.eq_comp_inv ((thickenedPushforwardRetractionIso a c₂ h₂).app M)).2
    ((Category.assoc _ _ _).trans
      (thickenedPushforwardRetractionIso_hom_app_smallEtaleRetractionCompIso a b c e₁ e₂ h₁ h₂ M))

include h₁ in
/-- `thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_eq_comp_inv` with the
comparison `c_*b_* ≅ (b ≫ c)_* ≅ c₂_*` split into its two components. -/
theorem thickenedPushforwardRetractionIso_hom_app_eq_comp_inv_of_eqToHom
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (pushforwardModulesCompAt B S hS b c).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)) ≫
        eqToHom (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj
            ((structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M))) e₂) =
      (thickenedPushforwardRetractionIso k c h₁).hom.app M ≫
        (thickenedPushforwardRetractionIso a c₂ h₂).inv.app M :=
  (whisker_eq _ (pushforwardModulesCompAt_trans_eqToIso_hom_app b c e₂ _)).symm.trans
    (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_eq_comp_inv a b c e₁ e₂ h₁
      h₂ M)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂} {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T}

/-- **The quotient map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, read on `X_T`**: for `r₂ = g ≫ r`,
`ρ_*` of the quotient map followed by `ρ_*(X_g)_* ≅ ρ₂_*` is `ρ_*i_*𝒢 ≅ 𝒢 ≅ ρ₂_*i₂_*𝒢`, in the
spelling of `thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_eq_comp_inv`
(the single instance of that variable statement; the crossing to the spelling of
`AlgebraicGeometry.Space.CoherentSituation.thickenedModuleRetractionIso` is not made here). -/
theorem retraction_map_thickeningLiftPullbackQuotientMap_eq_comp_inv (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h)
    (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T) (hgr : r₂ = g ≫ r) :
    type_of% (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_eq_comp_inv
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (D.relativeSquareSituation.relativeMap r) (relativeMap_comp_of_comp_eq g hg)
    (relativeMap_comp_of_eq_comp g hgr) (relativeMap_comp_relativeMap_retraction h r hr)
    (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂) ξ.F) :=
  thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso_eq_comp_inv
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (D.relativeSquareSituation.relativeMap r) (relativeMap_comp_of_comp_eq g hg)
    (relativeMap_comp_of_eq_comp g hgr) (relativeMap_comp_relativeMap_retraction h r hr)
    (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂) ξ.F

/-- `ρ_*i_*𝒢 ≅ 𝒢` (`AlgebraicGeometry.Space.CoherentSituation.thickenedModuleRetractionIso`) is the
component of `AlgebraicGeometry.Space.thickenedPushforwardRetractionIso`; a comparison of
isomorphisms of objects, by definition. -/
theorem thickenedModuleRetractionIso_eq (hr : h ≫ r = 𝟙 ξ.T) :
    thickenedModuleRetractionIso h r hr =
      (thickenedPushforwardRetractionIso (D.relativeSquareSituation.relativeMap h)
        (D.relativeSquareSituation.relativeMap r)
        (relativeMap_comp_relativeMap_retraction h r hr)).app ξ.F :=
  rfl

/-- `i_*𝒢` in the spelling of `Deformation.ToposThickening.thickenedModulesFunctor`. -/
theorem thickenedModule_eq (h : ξ.T ⟶ T') :
    thickenedModule ξ h = (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h))).obj ξ.F :=
  rfl

end AlgebraicGeometry.Space.CoherentSituation

end
