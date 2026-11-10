module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsIsoDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PointPullbackRigidityChart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Gluing isomorphisms of points from a tensor functor trivialized after base change

Let `F : QCoh(𝒪_𝒳) ⥤ Mod_R` be a functor, `π : R ⟶ T` a ring map, `x_T` a point of `𝒳` over
`Spec T` and `θ : T ⊗_R F(-) ≅ x_T^*` an isomorphism. This is the situation of Stacks 0GRQ after
the base change along the faithfully flat `R ⟶ C`, and the point `x_T` is to be descended to
`Spec R`. This file proves the rigidity statement which makes the descent datum unique: for points
`z, z'` over `Spec S` with arrows `χ : z ⟶ x_T`, `χ' : z' ⟶ x_T`, a 2-arrow `a : z ≅ z'` is
determined by the condition that restricting `θ(1 ⊗ f)` along `a⁻¹ ≫ χ` and along `χ'` gives the
same section, for every `f ∈ F(M)`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.span_range_hom_app_one_tmul`: the sections of `x_T^*M`
  are spanned over `T` by the elements `θ(1 ⊗ f)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.linearMap_ext_of_restrict_hom_app_one_tmul`: linear
  maps out of `z^*M` agreeing on the restrictions of the `θ(1 ⊗ f)` along `χ` agree.
* `AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_restrict_hom_app_one_tmul_eq`: the uniqueness of
  the gluing 2-arrows, from the rigidity of points along a smooth surjective affine chart.
* `AlgebraicGeometry.Stack.AlgebraicStacks.baseChangeOneTmul` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isMonoidal_baseChangeOneTmul`: the trivialization
  `S' ⊗_R F ≅ z^*` over an arrow `χ : z ⟶ x_T`, an isomorphism of tensor functors.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_restrict_hom_app_one_tmul_eq`: the existence
  of the gluing 2-arrows (Stacks 0GRP), and
  `AlgebraicGeometry.Stack.AlgebraicStacks.eq_of_restrict_hom_app_one_tmul`: the structure
  morphisms of the glued points agree.
* `AlgebraicGeometry.Stack.AlgebraicStacks.restrict_hom_app_one_tmul_of_comp` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.restrict_hom_app_one_tmul_trans`: the gluing condition
  is stable under base change and composition (for the cocycle condition).
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_pointPullback_of_gluing`: once `x_T` has
  descended to a point `x` of `Spec R` compatibly with a gluing 2-arrow over `Spec (T ⊗_R T)`,
  `θ` descends to an isomorphism of tensor functors `F ≅ x^*` (faithfully flat `π`).
* `AlgebraicGeometry.exists_spec_map_comp_eq_of_faithfullyFlat`: descent of morphisms out of
  `Spec T` along a faithfully flat `R ⟶ T`.

## References

* [Stacks Project, Tag 0GRQ](https://stacks.math.columbia.edu/tag/0GRQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat
attribute [local instance] fppfModulesMonoidal fppfModulesBraided fppfModulesSymmetric

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {R T : Type u} [CommRing R] [CommRing T] {π : R →+* T}
  {F : quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R} {xT : 𝒳.val.val.obj}
  {eT : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj xT) ≅ Spec (CommRingCat.of T)}
  (θ : F ⋙ ModuleCat.extendScalars π ≅ pointPullback B S hS 𝒳 xT eT)

/-- **The sections of `x_T^* M` are spanned over `T` by the elements `θ(1 ⊗ f)`**, `f ∈ F(M)`,
for an isomorphism `θ : T ⊗_R F(-) ≅ x_T^*`. -/
theorem span_range_hom_app_one_tmul (M : quasicoherentModules B S hS 𝒳) :
    Submodule.span T (Set.range fun f : F.obj M => (θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) =
      ⊤ := by
  refine eq_top_iff.2 fun m _ => ?_
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (θ.hom.app M)).2 m
  rw [← hz]
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul t f =>
    have ht := ModuleCat.ExtendScalars.smul_tmul π (M := F.obj M) (show T from t) (1 : T) f
    rw [mul_one] at ht
    have hm := (θ.hom.app M).hom.map_smul (show T from t)
      ((1 : T) ⊗ₜ[R, π] f : (ModuleCat.extendScalars π).obj (F.obj M))
    refine (congrArg (· ∈ _) ((congrArg (θ.hom.app M).hom ht).symm.trans hm)).mpr ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
  | add z z' hz hz' =>
    exact (congrArg (· ∈ _) (map_add (θ.hom.app M).hom z z')).mpr (Submodule.add_mem _ hz hz')

variable {S' : Type u} [CommRing S'] {g : T →+* S'} {z : 𝒳.val.val.obj}
  {e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z) ≅ Spec (CommRingCat.of S')}
  {χ : z ⟶ xT}

/-- **Linear maps out of `z^* M` are determined on the restrictions of the `θ(1 ⊗ f)`**: for an
arrow `χ : z ⟶ x_T` of points lying over `Spec S' ⟶ Spec T`, the sections of `z^* M` are spanned
over `S'` by the restrictions along `χ` of the elements `θ(1 ⊗ f)`, `f ∈ F(M)`, since
`S' ⊗_T x_T^* M ≅ z^* M`. -/
theorem linearMap_ext_of_restrict_hom_app_one_tmul
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (M : quasicoherentModules B S hS 𝒳) {N : Type u} [AddCommGroup N] [Module S' N]
    (L₁ L₂ : (pointPullback B S hS 𝒳 z e).obj M →ₗ[S'] N)
    (h : ∀ f : F.obj M,
      L₁ ((M.obj.val.map χ.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))) =
        L₂ ((M.obj.val.map χ.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)))) :
    L₁ = L₂ := by
  have hρ : ∀ n : (pointPullback B S hS 𝒳 xT eT).obj M,
      L₁ (((pointPullbackRestriction B S hS 𝒳 g eT e χ hχ).app M).hom n) =
        L₂ (((pointPullbackRestriction B S hS 𝒳 g eT e χ hχ).app M).hom n) := by
    intro n
    have hn : n ∈ Submodule.span T
        (Set.range fun f : F.obj M => (θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) := by
      rw [span_range_hom_app_one_tmul θ M]
      exact Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      exact h f
    | zero =>
      exact (congrArg L₁ (map_zero _)).trans ((map_zero L₁).trans
        ((map_zero L₂).symm.trans (congrArg L₂ (map_zero _)).symm))
    | add x y _ _ hx hy =>
      exact (congrArg L₁ (map_add _ x y)).trans ((map_add L₁ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans ((map_add L₂ _ _).symm.trans
          (congrArg L₂ (map_add _ x y)).symm)))
    | smul t x _ hx =>
      rw [map_smul]
      change L₁ (g t • (show (pointPullback B S hS 𝒳 z e).obj M from
          ((pointPullbackRestriction B S hS 𝒳 g eT e χ hχ).app M).hom x)) =
        L₂ (g t • (show (pointPullback B S hS 𝒳 z e).obj M from
          ((pointPullbackRestriction B S hS 𝒳 g eT e χ hχ).app M).hom x))
      rw [map_smul, map_smul, hx]
  ext m
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
    ((pointPullbackBaseChange B S hS 𝒳 g eT e χ hχ).app M)).2 m
  rw [← hw]
  clear hw
  induction w using TensorProduct.inductionOn with
  | tmul s n =>
    change L₁ (((pointPullbackBaseChange B S hS 𝒳 g eT e χ hχ).app M).hom (s ⊗ₜ[T, g] n)) =
      L₂ (((pointPullbackBaseChange B S hS 𝒳 g eT e χ hχ).app M).hom (s ⊗ₜ[T, g] n))
    exact (congrArg L₁ (pointPullbackBaseChange_app_tmul B S hS 𝒳 g eT e χ hχ M s n)).trans
      ((map_smul L₁ _ _).trans ((congrArg ((show S' from s) • ·) (hρ n)).trans
        ((map_smul L₂ _ _).symm.trans (congrArg L₂
          (pointPullbackBaseChange_app_tmul B S hS 𝒳 g eT e χ hχ M s n)).symm)))
  | add w w' hw hw' =>
    exact (congrArg L₁ (map_add _ w w')).trans ((map_add L₁ _ _).trans
      ((congrArg₂ (· + ·) hw hw').trans ((map_add L₂ _ _).symm.trans
        (congrArg L₂ (map_add _ w w')).symm)))

/-- Restriction along a composite is the composite of the restrictions. -/
private theorem restrict_comp_apply {x y v : 𝒳.val.val.obj} (M : quasicoherentModules B S hS 𝒳)
    (f : x ⟶ y) (g : y ⟶ v) (m : M.obj.val.obj (op v)) :
    (M.obj.val.map (f ≫ g).op).hom m =
      (M.obj.val.map f.op).hom ((M.obj.val.map g.op).hom m) := by
  rw [op_comp]
  exact M.obj.val.map_comp_apply _ _ _

/-- **The gluing 2-arrows are unique.** Let `c : U ⟶ 𝒳` be an affine, smooth and surjective
1-morphism from a scheme, `θ : T ⊗_R F(-) ≅ x_T^*`, and `χ : z ⟶ x_T`, `χ' : z' ⟶ x_T` arrows of
points lying over `Spec S' ⟶ Spec T` (for possibly different ring maps `T ⟶ S'`). Two 2-arrows
`a, b : z ≅ z'` over `Spec S'` such that restricting `θ(1 ⊗ f)` along `a⁻¹ ≫ χ`, respectively
`b⁻¹ ≫ χ`, gives its restriction along `χ'`, for every `f ∈ F(M)`, are equal. -/
theorem eq_of_restrict_hom_app_one_tmul_eq (U : BigFppfOver B S hS)
    (c : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hc : IsAffineHom B S hS c) (hsm : IsSmooth B S hS c)
    (hsurj : IsSurjective B S hS c)
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    {z' : 𝒳.val.val.obj}
    {e' : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z') ≅ Spec (CommRingCat.of S')}
    {χ' : z' ⟶ xT} (a b : z ≅ z')
    (ha : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ e'.hom = e.hom)
    (hb : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map b.hom) ≫ e'.hom = e.hom)
    (hPa : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      (M.obj.val.map (a.inv ≫ χ).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)) =
        (M.obj.val.map χ'.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)))
    (hPb : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      (M.obj.val.map (b.inv ≫ χ).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)) =
        (M.obj.val.map χ'.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f))) :
    a = b := by
  refine eq_of_pointPullbackTransportIso_eq_of_isSmooth B S hS U c hc hsm hsurj e e' a b ha hb ?_
  refine Iso.ext (NatTrans.ext (funext fun M => ModuleCat.hom_ext ?_))
  refine linearMap_ext_of_restrict_hom_app_one_tmul θ hχ M _ _ fun f => ?_
  have h₁ := restrict_comp_apply M a.inv χ ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  have h₂ := restrict_comp_apply M b.inv χ ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  exact h₁.symm.trans ((hPa M f).trans ((hPb M f).symm.trans h₂))

/-- `f ↦ θ(1 ⊗ f)|_z`, the restriction along `χ : z ⟶ x_T` of the elements `θ(1 ⊗ f)`, as a
natural transformation `F ⟶ z^* ⋙ restrictScalars κ` for `κ = g ∘ π : R ⟶ S'`. -/
def restrictOneTmul
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) :
    F ⟶ pointPullback B S hS 𝒳 z e ⋙ ModuleCat.restrictScalars κ where
  app M := (ModuleCat.extendRestrictScalarsAdj π).unit.app (F.obj M) ≫
    (ModuleCat.restrictScalars π).map
      ((θ.hom.app M) ≫ (pointPullbackRestriction B S hS 𝒳 g eT e χ hχ).app M) ≫
    (ModuleCat.restrictScalarsComp'App π g κ hκ ((pointPullback B S hS 𝒳 z e).obj M)).inv
  naturality M N φ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f => ?_)
    exact (congrArg (fun k => k.hom ((1 : T) ⊗ₜ[R, π] f))
      (θ.hom.naturality φ =≫ (pointPullbackRestriction B S hS 𝒳 g eT e χ hχ).app N)).trans
      (congrArg (fun k => k.hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)))
        ((pointPullbackRestriction B S hS 𝒳 g eT e χ hχ).naturality φ))

/-- `restrictOneTmul` sends `f` to `θ(1 ⊗ f)|_z`. -/
theorem restrictOneTmul_app_apply
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) (M : quasicoherentModules B S hS 𝒳) (f : F.obj M) :
    ((restrictOneTmul θ hχ κ hκ).app M).hom f =
      (M.obj.val.map χ.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) :=
  rfl

/-- **The trivialization of `F` over `z`**: `S' ⊗_R F(M) ⟶ z^* M`, `s ⊗ f ↦ s • θ(1 ⊗ f)|_z`, for
an arrow `χ : z ⟶ x_T` of points over `Spec S' ⟶ Spec T` and `κ = g ∘ π`; it is an isomorphism
(`AlgebraicGeometry.Stack.AlgebraicStacks.bijective_baseChangeOneTmul_app`). -/
def baseChangeOneTmul
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) :
    F ⋙ ModuleCat.extendScalars κ ⟶ pointPullback B S hS 𝒳 z e :=
  Functor.whiskerRight (restrictOneTmul θ hχ κ hκ) (ModuleCat.extendScalars κ) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (pointPullback B S hS 𝒳 z e)
      (ModuleCat.extendRestrictScalarsAdj κ).counit ≫ (Functor.rightUnitor _).hom

/-- The component of `baseChangeOneTmul` at `M` is the adjoint, under extension and restriction
of scalars along `κ`, of the component of `restrictOneTmul` at `M`. -/
theorem baseChangeOneTmul_app
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) (M : quasicoherentModules B S hS 𝒳) :
    (baseChangeOneTmul θ hχ κ hκ).app M =
      ((ModuleCat.extendRestrictScalarsAdj κ).homEquiv _ _).symm
        ((restrictOneTmul θ hχ κ hκ).app M) := by
  rw [Adjunction.homEquiv_counit]
  simp [baseChangeOneTmul]

/-- The trivialization sends `s ⊗ f` to `s • θ(1 ⊗ f)|_z`. -/
theorem baseChangeOneTmul_app_tmul
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) (M : quasicoherentModules B S hS 𝒳) (s : S')
    (f : F.obj M) :
    ((baseChangeOneTmul θ hχ κ hκ).app M).hom (s ⊗ₜ[R, κ] f) =
      s • (show (pointPullback B S hS 𝒳 z e).obj M from
        (M.obj.val.map χ.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))) := by
  rw [baseChangeOneTmul_app]
  let adj := ModuleCat.extendRestrictScalarsAdj κ
  have hone : (((adj.homEquiv _ _).symm
      ((restrictOneTmul θ hχ κ hκ).app M)).hom ((1 : S') ⊗ₜ[R, κ] f)) =
      ((restrictOneTmul θ hχ κ hκ).app M).hom f :=
    congrArg (fun k => k f)
      ((adj.homEquiv _ _).apply_symm_apply ((restrictOneTmul θ hχ κ hκ).app M))
  have hsm := ((adj.homEquiv _ _).symm
      ((restrictOneTmul θ hχ κ hκ).app M)).hom.map_smul s ((1 : S') ⊗ₜ[R, κ] f)
  exact (congrArg (fun c => ((adj.homEquiv _ _).symm
      ((restrictOneTmul θ hχ κ hκ).app M)).hom (c ⊗ₜ[R, κ] f))
      (mul_one s).symm).trans (hsm.trans (congrArg (fun y => s • y) hone))

/-- The trivialization `S' ⊗_R F(M) ⟶ z^* M` is bijective: it is the composite of
`S' ⊗_R F(M) ≅ S' ⊗_T (T ⊗_R F(M))`, of `S' ⊗_T θ` and of the base change isomorphism
`S' ⊗_T x_T^* M ≅ z^* M`. -/
theorem bijective_baseChangeOneTmul_app
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) (M : quasicoherentModules B S hS 𝒳) :
    Function.Bijective ((baseChangeOneTmul θ hχ κ hκ).app M) := by
  subst hκ
  have h : (baseChangeOneTmul θ hχ (g.comp π) rfl).app M =
      (ModuleCat.extendScalarsComp π g).hom.app (F.obj M) ≫
        (ModuleCat.extendScalars g).map (θ.hom.app M) ≫
        (pointPullbackBaseChange B S hS 𝒳 g eT e χ hχ).app M := by
    refine ModuleCat.ExtendScalars.hom_ext fun f => ?_
    refine (baseChangeOneTmul_app_tmul θ hχ (g.comp π) rfl M 1 f).trans ?_
    refine Eq.trans ?_ (congrArg (fun y => ((ModuleCat.extendScalars g).map (θ.hom.app M) ≫
        (pointPullbackBaseChange B S hS 𝒳 g eT e χ hχ).app M).hom y)
      (ModuleCat.extendScalarsComp_hom_app_one_tmul π g (F.obj M) f)).symm
    exact (pointPullbackBaseChange_app_tmul B S hS 𝒳 g eT e χ hχ M 1 _).symm
  rw [h]
  exact ConcreteCategory.bijective_of_isIso _

/-- The trivialization `F ⋙ extendScalars κ ⟶ z^*` is a natural isomorphism. -/
instance isIso_baseChangeOneTmul
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) :
    IsIso (baseChangeOneTmul θ hχ κ hκ) :=
  haveI : ∀ M, IsIso ((baseChangeOneTmul θ hχ κ hκ).app M) := fun M =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_baseChangeOneTmul_app θ hχ κ hκ M)
  NatIso.isIso_of_isIso_app _

section Monoidal

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable [F.LaxMonoidal] [NatTrans.IsMonoidal θ.hom]

/-- `θ(1 ⊗ ε(1)) = ε(1)`: the monoidality of `θ` on the unit, on elements. -/
theorem hom_app_one_tmul_ε :
    (θ.hom.app (𝟙_ _)).hom ((1 : T) ⊗ₜ[R, π] (ε F).hom (1 : R)) =
      (ε (pointPullback B S hS 𝒳 xT eT)).hom (1 : T) :=
  congrArg (fun k => k.hom (1 : T)) (NatTrans.IsMonoidal.unit (τ := θ.hom))

/-- Maps out of `A' ⊗_A (M ⊗ N)` agree once they agree on the elements `1 ⊗ (m ⊗ n)`. -/
theorem _root_.ModuleCat.ExtendScalars.hom_ext_tmul {A A' : Type u} [CommRing A] [CommRing A']
    {φ : A →+* A'} {M N : ModuleCat.{u} A} {P : ModuleCat.{u} A'}
    {α β : (ModuleCat.extendScalars φ).obj (M ⊗ N) ⟶ P}
    (h : ∀ (m : M) (n : N),
      α.hom ((1 : A') ⊗ₜ[A,φ] (show (M ⊗ N : ModuleCat.{u} A) from m ⊗ₜ[A] n)) =
        β.hom ((1 : A') ⊗ₜ[A,φ] (show (M ⊗ N : ModuleCat.{u} A) from m ⊗ₜ[A] n))) :
    α = β :=
  ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
    (ModuleCat.MonoidalCategory.tensor_ext fun m n => h m n)

/-- `μ(1 ⊗ m, 1 ⊗ n) = 1 ⊗ (m ⊗ n)` for the tensorator of extension of scalars. -/
theorem _root_.ModuleCat.extendScalars_μ_one_tmul_one_tmul {A A' : Type u} [CommRing A]
    [CommRing A'] (φ : A →+* A') (X Y : ModuleCat.{u} A) (m : X) (n : Y) :
    (μ (ModuleCat.extendScalars φ) X Y).hom
        (((1 : A') ⊗ₜ[A, φ] m : (ModuleCat.extendScalars φ).obj X) ⊗ₜ
          ((1 : A') ⊗ₜ[A, φ] n : (ModuleCat.extendScalars φ).obj Y)) =
      (1 : A') ⊗ₜ[A, φ] (show (X ⊗ Y : ModuleCat.{u} A) from m ⊗ₜ[A] n) := by
  have h := congrArg (fun k => k.hom
    ((1 : A') ⊗ₜ[A, φ] (show (X ⊗ Y : ModuleCat.{u} A) from m ⊗ₜ[A] n)))
    (Functor.Monoidal.δ_μ (ModuleCat.extendScalars φ) X Y)
  refine Eq.trans ?_ h
  exact congrArg (μ (ModuleCat.extendScalars φ) X Y).hom
    (ModuleCat.extendScalars_δ_tmul φ X Y m n).symm

/-- `θ(1 ⊗ μ(f ⊗ f')) = μ(θ(1 ⊗ f) ⊗ θ(1 ⊗ f'))`: the monoidality of `θ`, on elements. -/
theorem hom_app_one_tmul_μ (X Y : quasicoherentModules B S hS 𝒳) (f : F.obj X) (f' : F.obj Y) :
    (θ.hom.app (X ⊗ Y)).hom ((1 : T) ⊗ₜ[R, π] (μ F X Y).hom (f ⊗ₜ f')) =
      (μ (pointPullback B S hS 𝒳 xT eT) X Y).hom
        ((θ.hom.app X).hom ((1 : T) ⊗ₜ[R, π] f) ⊗ₜ (θ.hom.app Y).hom ((1 : T) ⊗ₜ[R, π] f')) := by
  have h := congrArg (fun k => k.hom
    (((1 : T) ⊗ₜ[R, π] f : (ModuleCat.extendScalars π).obj (F.obj X)) ⊗ₜ
      ((1 : T) ⊗ₜ[R, π] f' : (ModuleCat.extendScalars π).obj (F.obj Y))))
    (NatTrans.IsMonoidal.tensor (τ := θ.hom) X Y)
  refine Eq.trans ?_ h
  exact congrArg (fun y => (θ.hom.app (X ⊗ Y)).hom (((ModuleCat.extendScalars π).map
    (μ F X Y)).hom y)) (ModuleCat.extendScalars_μ_one_tmul_one_tmul π _ _ f f').symm

/-- **The trivialization of `F` over `z` is an isomorphism of tensor functors.** -/
instance isMonoidal_baseChangeOneTmul
    (hχ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ) ≫ eT.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom g))
    (κ : R →+* S') (hκ : κ = g.comp π) :
    NatTrans.IsMonoidal (baseChangeOneTmul θ hχ κ hκ) where
  unit := by
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change ((baseChangeOneTmul θ hχ κ hκ).app (𝟙_ _)).hom
      ((1 : S') ⊗ₜ[R, κ] (ε F).hom (1 : R)) = (ε (pointPullback B S hS 𝒳 z e)).hom 1
    refine (baseChangeOneTmul_app_tmul θ hχ κ hκ (𝟙_ _) 1 _).trans ((one_smul S' _).trans ?_)
    have h3 := congrArg (fun k => k.hom (1 : T))
      (NatTrans.IsMonoidal.unit (τ := pointPullbackRestriction B S hS 𝒳 g eT e χ hχ))
    simp only [Functor.LaxMonoidal.comp_ε, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.restrictScalars_η, map_one] at h3
    refine Eq.trans ?_ h3
    exact congrArg ((𝟙_ (quasicoherentModules B S hS 𝒳)).obj.val.map χ.op).hom
      (hom_app_one_tmul_ε θ)
  tensor X Y := by
    have key : (ModuleCat.extendScalars κ).map (μ F X Y) ≫
        (baseChangeOneTmul θ hχ κ hκ).app (X ⊗ Y) =
        δ (ModuleCat.extendScalars κ) (F.obj X) (F.obj Y) ≫
          ((baseChangeOneTmul θ hχ κ hκ).app X ⊗ₘ (baseChangeOneTmul θ hχ κ hκ).app Y) ≫
            μ (pointPullback B S hS 𝒳 z e) X Y := by
      refine ModuleCat.ExtendScalars.hom_ext_tmul fun f f' => ?_
      have hr := congrArg (fun k => k.hom ((θ.hom.app X).hom ((1 : T) ⊗ₜ[R, π] f) ⊗ₜ
          (θ.hom.app Y).hom ((1 : T) ⊗ₜ[R, π] f')))
        (NatTrans.IsMonoidal.tensor (τ := pointPullbackRestriction B S hS 𝒳 g eT e χ hχ) X Y)
      simp only [Functor.LaxMonoidal.comp_μ, ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.MonoidalCategory.tensorHom_tmul] at hr
      change ((baseChangeOneTmul θ hχ κ hκ).app (X ⊗ Y)).hom
          ((1 : S') ⊗ₜ[R, κ] (μ F X Y).hom (f ⊗ₜ f')) =
        (μ (pointPullback B S hS 𝒳 z e) X Y).hom
          (((baseChangeOneTmul θ hχ κ hκ).app X).hom ((1 : S') ⊗ₜ[R, κ] f) ⊗ₜ
            ((baseChangeOneTmul θ hχ κ hκ).app Y).hom ((1 : S') ⊗ₜ[R, κ] f'))
      rw [baseChangeOneTmul_app_tmul, baseChangeOneTmul_app_tmul, baseChangeOneTmul_app_tmul,
        one_smul, one_smul, one_smul]
      refine (congrArg ((X ⊗ Y).obj.val.map χ.op).hom (hom_app_one_tmul_μ θ X Y f f')).trans ?_
      exact hr.trans (congrArg ((ModuleCat.restrictScalars g).map
        (μ (pointPullback B S hS 𝒳 z e) X Y)).hom (ModuleCat.restrictScalars_μ_tmul g _ _ _ _))
    rw [Functor.LaxMonoidal.comp_μ, Category.assoc, key, Functor.Monoidal.μ_δ_assoc]

/-- The comparison of the two trivializations over `z₁` and `z₂` is monoidal. -/
private theorem isMonoidal_symm_trans_baseChangeOneTmul
    {g₁ g₂ : T →+* S'} {z₁ z₂ : 𝒳.val.val.obj}
    {e₁ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z₁) ≅ Spec (CommRingCat.of S')}
    {e₂ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z₂) ≅ Spec (CommRingCat.of S')}
    {χ₁ : z₁ ⟶ xT} {χ₂ : z₂ ⟶ xT}
    (hχ₁ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ₁) ≫ eT.hom =
      e₁.hom ≫ Spec.map (CommRingCat.ofHom g₁))
    (hχ₂ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ₂) ≫ eT.hom =
      e₂.hom ≫ Spec.map (CommRingCat.ofHom g₂))
    (hg : g₁.comp π = g₂.comp π) :
    NatTrans.IsMonoidal ((asIso (baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl)).symm ≪≫
      asIso (baseChangeOneTmul θ hχ₂ (g₁.comp π) hg)).hom :=
  have : NatTrans.IsMonoidal (asIso (baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl)).hom :=
    isMonoidal_baseChangeOneTmul θ hχ₁ _ rfl
  have : NatTrans.IsMonoidal (asIso (baseChangeOneTmul θ hχ₂ (g₁.comp π) hg)).hom :=
    isMonoidal_baseChangeOneTmul θ hχ₂ _ hg
  show NatTrans.IsMonoidal ((asIso (baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl)).inv ≫
    (asIso (baseChangeOneTmul θ hχ₂ (g₁.comp π) hg)).hom) from inferInstance

/-- **Existence of the gluing 2-arrows (Stacks 0GRP).** Let `𝒳` have affine (absolute) diagonal,
`F` be a lax monoidal functor and `θ : T ⊗_R F(-) ≅ x_T^*` monoidal. Let `χ₁ : z₁ ⟶ x_T` and
`χ₂ : z₂ ⟶ x_T` be arrows of points lying over `Spec S' ⟶ Spec T` for ring maps `g₁, g₂ : T ⟶ S'`
which agree on `R`. Then there is a 2-arrow `a : z₁ ≅ z₂` over `Spec S'` such that restricting
`θ(1 ⊗ f)` along `a⁻¹ ≫ χ₁` gives its restriction along `χ₂`, for every `f ∈ F(M)`: both
trivializations `S' ⊗_R F ≅ z_i^*` differ by an isomorphism of tensor functors, which comes from
a 2-arrow by Stacks 0GRP. -/
theorem exists_iso_restrict_hom_app_one_tmul_eq
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    {g₁ g₂ : T →+* S'} {z₁ z₂ : 𝒳.val.val.obj}
    {e₁ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z₁) ≅ Spec (CommRingCat.of S')}
    {e₂ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z₂) ≅ Spec (CommRingCat.of S')}
    {χ₁ : z₁ ⟶ xT} {χ₂ : z₂ ⟶ xT}
    (hχ₁ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ₁) ≫ eT.hom =
      e₁.hom ≫ Spec.map (CommRingCat.ofHom g₁))
    (hχ₂ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ₂) ≫ eT.hom =
      e₂.hom ≫ Spec.map (CommRingCat.ofHom g₂))
    (hg : g₁.comp π = g₂.comp π) :
    ∃ (a : z₁ ≅ z₂) (_ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ e₂.hom =
        e₁.hom), ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      (M.obj.val.map (a.inv ≫ χ₁).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) =
        (M.obj.val.map χ₂.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) := by
  have := isMonoidal_symm_trans_baseChangeOneTmul θ hχ₁ hχ₂ hg
  obtain ⟨a, ha, hat⟩ := exists_iso_pointPullbackTransportIso_eq B S hS e₁ e₂ hΔ
    ((asIso (baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl)).symm ≪≫
      asIso (baseChangeOneTmul θ hχ₂ (g₁.comp π) hg))
  refine ⟨a, ha, fun M f => ?_⟩
  have h := congrArg (fun t => (t.hom.app M).hom
    (((baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl).app M).hom ((1 : S') ⊗ₜ[R, g₁.comp π] f))) hat
  have hinv : ((inv (baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl)).app M).hom
      (((baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl).app M).hom ((1 : S') ⊗ₜ[R, g₁.comp π] f)) =
      (1 : S') ⊗ₜ[R, g₁.comp π] f :=
    congrArg (fun k => k.hom ((1 : S') ⊗ₜ[R, g₁.comp π] f))
      (NatTrans.congr_app (IsIso.hom_inv_id (baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl)) M)
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, NatTrans.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply, hinv] at h
  have h1 := (baseChangeOneTmul_app_tmul θ hχ₁ _ rfl M 1 f).trans (one_smul S' _)
  have h2 := (baseChangeOneTmul_app_tmul θ hχ₂ _ hg M 1 f).trans (one_smul S' _)
  have hc := restrict_comp_apply M a.inv χ₁ ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  exact hc.trans ((congrArg ((pointPullbackTransportIso B S hS 𝒳 e₁ e₂ a ha).hom.app M).hom
    h1.symm).trans (h.trans h2))

include θ in
/-- **The structure morphisms of the two points agree** (Stacks 0GRP, its part `q₁ = q₂`): with the
notation of `AlgebraicGeometry.Stack.AlgebraicStacks.exists_iso_restrict_hom_app_one_tmul_eq`, if
the points `z₁, z₂` lie over `q₁, q₂ : Spec S' ⟶ S`, then `q₁ = q₂`. -/
theorem eq_of_restrict_hom_app_one_tmul
    (hΔ : Stack.IsAffineHom B (⊤_ Scheme.{u}) (contains_terminalScheme B)
      (Stack.diagonal.{u, u, u + 1} B (⊤_ Scheme.{u}) (contains_terminalScheme B)
        (AlgebraicStacks.viewOverIntegers B S hS (contains_terminalScheme B) 𝒳).val))
    {hR' : B.Contains (Spec (CommRingCat.of S'))} {q₁ q₂ : B.obj hR' ⟶ B.obj hS}
    {g₁ g₂ : T →+* S'} {z₁ z₂ : 𝒳.val.val.obj}
    (hz₁ : 𝒳.val.val.p.obj z₁ = Over.mk q₁) (hz₂ : 𝒳.val.val.p.obj z₂ = Over.mk q₂)
    {χ₁ : z₁ ⟶ xT} {χ₂ : z₂ ⟶ xT}
    (hχ₁ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ₁) ≫ eT.hom =
      (overSpecIso B S hS 𝒳 hz₁).hom ≫ Spec.map (CommRingCat.ofHom g₁))
    (hχ₂ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map χ₂) ≫ eT.hom =
      (overSpecIso B S hS 𝒳 hz₂).hom ≫ Spec.map (CommRingCat.ofHom g₂))
    (hg : g₁.comp π = g₂.comp π) : q₁ = q₂ := by
  have := isMonoidal_symm_trans_baseChangeOneTmul θ hχ₁ hχ₂ hg
  exact (eq_and_exists_iso_pointPullbackTransportIso_eq B S hS hΔ hz₁ hz₂
    ((asIso (baseChangeOneTmul θ hχ₁ (g₁.comp π) rfl)).symm ≪≫
      asIso (baseChangeOneTmul θ hχ₂ (g₁.comp π) hg))).1

end Monoidal

/-- **Morphisms out of `Spec T` descend along a faithfully flat `R ⟶ T`**: a morphism
`q : Spec T ⟶ X` whose two composites with the projections `Spec (T ⊗_R T) ⟶ Spec T` agree
factors through `Spec T ⟶ Spec R`, which is an effective epimorphism (fpqc descent of morphisms,
Stacks 023Q, Mathlib's subcanonicity of the fpqc topology). -/
@[sga "3 XI 3.9" "partial"]
theorem _root_.AlgebraicGeometry.exists_spec_map_comp_eq_of_faithfullyFlat (R T : Type u)
    [CommRing R] [CommRing T] [Algebra R T] (hRT : (algebraMap R T).FaithfullyFlat)
    {X : Scheme.{u}} (q : Spec (CommRingCat.of T) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        T →+* T ⊗[R] T)) ≫ q =
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T))) ≫ q) :
    ∃ q' : Spec (CommRingCat.of R) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ q' = q := by
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R T))).2 hRT
  suffices key : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ Spec (CommRingCat.of T)),
      g₁ ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) =
        g₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) → g₁ ≫ q = g₂ ≫ q from
    ⟨EffectiveEpi.desc _ q key, EffectiveEpi.fac _ q key⟩
  intro Z g₁ g₂ hg
  have e₁ : g₁ = (pullback.lift g₁ g₂ hg ≫ (pullbackSpecIso R T T).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        T →+* T ⊗[R] T)) := by
    rw [Category.assoc, pullbackSpecIso_hom_fst, pullback.lift_fst]
  have e₂ : g₂ = (pullback.lift g₁ g₂ hg ≫ (pullbackSpecIso R T T).hom) ≫
      Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
        (Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T))) := by
    rw [Category.assoc, pullbackSpecIso_hom_snd, pullback.lift_snd]
  exact (congrArg (· ≫ q) e₁).trans ((Category.assoc _ _ _).trans ((congrArg
    ((pullback.lift g₁ g₂ hg ≫ (pullbackSpecIso R T T).hom) ≫ ·) h).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) e₂.symm))))

section Descend

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

/-- Restriction along an arrow `φ : y ⟶ x` of points over `Spec S' ⟶ Spec T` is semilinear. -/
theorem restrict_smul {x y : 𝒳.val.val.obj}
    {ex : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of T)}
    {ey : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) ≅ Spec (CommRingCat.of S')}
    {φ : y ⟶ x}
    (hφ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ) ≫ ex.hom =
      ey.hom ≫ Spec.map (CommRingCat.ofHom g))
    (M : quasicoherentModules B S hS 𝒳) (t : T) (m : (pointPullback B S hS 𝒳 x ex).obj M) :
    (M.obj.val.map φ.op).hom (t • m) =
      g t • (show (pointPullback B S hS 𝒳 y ey).obj M from (M.obj.val.map φ.op).hom m) :=
  ((pointPullbackRestriction B S hS 𝒳 g ex ey φ hφ).app M).hom.map_smul t m

end Descend

section DescendIso

open MonoidalCategory

variable [F.Monoidal] [NatTrans.IsMonoidal θ.hom]

/-- **Descent of the trivialization `θ` along a faithfully flat `π : R ⟶ T` (plan step 8 of
Stacks 0GRQ).** Let `ψ : x_T ⟶ x` be an arrow to a point `x` over `Spec R`, lying over
`Spec T ⟶ Spec R`, and let `φ₁ : y₁ ⟶ x_T`, `φ₂ : y₂ ⟶ x_T` be arrows of points over
`Spec (T ⊗_R T)` lying over the two projections, glued by a 2-arrow `a : y₁ ≅ y₂` over the
identity which carries `θ(1 ⊗ f)|_{y₁}` to `θ(1 ⊗ f)|_{y₂}` and is compatible with `ψ`
(`a⁻¹ ≫ φ₁ ≫ ψ = φ₂ ≫ ψ`). Then `F ≅ x^*` as tensor functors. -/
theorem exists_iso_pointPullback_of_gluing (hπ : π.FaithfullyFlat) {x : 𝒳.val.val.obj}
    {e : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (CommRingCat.of R)}
    {ψ : xT ⟶ x}
    (hψ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map ψ) ≫ e.hom =
      eT.hom ≫ Spec.map (CommRingCat.ofHom π)) :
    letI := π.toAlgebra
    ∀ {y₁ y₂ : 𝒳.val.val.obj}
      {e₁ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y₁) ≅
        Spec (CommRingCat.of (T ⊗[R] T))}
      {e₂ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y₂) ≅
        Spec (CommRingCat.of (T ⊗[R] T))}
      {φ₁ : y₁ ⟶ xT} {φ₂ : y₂ ⟶ xT}
      (_ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ₁) ≫ eT.hom =
        e₁.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          T →+* T ⊗[R] T)))
      (_ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map φ₂) ≫ eT.hom =
        e₂.hom ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom
          (Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T))))
      (a : y₁ ≅ y₂)
      (_ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map a.hom) ≫ e₂.hom = e₁.hom)
      (_ : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
        (M.obj.val.map (a.inv ≫ φ₁).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) =
          (M.obj.val.map φ₂.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)))
      (_ : a.inv ≫ φ₁ ≫ ψ = φ₂ ≫ ψ),
      ∃ e' : F ≅ pointPullback B S hS 𝒳 x e, NatTrans.IsMonoidal e'.hom := by
  let := π.toAlgebra
  intro y₁ y₂ e₁ e₂ φ₁ φ₂ hφ₁ hφ₂ a ha hP hcomp
  have hring : CommRingCat.ofHom π ≫ CommRingCat.ofHom (RingHomClass.toRingHom
      (Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T)) =
      CommRingCat.ofHom (algebraMap R (T ⊗[R] T)) :=
    CommRingCat.hom_ext (RingHom.ext (Algebra.TensorProduct.includeRight (A := T)).commutes)
  have hκ : (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ₂ ≫ ψ)) ≫ e.hom =
      e₂.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R (T ⊗[R] T))) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hψ, ← Category.assoc, hφ₂,
      Category.assoc, ← Spec.map_comp, hring]
  obtain ⟨eL, heL⟩ : ∃ eL : (T ⊗[R] T) ≃ₗ[R] (ModuleCat.restrictScalars
      (algebraMap R (T ⊗[R] T))).obj (ModuleCat.of (T ⊗[R] T) (T ⊗[R] T)), ∀ s, eL s = s :=
    ⟨{ toFun := fun s => s, invFun := fun s => s, map_add' := fun _ _ => rfl,
       map_smul' := fun r s => Algebra.smul_def r s, left_inv := fun _ => rfl,
       right_inv := fun _ => rfl }, fun _ => rfl⟩
  have hΨ : ∀ M : quasicoherentModules B S hS 𝒳, Function.Injective
      (fun w : (T ⊗[R] T) ⊗[R] (pointPullback B S hS 𝒳 x e).obj M =>
        ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂ (φ₂ ≫ ψ) hκ).app
          M).hom (TensorProduct.congr eL (LinearEquiv.refl R _) w)) := fun M =>
    (bijective_pointPullbackBaseChange_app B S hS 𝒳 _ e e₂ (φ₂ ≫ ψ) hκ M).1.comp
      (TensorProduct.congr eL (LinearEquiv.refl R _)).injective
  have hR : ∀ (M : quasicoherentModules B S hS 𝒳) (w : T ⊗[R] (pointPullback B S hS 𝒳 x e).obj M),
      ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂ (φ₂ ≫ ψ) hκ).app
          M).hom (TensorProduct.congr eL (LinearEquiv.refl R _)
            ((Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T).toLinearMap.rTensor _ w)) =
        (M.obj.val.map φ₂.op).hom
          (((pointPullbackBaseChange B S hS 𝒳 π e eT ψ hψ).app M).hom w) := by
    intro M w
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' =>
      exact (congrArg (fun w => ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
          (φ₂ ≫ ψ) hκ).app M).hom ((TensorProduct.congr eL
          (LinearEquiv.refl R ((pointPullback B S hS 𝒳 x e).obj M))) w)) (map_add _ w w')).trans
        ((congrArg ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
          (φ₂ ≫ ψ) hκ).app M).hom
        (map_add _ _ _)).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) hw hw').trans
          ((map_add _ _ _).symm.trans (congrArg (M.obj.val.map φ₂.op).hom (map_add _ w w')).symm))))
    | tmul t n =>
      have h1 := pointPullbackBaseChange_app_tmul B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
        (φ₂ ≫ ψ) hκ M ((Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T) t) n
      have h2 := pointPullbackBaseChange_app_tmul B S hS 𝒳 π e eT ψ hψ M t n
      have h3 := restrict_smul hφ₂ M t ((M.obj.val.map ψ.op).hom n)
      have h4 := restrict_comp_apply M φ₂ ψ n
      have h0 : (TensorProduct.congr eL (LinearEquiv.refl R ((pointPullback B S hS 𝒳 x e).obj M)))
          ((Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T).toLinearMap.rTensor _ (t ⊗ₜ n)) =
          ((Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T) t ⊗ₜ[R, algebraMap R (T ⊗[R] T)]
            n) := by
        rw [LinearMap.rTensor_tmul, TensorProduct.congr_tmul, heL]
        rfl
      refine (congrArg ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
          (φ₂ ≫ ψ) hκ).app M).hom h0).trans ?_
      exact h1.trans ((congrArg (fun v : (pointPullback B S hS 𝒳 y₂ e₂).obj M =>
        ((Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T) t) • v) h4).trans
          (h3.symm.trans (congrArg (M.obj.val.map φ₂.op).hom h2.symm)))
  have hL : ∀ (M : quasicoherentModules B S hS 𝒳) (w : T ⊗[R] (pointPullback B S hS 𝒳 x e).obj M),
      ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂ (φ₂ ≫ ψ) hκ).app
          M).hom (TensorProduct.congr eL (LinearEquiv.refl R _)
            ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] T).toLinearMap.rTensor _ w)) =
        (M.obj.val.map a.inv.op).hom ((M.obj.val.map φ₁.op).hom
          (((pointPullbackBaseChange B S hS 𝒳 π e eT ψ hψ).app M).hom w)) := by
    intro M w
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' =>
      exact (congrArg (fun w => ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
          (φ₂ ≫ ψ) hκ).app M).hom ((TensorProduct.congr eL
          (LinearEquiv.refl R ((pointPullback B S hS 𝒳 x e).obj M))) w)) (map_add _ w w')).trans
        ((congrArg ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
          (φ₂ ≫ ψ) hκ).app M).hom
        (map_add _ _ _)).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) hw hw').trans
          ((map_add _ _ _).symm.trans (congrArg (M.obj.val.map a.inv.op).hom
            ((map_add _ _ _).symm.trans (congrArg (M.obj.val.map φ₁.op).hom
              (map_add _ w w')).symm))))))
    | tmul t n =>
      have h1 := pointPullbackBaseChange_app_tmul B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
        (φ₂ ≫ ψ) hκ M ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] T) t) n
      have h2 := pointPullbackBaseChange_app_tmul B S hS 𝒳 π e eT ψ hψ M t n
      have h3 := restrict_smul hφ₁ M t ((M.obj.val.map ψ.op).hom n)
      have h4 := restrict_comp_apply M φ₁ ψ n
      have h5 := restrict_comp_apply M a.inv (φ₁ ≫ ψ) n
      rw [hcomp] at h5
      have h6 := ((pointPullbackTransportIso B S hS 𝒳 e₁ e₂ a ha).hom.app M).hom.map_smul
        ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] T) t)
        ((M.obj.val.map φ₁.op).hom ((M.obj.val.map ψ.op).hom n))
      have h0 : (TensorProduct.congr eL (LinearEquiv.refl R ((pointPullback B S hS 𝒳 x e).obj M)))
          ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] T).toLinearMap.rTensor _ (t ⊗ₜ n)) =
          ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] T) t ⊗ₜ[R, algebraMap R (T ⊗[R] T)]
            n) := by
        rw [LinearMap.rTensor_tmul, TensorProduct.congr_tmul, heL]
        rfl
      refine (congrArg ((pointPullbackBaseChange B S hS 𝒳 (algebraMap R (T ⊗[R] T)) e e₂
          (φ₂ ≫ ψ) hκ).app M).hom h0).trans ?_
      exact h1.trans ((congrArg (fun v : (pointPullback B S hS 𝒳 y₂ e₂).obj M =>
        ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] T) t) • v)
          (h5.trans (congrArg (M.obj.val.map a.inv.op).hom h4))).trans (h6.symm.trans
          (congrArg (M.obj.val.map a.inv.op).hom (h3.symm.trans
            (congrArg (M.obj.val.map φ₁.op).hom h2.symm)))))
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : F ⋙ ModuleCat.extendScalars π ≅
      pointPullback B S hS 𝒳 x e ⋙ ModuleCat.extendScalars π,
      Θ = θ ≪≫ (pointPullbackBaseChangeIso B S hS 𝒳 π e eT ψ hψ).symm := ⟨_, rfl⟩
  have : NatTrans.IsMonoidal Θ.hom := by
    subst hΘ
    exact (inferInstance : NatTrans.IsMonoidal
      (θ.hom ≫ (pointPullbackBaseChangeIso B S hS 𝒳 π e eT ψ hψ).inv))
  have hβ : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      ((pointPullbackBaseChange B S hS 𝒳 π e eT ψ hψ).app M).hom
        ((Θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) = (θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f) := by
    intro M f
    subst hΘ
    exact congrArg (fun k => k.hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)))
      ((pointPullbackBaseChangeIso B S hS 𝒳 π e eT ψ hψ).inv_hom_id_app M)
  have h : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      (Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] T).toLinearMap.rTensor _
          ((Θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) =
        (Algebra.TensorProduct.includeRight : T →ₐ[R] T ⊗[R] T).toLinearMap.rTensor _
          ((Θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) := by
    intro M f
    refine hΨ M ((hL M _).trans (Eq.trans ?_ (hR M _).symm))
    have hc := restrict_comp_apply M a.inv φ₁ ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
    exact (congrArg (fun v => (M.obj.val.map a.inv.op).hom ((M.obj.val.map φ₁.op).hom v))
      (hβ M f)).trans (hc.symm.trans ((hP M f).trans
        (congrArg (M.obj.val.map φ₂.op).hom (hβ M f).symm)))
  exact ⟨ModuleCat.descendIsoOfFaithfullyFlat π hπ Θ
      (ModuleCat.amitsurDiff₀_hom_app_eq_zero_of_rTensor_eq π Θ h),
    @ModuleCat.isMonoidal_descendIsoOfFaithfullyFlat R T _ _ π hπ _ _ F
      (pointPullback B S hS 𝒳 x e) Θ _ _ _ _ ‹NatTrans.IsMonoidal Θ.hom›⟩

end DescendIso

section GluingCondition

/-- **The gluing condition is stable under base change**: if `a : z₁ ≅ z₂` carries the
restrictions of the `θ(1 ⊗ f)` along `χ₁` to those along `χ₂`, and `a' : z₁' ≅ z₂'` lies over `a`
through arrows `k_i : z_i' ⟶ z_i` (with `χ_i' = k_i ≫ χ_i`), then `a'` satisfies the same condition
for `χ₁'` and `χ₂'`. -/
theorem restrict_hom_app_one_tmul_of_comp {z₁ z₂ z₁' z₂' : 𝒳.val.val.obj} {χ₁ : z₁ ⟶ xT}
    {χ₂ : z₂ ⟶ xT} (a : z₁ ≅ z₂) (a' : z₁' ≅ z₂') (k₁ : z₁' ⟶ z₁) (k₂ : z₂' ⟶ z₂)
    (hk : a'.hom ≫ k₂ = k₁ ≫ a.hom)
    (h : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      (M.obj.val.map (a.inv ≫ χ₁).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)) =
        (M.obj.val.map χ₂.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)))
    (M : quasicoherentModules B S hS 𝒳) (f : F.obj M) :
    (M.obj.val.map (a'.inv ≫ k₁ ≫ χ₁).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) =
      (M.obj.val.map (k₂ ≫ χ₂).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) := by
  have hk' : a'.inv ≫ k₁ = k₂ ≫ a.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hk, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hk', Category.assoc]
  have h₁ := restrict_comp_apply M k₂ (a.inv ≫ χ₁) ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  have h₂ := restrict_comp_apply M k₂ χ₂ ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  exact h₁.trans ((congrArg (M.obj.val.map k₂.op).hom (h M f)).trans h₂.symm)

/-- **The gluing condition is stable under composition.** -/
theorem restrict_hom_app_one_tmul_trans {z₁ z₂ z₃ : 𝒳.val.val.obj} {χ₁ : z₁ ⟶ xT}
    {χ₂ : z₂ ⟶ xT} {χ₃ : z₃ ⟶ xT} (a : z₁ ≅ z₂) (b : z₂ ≅ z₃)
    (ha : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      (M.obj.val.map (a.inv ≫ χ₁).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)) =
        (M.obj.val.map χ₂.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)))
    (hb : ∀ (M : quasicoherentModules B S hS 𝒳) (f : F.obj M),
      (M.obj.val.map (b.inv ≫ χ₂).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)) =
        (M.obj.val.map χ₃.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R,π] f)))
    (M : quasicoherentModules B S hS 𝒳) (f : F.obj M) :
    (M.obj.val.map ((a ≪≫ b).inv ≫ χ₁).op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) =
      (M.obj.val.map χ₃.op).hom ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f)) := by
  rw [Iso.trans_inv, Category.assoc]
  have h₁ := restrict_comp_apply M b.inv (a.inv ≫ χ₁) ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  have h₂ := restrict_comp_apply M b.inv χ₂ ((θ.hom.app M).hom ((1 : T) ⊗ₜ[R, π] f))
  exact h₁.trans ((congrArg (M.obj.val.map b.inv.op).hom (ha M f)).trans (h₂.symm.trans (hb M f)))

end GluingCondition

end AlgebraicGeometry.Stack.AlgebraicStacks
