module

public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheafHomEvaluation
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomOfDualizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyFreeDual
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ModuleSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image of the Tate twist `𝓗om(μ_N, -)`

Let `k` be a field, `U` a scheme over `k`, `N` invertible in `k` and `i : Z ⟶ U` any morphism of
schemes (in the application, the closed immersion of a divisor). For a sheaf `H` of
`ℤ/N`-modules on `U_étale`,

`i⁻¹ 𝓗om(μ_{N,U}, H) ≅ 𝓗om(μ_{N,Z}, i⁻¹ H)`,

that is, the inverse image of the Tate twist `H(-1)` is the Tate twist of the inverse image
(`Stacks.Kummer.twistNegOneModuleInverseImageIso`). In the Gysin step of relative purity,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), it identifies `i⁻¹(R¹ j_* j⁻¹ H)` with
`(i⁻¹ H)(-1)`.

The proof uses no tensor–hom adjunction of the inverse image. `𝓗om(μ, H)` with its evaluation
`𝓗om(μ, H) ⊗ μ ⟶ H` is an internal hom from `μ` to `H`
(`Stacks.ConstantSheaf.tensorHomBijective_moduleSheafHomEvaluation`); `μ_{N,U}` is étale-locally
free of rank one, hence dualizable (`Stacks.EtaleCohomology.etaleModuleDualExactPairing`); and the
inverse image is monoidal
(`Stacks.EtaleCohomology.etaleModuleInverseImageSheafPullbackMonoidal`). A monoidal functor
carries an internal hom out of a dualizable object to an internal hom
(`CategoryTheory.MonoidalCategory.tensorHomBijective_map`), and two internal homs out of one
object are canonically isomorphic compatibly with their evaluations. Finally
`i⁻¹ μ_{N,U} ≅ μ_{N,Z}` (`Stacks.Kummer.rootsOfUnityModuleInverseImageIso`), the comparison of
abelian sheaves `Stacks.Kummer.rootsOfUnityInverseImageIso` lifted along the fully faithful
forgetful functor from `ℤ/N`-modules.

## Main definitions

* `Stacks.Kummer.rootsOfUnityModuleInverseImageIso`: `π⁻¹ μ_{N,Y} ≅ μ_{N,X}` as sheaves of
  `ℤ/N`-modules, for `N` invertible on `Y`.
* `Stacks.Kummer.twistNegOneModuleInverseImageIso`: `i⁻¹ (H(-1)) ≅ (i⁻¹ H)(-1)`.

## Main results

* `Stacks.Kummer.exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso`: the isomorphism
  `i⁻¹ 𝓗om(μ_{N,U}, H) ≅ 𝓗om(i⁻¹ μ_{N,U}, i⁻¹ H)` compatible with the two evaluations.
* `Stacks.Kummer.twistNegOneModuleInverseImageIso_spec`: the isomorphism of the main definition is
  that one, followed by the identification `i⁻¹ μ_{N,U} ≅ μ_{N,Z}`.
* `Stacks.Kummer.twistNegOneModuleInverseImageIso_hom_naturality`: it is natural in `H`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open Stacks.EtaleCohomology Stacks.ConstantSheaf

universe u

namespace Stacks.Kummer

section RootsOfUnity

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (N : ℕ) [NeZero N]

/-- **`π⁻¹ μ_{N,Y} ≅ μ_{N,X}` as sheaves of `ℤ/N`-modules**, for `N` invertible on `Y`: the
comparison of abelian sheaves `Stacks.Kummer.rootsOfUnityInverseImageIso`, read through the
inverse image of the underlying abelian sheaves and lifted along the fully faithful forgetful
functor from sheaves of `ℤ/N`-modules. -/
def rootsOfUnityModuleInverseImageIso (hN : IsUnit ((N : ℕ) : Γ(Y, ⊤))) :
    (etaleModuleInverseImage.{u, 0} (ZMod N) π).obj (rootsOfUnityModule.{u, 0} Y N) ≅
      rootsOfUnityModule.{u, 0} X N :=
  (ArtinSchreier.etaleModuleForgetZModFullyFaithful X N).preimageIso
    (((etaleModuleUnderlyingAbelianInverseImageIso (ZMod N) π).app
        (rootsOfUnityModule.{u, 0} Y N)).symm ≪≫
      (etaleAbelianInverseImage.{u, 0} π).mapIso (rootsOfUnityModuleForgetIso.{u, 0} Y N) ≪≫
      rootsOfUnityInverseImageIso.{u, 0} π N hN ≪≫ (rootsOfUnityModuleForgetIso.{u, 0} X N).symm)

end RootsOfUnity

section Twist

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  etaleModuleInverseImageSheafPullbackMonoidal

variable {k : Type u} [Field k] {Z U : Scheme.{u}} (f : U ⟶ Spec (.of k)) (i : Z ⟶ U) (N : ℕ)
  [NeZero N]

include f in
omit [NeZero N] in
/-- `N` invertible in the field `k` is invertible on any `k`-scheme. -/
theorem isUnit_natCast_globalSections_of_isUnit_field (hN : IsUnit (N : k)) :
    IsUnit ((N : ℕ) : Γ(U, ⊤)) := by
  simpa only [map_natCast] using hN.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

include f in
/-- **`i⁻¹ 𝓗om(μ_{N,U}, H) ≅ 𝓗om(i⁻¹ μ_{N,U}, i⁻¹ H)`, compatibly with the evaluations**: the
inverse image is monoidal and `μ_{N,U}` is dualizable, so the inverse image of the internal hom
`𝓗om(μ_{N,U}, H)` with the inverse image of its evaluation is an internal hom from `i⁻¹ μ_{N,U}`
to `i⁻¹ H`, as is `𝓗om(i⁻¹ μ_{N,U}, i⁻¹ H)` with its evaluation. -/
theorem exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso (hN : IsUnit (N : k))
    (H : EtaleModules.{u, 0} (ZMod N) U) :
    ∃ e : (etaleModuleInverseImage.{u, 0} (ZMod N) i).obj
          (moduleSheafHom U.smallEtaleTopology (ZMod N) (rootsOfUnityModule.{u, 0} U N) H) ≅
        moduleSheafHom Z.smallEtaleTopology (ZMod N)
          ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (rootsOfUnityModule.{u, 0} U N))
          ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj H),
      e.hom ▷ (etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (rootsOfUnityModule.{u, 0} U N) ≫
          moduleSheafHomEvaluation Z.smallEtaleTopology (ZMod N)
            ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (rootsOfUnityModule.{u, 0} U N))
            ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj H) =
        Functor.LaxMonoidal.μ (etaleModuleInverseImage.{u, 0} (ZMod N) i) _ _ ≫
          (etaleModuleInverseImage.{u, 0} (ZMod N) i).map
            (moduleSheafHomEvaluation U.smallEtaleTopology (ZMod N)
              (rootsOfUnityModule.{u, 0} U N) H) := by
  have : NeZero (N : k) := ⟨hN.ne_zero⟩
  let := etaleModuleDualExactPairing (rootsOfUnityModule.{u, 0} U N) (by
    intro V
    obtain ⟨I, W, g, hcov, htriv⟩ := isFreeFiniteLocallyConstant_rootsOfUnityModule.{u, 0} f N V
    exact ⟨I, W, g, hcov, fun j => by
      obtain ⟨E, hfree, hfin, he⟩ := htriv j
      exact ⟨E, ⟨hfree, hfin⟩, he⟩⟩)
  exact exists_iso_whiskerRight_comp_of_tensorHomBijective _ _
    (tensorHomBijective_map (etaleModuleInverseImage.{u, 0} (ZMod N) i)
      (rootsOfUnityModule.{u, 0} U N) (etaleModuleDual (rootsOfUnityModule.{u, 0} U N))
      (tensorHomBijective_moduleSheafHomEvaluation U.smallEtaleTopology (ZMod N)
        (rootsOfUnityModule.{u, 0} U N) H))
    (tensorHomBijective_moduleSheafHomEvaluation Z.smallEtaleTopology (ZMod N)
      ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (rootsOfUnityModule.{u, 0} U N))
      ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj H))

/-- **The inverse image of the Tate twist is the Tate twist of the inverse image**:
`i⁻¹ (H(-1)) = i⁻¹ 𝓗om(μ_{N,U}, H) ≅ 𝓗om(μ_{N,Z}, i⁻¹ H) = (i⁻¹ H)(-1)` for `U` over a field `k`
in which `N` is invertible and any morphism `i : Z ⟶ U`. It is the isomorphism of
`Stacks.Kummer.exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso`, compatible with the
evaluations, followed by `i⁻¹ μ_{N,U} ≅ μ_{N,Z}`
(`Stacks.Kummer.rootsOfUnityModuleInverseImageIso`). -/
@[sga "4 XVIII 1.1.1" "i = -1"]
def twistNegOneModuleInverseImageIso (hN : IsUnit (N : k)) (H : EtaleModules.{u, 0} (ZMod N) U) :
    (etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (twistNegOneModule.{u, 0} U N H) ≅
      twistNegOneModule.{u, 0} Z N ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj H) :=
  (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H).choose ≪≫
    moduleSheafHomMapIso Z.smallEtaleTopology (ZMod N)
      (rootsOfUnityModuleInverseImageIso i N
        (isUnit_natCast_globalSections_of_isUnit_field f N hN)) (Iso.refl _)

/-- The isomorphism `Stacks.Kummer.twistNegOneModuleInverseImageIso` is the composite of an
isomorphism `i⁻¹ 𝓗om(μ_{N,U}, H) ≅ 𝓗om(i⁻¹ μ_{N,U}, i⁻¹ H)` compatible with the evaluations and
the identification `i⁻¹ μ_{N,U} ≅ μ_{N,Z}`. -/
theorem twistNegOneModuleInverseImageIso_spec (hN : IsUnit (N : k))
    (H : EtaleModules.{u, 0} (ZMod N) U) :
    ∃ e : (etaleModuleInverseImage.{u, 0} (ZMod N) i).obj
          (moduleSheafHom U.smallEtaleTopology (ZMod N) (rootsOfUnityModule.{u, 0} U N) H) ≅
        moduleSheafHom Z.smallEtaleTopology (ZMod N)
          ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (rootsOfUnityModule.{u, 0} U N))
          ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj H),
      (e.hom ▷ (etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (rootsOfUnityModule.{u, 0} U N) ≫
          moduleSheafHomEvaluation Z.smallEtaleTopology (ZMod N)
            ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj (rootsOfUnityModule.{u, 0} U N))
            ((etaleModuleInverseImage.{u, 0} (ZMod N) i).obj H) =
        Functor.LaxMonoidal.μ (etaleModuleInverseImage.{u, 0} (ZMod N) i) _ _ ≫
          (etaleModuleInverseImage.{u, 0} (ZMod N) i).map
            (moduleSheafHomEvaluation U.smallEtaleTopology (ZMod N)
              (rootsOfUnityModule.{u, 0} U N) H)) ∧
      twistNegOneModuleInverseImageIso f i N hN H = e ≪≫
        moduleSheafHomMapIso Z.smallEtaleTopology (ZMod N)
          (rootsOfUnityModuleInverseImageIso i N
            (isUnit_natCast_globalSections_of_isUnit_field f N hN)) (Iso.refl _) :=
  ⟨_, (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H).choose_spec, rfl⟩

/-- **The isomorphism `i⁻¹ 𝓗om(μ_{N,U}, H) ≅ 𝓗om(i⁻¹ μ_{N,U}, i⁻¹ H)` is natural in `H`**: both
composites are matched with `μ ≫ i⁻¹(ev) ≫ i⁻¹ w` by the bijection of the internal hom
`𝓗om(i⁻¹ μ_{N,U}, i⁻¹ H')`. -/
theorem inverseImage_moduleSheafHom_rootsOfUnityModule_iso_naturality (hN : IsUnit (N : k))
    {H H' : EtaleModules.{u, 0} (ZMod N) U} (w : H ⟶ H') :
    (etaleModuleInverseImage.{u, 0} (ZMod N) i).map
        (moduleSheafHomMap U.smallEtaleTopology (ZMod N) (𝟙 _) w) ≫
        (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H').choose.hom =
      (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H).choose.hom ≫
        moduleSheafHomMap Z.smallEtaleTopology (ZMod N) (𝟙 _)
          ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map w) := by
  let P := etaleModuleInverseImage.{u, 0} (ZMod N) i
  have hH := (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H).choose_spec
  have hH' := (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H').choose_spec
  refine (tensorHomBijective_moduleSheafHomEvaluation Z.smallEtaleTopology (ZMod N)
    (P.obj (rootsOfUnityModule.{u, 0} U N)) (P.obj H') _).injective ?_
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc, hH',
    moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation, reassoc_of% hH,
    Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp, ← Functor.map_comp,
    moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation]

/-- **The isomorphism `i⁻¹ (H(-1)) ≅ (i⁻¹ H)(-1)` is natural in `H`.** -/
theorem twistNegOneModuleInverseImageIso_hom_naturality (hN : IsUnit (N : k))
    {H H' : EtaleModules.{u, 0} (ZMod N) U} (w : H ⟶ H') :
    (etaleModuleInverseImage.{u, 0} (ZMod N) i).map (twistNegOneModuleMap.{u, 0} U N w) ≫
        (twistNegOneModuleInverseImageIso f i N hN H').hom =
      (twistNegOneModuleInverseImageIso f i N hN H).hom ≫
        twistNegOneModuleMap.{u, 0} Z N ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map w) := by
  have hcomm : ∀ {A A' : EtaleModules.{u, 0} (ZMod N) Z} (a : A' ⟶ A)
      {B B' : EtaleModules.{u, 0} (ZMod N) Z} (b : B ⟶ B'),
      moduleSheafHomMap Z.smallEtaleTopology (ZMod N) (𝟙 A) b ≫
          moduleSheafHomMap Z.smallEtaleTopology (ZMod N) a (𝟙 B') =
        moduleSheafHomMap Z.smallEtaleTopology (ZMod N) a (𝟙 B) ≫
          moduleSheafHomMap Z.smallEtaleTopology (ZMod N) (𝟙 A') b := by
    intro A A' a B B' b
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    let O := Z.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) V.unop
    have key : ∀ β : O.obj A ⟶ O.obj B, O.map a ≫ (O.map (𝟙 A) ≫ β ≫ O.map b) ≫ O.map (𝟙 B') =
        O.map (𝟙 A') ≫ (O.map a ≫ β ≫ O.map (𝟙 B)) ≫ O.map b := fun β => by
      simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        Category.assoc]
    exact key α
  let ρ := rootsOfUnityModuleInverseImageIso i N
    (isUnit_natCast_globalSections_of_isUnit_field f N hN)
  have e : ∀ H : EtaleModules.{u, 0} (ZMod N) U, (twistNegOneModuleInverseImageIso f i N hN H).hom =
      (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H).choose.hom ≫
        moduleSheafHomMap Z.smallEtaleTopology (ZMod N) ρ.inv (𝟙 _) := fun _ => rfl
  have e' : twistNegOneModuleMap.{u, 0} U N w =
      moduleSheafHomMap U.smallEtaleTopology (ZMod N) (𝟙 _) w := rfl
  have e'' : twistNegOneModuleMap.{u, 0} Z N ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map w) =
      moduleSheafHomMap Z.smallEtaleTopology (ZMod N) (𝟙 _)
        ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map w) := rfl
  rw [e, e, e', e'']
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ moduleSheafHomMap Z.smallEtaleTopology (ZMod N) ρ.inv (𝟙 _))
    (inverseImage_moduleSheafHom_rootsOfUnityModule_iso_naturality f i N hN w)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun z => (exists_inverseImage_moduleSheafHom_rootsOfUnityModule_iso f i N hN H).choose.hom ≫ z)
    (hcomm ρ.inv ((etaleModuleInverseImage.{u, 0} (ZMod N) i).map w))).trans
      (Category.assoc _ _ _).symm)

end Twist

end Stacks.Kummer

end
