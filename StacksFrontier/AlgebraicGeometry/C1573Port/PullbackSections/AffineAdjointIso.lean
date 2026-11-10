module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective
public import StacksFrontier.RingTheory.C1573Port.IsBaseChangeRingEquiv
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing

namespace AlgebraicGeometry.ModuleCat.ExtendScalars.C1573
end AlgebraicGeometry.ModuleCat.ExtendScalars.C1573
namespace AlgebraicGeometry.Scheme.Modules.C1573
end AlgebraicGeometry.Scheme.Modules.C1573
namespace AlgebraicGeometry.C1573
end AlgebraicGeometry.C1573

/-!
# Detecting that the adjoint of a map into a direct image is an isomorphism

Let `f : X ⟶ T` be a morphism of schemes with `T` affine, `M` a module over `Γ(T, ⊤)` with
associated sheaf `M̃`, and `γ : M̃ ⟶ f_*N` a morphism of `𝒪_T`-modules.  Its adjoint
`f^*M̃ ⟶ N` is an isomorphism as soon as, over every affine open `W` of `X`, the map

`Γ(X, W) ⊗_{Γ(T, ⊤)} M ⟶ N(W),  a ⊗ m ↦ a · γ(m)|_W`

is bijective.  Over `W` the sections of `f^*M̃` are `Γ(X, W) ⊗ M` by Stacks 01I9, compatibly
with the pullback of sections, and a morphism of `𝒪_X`-modules which is bijective over every
affine open is an isomorphism, the affine opens forming a basis.

## Main results

* `AlgebraicGeometry.Scheme.Modules.C1573.isIso_of_bijective_app_affineOpens`: a morphism of
  `𝒪_X`-modules bijective on the sections over every affine open is an isomorphism.
* `AlgebraicGeometry.C1573.isIso_homEquiv_symm_of_bijective_affineOpens`: **the criterion.**

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry.C1573
/-- Induction on the elements of an extension of scalars: a property holding at the pure
tensors and stable under sums holds everywhere. -/
theorem ModuleCat.ExtendScalars.C1573.induction_on {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {M : ModuleCat.{u} R} (P : (ModuleCat.extendScalars φ).obj M → Prop)
    (htmul : ∀ (s : S) (m : M), P (s ⊗ₜ[R,φ] m)) (hadd : ∀ x y, P x → P y → P (x + y))
    (x : (ModuleCat.extendScalars φ).obj M) : P x :=
  TensorProduct.inductionOn x htmul hadd

open scoped ChangeOfRings in
/-- **A map out of an extension of scalars is bijective as soon as its restriction along `1 ⊗ -`
exhibits the target as a base change.** -/
theorem ModuleCat.ExtendScalars.C1573.bijective_of_isBaseChange {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (ψ : (ModuleCat.extendScalars φ.hom).obj M ⟶ N)
    (hb : letI := φ.hom.toAlgebra
      letI : Module R N := Module.compHom _ φ.hom
      haveI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      ∃ ξ : M →ₗ[R] N, (∀ m, ξ m = ψ ((1 : S) ⊗ₜ[R, φ.hom] m)) ∧ IsBaseChange S ξ) :
    Function.Bijective ψ := by
  let := φ.hom.toAlgebra
  let : Module R N := Module.compHom _ φ.hom
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ξ, hξ, hb⟩ := hb
  exact IsBaseChange.C1573.bijective_of_comp_eq (TensorProduct.isBaseChange R M S) hb
    (ψ.hom : TensorProduct R S M →ₗ[S] N) fun m => (hξ m).symm

namespace Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules.C1573
/-- **A morphism of `𝒪_X`-modules which is bijective on the sections over every affine open is an
isomorphism.**  The affine opens contained in an open `U` cover it, so the morphism is locally
injective and locally surjective. -/
theorem C1573.isIso_of_bijective_app_affineOpens {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Bijective (φ.app U.1)) : IsIso φ := by
  have hcov : ∀ (U : X.Opens) (S : Sieve U),
      (∀ (W : X.Opens) (i : W ⟶ U), IsAffineOpen W → S i) →
        S ∈ Opens.grothendieckTopology X U := by
    intro U S hS x hx
    obtain ⟨W, hW, hxW, hWU⟩ :=
      (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
    exact ⟨W, homOfLE hWU, hS W (homOfLE hWU) hW, hxW⟩
  have hinj : PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) φ.val := by
    constructor
    intro Z x y hxy
    refine hcov Z.unop _ fun W i hW => ?_
    refine (h ⟨W, hW⟩).1 ?_
    have hx := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) i.op x
    have hy := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) i.op y
    exact hx.trans ((congrArg (((PresheafOfModules.toPresheaf _).obj N.val).map i.op) hxy).trans
      hy.symm)
  have hsurj : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) φ.val := by
    constructor
    intro Z s
    refine hcov Z _ fun W i hW => ?_
    obtain ⟨t, ht⟩ := (h ⟨W, hW⟩).2 (((PresheafOfModules.toPresheaf _).obj N.val).map i.op s)
    exact ⟨t, ht⟩
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective φ

end Scheme.Modules

/-- A linear map is bijective as soon as its precomposition with an isomorphism is. -/
private theorem ModuleCat.C1573.bijective_of_bijective_iso_hom_comp {R : Type u} [Ring R]
    {A B C : ModuleCat.{u} R} (e : A ≅ B) (g : B ⟶ C)
    (h : Function.Bijective (e.hom ≫ g)) : Function.Bijective g := by
  have h3 : ⇑g = ⇑(e.hom ≫ g) ∘ e.inv := by
    funext x
    change _ = g (e.hom (e.inv x))
    rw [← ConcreteCategory.comp_apply e.inv e.hom, e.inv_hom_id, ModuleCat.id_apply]
  rw [h3]
  exact h.comp (ConcreteCategory.bijective_of_isIso e.inv)

/-- Over an affine open `W`, the adjoint of `γ : F ⟶ f_*N` sends `1 ⊗ s` in the base change of
the global sections of `F` to the restriction `γ(s)|_W`. -/
private theorem C1573.affinePullbackSectionsBaseChangeIso_hom_comp_one_tmul {X T : Scheme.{u}}
    [IsAffine T] (f : X ⟶ T) (F : T.Modules) [F.IsQuasicoherent] (N : X.Modules)
    (γ : F ⟶ (Scheme.Modules.pushforward f).obj N) (W : X.affineOpens) (s : Γ(F, ⊤)) :
    ((affinePullbackSectionsBaseChangeIso f F (isAffineOpen_top T) W.2
        (le_top : W.1 ≤ f ⁻¹ᵁ ⊤)).hom ≫ ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap
          (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm γ) W.1))
      ((1 : Γ(X, W.1)) ⊗ₜ[Γ(T, ⊤), (f.appLE ⊤ W.1 le_top).hom] s) =
      N.presheaf.map (homOfLE (le_top : W.1 ≤ f ⁻¹ᵁ ⊤)).op (γ.app ⊤ s) := by
  set ψ := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm γ with hψ
  have hγ : γ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _ ≫
      (Scheme.Modules.pushforward f).map ψ := by
    have h := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit F N ψ
    rwa [hψ, Equiv.apply_symm_apply] at h
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg (ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap ψ W.1))
    (affinePullbackSectionsBaseChangeIso_one_tmul f F (isAffineOpen_top T) W.2
      (le_top : W.1 ≤ f ⁻¹ᵁ ⊤) s)).trans ?_
  change ψ.app W.1 _ = _
  rw [hγ]
  exact NatTrans.naturality_apply ψ.mapPresheaf _ _

/-- The adjoint of `γ : M̃ ⟶ f_*N` is an isomorphism as soon as, over every affine open `W`, the
adjoint section map precomposed with the base change isomorphism is bijective. -/
private theorem C1573.isIso_homEquiv_symm_of_bijective_comp {X T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ T) (M : ModuleCat.{u} Γ(T, ⊤)) (N : X.Modules)
    [((Stacks.Coherent.affineTilde T).obj M).IsQuasicoherent]
    (γ : (Stacks.Coherent.affineTilde T).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (h : ∀ W : X.affineOpens, Function.Bijective
      ((affinePullbackSectionsBaseChangeIso f ((Stacks.Coherent.affineTilde T).obj M)
        (isAffineOpen_top T) W.2 (le_top : W.1 ≤ f ⁻¹ᵁ ⊤)).hom ≫
        ModuleCat.ofHom (Scheme.Modules.sectionsLinearMap
          (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm γ) W.1))) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm γ) :=
  Scheme.Modules.C1573.isIso_of_bijective_app_affineOpens _ fun W =>
    ModuleCat.C1573.bijective_of_bijective_iso_hom_comp _ _ (h W)

/-- **The adjoint of a map from an associated sheaf into a direct image is an isomorphism if it
is so on the base change of sections over every affine open.**  Let `f : X ⟶ T` with `T` affine,
`M` a `Γ(T, ⊤)`-module and `γ : M̃ ⟶ f_*N`.  Suppose that for every affine open `W` of `X` some
`Γ(X, W)`-linear map `Θ_W : Γ(X, W) ⊗ Γ(M̃, ⊤) ⟶ N(W)` sending `1 ⊗ s` to `γ(s)|_W` is bijective.
Then the adjoint `f^*M̃ ⟶ N` of `γ` is an isomorphism. -/
theorem C1573.isIso_homEquiv_symm_of_bijective_affineOpens {X T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ T) (M : ModuleCat.{u} Γ(T, ⊤)) (N : X.Modules)
    (γ : (Stacks.Coherent.affineTilde T).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (Θ : ∀ W : X.affineOpens, (ModuleCat.extendScalars (f.appLE ⊤ W.1 le_top).hom).obj
        (ModuleCat.of Γ(T, ⊤) Γ((Stacks.Coherent.affineTilde T).obj M, ⊤)) ⟶
      ModuleCat.of Γ(X, W.1) Γ(N, W.1))
    (hΘ : ∀ (W : X.affineOpens) (s : Γ((Stacks.Coherent.affineTilde T).obj M, ⊤)),
      Θ W ((1 : Γ(X, W.1)) ⊗ₜ[Γ(T, ⊤), (f.appLE ⊤ W.1 le_top).hom] s) =
        N.presheaf.map (homOfLE (le_top : W.1 ≤ f ⁻¹ᵁ ⊤)).op (γ.app ⊤ s))
    (hbij : ∀ W, Function.Bijective (Θ W)) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm γ) := by
  have := Stacks.Coherent.affineTilde_quasicoherent T M
  refine C1573.isIso_homEquiv_symm_of_bijective_comp f M N γ fun W => ?_
  convert hbij W using 3
  refine ModuleCat.ExtendScalars.hom_ext_one_tmul (f.appLE ⊤ W.1 le_top).hom fun s => ?_
  exact (C1573.affinePullbackSectionsBaseChangeIso_hom_comp_one_tmul f _ N γ W s).trans
    (hΘ W s).symm

/-- **The adjoint of a map from an associated sheaf into a direct image is an isomorphism if its
restrictions to the affine opens are base changes.**  Let `f : X ⟶ T` with `T` affine, `M` a
`Γ(T, ⊤)`-module and `γ : M̃ ⟶ f_*N`.  Suppose that for every affine open `W` of `X` the map
`Γ(M̃, ⊤) ⟶ N(W)`, `s ↦ γ(s)|_W`, exhibits `N(W)` as the base change of `Γ(M̃, ⊤)` along
`f^♯ : Γ(T, ⊤) ⟶ Γ(X, W)`.  Then the adjoint `f^*M̃ ⟶ N` of `γ` is an isomorphism. -/
theorem C1573.isIso_homEquiv_symm_of_isBaseChange {X T : Scheme.{u}} [IsAffine T]
    (f : X ⟶ T) (M : ModuleCat.{u} Γ(T, ⊤)) (N : X.Modules)
    (γ : (Stacks.Coherent.affineTilde T).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (h : ∀ W : X.affineOpens,
      letI := (f.appLE ⊤ W.1 le_top).hom.toAlgebra
      letI : Module Γ(T, ⊤) (ModuleCat.of Γ(X, W.1) Γ(N, W.1)) :=
        Module.compHom _ (f.appLE ⊤ W.1 le_top).hom
      haveI : IsScalarTower Γ(T, ⊤) Γ(X, W.1) (ModuleCat.of Γ(X, W.1) Γ(N, W.1)) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      ∃ ξ : ModuleCat.of Γ(T, ⊤) Γ((Stacks.Coherent.affineTilde T).obj M, ⊤) →ₗ[Γ(T, ⊤)]
          ModuleCat.of Γ(X, W.1) Γ(N, W.1),
        (∀ s, ξ s = N.presheaf.map (homOfLE (le_top : W.1 ≤ f ⁻¹ᵁ ⊤)).op (γ.app ⊤ s)) ∧
        IsBaseChange Γ(X, W.1) ξ) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm γ) := by
  have := Stacks.Coherent.affineTilde_quasicoherent T M
  refine C1573.isIso_homEquiv_symm_of_bijective_comp f M N γ fun W => ?_
  refine ModuleCat.ExtendScalars.C1573.bijective_of_isBaseChange (f.appLE ⊤ W.1 le_top) _ ?_
  obtain ⟨ξ, hξ, hb⟩ := h W
  exact ⟨ξ, fun s => (hξ s).trans
    (C1573.affinePullbackSectionsBaseChangeIso_hom_comp_one_tmul f _ N γ W s).symm, hb⟩

end AlgebraicGeometry

end

