module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.VeryAmpleGlue.TwistPullback
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic

/-!
# Surjectivity of a map `f^* F ⟶ N` onto an invertible module, read on sections

Let `f : X ⟶ S` be a morphism of schemes, `F` an `𝒪_S`-module, `N` an invertible `𝒪_X`-module and
`u : F ⟶ f_* N` a map of `𝒪_S`-modules, with adjoint `ū : f^* F ⟶ N`. Then `ū` is surjective if
and only if every point `x` of `X` lies in the nonvanishing locus of `u(s) ∈ Γ(f⁻¹V, N)` for some
section `s` of `F` over an affine open `V` of `S` containing `f(x)`.

## Main results

* `Stacks.Tag01VMVeryAmple.adjoint_app_unit`: the adjoint `ū` carries `η(s)` to `u(s)`.
* `Stacks.Tag01VMVeryAmple.epi_adjoint_of_forall_mem_nonvanishingLocusOn`: the converse
  direction, with no condition on the open `V`.
* `Stacks.Tag01VMVeryAmple.exists_mem_nonvanishingLocusOn_of_epi_adjoint`: **the forward
  direction**, with `V` affine.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn)
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.Tag01VMVeryAmple

variable {X S : Scheme.{u}} (f : X ⟶ S) {F : S.Modules} {N : X.Modules}

/-- **The adjoint of `u : F ⟶ f_* N` carries the pullback-unit image of a section `s` of `F`
to `u(s)`.** -/
theorem adjoint_app_unit (u : F ⟶ (Scheme.Modules.pushforward f).obj N) (V : S.Opens)
    (s : Γ(F, V)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F N).symm u).app (f ⁻¹ᵁ V)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V s) =
      u.app V s := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit F N
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F N).symm u)
  rw [Equiv.apply_symm_apply] at h
  conv_rhs => rw [h]
  rfl

/-- **The adjoint of `u : F ⟶ f_* N` is an epimorphism onto the invertible module `N`** as soon as
every point of `X` lies in the nonvanishing locus of `u(s)` for a section `s` of `F` over some
open of `S`. -/
theorem epi_adjoint_of_forall_mem_nonvanishingLocusOn [Stacks.Ample.IsInvertibleModule X N]
    (u : F ⟶ (Scheme.Modules.pushforward f).obj N)
    (h : ∀ x : X, ∃ (V : S.Opens) (s : Γ(F, V)),
      x ∈ nonvanishingLocusOn N (f ⁻¹ᵁ V) (u.app V s)) :
    Epi (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F N).symm u) := by
  refine Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn _ fun x => ?_
  obtain ⟨V, s, hx⟩ := h x
  refine ⟨f ⁻¹ᵁ V, ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V s, ?_⟩
  rwa [adjoint_app_unit]

/-- The germ at a point of `f⁻¹V` of the image under `ū` of a restriction of the pullback-unit
image of a section `s` of `F` over `V` is the germ of `u(s)`. -/
theorem germ_adjoint_restrict_unit (u : F ⟶ (Scheme.Modules.pushforward f).obj N)
    {V : S.Opens} {W : X.Opens} (hW : W ≤ f ⁻¹ᵁ V) (s : Γ(F, V)) (x : X) (hx : x ∈ W) :
    (N.presheaf.germ W x hx).hom
        ((((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F N).symm u).app W
          (((Scheme.Modules.pullback f).obj F).presheaf.map (homOfLE hW).op
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app V s))) =
      (N.presheaf.germ (f ⁻¹ᵁ V) x (hW hx)).hom (u.app V s) := by
  rw [← adjoint_app_unit f u V s,
    ← TopCat.Presheaf.germ_res_apply (C := Ab.{u}) N.presheaf (homOfLE hW) x hx]
  congr 1
  exact PresheafOfModules.naturality_apply
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F N).symm u).val (homOfLE hW).op _

/-- **If the adjoint `ū : f^* F ⟶ N` of `u : F ⟶ f_* N` is an epimorphism onto the invertible
module `N`, then every point `x` of `X` lies in the nonvanishing locus of `u(s)` for a section `s`
of `F` over an affine open of `S` containing `f(x)`.** -/
theorem exists_mem_nonvanishingLocusOn_of_epi_adjoint [Stacks.Ample.IsInvertibleModule X N]
    (u : F ⟶ (Scheme.Modules.pushforward f).obj N)
    [hepi : Epi (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F N).symm u)]
    (x : X) :
    ∃ (V : S.Opens) (_ : IsAffineOpen V) (s : Γ(F, V)),
      x ∈ nonvanishingLocusOn N (f ⁻¹ᵁ V) (u.app V s) := by
  set ub := ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv F N).symm u with hub
  have : @Epi (SheafOfModules.{u} X.ringCatSheaf) _ _ _ ub := hepi
  suffices H : ∃ (V : S.Opens) (s : Γ(F, V)), x ∈ nonvanishingLocusOn N (f ⁻¹ᵁ V) (u.app V s) by
    obtain ⟨V, s, hx⟩ := H
    have hxV : f x ∈ V := hx.1
    obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hV'V⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open hxV V.2
    have hle : V' ≤ V := hV'V
    have hxV'' : x ∈ f ⁻¹ᵁ V' := hxV'
    refine ⟨V', hV', F.presheaf.map (homOfLE hle).op s, hxV'', ?_⟩
    have e : u.app V' (F.presheaf.map (homOfLE hle).op s) =
        N.presheaf.map (homOfLE (f.preimage_mono hle)).op (u.app V s) :=
      ConcreteCategory.congr_hom (u.mapPresheaf.naturality (homOfLE hle).op) s
    rw [e]
    have h4 := TopCat.Presheaf.germ_res_apply (C := Ab.{u}) N.presheaf
      (homOfLE (f.preimage_mono hle)) x hxV'' (show Γ(N, f ⁻¹ᵁ V) from u.app V s)
    convert hx.2 using 1
    exact iff_of_eq (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul N x) h4)
  by_contra hcon
  push Not at hcon
  have hvan : ∀ (V : S.Opens) (s : Γ(F, V)) (hxV : x ∈ f ⁻¹ᵁ V),
      (N.presheaf.germ (f ⁻¹ᵁ V) x hxV).hom (u.app V s) ∈ Stacks.ModuleStalk.maximalSmul N x :=
    fun V s hxV => of_not_not fun hne => hcon V s ⟨hxV, hne⟩
  obtain ⟨W, hxW, ⟨t⟩⟩ := Stacks.SectionProduct.exists_trivialization_at N x
  have hb := Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis t hxW
  obtain ⟨Sv, hSv, hS⟩ := Stacks.SheafOfModules.EpiMono.exists_covering_of_epi ub
    (V := W) (Stacks.NonvanishingOpen.basis t)
  obtain ⟨W₁, i₁, hi₁, hxW₁⟩ := hSv x hxW
  obtain ⟨m, hm⟩ := hS i₁ hi₁
  obtain ⟨W₂, i₂, hxW₂, hspan⟩ := Stacks.PullbackUnitGenerators.exists_mem_span
    f.toLRSHom.toShHom F (op W₁) m x hxW₁
  let Φ : Γ((Scheme.Modules.pullback f).obj F, W₂) →+
      TopCat.Presheaf.stalk (C := Ab.{u}) N.presheaf x :=
    (N.presheaf.germ W₂ x hxW₂).hom.comp (ub.app W₂).hom
  have hΦsmul : ∀ (c : Γ(X, W₂)) (y : Γ((Scheme.Modules.pullback f).obj F, W₂)),
      Φ (c • y) = (X.presheaf.germ W₂ x hxW₂).hom c • Φ y := by
    intro c y
    change (N.presheaf.germ W₂ x hxW₂).hom (ub.app W₂ (c • y)) = _
    rw [Scheme.Modules.Hom.app_smul, Stacks.ModuleStalk.germ_smul]
    rfl
  have key : ∀ y ∈ (Stacks.SheafOfModules.spanSubmodule
      ((modulePullback f.toLRSHom.toShHom).obj F)
      (Stacks.PullbackUnitGenerators.unitSections f.toLRSHom.toShHom F)).obj (op W₂),
      (N.presheaf.germ W₂ x hxW₂).hom (ub.app W₂ y) ∈ Stacks.ModuleStalk.maximalSmul N x := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨Z, g, z, ⟨V, g', s, rfl⟩, rfl⟩ := hy
      have hle : W₂ ≤ f ⁻¹ᵁ V.unop := (g' ≫ g).unop.le
      have h3 := hvan V.unop s (hle hxW₂)
      rw [← germ_adjoint_restrict_unit f u hle s x hxW₂] at h3
      convert h3 using 3
      rw [← PresheafOfModules.map_comp_apply]
      rfl
    | zero =>
      refine (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul N x) (map_zero Φ)).mpr ?_
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      refine (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul N x) (map_add Φ y z)).mpr ?_
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      refine (congrArg (· ∈ Stacks.ModuleStalk.maximalSmul N x) (hΦsmul c y)).mpr ?_
      exact Submodule.smul_mem _ _ hy
  have hfin := key _ hspan
  have e2 : ub.app W₂ (((modulePullback f.toLRSHom.toShHom).obj F).val.map i₂.op m) =
      N.presheaf.map (i₂ ≫ i₁).op (Stacks.NonvanishingOpen.basis t) := by
    refine (PresheafOfModules.naturality_apply ub.val i₂.op m).trans ?_
    change N.presheaf.map i₂.op (ub.app W₁ m) = _
    rw [show ub.app W₁ m = N.presheaf.map i₁.op (Stacks.NonvanishingOpen.basis t) from hm,
      op_comp, Functor.map_comp]
    rfl
  rw [e2, TopCat.Presheaf.germ_res_apply (C := Ab.{u}) N.presheaf] at hfin
  exact hb hfin

end Stacks.Tag01VMVeryAmple

end
