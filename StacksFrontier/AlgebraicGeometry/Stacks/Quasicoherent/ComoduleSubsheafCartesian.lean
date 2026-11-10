module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianSubmodule
public import StacksFrontier.Algebra.Module.FaithfullyFlat.PreimageBaseChange
public import StacksFrontier.RingTheory.Flat.EqualizerBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ComoduleSubsheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers

/-!
# The comodule subsheaf is cartesian along flat arrows between affine objects

Let `ℱ` be a quasi-coherent module on the fppf site of a category fibred in groupoids `𝒳`,
`H ⊆ ℱ(u)` a submodule and `ℱ ∩ u_*H` the subsheaf of
`AlgebraicGeometry.FibredSite.comoduleSubsheaf`.  Suppose every object `x` over an affine scheme
has a universal pair `w ⟶ x`, `w ⟶ u` with `w` over an affine scheme (the affine objects of
`x ×_𝒳 u` are dominated by one of them, which is where quasi-separatedness of `𝒳` enters).  Then
along every arrow `φ : z ⟶ x` between objects over affine schemes which lies over a flat morphism
the comparison `Γ(z) ⊗_{Γ(x)} (ℱ ∩ u_*H)(x) ⟶ (ℱ ∩ u_*H)(z)` is an isomorphism.

## The argument

Over `x` the subsheaf is the preimage of `pr₂^*H`-span under `pr₁^*`, that is the kernel of
`ℱ(x) ⟶ ℱ(w)/Σ`.  The fibre product `w' = w ×_x z` (in the affine subcategory) carries the
universal pair of `z`, and `Γ(w') = Γ(z) ⊗_{Γ(x)} Γ(w)`; so the kernel over `z` is the kernel of
the base change of `ℱ(x) ⟶ ℱ(w)/Σ` along the flat map `Γ(x) ⟶ Γ(z)`, which is the base change of
the kernel.

## Main results

* `AlgebraicGeometry.FibredSite.isUniversalPair_pullback`: the universal pair of a fibre product.
* `AlgebraicGeometry.FibredSite.isIso_restrictionBaseChange_comoduleSubsheaf`: the cartesian
  property.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w

namespace AlgebraicGeometry.FibredSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type v} [Category.{w} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

attribute [local instance] objModule

open AlgebraicGeometry.Stack

section Pullback

variable {u x z w : 𝒳} (pr₁ : w ⟶ x) (φ : z ⟶ x) (hx : IsAffineOver B S hS (p.obj x))
  (hz : IsAffineOver B S hS (p.obj z)) (hw : IsAffineOver B S hS (p.obj w))

/-- The cospan `w ⟶ x ⟵ z` in the affine subcategory. -/
abbrev affineCospanFst : (⟨w, hw⟩ : AffineCategory B S hS p) ⟶ ⟨x, hx⟩ := ObjectProperty.homMk pr₁

/-- The cospan `w ⟶ x ⟵ z` in the affine subcategory. -/
abbrev affineCospanSnd : (⟨z, hz⟩ : AffineCategory B S hS p) ⟶ ⟨x, hx⟩ := ObjectProperty.homMk φ

include hp in
/-- **The universal pair of a fibre product.**  If `pr₁ : w ⟶ x`, `pr₂ : w ⟶ u` is universal and
`φ : z ⟶ x` is an arrow, all of `w`, `x`, `z` over affine schemes, then the fibre product
`w ×_x z` in the affine subcategory, with its projection to `z` and its projection to `w`
followed by `pr₂`, is a universal pair for `(z, u)`. -/
theorem isUniversalPair_pullback {pr₂ : w ⟶ u} (hpr : IsUniversalPair B S hS p pr₁ pr₂) :
    letI := AffineCategory.hasPullbacks B S hS p hp
    IsUniversalPair B S hS p
      (pullback.snd (affineCospanFst pr₁ hx hw) (affineCospanSnd φ hx hz)).hom
      ((pullback.fst (affineCospanFst pr₁ hx hw) (affineCospanSnd φ hx hz)).hom ≫ pr₂) := by
  let := AffineCategory.hasPullbacks B S hS p hp
  intro t c b ht
  obtain ⟨T, hT, hfac⟩ := hpr (c ≫ φ) b ht
  refine ⟨T, hT, fun t' g hg ht' => ?_⟩
  obtain ⟨r, hr₁, hr₂⟩ := hfac g hg ht'
  have hcond : (ObjectProperty.homMk r : (⟨t', ht'⟩ : AffineCategory B S hS p) ⟶ ⟨w, hw⟩) ≫
      affineCospanFst pr₁ hx hw =
      (ObjectProperty.homMk (g ≫ c) : (⟨t', ht'⟩ : AffineCategory B S hS p) ⟶ ⟨z, hz⟩) ≫
      affineCospanSnd φ hx hz :=
    ObjectProperty.hom_ext _ (by simpa [Category.assoc] using hr₁)
  have h₁ := congrArg (fun f => InducedCategory.Hom.hom f) (pullback.lift_fst _ _ hcond)
  have h₂ := congrArg (fun f => InducedCategory.Hom.hom f) (pullback.lift_snd _ _ hcond)
  rw [ObjectProperty.FullSubcategory.comp_hom] at h₁ h₂
  refine ⟨(pullback.lift _ _ hcond).hom, h₂, ?_⟩
  rwa [← Category.assoc, h₁]

end Pullback

section Cartesian

variable (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) {u : 𝒳}
  (H : Submodule (objRing B S hS p u) (F.val.obj (op u)))

include hp in
/-- **The comodule subsheaf over `z` is spanned by its restriction from `x`**, along an arrow
`φ : z ⟶ x` between objects over affine schemes lying over a flat morphism, when `x` has a
universal pair over an affine scheme. -/
theorem comoduleSubmodule_le_span (hF : F.IsQuasicoherentOnSite) {x z w : 𝒳}
    (φ : z ⟶ x) (hφ : Flat ((BigFppfOver.toScheme B S hS).map (p.map φ)))
    (hx : IsAffineOver B S hS (p.obj x)) (hz : IsAffineOver B S hS (p.obj z))
    (hw : IsAffineOver B S hS (p.obj w)) {pr₁ : w ⟶ x} {pr₂ : w ⟶ u}
    (hpr : IsUniversalPair B S hS p pr₁ pr₂) :
    comoduleSubmodule F H z ≤
      Submodule.span (objRing B S hS p z) (F.val.restrictₛₗ φ.op '' comoduleSubmodule F H x) := by
  let := AffineCategory.hasPullbacks B S hS p hp
  let a := affineCospanFst pr₁ hx hw
  let a' := affineCospanSnd φ hx hz
  let P := pullback a a'
  let w' : 𝒳 := P.obj
  have hw' : IsAffineOver B S hS (p.obj w') := P.property
  let k' : w' ⟶ w := (pullback.fst a a').hom
  let q : w' ⟶ z := (pullback.snd a a').hom
  have hcond : k' ≫ pr₁ = q ≫ φ :=
    congrArg (fun f => InducedCategory.Hom.hom f) (pullback.condition (f := a) (g := a'))
  have hpr' : IsUniversalPair B S hS p q (k' ≫ pr₂) :=
    isUniversalPair_pullback (hp := hp) pr₁ φ hx hz hw hpr
  let A := objRing B S hS p x
  let A' := objRing B S hS p z
  let C := objRing B S hS p w
  let C' := objRing B S hS p w'
  let : Algebra A A' := objAlgebra B S hS p φ
  let : Algebra A C := objAlgebra B S hS p pr₁
  let : Algebra C C' := objAlgebra B S hS p k'
  let : Algebra A' C' := objAlgebra B S hS p q
  let : Algebra A C' := objAlgebra B S hS p (k' ≫ pr₁)
  let T := p ⋙ BigFppfOver.toScheme B S hS
  have hmap : ∀ {a b c : 𝒳} (f : a ⟶ b) (g : b ⟶ c) (r : objRing B S hS p c),
      (T.map (f ≫ g)).appTop.hom r = (T.map f).appTop.hom ((T.map g).appTop.hom r) :=
    fun f g r => by rw [Functor.map_comp, Scheme.Hom.comp_appTop]; rfl
  have : IsScalarTower A C C' := IsScalarTower.of_algebraMap_eq (hmap k' pr₁)
  have : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun r => by
    change (T.map (k' ≫ pr₁)).appTop.hom r = _
    rw [hcond]; exact hmap q φ r
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x)) := hx
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj z)) := hz
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj w)) := hw
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj w')) := hw'
  have : Module.Flat A A' :=
    HasRingHomProperty.appTop (P := @Flat) ((BigFppfOver.toScheme B S hS).map (p.map φ)) hφ
  have hpb : IsPullback ((BigFppfOver.toScheme B S hS).map (p.map k'))
      ((BigFppfOver.toScheme B S hS).map (p.map q))
      ((BigFppfOver.toScheme B S hS).map (p.map pr₁))
      ((BigFppfOver.toScheme B S hS).map (p.map φ)) := by
    have := AffineCategory.preservesPullbacks_toScheme B S hS p hp
    exact Functor.map_isPullback (AffineCategory.toScheme B S hS p) (IsPullback.of_hasPullback a a')
  have : Algebra.IsPushout A C A' C' :=
    algebra_isPushout_appTop_of_isPullback hpb rfl rfl rfl rfl
  have : Algebra.IsPushout A A' C C' := Algebra.IsPushout.symm inferInstance
  let : Module A (F.val.obj (op w)) := Module.compHom _ (algebraMap A C)
  have : IsScalarTower A C (F.val.obj (op w)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module A (F.val.obj (op z)) := Module.compHom _ (algebraMap A A')
  have : IsScalarTower A A' (F.val.obj (op z)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module A' (F.val.obj (op w')) := Module.compHom _ (algebraMap A' C')
  let : Module C (F.val.obj (op w')) := Module.compHom _ (algebraMap C C')
  let : Module A (F.val.obj (op w')) := Module.compHom _ (algebraMap A C')
  have : IsScalarTower A' C' (F.val.obj (op w')) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower C C' (F.val.obj (op w')) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower A A' (F.val.obj (op w')) := IsScalarTower.of_algebraMap_smul fun r m => by
    change algebraMap A' C' (algebraMap A A' r) • m = algebraMap A C' r • m
    rw [← IsScalarTower.algebraMap_apply]
  have : IsScalarTower A C (F.val.obj (op w')) := IsScalarTower.of_algebraMap_smul fun r m => by
    change algebraMap C C' (algebraMap A C r) • m = algebraMap A C' r • m
    rw [← IsScalarTower.algebraMap_apply]
  let rM := restrictionLinear F φ
  let S₀ := restrictedSpan F pr₂ H
  let N := S₀.restrictScalars A
  let ψ : F.val.obj (op x) →ₗ[A] F.val.obj (op w) ⧸ N := N.mkQ ∘ₗ restrictionLinear F pr₁
  let S₁ := restrictedSpan F (k' ≫ pr₂) H
  let N' := S₁.restrictScalars A'
  let ψ' : F.val.obj (op z) →ₗ[A'] F.val.obj (op w') ⧸ N' := N'.mkQ ∘ₗ restrictionLinear F q
  let rP : F.val.obj (op w) →ₗ[A] F.val.obj (op w') := (restrictionLinear F k').restrictScalars A
  have hNN' : ∀ n ∈ N, rP n ∈ N' := fun n hn => by
    change F.val.restrictₛₗ k'.op n ∈ restrictedSpan F (k' ≫ pr₂) H
    rw [restrictedSpan_comp]
    exact map_mem_restrictedSpan F k' hn
  let τ : (F.val.obj (op w) ⧸ N) →ₗ[A] (F.val.obj (op w') ⧸ N') :=
    N.liftQ ((N'.mkQ.restrictScalars A) ∘ₗ rP) fun n hn => by
      simpa using (Submodule.Quotient.mk_eq_zero N').2 (hNN' n hn)
  have hβ := LinearMap.bijective_liftBaseChange_restrictScalars_of_isPushout (R := A) (S := A')
    (A := C) (B := C') (restrictionLinear F k')
    (bijective_liftBaseChange_of_eq_restriction F hF k' hw hw' _ fun _ => rfl)
  have hN : N' ≤ Submodule.span A' (rP '' N) := fun y hy =>
    Submodule.mem_span_image_of_isPushout A A' C C' (restrictionLinear F k') S₀
      (by rwa [← restrictedSpan_comp] : y ∈ restrictedSpan F k' S₀)
  have hτinj := LinearMap.injective_liftBaseChange_of_quotient rP hβ N N' hN τ fun _ => rfl
  have hcomm : ∀ m, ψ' (rM m) = τ (ψ m) := by
    intro m
    change N'.mkQ (F.val.restrictₛₗ q.op (F.val.restrictₛₗ φ.op m)) =
      N'.mkQ (F.val.restrictₛₗ k'.op (F.val.restrictₛₗ pr₁.op m))
    rw [← restrictₛₗ_comp_apply, ← restrictₛₗ_comp_apply, hcond]
  have hker := LinearMap.ker_le_span_image_ker_of_flat rM
    (bijective_liftBaseChange_of_eq_restriction F hF φ hx hz rM fun _ => rfl).2 ψ τ hτinj ψ' hcomm
  intro g hg
  have hg' : g ∈ LinearMap.ker ψ' :=
    (Submodule.Quotient.mk_eq_zero N').2
      ((mem_comoduleSubmodule_iff_of_isUniversalPair hF hpr' hw').1 hg)
  refine Submodule.span_mono ?_ (hker hg')
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, (mem_comoduleSubmodule_iff_of_isUniversalPair hF hpr hw).2
    ((Submodule.Quotient.mk_eq_zero N).1 hm), rfl⟩

end Cartesian

end AlgebraicGeometry.FibredSite

end
