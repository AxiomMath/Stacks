module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityPowMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The transition maps of the Tate twist

Let `N' = ℓN`. A morphism `G' ⟶ G` from a sheaf of `ℤ/N'`-modules to the restriction of
scalars of a sheaf of `ℤ/N`-modules induces `𝓗om(μ_{N'}, G') ⟶ 𝓗om(μ_N, G)`. It is the
composite of `𝓗om(μ_{N'}, G') ⟶ 𝓗om(μ_{N'}, G)` with the inverse of precomposition with the
`ℓ`-th power map `p : μ_{N'} ⟶ μ_N`. Precomposition with `p`,
`𝓗om_{ℤ/N}(μ_N, G) ⟶ 𝓗om_{ℤ/N'}(μ_{N'}, G)`, is an isomorphism: over an étale scheme carrying a
primitive `N'`-th root of unity `ζ` it is evaluation at `ζ^ℓ = p(ζ)` on the left and at `ζ` on
the right (`Stacks.Kummer.bijective_twistNegOneModuleEvalRoot`), and such schemes cover.

## Main definitions

* `Stacks.Kummer.rootsOfUnityModulePowMap`: `p` as a morphism of sheaves of `ℤ/N'`-modules.
* `Stacks.Kummer.twistNegOnePrecompPow`: precomposition with `p`.
* `Stacks.Kummer.twistNegOneModuleTransition`: the transition map
  `𝓗om(μ_{N'}, G') ⟶ 𝓗om(μ_N, G)` attached to `G' ⟶ G`.

## Main results

* `Stacks.Kummer.isIso_twistNegOnePrecompPow`: precomposition with `p` is an isomorphism over a
  field in which `N'` is invertible.
* `Stacks.Kummer.twistNegOneModuleTransition_comp_precompPow`: the transition followed by
  precomposition with `p` is postcomposition with `G' ⟶ G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.Kummer

variable (X : Scheme.{u}) (ℓ N N' : ℕ) (hN : ℓ * N = N') [NeZero N] [NeZero N']

omit [NeZero N] in
/-- An element killed by `N` is acted on by `a` as by `a % N`. -/
theorem nsmul_eq_mod_nsmul_of_nsmul_eq_zero {M : Type*} [AddCommGroup M] {x : M}
    (hx : N • x = 0) (a : ℕ) : a • x = (a % N) • x := by
  conv_lhs => rw [← Nat.mod_add_div a N, add_nsmul, mul_comm, mul_smul, hx, smul_zero, add_zero]

omit [NeZero N] in
/-- A section of `μ_N` is killed by `N`. -/
theorem nsmul_rootsOfUnitySheaf_apply (U : (X.Etale)ᵒᵖ)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X N).obj.obj U)) : N • s = 0 := by
  have h := sheaf_nsmul_hom_app_apply X (𝟙 (rootsOfUnitySheaf.{u, v} X N)) N U s
  rwa [nsmul_id_rootsOfUnitySheaf_univ, eq_comm] at h

/-- `N` divides `N' = ℓN`. -/
theorem dvd_of_mul_eq {ℓ N N' : ℕ} (hN : ℓ * N = N') : N ∣ N' := ⟨ℓ, by rw [← hN, mul_comm]⟩

/-- Restriction of scalars from `ℤ/N` to `ℤ/N'`, `N' = ℓN`. -/
abbrev zmodRestrict (ℓ N N' : ℕ) (hN : ℓ * N = N') :
    ModuleCat.{max (u + 1) v} (ZMod N) ⥤ ModuleCat.{max (u + 1) v} (ZMod N') :=
  ModuleCat.restrictScalars (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N))

/-- **The `ℓ`-th power map `μ_{ℓN} ⟶ μ_N` of sheaves of `ℤ/ℓN`-modules**, `μ_N` being a
`ℤ/ℓN`-module by restriction of scalars. -/
def rootsOfUnityModulePowMap :
    rootsOfUnityModule.{u, v} X N' ⟶
      (sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj
        (rootsOfUnityModule.{u, v} X N) :=
  ⟨{ app := fun U => ModuleCat.ofHom (X := (rootsOfUnityModule.{u, v} X N').obj.obj U)
        (Y := ((sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj
          (rootsOfUnityModule.{u, v} X N)).obj.obj U)
        { toFun := fun s => (rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.app U s
          map_add' := fun a b => map_add ((rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.app U).hom a b
          map_smul' := fun a s => by
            have hc : (ZMod.castHom (dvd_of_mul_eq hN) (ZMod N) a).val = a.val % N := by
              rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
            refine (congrArg ((rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.app U)
              (rootsOfUnityModule_smul (op (unop U)) a s)).trans ?_
            refine (map_nsmul ((rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.app U).hom
              a.val s).trans ?_
            refine (nsmul_eq_mod_nsmul_of_nsmul_eq_zero N
              (nsmul_rootsOfUnitySheaf_apply X N U _) a.val).trans ?_
            rw [← hc]
            exact (rootsOfUnityModule_smul (N := N) (op (unop U)) _ _).symm }
     naturality := fun U V g => by
       ext s
       exact ConcreteCategory.congr_hom
         ((rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.naturality g) s }⟩

variable (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v} (ZMod N)))

/-- **Precomposition with the `ℓ`-th power map**, `𝓗om_{ℤ/N}(μ_N, G) ⟶ 𝓗om_{ℤ/ℓN}(μ_{ℓN}, G)`,
the source read as a sheaf of `ℤ/ℓN`-modules by restriction of scalars: a local morphism
`β : μ_N|_U ⟶ G|_U` goes to `p|_U ≫ β`. -/
def twistNegOnePrecompPow :
    (sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj
        (twistNegOneModule.{u, v} X N G) ⟶
      Stacks.ConstantSheaf.moduleSheafHom X.smallEtaleTopology (ZMod N')
        (rootsOfUnityModule.{u, v} X N')
        ((sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj G) :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (X := ((sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj
          (twistNegOneModule.{u, v} X N G)).obj.obj U)
        (Y := (Stacks.ConstantSheaf.moduleSheafHom X.smallEtaleTopology (ZMod N')
          (rootsOfUnityModule.{u, v} X N')
          ((sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj G)).obj.obj U)
        { toFun := fun β => (X.smallEtaleTopology.overPullback _ U.unop).map
              (rootsOfUnityModulePowMap.{u, v} X ℓ N N' hN) ≫
            (sheafCompose (X.smallEtaleTopology.over U.unop) (zmodRestrict.{u, v} ℓ N N' hN)).map β
          map_add' := fun a b => by
            apply Sheaf.hom_ext
            apply NatTrans.ext
            funext W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro s
            rfl
          map_smul' := fun a b => by
            apply Sheaf.hom_ext
            apply NatTrans.ext
            funext W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro s
            rfl }
     naturality := fun U V g => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro β
       apply Sheaf.hom_ext
       apply NatTrans.ext
       rfl }⟩

/-- **Precomposition with the `ℓ`-th power map is bijective over an étale scheme carrying a
primitive `ℓN`-th root of unity `ζ`**. -/
theorem bijective_twistNegOnePrecompPow_app (W : X.Etale) {k : Type u} [Field k]
    (κ : k →+* Γ(W.left, ⊤)) {ζ : k} (hζ : IsPrimitiveRoot ζ N')
    (hζ' : IsPrimitiveRoot (ζ ^ ℓ) N) :
    Function.Bijective ((twistNegOnePrecompPow.{u, v} X ℓ N N' hN G).hom.app (op W)) := by
  have hK := bijective_twistNegOneModuleEvalRoot.{u, v} W κ hζ
    ((sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj G)
  have hK' := bijective_twistNegOneModuleEvalRoot.{u, v} W κ hζ' G
  have hcomp : ∀ β, twistNegOneModuleEvalRoot.{u, v} W κ hζ
      ((sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj G)
        ((twistNegOnePrecompPow.{u, v} X ℓ N N' hN G).hom.app (op W) β) =
      twistNegOneModuleEvalRoot.{u, v} W κ hζ' G β := by
    intro β
    show β.hom.app (op (Over.mk (𝟙 W))) ((rootsOfUnityPowMap.{u, v} X ℓ N N' hN).hom.app (op W)
      (sliceRootSection.{u, v} W κ hζ (Over.mk (𝟙 W)) 1)) =
        β.hom.app (op (Over.mk (𝟙 W))) (sliceRootSection.{u, v} W κ hζ' (Over.mk (𝟙 W)) 1)
    have h := rootsOfUnityPowMap_sliceRootSection.{u, v} ℓ N N' hN W κ hζ hζ' (Over.mk (𝟙 W)) 1
    rw [Nat.cast_one, Nat.cast_one] at h
    exact congrArg (β.hom.app (op (Over.mk (𝟙 W)))) h
  exact (Function.Bijective.of_comp_iff' hK _).1
    ((congrArg Function.Bijective (funext hcomp)).mpr hK')

section Field

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [NeZero ((N' : ℕ) : k)]

include f in
/-- **Precomposition with the `ℓ`-th power map is an isomorphism**
`𝓗om_{ℤ/N}(μ_N, G) ≅ 𝓗om_{ℤ/ℓN}(μ_{ℓN}, G)` on a scheme over a field in which `ℓN` is
invertible. -/
theorem isIso_twistNegOnePrecompPow : IsIso (twistNegOnePrecompPow.{u, v} X ℓ N N' hN G) := by
  have hℓ : ℓ ≠ 0 := fun h => NeZero.ne N' (by rw [← hN, h, zero_mul])
  let ζ := IsCyclotomicExtension.zeta N' k (CyclotomicField N' k)
  have hζ : IsPrimitiveRoot ζ N' := IsCyclotomicExtension.zeta_spec N' k _
  have hζ' : IsPrimitiveRoot (ζ ^ ℓ) N := by
    have h := hζ.pow_of_dvd hℓ (hN ▸ dvd_mul_right ℓ N)
    have hd : N' / ℓ = N := by rw [← hN, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hℓ)]
    rwa [hd] at h
  let P := twistNegOnePrecompPow.{u, v} X ℓ N N' hN G
  have hbij : ∀ U : X.Etale, Function.Bijective (P.hom.app (op (cyclotomicBaseChange f N' U))) :=
    fun U => bijective_twistNegOnePrecompPow_app X ℓ N N' hN G _
      (cyclotomicBaseChangeStructMap f N' U) hζ hζ'
  have hloc : ∀ (U : X.Etale) (S : Sieve U), S (cyclotomicBaseChangeπ f N' U) →
      S ∈ X.smallEtaleTopology U := fun U S h =>
    X.smallEtaleTopology.superset_covering ((Sieve.generate_le_iff _ _).2 (by
      rintro _ _ ⟨⟩; exact h))
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff
        (fun _ : PUnit.{u + 2} => cyclotomicBaseChangeπ f N' U)).2
        (Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨PUnit.unit, by
          rw [range_cyclotomicBaseChangeπ]; trivial⟩))
  let Hsrc := (sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj
    (twistNegOneModule.{u, v} X N G)
  let Htgt := Stacks.ConstantSheaf.moduleSheafHom X.smallEtaleTopology (ZMod N')
    (rootsOfUnityModule.{u, v} X N')
    ((sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj G)
  have hnat : ∀ (U : X.Etale) (a : ToType (Hsrc.obj.obj (op U))),
      P.hom.app (op (cyclotomicBaseChange f N' U))
          (Hsrc.obj.map (cyclotomicBaseChangeπ f N' U).op a) =
        Htgt.obj.map (cyclotomicBaseChangeπ f N' U).op (P.hom.app (op U) a) := fun U a =>
    ConcreteCategory.congr_hom (P.hom.naturality (cyclotomicBaseChangeπ f N' U).op) a
  have : Presheaf.IsLocallyInjective X.smallEtaleTopology P.hom := ⟨fun {U} a b h =>
    hloc _ _ ((hbij U.unop).1 ((hnat U.unop a).trans
      ((congrArg (Htgt.obj.map (cyclotomicBaseChangeπ f N' U.unop).op) h).trans
        (hnat U.unop b).symm)))⟩
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology P.hom := ⟨fun {U} γ =>
    hloc _ _ ((hbij U).2 (Htgt.obj.map (cyclotomicBaseChangeπ f N' U).op γ))⟩
  exact (Sheaf.isLocallyBijective_iff_isIso P).1 ⟨inferInstance, inferInstance⟩

include f in
/-- **The transition map of the Tate twist** `𝓗om(μ_{ℓN}, G') ⟶ 𝓗om(μ_N, G)` attached to
`t : G' ⟶ G` (`G` read as a sheaf of `ℤ/ℓN`-modules): a local morphism `α : μ_{ℓN} ⟶ G'` goes to
the unique `β : μ_N ⟶ G` with `p ≫ β = α ≫ t`, `p` the `ℓ`-th power map. -/
@[sga "4 XVIII 1.1.1" "i = -1"]
def twistNegOneModuleTransition (G' : Sheaf X.smallEtaleTopology
      (ModuleCat.{max (u + 1) v} (ZMod N')))
    (t : G' ⟶ (sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj G) :
    twistNegOneModule.{u, v} X N' G' ⟶
      (sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj
        (twistNegOneModule.{u, v} X N G) :=
  twistNegOneModuleMap.{u, v} X N' t ≫
    @inv _ _ _ _ (twistNegOnePrecompPow.{u, v} X ℓ N N' hN G)
      (isIso_twistNegOnePrecompPow.{u, v} X ℓ N N' hN G f)

include f in
/-- The transition attached to `t`, followed by precomposition with `p`, is postcomposition
with `t`. -/
theorem twistNegOneModuleTransition_comp_precompPow (G' : Sheaf X.smallEtaleTopology
      (ModuleCat.{max (u + 1) v} (ZMod N')))
    (t : G' ⟶ (sheafCompose X.smallEtaleTopology (zmodRestrict.{u, v} ℓ N N' hN)).obj G) :
    twistNegOneModuleTransition X ℓ N N' hN G f G' t ≫ twistNegOnePrecompPow.{u, v} X ℓ N N' hN G =
      twistNegOneModuleMap.{u, v} X N' t := by
  have := isIso_twistNegOnePrecompPow.{u, v} X ℓ N N' hN G f
  rw [twistNegOneModuleTransition, Category.assoc]
  exact (congrArg (twistNegOneModuleMap.{u, v} X N' t ≫ ·)
    (IsIso.inv_hom_id (twistNegOnePrecompPow.{u, v} X ℓ N N' hN G))).trans (Category.comp_id _)

end Field

end Stacks.Kummer

end
