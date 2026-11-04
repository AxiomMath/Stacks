module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationIdeal
public import StacksFrontier.Deformation.RingThickening.SquareZeroKernelModule

/-!
# The ideal of the extension of a deformation over `k[V]` is `𝒪_{X₀} ⊗_k V`

For a deformation `X' ⟶ Spec A` of `x₀ = (X₀ ⟶ Spec k)` over an algebra `A` of `𝒞_Λ` with
square-zero residue kernel `𝔪_A`, the ideal of the extension
`AlgebraicGeometry.Space.deformationBaseExtension` of `𝒪_{X₀}` is `𝒪_{X₀} ⊗_k 𝔪_A`, the field
`k` acting on `𝒪_{X₀}` through the structure morphism of `x₀` and on `𝔪_A` through `A ⟶ k`
(`AlgebraicGeometry.Space.deformationBaseExtensionLinearIdealIso`). For `A = k[V]` this is
`𝒪_{X₀} ⊗_k V` (`AlgebraicGeometry.Space.deformationBaseExtensionSquareZeroIdealIso`), the module
of the proof of [Stacks Project, Tag 0D1K].

## Main definitions

* `RingHom.squareZeroKerRingEquivIso`: the kernel of a square-zero surjection, transported along
  isomorphisms of the source and the target.
* `AlgebraicGeometry.Space.rangeConormalBaseModuleIso`: `R ⊗_{R'} I ≅ I` for `I² = 0`.
* `AlgebraicGeometry.Space.baseResidueFieldEquiv` and
  `AlgebraicGeometry.Space.deformationAlgebraEquiv`: `k ≃+* Γ(Spec k)` and `A ≃+* Γ(Spec A)` for
  the bases of `x₀` and of a deformation.
* `AlgebraicGeometry.Space.deformationBaseExtensionLinearIdealIso`: the ideal is `𝒪_{X₀} ⊗_k 𝔪_A`.
* `AlgebraicGeometry.Space.deformationBaseExtensionSquareZeroIdealIso`: over `k[V]` it is
  `𝒪_{X₀} ⊗_k V`.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace RingHom

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  (ψ : A →+* B) (ψ' : A' →+* B') (α : A' ≃+* A) (β : B' ≃+* B)
  (h : ψ.comp α.toRingHom = β.toRingHom.comp ψ')

include h in
/-- The kernel of `ψ` is the image of the kernel of `ψ'` along `α` when `ψ ∘ α = β ∘ ψ'`. -/
theorem ker_eq_map_ker_of_ringEquiv : RingHom.ker ψ = (RingHom.ker ψ').map α := by
  have hψ : ψ = (β.toRingHom.comp ψ').comp α.symm.toRingHom := by
    rw [← h, RingHom.comp_assoc]
    ext a
    simp
  rw [hψ, ← RingHom.comap_ker, RingHom.ker_comp_of_injective _ β.injective]
  exact Ideal.comap_symm α

include h in
/-- A square-zero kernel stays square-zero across `ψ ∘ α = β ∘ ψ'`. -/
theorem ker_sq_eq_bot_of_ringEquiv (hsq' : RingHom.ker ψ' ^ 2 = ⊥) : RingHom.ker ψ ^ 2 = ⊥ := by
  rw [ker_eq_map_ker_of_ringEquiv ψ ψ' α β h, ← Ideal.map_pow, hsq', Ideal.map_bot]

include h in
/-- Surjectivity transfers across `ψ ∘ α = β ∘ ψ'`. -/
theorem surjective_of_ringEquiv (hψ' : Function.Surjective ψ') : Function.Surjective ψ := by
  intro b
  obtain ⟨a', ha'⟩ := hψ' (β.symm b)
  refine ⟨α a', ?_⟩
  have := congrArg (fun f => f a') h
  simp only [RingHom.comp_apply] at this
  exact this.trans (by
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ha', RingEquiv.apply_symm_apply])

variable (hψ : Function.Surjective ψ) (hsq : RingHom.ker ψ ^ 2 = ⊥)
  (hψ' : Function.Surjective ψ') (hsq' : RingHom.ker ψ' ^ 2 = ⊥)

/-- **The kernel of a square-zero surjection, across isomorphisms.** For `ψ ∘ α = β ∘ ψ'`
(`α`, `β` ring isomorphisms), `Ker(ψ)` read as a `B'`-module through `β` is `Ker(ψ')`. -/
def squareZeroKerRingEquivIso :
    (ModuleCat.restrictScalars.{u} β.toRingHom).obj (squareZeroKer ψ hψ hsq) ≅
      squareZeroKer ψ' hψ' hsq' :=
  letI := squareZeroKerModule ψ hψ hsq
  letI := squareZeroKerModule ψ' hψ' hsq'
  have hmem : ∀ x : RingHom.ker ψ, α.symm x ∈ RingHom.ker ψ' := fun x => by
    rw [RingHom.mem_ker]
    have := congrArg (fun f => f (α.symm x)) h
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply] at this
    rw [← β.injective.eq_iff, ← this, x.2, map_zero]
  have hmem' : ∀ x : RingHom.ker ψ', α x ∈ RingHom.ker ψ := fun x => by
    rw [RingHom.mem_ker]
    have := congrArg (fun f => f (x : A')) h
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, x.2, map_zero]
  have hsmul : ∀ (c : B') (x : RingHom.ker ψ),
      (α.symm ((β c • x : RingHom.ker ψ) : A) : A') = ((c • ⟨α.symm x, hmem x⟩ :
        RingHom.ker ψ') : A') := fun c x => by
    obtain ⟨a', rfl⟩ := hψ' c
    have hβ : β (ψ' a') = ψ (α a') := by
      have := congrArg (fun f => f a') h
      simpa using this.symm
    rw [hβ, squareZeroKerModule_smul ψ hψ hsq, squareZeroKerModule_smul ψ' hψ' hsq', map_mul,
      RingEquiv.symm_apply_apply]
  LinearEquiv.toModuleIso (X₁ := (ModuleCat.restrictScalars.{u} β.toRingHom).obj
      (squareZeroKer ψ hψ hsq)) (X₂ := squareZeroKer ψ' hψ' hsq')
    (m₁ := ((ModuleCat.restrictScalars.{u} β.toRingHom).obj (squareZeroKer ψ hψ hsq)).isModule)
    (m₂ := (squareZeroKer ψ' hψ' hsq').isModule)
    { toFun := fun x => ⟨α.symm (show RingHom.ker ψ from x), hmem x⟩
      map_add' := fun x y => Subtype.ext (map_add α.symm x.1 y.1)
      map_smul' := fun c x => Subtype.ext (hsmul c x)
      invFun := fun x => (show RingHom.ker ψ from ⟨α (show RingHom.ker ψ' from x).1, hmem' x⟩)
      left_inv := fun x => Subtype.ext (α.apply_symm_apply (show RingHom.ker ψ from x).1)
      right_inv := fun x => Subtype.ext (α.symm_apply_apply (show RingHom.ker ψ' from x).1) }

end RingHom

namespace Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The right action of `k` on a `k`-module, the one through which `k[V]` is formed. -/
local instance (M : ModuleCat.{u} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

/-- The left and right actions of `k` on a `k`-module agree. -/
local instance (M : ModuleCat.{u} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

variable (Λ) in
/-- **The maximal ideal of `k[V]` is `V`**, as a `k`-module: `𝔪_{k[V]}` with its module structure
over `k[V]/𝔪 = k` (`RingHom.squareZeroKer`) is `V`, through the second coordinate. -/
def squareZeroKerArtinianSquareZeroIso (V : FGModuleCat.{u} k) :
    RingHom.squareZeroKer (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V))
        (residueMap_surjective' _)
        (ker_residueMap_sq_artinianSquareZero Λ k V) ≅
      (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V :=
  letI := RingHom.squareZeroKerModule
    (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V))
    (residueMap_surjective' _)
    (ker_residueMap_sq_artinianSquareZero Λ k V)
  have hfst : ∀ x : RingHom.ker (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V)),
      TrivSqZeroExt.fst (R := k) (M := V.obj) x.1 = 0 := fun x => x.2
  LinearEquiv.toModuleIso
    (m₁ := (RingHom.squareZeroKer (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V))
        (residueMap_surjective' _)
        (ker_residueMap_sq_artinianSquareZero Λ k V)).isModule)
    (m₂ := ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V).isModule)
    { toFun := fun x => TrivSqZeroExt.snd (R := k) (M := V.obj)
        (show RingHom.ker (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V)) from x).1
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => by
        have h := RingHom.squareZeroKerModule_smul
          (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V))
          (residueMap_surjective' _)
          (ker_residueMap_sq_artinianSquareZero Λ k V)
          (TrivSqZeroExt.inl c) x
        refine (congrArg (TrivSqZeroExt.snd (R := k) (M := V.obj)) h).trans ?_
        refine (TrivSqZeroExt.snd_mul _ _).trans ?_
        simp only [TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, hfst x, MulOpposite.op_zero,
          zero_smul, add_zero]
        rfl
      invFun := fun v => (show RingHom.ker
          (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V)) from
        ⟨TrivSqZeroExt.inr (R := k) (M := V.obj) v, TrivSqZeroExt.fst_inr (R := k) v⟩)
      left_inv := fun x => Subtype.ext (TrivSqZeroExt.ext (hfst x).symm rfl)
      right_inv := fun _ => rfl }

variable (Λ) in
/-- `𝔪_A ≅ V` for an algebra `A` of `𝒞_Λ` equal to `k[V]`. -/
def squareZeroKerOfEqIso (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (V : FGModuleCat.{u} k)
    (hA : A = (artinianSquareZeroExtensionFunctor Λ k).obj V)
    (hsq : RingHom.ker (residueMap A) ^ 2 = ⊥) :
    RingHom.squareZeroKer (residueMap A) (residueMap_surjective' A) hsq ≅
      (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V := by
  subst hA
  exact squareZeroKerArtinianSquareZeroIso Λ V

end Deformation.Artin

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Range

variable {T T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hψ : Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom)
  (hsq : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom ^ 2 = ⊥)

/-- **`R ⊗_{R'} I ≅ I` when `I² = 0`.** For a closed immersion `j : T ⟶ T'` whose ring map
`ψ : R' = Γ(T', 𝒪) ⟶ R = Γ(T, 𝒪)` is surjective with square-zero kernel `I`, the `R`-module
`R ⊗_{R'} I` is `I` with its `R`-module structure `RingHom.squareZeroKer`. -/
def rangeConormalBaseModuleIso :
    rangeConormalBaseModule B S hS j hj ≅ RingHom.squareZeroKer _ hψ hsq :=
  haveI : Fact (Function.Surjective
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom) := ⟨hψ⟩
  (ModuleCat.extendScalars.{u, u, u}
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).mapIso
      (eqToIso (congrArg (fun I : Ideal (baseRing B S hS T') => ModuleCat.of _ I)
        (closedSubspaceBaseIdeal_rangeSubspace B S hS j hj)) ≪≫
      (RingHom.restrictScalarsSquareZeroKerIso _ hψ hsq).symm) ≪≫
    asIso ((ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom).counit.app
        (RingHom.squareZeroKer _ hψ hsq))

end Range

section Deformation

open Deformation Deformation.Artin

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S}
  {y₀ : CartesianProperFlatSpaces B S hS}

variable (hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The base of `x₀` is `Spec k`. -/
abbrev baseSpecIso :
    (BigFppfOver.toScheme B S hS).obj ((cartesianProperFlatProjection B S hS).obj y₀) ≅
      Spec (.of k) :=
  eqToIso (congrArg Over.left hy₀)

/-- **`k ≅ Γ(Spec k)`** for the base of `x₀`. -/
def baseResidueFieldIso :
    CommRingCat.of k ≅ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj
      ((cartesianProperFlatProjection B S hS).obj y₀))) :=
  (Scheme.ΓSpecIso (.of k)).symm ≪≫ Scheme.Γ.mapIso (baseSpecIso B S hS hy₀).op

/-- **`k ≃ Γ(Spec k)`** for the base of `x₀`, as a ring isomorphism. -/
abbrev baseResidueFieldEquiv :
    k ≃+* baseRing B S hS ((cartesianProperFlatProjection B S hS).obj y₀) :=
  (baseResidueFieldIso B S hS hy₀).commRingCatIsoToRingEquiv

variable {hy₀}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) y₀ hy₀)

/-- The base of a deformation over `A` is `Spec A`. -/
abbrev deformationSpecIso :
    (BigFppfOver.toScheme B S hS).obj ((cartesianProperFlatProjection B S hS).obj x.point) ≅
      Spec (.of x.algebra) :=
  eqToIso (congrArg Over.left x.base)

/-- **`A ≅ Γ(Spec A)`** for the base of a deformation over `A`. -/
def deformationAlgebraIso :
    CommRingCat.of x.algebra ≅ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj
      ((cartesianProperFlatProjection B S hS).obj x.point))) :=
  (Scheme.ΓSpecIso (.of x.algebra)).symm ≪≫ Scheme.Γ.mapIso (deformationSpecIso B S hS x).op

/-- **`A ≃ Γ(Spec A)`** for the base of a deformation over `A`, as a ring isomorphism. -/
abbrev deformationAlgebraEquiv :
    x.algebra ≃+* baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x.point) :=
  (deformationAlgebraIso B S hS x).commRingCatIsoToRingEquiv

/-- The base immersion `Spec k ⟶ Spec A` of a deformation is the spectrum of the residue map. -/
theorem deformationBaseImmersion_comp_specIso :
    (BigFppfOver.toScheme B S hS).map (deformationBaseImmersion B S hS x) ≫
        (deformationSpecIso B S hS x).hom =
      (baseSpecIso B S hS hy₀).hom ≫ Spec.map (CommRingCat.ofHom (residueMap x.algebra)) := by
  have h := x.arrow_base
  rw [← eqToIso.inv, Iso.inv_comp_eq] at h
  exact h

/-- **Pullback of functions along `Spec k ⟶ Spec A` is the residue map**, read through
`A ≅ Γ(Spec A)` and `k ≅ Γ(Spec k)`. -/
theorem deformationBaseImmersion_Γ_comp :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (deformationBaseImmersion B S hS x)).op).hom.comp
        (deformationAlgebraEquiv B S hS x).toRingHom =
      (baseResidueFieldEquiv B S hS hy₀).toRingHom.comp (residueMap x.algebra) := by
  have h : (deformationAlgebraIso B S hS x).hom ≫
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (deformationBaseImmersion B S hS x)).op =
      CommRingCat.ofHom (residueMap x.algebra) ≫ (baseResidueFieldIso B S hS hy₀).hom := by
    have e1 : Scheme.Γ.map (deformationSpecIso B S hS x).hom.op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (deformationBaseImmersion B S hS x)).op =
        Scheme.Γ.map (Spec.map (CommRingCat.ofHom (residueMap x.algebra))).op ≫
          Scheme.Γ.map (baseSpecIso B S hS hy₀).hom.op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
        deformationBaseImmersion_comp_specIso]
    change (Scheme.ΓSpecIso _).inv ≫ (Scheme.Γ.map (deformationSpecIso B S hS x).hom.op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (deformationBaseImmersion B S hS x)).op) =
      CommRingCat.ofHom (residueMap x.algebra) ≫ (Scheme.ΓSpecIso _).inv ≫
        Scheme.Γ.map (baseSpecIso B S hS hy₀).hom.op
    refine (congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of x.algebra)).inv ≫ g) e1).trans ?_
    exact ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ Scheme.Γ.map (baseSpecIso B S hS hy₀).hom.op)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (residueMap x.algebra))).symm)).trans
      (Category.assoc _ _ _)
  exact congrArg CommRingCat.Hom.hom h

variable (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥)

/-- The ring map `Γ(Spec A) ⟶ Γ(Spec k)` of the base immersion of a deformation is surjective. -/
theorem deformationBaseImmersion_Γ_surjective :
    Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (deformationBaseImmersion B S hS x)).op).hom :=
  RingHom.surjective_of_ringEquiv _ _ _ _ (deformationBaseImmersion_Γ_comp B S hS x)
    (residueMap_surjective' x.algebra)

include hsq in
/-- The kernel of `Γ(Spec A) ⟶ Γ(Spec k)` squares to zero when `𝔪_A² = 0`. -/
theorem deformationBaseImmersion_Γ_ker_sq :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (deformationBaseImmersion B S hS x)).op).hom ^ 2 = ⊥ :=
  RingHom.ker_sq_eq_bot_of_ringEquiv _ _ _ _ (deformationBaseImmersion_Γ_comp B S hS x) hsq

/-- The base-ring datum `k ⟶ Γ(X₀, 𝒪)` of the structure morphism of `x₀`. -/
abbrev baseFieldHom : k →+* modelGlobalFunctions B S hS y₀.obj.obj.left :=
  (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀))).comp
    (baseResidueFieldEquiv B S hS hy₀).toRingHom

/-- **The ideal of the extension of a deformation is `𝒪_{X₀} ⊗_k 𝔪_A`.** For a deformation
`X' ⟶ Spec A` of `x₀ = (X₀ ⟶ Spec k)` over an algebra with square-zero residue kernel `𝔪_A`, the
ideal of `AlgebraicGeometry.Space.deformationBaseExtension` is `𝒪_{X₀} ⊗_k 𝔪_A`, `k` acting on
`𝒪_{X₀}` through the structure morphism of `x₀` and on `𝔪_A` through `A ⟶ k`
(`RingHom.squareZeroKer`). -/
def deformationBaseExtensionLinearIdealIso :
    (etaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS _)).obj
        ((modulePullback B S hS (preimageProjection B S hS (deformationStructureMap B S hS x)
          (squareZeroSubspace B S hS _
            (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
              hsq)))).obj
        (conormalModule B S hS _ (squareZeroSubspace B S hS _
          (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
            hsq)))) ≅
      (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).obj
        (RingHom.squareZeroKer (residueMap x.algebra) (residueMap_surjective' x.algebra) hsq) :=
  deformationBaseExtensionIdealIso B S hS x hsq ≪≫
    (baseRingTensorModule B S hS y₀.obj.obj.left
      (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))).mapIso
      (rangeConormalBaseModuleIso B S hS (deformationBaseImmersion B S hS x)
        (isClosedImmersion_deformationBaseImmersion B S hS x hsq)
        (deformationBaseImmersion_Γ_surjective B S hS x)
        (deformationBaseImmersion_Γ_ker_sq B S hS x hsq)) ≪≫
    ((baseRingTensorModuleRestrictScalarsIso B S hS y₀.obj.obj.left
      (baseResidueFieldEquiv B S hS hy₀).toRingHom
      (baseRingHomOfMap (baseStructureMap B S hS (y₀ := y₀)))
      (baseResidueFieldEquiv B S hS hy₀).surjective).app _).symm ≪≫
    (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).mapIso
      (RingHom.squareZeroKerRingEquivIso _ _ (deformationAlgebraEquiv B S hS x)
        (baseResidueFieldEquiv B S hS hy₀) (deformationBaseImmersion_Γ_comp B S hS x) _ _
        (residueMap_surjective' x.algebra) hsq)

variable (Λ) in
/-- **The ideal of the extension of a deformation over `k[V]` is `𝒪_{X₀} ⊗_k V`**, `k` acting on
`𝒪_{X₀}` through the structure morphism of `x₀`: the module of the proof of
[Stacks Project, Tag 0D1K]. -/
def deformationBaseExtensionSquareZeroIdealIso (V : FGModuleCat.{u} k)
    (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    (etaleRestrictionModule B S hS (deformationThickeningIso B S hS x hsq).hom
        (isEtale_hom_of_iso B S hS _)).obj
        ((modulePullback B S hS (preimageProjection B S hS (deformationStructureMap B S hS x)
          (squareZeroSubspace B S hS _
            (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
              hsq)))).obj
        (conormalModule B S hS _ (squareZeroSubspace B S hS _
          (isSquareZeroClosedImmersion_map_arrow (cartesianProperFlatProjection B S hS) x
            hsq)))) ≅
      (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).obj
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) :=
  deformationBaseExtensionLinearIdealIso B S hS x hsq ≪≫
    (baseRingTensorModule B S hS y₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hy₀))).mapIso
      (squareZeroKerOfEqIso Λ x.algebra V hx hsq)

end Deformation

end AlgebraicGeometry.Space
