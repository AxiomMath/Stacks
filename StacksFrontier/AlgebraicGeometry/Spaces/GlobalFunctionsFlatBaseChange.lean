module

public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.AlgebraicGeometry.Scheme.AffinePullbackGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAlongBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsChartEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet

/-!
# Flat base change for the global functions of an algebraic space

Let `A` be a ring, let `T` be a flat `A`-algebra, let `X` be an algebraic space over `Spec A`
and let `X' = X ×_{Spec A} Spec T`. Then

`Γ(X', 𝒪_{X'}) = T ⊗_A Γ(X, 𝒪_X)`

for an algebraic space admitting a surjective étale chart `U` by an *affine* scheme whose kernel
pair `V = U ×_X U` is again affine, in particular for a quasi-compact separated algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.specAlgebraObj`: the object `Spec T` of the big fppf site over
  `Spec A`, for an `A`-algebra `T`.
* `AlgebraicGeometry.Space.siteObjSectionsAlgebra`: the `A`-algebra structure on the regular
  functions of an object of the big fppf site over `Spec A`.
* `AlgebraicGeometry.Space.siteBaseChangeEtaleChart`: the base change to `Spec T` of an étale
  chart, as an étale chart of the base change.

## Main results

* `AlgebraicGeometry.Space.ringEquiv_equalizer_of_intertwine`: transport of an equalizer of two
  algebra maps along isomorphisms of the source and target that intertwine the two pairs.
* `AlgebraicGeometry.Space.siteBaseChangeChartTensorRingEquiv`: the regular functions of a
  base-changed affine chart are `T ⊗_A` of its regular functions.
* `AlgebraicGeometry.Space.equalizerSiteBaseChangeRingEquiv`: extension of scalars along a flat
  `A → T` commutes with the equalizer of the two restriction maps of a kernel pair of affine
  objects of the site.
* `AlgebraicGeometry.Space.globalFunctionsBaseChangeRingEquiv`: **the degree-zero flat base
  change**, `Γ(X', 𝒪_{X'}) ≅ T ⊗_A Γ(X, 𝒪_X)`, for a chart with affine kernel pair.
* `AlgebraicGeometry.Space.nonempty_ringEquiv_globalFunctions_baseChange`: the same for a
  quasi-compact separated algebraic space, with no chart in the statement.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0792](https://stacks.math.columbia.edu/tag/0792)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-! ### Transport of an equalizer along intertwining isomorphisms -/

/-- **Transport of an equalizer of two algebra maps.** If `eC` and `eD` are isomorphisms
intertwining a pair of algebra maps `ρ₀, σ₀` with a pair `ρ, σ`, then they identify the two
equalizers. -/
def ringEquiv_equalizer_of_intertwine {A C₀ D₀ C D : Type*} [CommRing A] [CommRing C₀]
    [CommRing D₀] [CommRing C] [CommRing D] [Algebra A C₀] [Algebra A D₀] [Algebra A C]
    [Algebra A D] (eC : C₀ ≃+* C) (eD : D₀ ≃+* D) (ρ₀ σ₀ : C₀ →ₐ[A] D₀)
    (ρ σ : C →ₐ[A] D) (hρ : ∀ x, ρ (eC x) = eD (ρ₀ x)) (hσ : ∀ x, σ (eC x) = eD (σ₀ x)) :
    AlgHom.equalizer ρ₀ σ₀ ≃+* AlgHom.equalizer ρ σ where
  toFun x := ⟨eC x.1, by
    have hx : ρ₀ x.1 = σ₀ x.1 := x.2
    change ρ (eC x.1) = σ (eC x.1)
    rw [hρ, hσ, hx]⟩
  invFun y := ⟨eC.symm y.1, by
    have h : ρ y.1 = σ y.1 := y.2
    rw [← eC.apply_symm_apply y.1, hρ, hσ] at h
    exact eD.injective h⟩
  left_inv x := Subtype.ext (eC.symm_apply_apply x.1)
  right_inv y := Subtype.ext (eC.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (eC.map_mul x.1 y.1)
  map_add' x y := Subtype.ext (eC.map_add x.1 y.1)

/-- The equalizer of the two ring homomorphisms underlying a pair of algebra homomorphisms is
the equalizer of that pair. -/
def eqLocusRingEquivEqualizer {A C D : Type*} [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C] [Algebra A D] (ρ σ : C →ₐ[A] D) (ρ' σ' : C →+* D)
    (hρ : ∀ x, ρ' x = ρ x) (hσ : ∀ x, σ' x = σ x) :
    RingHom.eqLocus ρ' σ' ≃+* AlgHom.equalizer ρ σ where
  toFun x := ⟨x.1, by
    have hx : ρ' x.1 = σ' x.1 := x.2
    change ρ x.1 = σ x.1
    rw [← hρ, ← hσ, hx]⟩
  invFun x := ⟨x.1, by
    have hx : ρ x.1 = σ x.1 := x.2
    change ρ' x.1 = σ' x.1
    rw [hρ, hσ, hx]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-! ### `Spec T` as an object of the big fppf site over `Spec A` -/

variable (A T : Type u) [CommRing A] [CommRing T] [Algebra A T]
variable (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (hT : B.Contains (Spec (.of T)))

/-- The object `Spec T` of the big fppf site over `Spec A`, for an `A`-algebra `T`, with its
structure morphism `Spec T ⟶ Spec A`. -/
def specAlgebraObj : BigFppfOver B (Spec (.of A)) hA :=
  Over.mk (B.inclusion.preimage (X := B.obj hT) (Y := B.obj hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A T))))

/-- The underlying scheme of `specAlgebraObj A T` is `Spec T`. -/
@[simp] theorem toScheme_obj_specAlgebraObj :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).obj (specAlgebraObj A T B hA hT) =
      Spec (.of T) :=
  rfl

/-- The underlying morphism of schemes of the structure morphism of `Spec T` is `Spec` of the
structure map `A ⟶ T`. -/
theorem toScheme_map_siteTerminalHom_specAlgebraObj :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (siteTerminalHom B (Spec (.of A)) hA (specAlgebraObj A T B hA hT)) =
      Spec.map (CommRingCat.ofHom (algebraMap A T)) := by
  show B.inclusion.map (B.inclusion.preimage (X := B.obj hT) (Y := B.obj hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A T)))) = _
  rw [Functor.map_preimage]

/-! ### The `A`-algebra structure on the regular functions of a chart -/

variable {B hA}

/-- The regular functions on an object of the big fppf site over `Spec A`, as an `A`-algebra
through its structure morphism. -/
@[instance_reducible] def siteObjSectionsAlgebra (U : BigFppfOver B (Spec (.of A)) hA) :
    Algebra A Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) :=
  (((Scheme.ΓSpecIso (.of A)).inv ≫
    ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
      (siteTerminalHom B (Spec (.of A)) hA U)).appTop).hom).toAlgebra

attribute [local instance] siteObjSectionsAlgebra

/-- The structure map `A → Γ(U, ⊤)` is the composite of `Γ(Spec A) ≅ A` with the map on global
sections induced by the structure morphism of `U`. -/
theorem algebraMap_siteObjSectionsAlgebra (U : BigFppfOver B (Spec (.of A)) hA) :
    algebraMap A Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
          (siteTerminalHom B (Spec (.of A)) hA U)).appTop).hom :=
  rfl

/-- The structure morphism of an object of the big fppf site over `Spec A`, in the normalized
form `U ≅ Spec Γ(U) ⟶ Spec A`. -/
theorem siteTerminalHom_eq_isoSpec (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)] :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (siteTerminalHom B (Spec (.of A)) hA U) =
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A
          Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤))) := by
  set g := (BigFppfOver.toScheme B (Spec (.of A)) hA).map
    (siteTerminalHom B (Spec (.of A)) hA U) with hg
  have key : ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
        (Over.mk (𝟙 (B.obj hA)))).toSpecΓ ≫
      Spec.map (Scheme.ΓSpecIso (.of A)).inv = 𝟙 _ :=
    toSpecΓ_SpecMap_ΓSpecIso_inv (.of A)
  rw [algebraMap_siteObjSectionsAlgebra, show CommRingCat.ofHom
      ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom =
      (Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop from rfl, Spec.map_comp,
    Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, key,
    Category.comp_id]

/-- Restriction along a morphism of the site is a morphism of `A`-algebras. -/
def chartSectionsRestrictionAlgHom {U V : BigFppfOver B (Spec (.of A)) hA} (α : V ⟶ U) :
    Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) →ₐ[A]
      Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V, ⊤) where
  __ := ((BigFppfOver.toScheme B (Spec (.of A)) hA).map α).appTop.hom
  commutes' a := by
    have hα : siteTerminalHom B (Spec (.of A)) hA V =
        α ≫ siteTerminalHom B (Spec (.of A)) hA U := Over.mkIdTerminal.hom_ext _ _
    change _ = ((Scheme.ΓSpecIso (.of A)).inv ≫ _).hom a
    rw [algebraMap_siteObjSectionsAlgebra, hα, Functor.map_comp]
    rfl

/-! ### The regular functions of a base-changed chart -/

/-- The cartesian square of schemes underlying the base change of an affine object of the site
to `Spec T`, with the structure morphism of `U` written as `U ≅ Spec Γ(U) ⟶ Spec A`. -/
theorem isPullback_toScheme_siteBaseChangeObj_specAlgebraObj
    (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)] :
    IsPullback
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.fst
        (siteTerminalHom B (Spec (.of A)) hA U)
        (siteTerminalHom B (Spec (.of A)) hA (specAlgebraObj A T B hA hT))))
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.snd
        (siteTerminalHom B (Spec (.of A)) hA U)
        (siteTerminalHom B (Spec (.of A)) hA (specAlgebraObj A T B hA hT))))
      (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A
          Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap A T))) := by
  have h := isPullback_toScheme_siteBaseChangeObj B (Spec (.of A)) hA U
    (specAlgebraObj A T B hA hT)
  rwa [siteTerminalHom_eq_isoSpec A U,
    toScheme_map_siteTerminalHom_specAlgebraObj A T B hA hT] at h

/-- **The regular functions of a base-changed chart.** For an affine object `U` of the big fppf
site over `Spec A`, the regular functions on `U ×_{Spec A} Spec T` are `T ⊗_A Γ(U, 𝒪_U)`. -/
def siteBaseChangeChartTensorRingEquiv (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)] :
    T ⊗[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤) ≃+*
      Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
        (pullback (siteTerminalHom B (Spec (.of A)) hA U)
          (siteTerminalHom B (Spec (.of A)) hA (specAlgebraObj A T B hA hT))), ⊤) :=
  (Algebra.TensorProduct.comm A T _).toRingEquiv.trans
    (tensorAppTopIso
      (isPullback_toScheme_siteBaseChangeObj_specAlgebraObj A T hT U)).commRingCatIsoToRingEquiv

/-- `siteBaseChangeChartTensorRingEquiv` is `AlgebraicGeometry.tensorAppTopIso` precomposed with
the swap `T ⊗[A] Γ(U, ⊤) ≃ Γ(U, ⊤) ⊗[A] T`. -/
theorem siteBaseChangeChartTensorRingEquiv_apply (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)]
    (x : T ⊗[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤)) :
    siteBaseChangeChartTensorRingEquiv A T hT U x =
      (tensorAppTopIso
        (isPullback_toScheme_siteBaseChangeObj_specAlgebraObj A T hT U)).hom.hom
          (Algebra.TensorProduct.comm A T _ x) :=
  rfl

/-- `siteBaseChangeChartTensorRingEquiv` sends `1 ⊗ₜ c` to the pullback of `c` along the first
projection `U ×_{Spec A} Spec T ⟶ U`. -/
theorem siteBaseChangeChartTensorRingEquiv_one_tmul (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)]
    (c : Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤)) :
    siteBaseChangeChartTensorRingEquiv A T hT U (1 ⊗ₜ c) =
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.fst
        (siteTerminalHom B (Spec (.of A)) hA U)
        (siteTerminalHom B (Spec (.of A)) hA
          (specAlgebraObj A T B hA hT)))).appTop.hom c := by
  rw [siteBaseChangeChartTensorRingEquiv_apply, Algebra.TensorProduct.comm_tmul]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (tensorAppTopIso_includeLeft
    (isPullback_toScheme_siteBaseChangeObj_specAlgebraObj A T hT U))) c

/-- `siteBaseChangeChartTensorRingEquiv` sends `t ⊗ₜ 1` to the pullback of `t ∈ Γ(Spec T)` along
the second projection `U ×_{Spec A} Spec T ⟶ Spec T`. -/
theorem siteBaseChangeChartTensorRingEquiv_tmul_one (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)] (t : T) :
    siteBaseChangeChartTensorRingEquiv A T hT U (t ⊗ₜ 1) =
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (pullback.snd
        (siteTerminalHom B (Spec (.of A)) hA U)
        (siteTerminalHom B (Spec (.of A)) hA
          (specAlgebraObj A T B hA hT)))).appTop.hom
        ((Scheme.ΓSpecIso (.of T)).inv.hom t) := by
  rw [siteBaseChangeChartTensorRingEquiv_apply, Algebra.TensorProduct.comm_tmul]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (tensorAppTopIso_includeRight
    (isPullback_toScheme_siteBaseChangeObj_specAlgebraObj A T hT U))) t

/-- The image of `t ⊗ₜ c` under `siteBaseChangeChartTensorRingEquiv` is the product of the images
of `t ⊗ₜ 1` and `1 ⊗ₜ c`. -/
theorem siteBaseChangeChartTensorRingEquiv_tmul (U : BigFppfOver B (Spec (.of A)) hA)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)] (t : T)
    (c : Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤)) :
    siteBaseChangeChartTensorRingEquiv A T hT U (t ⊗ₜ c) =
      siteBaseChangeChartTensorRingEquiv A T hT U (t ⊗ₜ 1) *
        siteBaseChangeChartTensorRingEquiv A T hT U (1 ⊗ₜ c) := by
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- **The base change of a restriction map.** Under the identification of the regular functions
of a base-changed chart with a tensor product, restriction along the base change of a morphism
of the site is extension of scalars of restriction along that morphism. -/
theorem chartSectionsRestrictionAlgHom_siteBaseChangeHom_apply
    {U V : BigFppfOver B (Spec (.of A)) hA} (α : V ⟶ U)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)]
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V)]
    (x : T ⊗[A] Γ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U, ⊤)) :
    chartSectionsRestrictionAlgHom A (siteBaseChangeHom B (Spec (.of A)) hA
        (W := specAlgebraObj A T B hA hT) α)
        (siteBaseChangeChartTensorRingEquiv A T hT U x) =
      siteBaseChangeChartTensorRingEquiv A T hT V
        (Algebra.TensorProduct.map (AlgHom.id A T) (chartSectionsRestrictionAlgHom A α) x) := by
  set W := specAlgebraObj A T B hA hT with hW
  set G := BigFppfOver.toScheme B (Spec (.of A)) hA with hG
  set bc := siteBaseChangeHom B (Spec (.of A)) hA (W := W) α with hbc
  have hcomp : ∀ {P Q R : Scheme.{u}} (f : P ⟶ Q) (g : Q ⟶ R) (c : Γ(R, ⊤)),
      f.appTop.hom (g.appTop.hom c) = (f ≫ g).appTop.hom c := fun f g c => by
    rw [Scheme.Hom.comp_appTop]; rfl
  have hfst : ∀ c, (G.map bc).appTop.hom
        ((G.map (pullback.fst (siteTerminalHom B (Spec (.of A)) hA U)
          (siteTerminalHom B (Spec (.of A)) hA W))).appTop.hom c) =
      (G.map (pullback.fst (siteTerminalHom B (Spec (.of A)) hA V)
          (siteTerminalHom B (Spec (.of A)) hA W))).appTop.hom
        ((G.map α).appTop.hom c) := by
    intro c
    rw [hcomp, hcomp, ← Functor.map_comp, ← Functor.map_comp, hbc, siteBaseChangeHom_comp_fst]
  have hsnd : ∀ t, (G.map bc).appTop.hom
        ((G.map (pullback.snd (siteTerminalHom B (Spec (.of A)) hA U)
          (siteTerminalHom B (Spec (.of A)) hA W))).appTop.hom t) =
      (G.map (pullback.snd (siteTerminalHom B (Spec (.of A)) hA V)
          (siteTerminalHom B (Spec (.of A)) hA W))).appTop.hom t := by
    intro t
    rw [hcomp, ← Functor.map_comp, hbc, siteBaseChangeHom_comp_snd]
  induction x with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t c =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      siteBaseChangeChartTensorRingEquiv_tmul A T hT U t c,
      siteBaseChangeChartTensorRingEquiv_tmul A T hT V t (chartSectionsRestrictionAlgHom A α c),
      map_mul,
      siteBaseChangeChartTensorRingEquiv_tmul_one A T hT U t,
      siteBaseChangeChartTensorRingEquiv_tmul_one A T hT V t,
      siteBaseChangeChartTensorRingEquiv_one_tmul A T hT U c,
      siteBaseChangeChartTensorRingEquiv_one_tmul A T hT V (chartSectionsRestrictionAlgHom A α c)]
    exact congrArg₂ (· * ·) (hsnd _) (hfst c)

/-- **Flat base change for the equalizer of two restriction maps.** For affine objects `U`, `V`
of the big fppf site over `Spec A`, two morphisms `α, β : V ⟶ U` and a flat `A`-algebra `T`,
extension of scalars along `A → T` carries the equalizer of the two restriction maps
`Γ(U, 𝒪_U) ⇉ Γ(V, 𝒪_V)` to the equalizer of the two restriction maps of the base changes. -/
def equalizerSiteBaseChangeRingEquiv [Module.Flat A T]
    {U V : BigFppfOver B (Spec (.of A)) hA} (α β : V ⟶ U)
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)]
    [IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V)] :
    T ⊗[A] AlgHom.equalizer (chartSectionsRestrictionAlgHom A α)
        (chartSectionsRestrictionAlgHom A β) ≃+*
      AlgHom.equalizer
        (chartSectionsRestrictionAlgHom A (siteBaseChangeHom B (Spec (.of A)) hA
          (W := specAlgebraObj A T B hA hT) α))
        (chartSectionsRestrictionAlgHom A (siteBaseChangeHom B (Spec (.of A)) hA
          (W := specAlgebraObj A T B hA hT) β)) :=
  (AlgHom.tensorEqualizerEquiv A T (chartSectionsRestrictionAlgHom A α)
      (chartSectionsRestrictionAlgHom A β)).toRingEquiv.trans
    (ringEquiv_equalizer_of_intertwine (siteBaseChangeChartTensorRingEquiv A T hT U)
      (siteBaseChangeChartTensorRingEquiv A T hT V) _ _ _ _
      (chartSectionsRestrictionAlgHom_siteBaseChangeHom_apply A T hT α)
      (chartSectionsRestrictionAlgHom_siteBaseChangeHom_apply A T hT β))

/-! ### Flat base change in degree zero -/

/-- The equalizer presentation of the global functions of an algebraic space over `Spec A`, as
an isomorphism of `A`-algebras. -/
def globalFunctionsEqualizerAlgEquiv (X : AlgebraicSpaces B (Spec (.of A)) hA)
    {Uc Vc : SmallEtale B (Spec (.of A)) hA X.obj} (α β : Vc ⟶ Uc)
    (hcov : (SmallEtale.topology B (Spec (.of A)) hA X.obj).CoversTop (fun _ : Unit => Uc))
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map α))
      (yoneda.map ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map β))
      Uc.obj.hom Uc.obj.hom) :
    globalFunctions B (Spec (.of A)) hA X.obj ≃ₐ[A]
      AlgHom.equalizer
        (chartSectionsRestrictionAlgHom A ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map α))
        (chartSectionsRestrictionAlgHom A ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map β)) :=
  AlgEquiv.ofRingEquiv
    (f := (globalFunctionsEqualizerRingEquiv X α β hcov hsq).trans
      (eqLocusRingEquivEqualizer _ _ _ _ (fun _ => rfl) (fun _ => rfl)))
    (fun _ => Subtype.ext rfl)

variable {X X' : AlgebraicSpaces B (Spec (.of A)) hA}
    (f : X.obj ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
    {q : X'.obj ⟶ X.obj} {r : X'.obj ⟶ yoneda.obj (specAlgebraObj A T B hA hT)}
    (hX' : IsPullback q r f (yoneda.map (siteTerminalHom B (Spec (.of A)) hA
      (specAlgebraObj A T B hA hT))))

/-- **The base change of an étale chart**, as an étale chart of the base change. -/
def siteBaseChangeEtaleChart (Uc : SmallEtale B (Spec (.of A)) hA X.obj) :
    SmallEtale B (Spec (.of A)) hA X'.obj :=
  ⟨CostructuredArrow.mk (siteBaseChangeChartMap B (Spec (.of A)) hA f hX' Uc.obj.hom),
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (isPullback_siteBaseChangeChartMap B (Spec (.of A)) hA f hX' Uc.obj.hom) Uc.property⟩

/-- The base change of a morphism of étale charts of `X`, as a morphism of étale charts of the
base change `X'`. -/
def siteBaseChangeEtaleChartHom {Uc Vc : SmallEtale B (Spec (.of A)) hA X.obj} (α : Vc ⟶ Uc) :
    siteBaseChangeEtaleChart A T hT f hX' Vc ⟶ siteBaseChangeEtaleChart A T hT f hX' Uc :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (siteBaseChangeHom B (Spec (.of A)) hA (W := specAlgebraObj A T B hA hT)
      ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map α))
    (by
      change yoneda.map _ ≫ siteBaseChangeChartMap B (Spec (.of A)) hA f hX' Uc.obj.hom =
        siteBaseChangeChartMap B (Spec (.of A)) hA f hX' Vc.obj.hom
      rw [← CostructuredArrow.w α.hom, siteBaseChangeChartMap_siteBaseChangeHom]
      rfl))

/-- **The base change of a covering chart covers the base change.** If the one-element family
of an étale chart `U` of `X` covers the final object of the small étale site of `X`, then the
one-element family of its base change covers the final object of the small étale site of `X'`. -/
theorem coversTop_siteBaseChangeEtaleChart (Uc : SmallEtale B (Spec (.of A)) hA X.obj)
    (hUsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf Uc.obj.hom) :
    (SmallEtale.topology B (Spec (.of A)) hA X'.obj).CoversTop
      (fun _ : Unit => siteBaseChangeEtaleChart A T hT f hX' Uc) :=
  have hsurj' := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (isPullback_siteBaseChangeChartMap B (Spec (.of A)) hA f hX' Uc.obj.hom) hUsurj
  GrothendieckTopology.coversTop_punit
    (SmallEtale.coversTop_of_isSurjective B (Spec (.of A)) hA X'.obj X'.property
      (siteBaseChangeEtaleChart A T hT f hX' Uc)
      (isSurjective_of_presheafSurjective B (Spec (.of A)) hA _ hsurj'))

/-- **Flat base change for the global functions of an algebraic space, in degree zero.** Let
`A` be a ring, `T` a flat `A`-algebra, `X` an algebraic space over `Spec A` and
`X' = X ×_{Spec A} Spec T`.  If `X` has a surjective étale chart `U` by an affine scheme whose
kernel pair `V = U ×_X U` is affine as well, then

`Γ(X', 𝒪_{X'}) = T ⊗_A Γ(X, 𝒪_X)`. -/
def globalFunctionsBaseChangeRingEquiv [Module.Flat A T]
    {Uc Vc : SmallEtale B (Spec (.of A)) hA X.obj} (α β : Vc ⟶ Uc)
    [IsAffine (chartScheme Uc)] [IsAffine (chartScheme Vc)]
    (hcov : (SmallEtale.topology B (Spec (.of A)) hA X.obj).CoversTop (fun _ : Unit => Uc))
    (hsq : IsPullback (yoneda.map ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map α))
      (yoneda.map ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map β))
      Uc.obj.hom Uc.obj.hom)
    (hUsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf Uc.obj.hom) :
    globalFunctions B (Spec (.of A)) hA X'.obj ≃+*
      T ⊗[A] globalFunctions B (Spec (.of A)) hA X.obj :=
  (globalFunctionsEqualizerAlgEquiv A X' (siteBaseChangeEtaleChartHom A T hT f hX' α)
        (siteBaseChangeEtaleChartHom A T hT f hX' β)
        (coversTop_siteBaseChangeEtaleChart A T hT f hX' Uc hUsurj)
        (isPullback_kernelPair_siteBaseChangeChartMap B (Spec (.of A)) hA f hX' _ _
          hsq)).toRingEquiv.trans
    (((equalizerSiteBaseChangeRingEquiv A T hT
          ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map α)
          ((SmallEtale.toOver B (Spec (.of A)) hA X.obj).map β)).symm).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := T))
        (globalFunctionsEqualizerAlgEquiv A X α β hcov hsq)).symm.toRingEquiv)

/-! ### The quasi-compact separated case -/

include hT f hX'

/-- **Flat base change for the global functions of a quasi-compact separated algebraic space,
in degree zero.** For a ring `A`, a flat `A`-algebra `T`, a quasi-compact and separated
algebraic space `X` over `Spec A` and its base change `X' = X ×_{Spec A} Spec T`,

`Γ(X', 𝒪_{X'}) = T ⊗_A Γ(X, 𝒪_X)`. -/
theorem nonempty_ringEquiv_globalFunctions_baseChange [Module.Flat A T]
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B (Spec (.of A)) hA X.obj)
    (hsep : IsAbsolutelySeparated B (Spec (.of A)) hA hZ X.obj) :
    Nonempty (globalFunctions B (Spec (.of A)) hA X'.obj ≃+*
      T ⊗[A] globalFunctions B (Spec (.of A)) hA X.obj) := by
  classical
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B (Spec (.of A)) hA X.obj
      X.property).mp hqc
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf (yoneda.map (𝟙 U)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of A)) hA
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have haet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf a := by
    have h := haet U (yoneda.map (𝟙 U)) hid
    rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h
  obtain ⟨W, p, qq, hsq⟩ := isAffineHom_of_affine_source_of_isAbsolutelySeparated
    B (Spec (.of A)) hA hZ ⟨U, hUaff⟩ a hsep ⟨U, hUaff⟩ a
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : (BigAffineFppf.inclusion B (Spec (.of A)) hA).obj W ⟶ U,
      yoneda.map p₀ = p := ⟨yoneda.preimage p, yoneda.map_preimage p⟩
  rw [← hp₀] at hsq
  have hp₀et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)) p₀ :=
    haet'.property a (yoneda.map qq) p₀ hsq.flip
  have hUa : IsAffine (chartScheme
      (⟨CostructuredArrow.mk a, haet'⟩ : SmallEtale B (Spec (.of A)) hA X.obj)) := hUaff
  have hVa : IsAffine (chartScheme
      (⟨CostructuredArrow.mk (yoneda.map p₀ ≫ a),
        chart_preimage_etale B (Spec (.of A)) hA X a haet' p₀ hp₀et⟩ :
          SmallEtale B (Spec (.of A)) hA X.obj)) := W.property
  refine ⟨globalFunctionsBaseChangeRingEquiv A T hT f hX'
    (Uc := ⟨CostructuredArrow.mk a, haet'⟩)
    (Vc := ⟨CostructuredArrow.mk (yoneda.map p₀ ≫ a),
      chart_preimage_etale B (Spec (.of A)) hA X a haet' p₀ hp₀et⟩)
    (ObjectProperty.homMk (CostructuredArrow.homMk p₀ rfl))
    (ObjectProperty.homMk (CostructuredArrow.homMk qq hsq.w.symm))
    (GrothendieckTopology.coversTop_punit
      (SmallEtale.coversTop_of_isSurjective B (Spec (.of A)) hA X.obj X.property
        ⟨CostructuredArrow.mk a, haet'⟩
        (isSurjective_of_presheafSurjective B (Spec (.of A)) hA a hasurj)))
    hsq hasurj⟩

end AlgebraicGeometry.Space

end
