module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalDeformationSheafAction
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale

/-!
# Infinitesimal deformations of maps and étale localization, for arbitrary schemes

Consider a commutative diagram of first-order thickenings together with a commutative square of
schemes,
```
(T₂ ⊂ T₂') --(a₂, a₂')--> (X₂ ⊂ X₂')        X₂' --> S₂
   |                          |               |       |
 (h, h')                   (f, f')            v       v
   v                          v              X₁' --> S₁
(T₁ ⊂ T₁') --(a₁, a₁')--> (X₁ ⊂ X₁')
```
with `f : X₂ ⟶ X₁` and `k : S₂ ⟶ S₁` étale. An `𝒪_{T₁}`-linear map
`θ₁ : a₁^*Ω_{X₁/S₁} ⟶ 𝒞_{T₁/T₁'}` is transported to a map `θ₂ : a₂^*Ω_{X₂/S₂} ⟶ 𝒞_{T₂/T₂'}` along
the identification `a₂^*Ω_{X₂/S₂} = h^*a₁^*Ω_{X₁/S₁}` of [Stacks Project, Tag 04BX], and the two
actions of [Stacks Project, Tag 0CK1] are then compatible with the vertical maps:
```
(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁').
```
Nothing is assumed affine, `θ₁` and `θ₂` are morphisms of sheaves of modules, and the two actions
are the ones constructed by `Stacks.Thickenings.derivationActionSheaf`.

## Main definitions

* `Stacks.Thickenings.conormalSheafTranspose`: the map `h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}` of
  [Stacks Project, Tag 01R4], transposed along `h^* ⊣ h_*`.
* `Stacks.Thickenings.etaleDifferentialsInv`: the inverse of the canonical map
  `f^*Ω_{X₁/S₁} ⟶ Ω_{X₂/S₂}` of [Stacks Project, Tag 01UV], which is invertible by
  [Stacks Project, Tag 04BX].
* `Stacks.Thickenings.localizedDerivationSheaf`: the transported datum `θ₂`.
* `Stacks.Thickenings.localizedTranspose`: the composite `Ω_{X₁/S₁} ⟶ (a₂ ≫ f)_*𝒞_{T₂/T₂'}`
  that `θ₂` transposes to.

## Main results

* `RingedSpaceModuleAdjunction.homEquiv_modulePullbackSquareIso_inv_comp`: the transposition of
  the comparison of a commuting square across three adjunctions.
* `Stacks.Thickenings.homEquiv_localizedDerivationSheaf`: `θ₂` transposed is
  `Stacks.Thickenings.localizedTranspose` transposed back, precomposed with the inverse
  differential map.
* `Stacks.Thickenings.derivationSectionι_localizedDerivationSheaf`: the compatibility
  `D₂(f^♯ y) = (h')^♯(D₁ y)` of the derivations attached to `θ₁` and `θ₂`.
* `Stacks.Thickenings.derivationActionSheaf_comp_etaleLocalization`: the compatibility of the two
  actions, with no affineness assumption.

## Implementation notes

The transported datum `Stacks.Thickenings.localizedDerivationSheaf` is the composite
```
a₂^*Ω_{X₂/S₂} --a₂^*(d)⁻¹--> a₂^*f^*Ω_{X₁/S₁} ≅ h^*a₁^*Ω_{X₁/S₁} --h^*θ₁--> h^*𝒞_{T₁/T₁'}
  --Tag 01R4--> 𝒞_{T₂/T₂'}
```
where `d` is the canonical map of [Stacks Project, Tag 01UV], invertible by
`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_etale`
([Stacks Project, Tag 04BX]); the middle identification is
`RingedSpaceModuleAdjunction.modulePullbackSquareIso` of the square `a₂ ≫ f = h ≫ a₁`; and the
last map is `Stacks.Immersion.immersionConormalSheafMap` for the square `i₂ ≫ h' = h ≫ i₁`.

`X₂ ⊂ X₂'` and `X₁ ⊂ X₁'` are not assumed to be first-order thickenings. The commutativity of the
square of bases is assumed only as the square `f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k` of the closed
subschemes, which the ambient square `f' ≫ p₁ = p₂ ≫ k` implies.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 02H5](https://stacks.math.columbia.edu/tag/02H5)
* [Stacks Project, Tag 04BV](https://stacks.math.columbia.edu/tag/04BV)
* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX)
* [Stacks Project, Tag 04BY](https://stacks.math.columbia.edu/tag/04BY)
* [Stacks Project, Tag 04BZ](https://stacks.math.columbia.edu/tag/04BZ)
* [Stacks Project, Tag 0CK1](https://stacks.math.columbia.edu/tag/0CK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction Opposite TopologicalSpace
open Stacks.Immersion

universe u

namespace RingedSpaceModuleAdjunction

/-! ### Transposing the comparison of a commuting square -/

/-- **The pullback comparison of a commuting square, transposed across its two right-hand
adjunctions.** For a commuting square `j₁ ≫ b = a ≫ j₂` of ringed spaces, a module `M` on the
far corner, a morphism `θ : b^*M ⟶ C₁` and a morphism `ψ : (j₁)^*C₁ ⟶ C₂`, the composite
```
a^*(j₂)^*M --comparison--> (j₁)^*b^*M --(j₁)^*θ--> (j₁)^*C₁ --ψ--> C₂
```
transposed first across `a^* ⊣ a_*` and then across `(j₂)^* ⊣ (j₂)_*` is `θ` and `ψ`
transposed, joined by `RingedSpaceModuleAdjunction.modulePushforwardSquareIso`. -/
theorem homEquiv_modulePullbackSquareIso_inv_comp
    {Z₁ Z₂ W₁ W₂ : RingedSpace.{u, u}} (a : Z₁ ⟶ Z₂) (b : W₁ ⟶ W₂) (j₁ : Z₁ ⟶ W₁)
    (j₂ : Z₂ ⟶ W₂) (comm : j₁ ≫ b = a ≫ j₂)
    (M : SheafOfModules.{u} (structureSheafRing W₂))
    (C₁ : SheafOfModules.{u} (structureSheafRing W₁))
    (C₂ : SheafOfModules.{u} (structureSheafRing Z₁))
    (θ : (modulePullback b).obj M ⟶ C₁) (ψ : (modulePullback j₁).obj C₁ ⟶ C₂) :
    (modulePullbackPushforwardAdjunction j₂).homEquiv _ _
        ((modulePullbackPushforwardAdjunction a).homEquiv _ _
          ((modulePullbackSquareIso a b j₁ j₂ comm).inv.app M ≫
            (modulePullback j₁).map θ ≫ ψ)) =
      (modulePullbackPushforwardAdjunction b).homEquiv _ _ θ ≫
        (modulePushforward b).map
            ((modulePullbackPushforwardAdjunction j₁).homEquiv _ _ ψ) ≫
          (modulePushforwardSquareIso a b j₁ j₂ comm).hom.app C₂ := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_modulePullbackSquareIso a b j₁ j₂ comm M]
  have nat1 := (modulePushforwardSquareIso a b j₁ j₂ comm).hom.naturality
    ((modulePullbackSquareIso a b j₁ j₂ comm).inv.app M)
  have nat2 := (modulePushforwardSquareIso a b j₁ j₂ comm).hom.naturality
    ((modulePullback j₁).map θ)
  have nat3 := (modulePushforwardSquareIso a b j₁ j₂ comm).hom.naturality ψ
  simp only [Functor.comp_map, Functor.comp_obj] at nat1 nat2 nat3
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map, Functor.comp_obj,
    Adjunction.homEquiv_unit]
  slice_lhs 4 5 => rw [← nat1]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Category.id_comp]
  slice_lhs 3 4 => rw [← nat2]
  slice_lhs 4 5 => rw [← nat3]
  slice_lhs 2 3 => rw [← Functor.map_comp,
    (modulePullbackPushforwardAdjunction j₁).unit_naturality θ, Functor.map_comp]
  simp only [Category.assoc]

end RingedSpaceModuleAdjunction

namespace Stacks.Thickenings

/-- Two restriction maps of a sheaf of modules on a scheme with the same source and target
agree. -/
theorem module_map_eq {X : Scheme.{u}} {M : X.Modules} {A B : (X.Opens)ᵒᵖ} (u v : A ⟶ B)
    (m : M.val.obj A) : M.val.map u m = M.val.map v m :=
  M.val.congr_map_apply (Quiver.Hom.unop_inj (Subsingleton.elim _ _)) m

/-- Restricting a section known to be a restriction of `y` is restricting `y` directly. -/
private theorem module_map_eq_map_of_eq {X : Scheme.{u}} {M : X.Modules} {A B C : (X.Opens)ᵒᵖ}
    {k : A ⟶ B} {v : B ⟶ C} (w : A ⟶ C) {x : M.val.obj B} {y : M.val.obj A}
    (h : x = M.val.map k y) : M.val.map v x = M.val.map w y :=
  h ▸ module_map_map k v w y

variable {S₁ S₂ T₁ T₁' T₂ T₂' X₁ X₁' X₂ X₂' : Scheme.{u}}
  {i₁ : T₁ ⟶ T₁'} {i₂ : T₂ ⟶ T₂'} {j₁ : X₁ ⟶ X₁'} {j₂ : X₂ ⟶ X₂'}
  {a₁ : T₁ ⟶ X₁} {a₁' : T₁' ⟶ X₁'} {a₂ : T₂ ⟶ X₂} {a₂' : T₂' ⟶ X₂'}
  {h : T₂ ⟶ T₁} {h' : T₂' ⟶ T₁'} {f : X₂ ⟶ X₁} {f' : X₂' ⟶ X₁'}
  [IsClosedImmersion i₁] [IsClosedImmersion i₂]

/-! ### The transposed conormal map -/

/-- **The map `h^*𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}` of [Stacks Project, Tag 01R4], transposed.** For a
morphism of thickenings `i₂ ≫ h' = h ≫ i₁` this is
`Stacks.Immersion.immersionConormalSheafMap` read across the adjunction `h^* ⊣ h_*`, that is a
morphism `𝒞_{T₁/T₁'} ⟶ h_*𝒞_{T₂/T₂'}`. -/
def conormalSheafTranspose (cT : i₂ ≫ h' = h ≫ i₁) :
    immersionConormalSheaf i₁ ⟶
      (modulePushforward h.toLRSHom.toShHom).obj (immersionConormalSheaf i₂) :=
  (modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
    (immersionConormalSheafMap i₂ i₁ h h' (toShHom_square cT))

/-- **`Stacks.Thickenings.conormalSheafTranspose` read inside the ambient structure sheaves is
the ring map `(h')^♯`.** For a conormal section `m` of `i₁` over `i₁⁻¹W`, the image under
`(h')^♯` of its image in `𝒪_{T₁'}` is the image in `𝒪_{T₂'}` of its image under the transposed
map of [Stacks Project, Tag 01R4]. -/
theorem app_conormalSheafTranspose (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (cT : i₂ ≫ h' = h ≫ i₁) (W : T₁'.Opens)
    (m : ((modulePushforward i₁.toLRSHom.toShHom).obj (immersionConormalSheaf i₁)).val.obj
      (op W)) :
    (h'.app W).hom ((firstOrderImmersionConormalSheafι i₁ hi₁).val.app (op W) m) =
      (firstOrderImmersionConormalSheafι i₂ hi₂).val.app (op (h' ⁻¹ᵁ W))
        ((Stacks.Conormal.conormalSheaf i₂).val.map
          (eqToHom (preimage_comp_eq cT W)).op
          ((conormalSheafTranspose cT).val.app (op (i₁ ⁻¹ᵁ W)) m)) := by
  refine (conormalTransportSheaf_apply hi₁ hi₂ cT W m).symm.trans ?_
  have hdef : conormalTransportSheaf hi₂ cT =
      (modulePushforward i₁.toLRSHom.toShHom).map (conormalSheafTranspose cT) ≫
        (modulePushforwardSquareIso h.toLRSHom.toShHom h'.toLRSHom.toShHom
              i₂.toLRSHom.toShHom i₁.toLRSHom.toShHom (toShHom_square cT)).inv.app
            (immersionConormalSheaf i₂) ≫
          (modulePushforward h'.toLRSHom.toShHom).map
            (firstOrderImmersionConormalSheafι i₂ hi₂) := rfl
  rw [hdef, AlgebraicGeometry.RingedSpace.comp_val_app_apply,
    AlgebraicGeometry.RingedSpace.comp_val_app_apply,
    AlgebraicGeometry.RingedSpace.modulePushforward_map_val_app,
    AlgebraicGeometry.RingedSpace.modulePushforward_map_val_app]
  refine congrArg
    ((firstOrderImmersionConormalSheafι i₂ hi₂).val.app (op (h' ⁻¹ᵁ W))) ?_
  refine (modulePushforwardSquareIso_inv_val_app h.toLRSHom.toShHom h'.toLRSHom.toShHom
    i₂.toLRSHom.toShHom i₁.toLRSHom.toShHom (toShHom_square cT) (immersionConormalSheaf i₂) W
    _).trans ?_
  exact module_map_eq (M := Stacks.Conormal.conormalSheaf i₂) _ _ _

/-! ### The transported datum -/

variable {p₁ : X₁' ⟶ S₁} {p₂ : X₂' ⟶ S₂} {k : S₂ ⟶ S₁}

/-- **The composite `Ω_{X₁/S₁} ⟶ (a₂ ≫ f)_*𝒞_{T₂/T₂'}` that the transported datum transposes
to.** It is `θ₁` transposed along `a₁^* ⊣ a_{1,*}`, then `a_{1,*}` of
`Stacks.Thickenings.conormalSheafTranspose`, then the pushforward comparison
`RingedSpaceModuleAdjunction.modulePushforwardSquareIso` of the square `a₂ ≫ f = h ≫ a₁`:
```
Ω_{X₁/S₁} ⟶ a_{1,*}𝒞_{T₁/T₁'} ⟶ a_{1,*}h_*𝒞_{T₂/T₂'} ≅ f_*a_{2,*}𝒞_{T₂/T₂'}.
``` -/
def localizedTranspose (cT : i₂ ≫ h' = h ≫ i₁) (cX : a₂ ≫ f = h ≫ a₁)
    (θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁) :
    Scheme.Hom.relativeDifferentials (j₁ ≫ p₁) ⟶
      (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward a₂).obj (Stacks.Conormal.conormalSheaf i₂)) :=
  (modulePullbackPushforwardAdjunction a₁.toLRSHom.toShHom).homEquiv _ _ θ₁ ≫
    (modulePushforward a₁.toLRSHom.toShHom).map (conormalSheafTranspose cT) ≫
      (modulePushforwardSquareIso a₂.toLRSHom.toShHom a₁.toLRSHom.toShHom h.toLRSHom.toShHom
        f.toLRSHom.toShHom (toShHom_square cX.symm)).hom.app
          (Stacks.Conormal.conormalSheaf i₂)

/-- **`Stacks.Thickenings.localizedTranspose` on sections.** Over an open `U` of `X₁` it is
`θ₁` transposed, followed by `Stacks.Thickenings.conormalSheafTranspose` and by the restriction
along the equality of opens `a₂⁻¹f⁻¹U = h⁻¹a₁⁻¹U`. -/
theorem app_localizedTranspose (cT : i₂ ≫ h' = h ≫ i₁) (cX : a₂ ≫ f = h ≫ a₁)
    (θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁) (U : X₁.Opens)
    (w : (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)).val.obj (op U)) :
    (localizedTranspose cT cX θ₁).val.app (op U) w =
      (Stacks.Conormal.conormalSheaf i₂).val.map (eqToHom (preimage_comp_eq cX U)).op
        ((conormalSheafTranspose cT).val.app (op (a₁ ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction a₁).homEquiv _ _ θ₁).val.app
            (op U) w)) :=
  (modulePushforwardSquareIso_hom_val_app a₂.toLRSHom.toShHom a₁.toLRSHom.toShHom
      h.toLRSHom.toShHom f.toLRSHom.toShHom (toShHom_square cX.symm)
      (Stacks.Conormal.conormalSheaf i₂) U _).trans
    (module_map_eq (M := Stacks.Conormal.conormalSheaf i₂) _ _ _)

/-- **The inverse `Ω_{X₂/S₂} ⟶ f^*Ω_{X₁/S₁}` of the canonical map of
[Stacks Project, Tag 01UV]**, which is invertible because `f` and `k` are étale
([Stacks Project, Tag 04BX]). -/
def etaleDifferentialsInv (cS : f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k] :
    Scheme.Hom.relativeDifferentials (j₂ ≫ p₂) ⟶
      (Scheme.Modules.pullback f).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) :=
  let := Scheme.Hom.isIso_relativeDifferentialsMap_of_etale f (j₁ ≫ p₁) (j₂ ≫ p₂) k cS
  inv (Scheme.Hom.relativeDifferentialsMap f (j₁ ≫ p₁) (j₂ ≫ p₂) k cS)

/-- `Stacks.Thickenings.etaleDifferentialsInv` is a right inverse of the canonical map of
[Stacks Project, Tag 01UV]. -/
theorem relativeDifferentialsMap_comp_etaleDifferentialsInv
    (cS : f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k] :
    Scheme.Hom.relativeDifferentialsMap f (j₁ ≫ p₁) (j₂ ≫ p₂) k cS ≫
        etaleDifferentialsInv cS = 𝟙 _ := by
  let := Scheme.Hom.isIso_relativeDifferentialsMap_of_etale f (j₁ ≫ p₁) (j₂ ≫ p₂) k cS
  exact IsIso.hom_inv_id _

/-- **The transported derivation datum `θ₂`.** The composite
```
a₂^*Ω_{X₂/S₂} --a₂^*(d)⁻¹--> a₂^*f^*Ω_{X₁/S₁} ≅ h^*a₁^*Ω_{X₁/S₁} --h^*θ₁--> h^*𝒞_{T₁/T₁'}
  --Tag 01R4--> 𝒞_{T₂/T₂'}
```
the pullback along `a₂` of `Stacks.Thickenings.etaleDifferentialsInv`, the
comparison `RingedSpaceModuleAdjunction.modulePullbackSquareIso` of the square
`a₂ ≫ f = h ≫ a₁`, the pullback along `h` of `θ₁`, and
`Stacks.Immersion.immersionConormalSheafMap` for the square `i₂ ≫ h' = h ≫ i₁`. -/
def localizedDerivationSheaf (cT : i₂ ≫ h' = h ≫ i₁) (cX : a₂ ≫ f = h ≫ a₁)
    (cS : f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k]
    (θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁) :
    (Scheme.Modules.pullback a₂).obj (Scheme.Hom.relativeDifferentials (j₂ ≫ p₂)) ⟶
      Stacks.Conormal.conormalSheaf i₂ :=
  (modulePullback a₂.toLRSHom.toShHom).map (etaleDifferentialsInv cS) ≫
    (modulePullbackSquareIso a₂.toLRSHom.toShHom a₁.toLRSHom.toShHom h.toLRSHom.toShHom
          f.toLRSHom.toShHom (toShHom_square cX.symm)).inv.app
        (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ≫
      (modulePullback h.toLRSHom.toShHom).map θ₁ ≫
        immersionConormalSheafMap i₂ i₁ h h' (toShHom_square cT)

/-- **The transported datum, transposed.** Along `a₂^* ⊣ a_{2,*}` the datum `θ₂` becomes
`Stacks.Thickenings.etaleDifferentialsInv` followed by `Stacks.Thickenings.localizedTranspose`
transposed back along `f^* ⊣ f_*`. -/
theorem homEquiv_localizedDerivationSheaf (cT : i₂ ≫ h' = h ≫ i₁) (cX : a₂ ≫ f = h ≫ a₁)
    (cS : f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k]
    (θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁) :
    (Scheme.Modules.pullbackPushforwardAdjunction a₂).homEquiv _ _
        (localizedDerivationSheaf cT cX cS θ₁) =
      etaleDifferentialsInv cS ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
          (localizedTranspose cT cX θ₁) :=
  ((modulePullbackPushforwardAdjunction a₂.toLRSHom.toShHom).homEquiv_naturality_left
      (etaleDifferentialsInv cS) _).trans
    (congrArg (fun z => etaleDifferentialsInv cS ≫ z)
      ((Equiv.eq_symm_apply _).mpr
        (homEquiv_modulePullbackSquareIso_inv_comp a₂.toLRSHom.toShHom a₁.toLRSHom.toShHom
          h.toLRSHom.toShHom f.toLRSHom.toShHom (toShHom_square cX.symm) _ _ _ θ₁ _)))

/-- **The transported datum on the differential of a section coming from `X₁`.** Transposed
along `a₂^* ⊣ a_{2,*}` and evaluated on `d_{X₂/S₂}(f^♯ y)`, the datum `θ₂` gives the value of
`Stacks.Thickenings.localizedTranspose` on `d_{X₁/S₁} y`. -/
theorem app_localizedDerivationSheaf (cT : i₂ ≫ h' = h ≫ i₁) (cX : a₂ ≫ f = h ≫ a₁)
    (cS : f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k]
    (θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁)
    (U : X₁.Opens) (y : Γ(X₁, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction a₂).homEquiv _ _
          (localizedDerivationSheaf cT cX cS θ₁)).val.app (op (f ⁻¹ᵁ U)))
        ((Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d ((f.app U).hom y)) =
      (localizedTranspose cT cX θ₁).val.app (op U)
        ((Scheme.Hom.universalRelativeDerivation (j₁ ≫ p₁)).d y) := by
  set c := Scheme.Hom.relativeDifferentialsMap f (j₁ ≫ p₁) (j₂ ≫ p₂) k cS with hc'
  set Ξ := localizedTranspose cT cX θ₁
  have hc : Scheme.Hom.IsRelativeDifferentialsMap f (j₁ ≫ p₁) (j₂ ≫ p₂) c :=
    (Scheme.Hom.isRelativeDifferentialsMap_iff_eq f (j₁ ≫ p₁) (j₂ ≫ p₂) k cS c).mpr rfl
  have hΘ := homEquiv_localizedDerivationSheaf cT cX cS θ₁
  have hkey : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ c ≫
      (Scheme.Modules.pushforward f).map
        (etaleDifferentialsInv cS ≫
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm Ξ) = Ξ := by
    rw [← Adjunction.homEquiv_naturality_right, ← Category.assoc, hc',
      relativeDifferentialsMap_comp_etaleDifferentialsInv, Category.id_comp,
      Equiv.apply_symm_apply]
  have hsec := congrArg (fun φ => φ.val.app (op U)
    ((Scheme.Hom.universalRelativeDerivation (j₁ ≫ p₁)).d y)) hkey
  simp only at hsec
  rw [hΘ]
  refine Eq.trans ?_ hsec
  exact congrArg
    ((etaleDifferentialsInv cS ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm Ξ).val.app
      (op (f ⁻¹ᵁ U))) (hc U y).symm

/-! ### The compatibility of the two data -/

/-- **The compatibility `D₂(f^♯ y) = (h')^♯(D₁ y)`.** The derivations `D_n = θ_n ∘ d_{X_n/S_n}`
of Equation [Stacks Project, Tag 04BV] attached to `θ₁` and to the transported datum
`Stacks.Thickenings.localizedDerivationSheaf`, read inside the ambient structure sheaves, are
compatible: on a section `s` of `𝒪_{X₁'}` over `V`, the image under `(h')^♯` of `D₁(j₁^♯ s)` is
`D₂(j₂^♯(f')^♯ s)`. -/
theorem derivationSectionι_localizedDerivationSheaf
    (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (ca₁ : i₁ ≫ a₁' = a₁ ≫ j₁) (ca₂ : i₂ ≫ a₂' = a₂ ≫ j₂)
    (cT : i₂ ≫ h' = h ≫ i₁) (cj : j₂ ≫ f' = f ≫ j₁) (cX : a₂ ≫ f = h ≫ a₁)
    (cA : a₂' ≫ f' = h' ≫ a₁') (cS : f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k]
    (θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁)
    (V : X₁'.Opens) (s : Γ(X₁', V)) :
    (T₂'.presheaf.map (eqToHom (preimage_comp_eq cA V)).op).hom
        ((h'.app (a₁' ⁻¹ᵁ V)).hom (derivationSectionι hi₁ p₁ ca₁ θ₁ V ((j₁.app V).hom s)))
      = derivationSectionι hi₂ p₂ ca₂ (localizedDerivationSheaf cT cX cS θ₁) (f' ⁻¹ᵁ V)
          ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s)) := by
  have E : i₂ ⁻¹ᵁ (a₂' ⁻¹ᵁ (f' ⁻¹ᵁ V)) = h ⁻¹ᵁ (a₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ V)) := by
    have hcomp : i₂ ≫ a₂' ≫ f' = h ≫ a₁ ≫ j₁ := by
      rw [reassoc_of% ca₂, cj, reassoc_of% cX]
    exact congrArg (fun p : T₂ ⟶ X₁' => p ⁻¹ᵁ V) hcomp
  set m₁ := ((Scheme.Modules.pullbackPushforwardAdjunction a₁).homEquiv _ _ θ₁).val.app
    (op (j₁ ⁻¹ᵁ V))
      ((Scheme.Hom.universalRelativeDerivation (j₁ ≫ p₁)).d ((j₁.app V).hom s)) with hm₁
  set n := (conormalSheafTranspose cT).val.app (op (a₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ V))) m₁ with hn
  have e1 : i₂ ⁻¹ᵁ (h' ⁻¹ᵁ (a₁' ⁻¹ᵁ V)) = h ⁻¹ᵁ (a₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ V)) :=
    (preimage_comp_eq cT (a₁' ⁻¹ᵁ V)).trans
      (congrArg (fun W : T₁.Opens => h ⁻¹ᵁ W) (preimage_square ca₁ V))
  have L1 : derivationSectionι hi₁ p₁ ca₁ θ₁ V ((j₁.app V).hom s) =
      (firstOrderImmersionConormalSheafι i₁ hi₁).val.app (op (a₁' ⁻¹ᵁ V))
        ((Stacks.Conormal.conormalSheaf i₁).val.map (eqToHom (preimage_square ca₁ V)).op m₁) :=
    rfl
  have L2 := app_conormalSheafTranspose hi₁ hi₂ cT (a₁' ⁻¹ᵁ V)
    ((Stacks.Conormal.conormalSheaf i₁).val.map (eqToHom (preimage_square ca₁ V)).op m₁)
  have L3 : (conormalSheafTranspose cT).val.app (op (i₁ ⁻¹ᵁ (a₁' ⁻¹ᵁ V)))
        ((Stacks.Conormal.conormalSheaf i₁).val.map (eqToHom (preimage_square ca₁ V)).op m₁) =
      (Stacks.Conormal.conormalSheaf i₂).val.map
        (eqToHom (congrArg (fun W : T₁.Opens => h ⁻¹ᵁ W) (preimage_square ca₁ V))).op n :=
    PresheafOfModules.naturality_apply (conormalSheafTranspose cT).val
      (eqToHom (preimage_square ca₁ V)).op m₁
  have L23 : (h'.app (a₁' ⁻¹ᵁ V)).hom
        ((firstOrderImmersionConormalSheafι i₁ hi₁).val.app (op (a₁' ⁻¹ᵁ V))
          ((Stacks.Conormal.conormalSheaf i₁).val.map (eqToHom (preimage_square ca₁ V)).op m₁)) =
      (firstOrderImmersionConormalSheafι i₂ hi₂).val.app (op (h' ⁻¹ᵁ (a₁' ⁻¹ᵁ V)))
        ((Stacks.Conormal.conormalSheaf i₂).val.map (eqToHom e1).op n) :=
    L2.trans (congrArg _ (module_map_eq_map_of_eq _ L3))
  have hL : (T₂'.presheaf.map (eqToHom (preimage_comp_eq cA V)).op).hom
        ((h'.app (a₁' ⁻¹ᵁ V)).hom (derivationSectionι hi₁ p₁ ca₁ θ₁ V ((j₁.app V).hom s)))
      = (firstOrderImmersionConormalSheafι i₂ hi₂).val.app (op (a₂' ⁻¹ᵁ (f' ⁻¹ᵁ V)))
          ((Stacks.Conormal.conormalSheaf i₂).val.map (eqToHom E).op n) := by
    rw [L1, L23]
    refine (PresheafOfModules.naturality_apply (firstOrderImmersionConormalSheafι i₂ hi₂).val
      (eqToHom (preimage_comp_eq cA V)).op _).symm.trans ?_
    exact congrArg _ (module_map_map (M := Stacks.Conormal.conormalSheaf i₂) _ _
      (eqToHom E).op n)
  have hy : (j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s) =
      (X₂.presheaf.map (eqToHom (preimage_comp_eq cj V)).op).hom
        ((f.app (j₁ ⁻¹ᵁ V)).hom ((j₁.app V).hom s)) := by
    have hcj := Scheme.Hom.congr_app cj V
    rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hcj
    exact congrArg (fun φ : Γ(X₁', V) ⟶ Γ(X₂, j₂ ⁻¹ᵁ (f' ⁻¹ᵁ V)) => φ.hom s) hcj
  have hΞ : (localizedTranspose cT cX θ₁).val.app (op (j₁ ⁻¹ᵁ V))
        ((Scheme.Hom.universalRelativeDerivation (j₁ ≫ p₁)).d ((j₁.app V).hom s)) =
      (Stacks.Conormal.conormalSheaf i₂).val.map
        (eqToHom (preimage_comp_eq cX (j₁ ⁻¹ᵁ V))).op n :=
    app_localizedTranspose cT cX θ₁ (j₁ ⁻¹ᵁ V) _
  have hd : (Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d
        ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s)) =
      (Scheme.Hom.relativeDifferentials (j₂ ≫ p₂)).val.map
        (eqToHom (preimage_comp_eq cj V)).op
        ((Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d
          ((f.app (j₁ ⁻¹ᵁ V)).hom ((j₁.app V).hom s))) := by
    rw [hy]
    exact (Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d_map _ _
  have e2 : a₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ (f' ⁻¹ᵁ V)) = h ⁻¹ᵁ (a₁ ⁻¹ᵁ (j₁ ⁻¹ᵁ V)) :=
    (congrArg (fun W : X₂.Opens => a₂ ⁻¹ᵁ W) (preimage_comp_eq cj V)).trans
      (preimage_comp_eq cX (j₁ ⁻¹ᵁ V))
  have hR : derivationSectionι hi₂ p₂ ca₂ (localizedDerivationSheaf cT cX cS θ₁) (f' ⁻¹ᵁ V)
        ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s))
      = (firstOrderImmersionConormalSheafι i₂ hi₂).val.app (op (a₂' ⁻¹ᵁ (f' ⁻¹ᵁ V)))
          ((Stacks.Conormal.conormalSheaf i₂).val.map (eqToHom E).op n) := by
    obtain ⟨Θ₂, hΘ₂⟩ : ∃ Θ₂, (Scheme.Modules.pullbackPushforwardAdjunction a₂).homEquiv
        (Scheme.Hom.relativeDifferentials (j₂ ≫ p₂)) (Stacks.Conormal.conormalSheaf i₂)
        (localizedDerivationSheaf cT cX cS θ₁) = Θ₂ := ⟨_, rfl⟩
    have R1 : derivationSectionι hi₂ p₂ ca₂ (localizedDerivationSheaf cT cX cS θ₁) (f' ⁻¹ᵁ V)
          ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s)) =
        (firstOrderImmersionConormalSheafι i₂ hi₂).val.app (op (a₂' ⁻¹ᵁ (f' ⁻¹ᵁ V)))
          ((Stacks.Conormal.conormalSheaf i₂).val.map
            (eqToHom (preimage_square ca₂ (f' ⁻¹ᵁ V))).op
            (Θ₂.val.app (op (j₂ ⁻¹ᵁ (f' ⁻¹ᵁ V)))
              ((Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d
                ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s))))) := by
      rw [← hΘ₂]
      exact rfl
    have hΘnat : Θ₂.val.app (op (j₂ ⁻¹ᵁ (f' ⁻¹ᵁ V)))
          ((Scheme.Hom.relativeDifferentials (j₂ ≫ p₂)).val.map
            (eqToHom (preimage_comp_eq cj V)).op
            ((Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d
              ((f.app (j₁ ⁻¹ᵁ V)).hom ((j₁.app V).hom s)))) =
        (Stacks.Conormal.conormalSheaf i₂).val.map
          (eqToHom (congrArg (fun W : X₂.Opens => a₂ ⁻¹ᵁ W) (preimage_comp_eq cj V))).op
          (Θ₂.val.app (op (f ⁻¹ᵁ (j₁ ⁻¹ᵁ V)))
            ((Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d
              ((f.app (j₁ ⁻¹ᵁ V)).hom ((j₁.app V).hom s)))) :=
      PresheafOfModules.naturality_apply Θ₂.val (eqToHom (preimage_comp_eq cj V)).op _
    have hA := app_localizedDerivationSheaf cT cX cS θ₁ (j₁ ⁻¹ᵁ V) ((j₁.app V).hom s)
    rw [hΘ₂] at hA
    have step1 : Θ₂.val.app (op (j₂ ⁻¹ᵁ (f' ⁻¹ᵁ V)))
          ((Scheme.Hom.universalRelativeDerivation (j₂ ≫ p₂)).d
            ((j₂.app (f' ⁻¹ᵁ V)).hom ((f'.app V).hom s))) =
        (Stacks.Conormal.conormalSheaf i₂).val.map (eqToHom e2).op n := by
      exact (congrArg (Θ₂.val.app (op (j₂ ⁻¹ᵁ (f' ⁻¹ᵁ V)))) hd).trans
        (hΘnat.trans (module_map_eq_map_of_eq _ (hA.trans hΞ)))
    refine R1.trans (congrArg
      ((firstOrderImmersionConormalSheafι i₂ hi₂).val.app (op (a₂' ⁻¹ᵁ (f' ⁻¹ᵁ V)))) ?_)
    exact module_map_eq_map_of_eq _ step1
  exact hL.trans hR.symm

/-! ### The compatibility of the actions -/

/-- **Acting by a derivation commutes with an étale localization.** Let
`(h, h') : (T₂ ⊂ T₂') ⟶ (T₁ ⊂ T₁')` be a morphism of first-order thickenings, let
`(f, f') : (X₂ ⟶ X₂') ⟶ (X₁ ⟶ X₁')` be a morphism of the right-hand pairs, let `(a₁, a₁')` and
`(a₂, a₂')` be morphisms of thickenings compatible with them, and let `p₁ : X₁' ⟶ S₁`,
`p₂ : X₂' ⟶ S₂` and `k : S₂ ⟶ S₁` form a commutative square with `f`. Assume `f` and `k` are étale.
Then for every `𝒪_{T₁}`-linear `θ₁ : a₁^*Ω_{X₁/S₁} ⟶ 𝒞_{T₁/T₁'}`, the lifts `θ₁ ⬝ a₁'` and
`θ₂ ⬝ a₂'` of [Stacks Project, Tag 0CK1] — for `θ₂` the transported datum
`Stacks.Thickenings.localizedDerivationSheaf` — give a commutative square:
```
(θ₂ ⬝ a₂') ≫ f' = h' ≫ (θ₁ ⬝ a₁').
```

Nothing is assumed affine, and both actions are the ones constructed by
`Stacks.Thickenings.derivationActionSheaf`, not morphisms assumed to satisfy a relation.

`j₁` and `j₂` are not assumed to be first-order thickenings, and the commutativity of the square
of bases is assumed only as the square `f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k` of the closed subschemes,
which the ambient square `f' ≫ p₁ = p₂ ≫ k` implies. -/
@[stacks 04BY]
theorem derivationActionSheaf_comp_etaleLocalization
    (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (ca₁ : i₁ ≫ a₁' = a₁ ≫ j₁) (ca₂ : i₂ ≫ a₂' = a₂ ≫ j₂)
    (cT : i₂ ≫ h' = h ≫ i₁) (cj : j₂ ≫ f' = f ≫ j₁) (cX : a₂ ≫ f = h ≫ a₁)
    (cA : a₂' ≫ f' = h' ≫ a₁') (cS : f ≫ (j₁ ≫ p₁) = (j₂ ≫ p₂) ≫ k)
    [AlgebraicGeometry.Etale f] [AlgebraicGeometry.Etale k]
    (θ₁ : (Scheme.Modules.pullback a₁).obj (Scheme.Hom.relativeDifferentials (j₁ ≫ p₁)) ⟶
      Stacks.Conormal.conormalSheaf i₁) :
    derivationActionSheaf hi₂ p₂ ca₂ (localizedDerivationSheaf cT cX cS θ₁) ≫ f' =
      h' ≫ derivationActionSheaf hi₁ p₁ ca₁ θ₁ :=
  derivationActionSheaf_comp_of_derivationSection_comm hi₁ hi₂ p₁ p₂ ca₁ ca₂ cT cj cX cA
    (derivationSectionι_localizedDerivationSheaf hi₁ hi₂ ca₁ ca₂ cT cj cX cA cS θ₁)

end Stacks.Thickenings

end
