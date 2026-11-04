module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethCechHodgeClass
public import StacksFrontier.AlgebraicGeometry.DeRham.KunnethWedgeSection
public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.BoxSectionsAffine

/-!
# Differential forms on a product of affine opens

Let `k` be a field, let `f : X ⟶ Spec k` and `g : Y ⟶ Spec k` be schemes over `k`, and let
`W = X ×_k Y` with projections `pr₁`, `pr₂`. For opens `U ⊆ X` and `V ⊆ Y` write
`U × V = pr₁⁻¹U ∩ pr₂⁻¹V`. Pulling back along the projections and multiplying in the exterior
algebra of `Ω_{W/k}` gives, in each degree `r`, the `k`-linear map

`⨁_{a + c = r} Γ(U, Ω^a_{X/k}) ⊗_k Γ(V, Ω^c_{Y/k}) ⟶ Γ(U × V, Ω^r_{W/k})`,
`ω ⊗ η ↦ (pr₁^*ω)|_{U × V} ∧ (pr₂^*η)|_{U × V}`.

It commutes with restriction to smaller opens `U' ⊆ U`, `V' ⊆ V`, and it is bijective when `U`
and `V` are affine. This is the computation on a product of affine opens which, together with the
Künneth formula for Čech cohomology, gives the Künneth formula for Hodge cohomology of
[Stacks, Remark 0FWE].

## Main definitions

* `Stacks.HodgeWeil.kunnethSectionsMap`: the map above.

## Main results

* `Stacks.HodgeWeil.kunnethSectionsMap_lof_tmul`: its value on `ω ⊗ η` in the summand of index
  `(a, c)` is `(pr₁^*ω)|_{U × V} ∧ (pr₂^*η)|_{U × V}`, read in degree `r` along `a + c = r`;
  `Stacks.HodgeWeil.kunnethSectionsMap_lof_tmul_add` is the case `r = a + c`.
* `Stacks.HodgeWeil.kunnethSectionsMap_naturality`: it commutes with restriction.
* `Stacks.HodgeWeil.bijective_kunnethSectionsMap`: it is bijective for `U` and `V` affine.
* `Stacks.HodgeWeil.bijective_toModule_sectionsKHom_biproduct_ι`: the sections of a finite
  biproduct of `𝒪_W`-modules are the direct sum of the sections of the summands.

## Implementation notes

The map is the composite of four maps, each of which is bijective over a product of affine opens.

* The identity of `Γ(U, Ω^a_{X/k})`, from the `k`-structure of `Stacks.HodgeWeil.hodgeSectionsK`
  (through `k ⟶ Γ(X, f⁻¹𝒪_{Spec k})`) to that of `Stacks.CechKunneth.sectionsK` (through
  `k ⟶ Γ(X, 𝒪_X)`); the two actions agree by `Stacks.HodgeWeil.hodgeSectionsK_smul`.
* `ω ⊗ η ↦ ω ⊠ η` into the sections of `Ω^a_{X/k} ⊠ Ω^c_{Y/k}` over `U × V`, which is
  `Stacks.CechKunneth.boxMap` and is bijective on affines by
  `Stacks.CechKunneth.bijective_boxMap_app`.
* The inclusion of the summands into the biproduct `⨁_{a + c = r} Ω^a_{X/k} ⊠ Ω^c_{Y/k}`, read
  on sections over `U × V`.
* The degreewise Künneth isomorphism `⨁_{a + c = r} Ω^a_{X/k} ⊠ Ω^c_{Y/k} ≅ Ω^r_{W/k}` of
  [Stacks, Tag 0FMA], `AlgebraicGeometry.Scheme.Hom.deRhamBoxModuleIso`, read on sections.

The wedge formula is then the evaluation of the degreewise Künneth isomorphism on an external
tensor section,
`AlgebraicGeometry.Scheme.Hom.prodWedgeHom_deRhamBoxSummandIso_inv_externalTensorSection`.
The open `U × V` is written `pr₁⁻¹U ⊓ pr₂⁻¹V`, which is
`(Stacks.CechKunneth.boxOpen f g).obj (U, V)` by definition.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FMA](https://stacks.math.columbia.edu/tag/0FMA)
* [Stacks Project, Tag 01V1](https://stacks.math.columbia.edu/tag/01V1)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.HodgeWeil

section Scalars

variable {k : Type u} [CommRing k] {X S : Scheme.{u}} (f : X ⟶ S)
  (τ : k →+* S.sheaf.obj.obj (op ⊤))

/-- **The scalars of `hodgeSectionsK` act through the structure morphism**: `x ∈ k` acts on
`Γ(V, Ω^p_{X/S})` as the function `f^♯(τ x)` restricted to `V`. -/
theorem hodgeSectionsK_smul (p : ℕ) (V : X.Opens) (x : k)
    (ω : (hodgeSectionsK f (hodgeScalars τ f) p).obj (op V)) :
    (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from x • ω) =
      (f.appLE ⊤ V le_top).hom (τ x) •
        (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from ω) := by
  have h := ConcreteCategory.congr_hom
    (Scheme.Hom.inverseImageGlobalSections_comp_inverseImageStructureMap_app f) (τ x)
  have e : (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from x • ω) =
      (show Γ(X, V) from ((inverseImageStructureMap f).hom.app (op V)).hom
        (((f.inverseImageRingSheaf).obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom
          (hodgeScalars τ f x))) •
        (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from ω) := rfl
  rw [e]
  have n := ConcreteCategory.congr_hom ((inverseImageStructureMap f).hom.naturality
    (homOfLE (le_top : V ≤ ⊤)).op) (hodgeScalars τ f x)
  refine congrArg (fun r : Γ(X, V) =>
    r • (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from ω)) ?_
  exact n.trans (congrArg (X.sheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom h)

/-- The sections of `Ω^p_{X/S}` over `V` with the `k`-structure of `hodgeSectionsK` are the
sections with the `k`-structure of `Stacks.CechKunneth.sectionsK`: the identity is `k`-linear. -/
def hodgeSectionsKEquiv (p : ℕ) (V : X.Opens) :
    (hodgeSectionsK f (hodgeScalars τ f) p).obj (op V) ≃ₗ[k]
      (Stacks.CechKunneth.sectionsK X (Stacks.CechKunneth.baseRingHom τ f)
        (Scheme.Hom.relativeDifferentialForms f (p : ℤ))).obj (op V) where
  toFun ω := ω
  invFun ω := ω
  map_add' _ _ := rfl
  map_smul' x ω := (hodgeSectionsK_smul f τ p V x ω).trans
    (congrArg (fun r : Γ(X, V) =>
      r • (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from ω))
      (Stacks.CechKunneth.map_baseRingHom τ f V x).symm)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Stacks.HodgeWeil.hodgeSectionsKEquiv` is the identity on sections. -/
theorem hodgeSectionsKEquiv_apply (p : ℕ) (V : X.Opens)
    (ω : (hodgeSectionsK f (hodgeScalars τ f) p).obj (op V)) :
    (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from
      hodgeSectionsKEquiv f τ p V ω) = ω :=
  rfl

/-- The inverse of `Stacks.HodgeWeil.hodgeSectionsKEquiv` is the identity on sections. -/
theorem hodgeSectionsKEquiv_symm_apply (p : ℕ) (V : X.Opens)
    (ω : (Stacks.CechKunneth.sectionsK X (Stacks.CechKunneth.baseRingHom τ f)
      (Scheme.Hom.relativeDifferentialForms f (p : ℤ))).obj (op V)) :
    (show Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), V) from
      (hodgeSectionsKEquiv f τ p V).symm ω) = ω :=
  rfl

end Scalars

section SectionsK

variable {k : Type u} [CommRing k] {W : Scheme.{u}} (φ : k →+* Γ(W, ⊤))

/-- A morphism of `𝒪_W`-modules on the sections over `V`, as a `k`-linear map of the sections
with the `k`-structure of `Stacks.CechKunneth.sectionsK`. -/
def sectionsKHom {M N : W.Modules} (h : M ⟶ N) (V : W.Opens) :
    (Stacks.CechKunneth.sectionsK W φ M).obj (op V) →ₗ[k]
      (Stacks.CechKunneth.sectionsK W φ N).obj (op V) where
  toFun s := h.app V s
  map_add' s s' := map_add (h.app V).hom s s'
  map_smul' x s := Scheme.Modules.Hom.app_smul (U := V) h
    ((W.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (φ x)) (show Γ(M, V) from s)

/-- `Stacks.HodgeWeil.sectionsKHom` is the morphism on sections. -/
theorem sectionsKHom_apply {M N : W.Modules} (h : M ⟶ N) (V : W.Opens)
    (s : (Stacks.CechKunneth.sectionsK W φ M).obj (op V)) :
    sectionsKHom φ h V s = h.app V s :=
  rfl

/-- Applying a relation `a ≫ b = c` of morphisms of `𝒪_W`-modules to a section over `V`. -/
private theorem app_comp_apply {M N P : W.Modules} {a : M ⟶ N} {b : N ⟶ P} {c : M ⟶ P}
    (e : a ≫ b = c) (V : W.Opens) (s : Γ(M, V)) : b.app V (a.app V s) = c.app V s :=
  ConcreteCategory.congr_hom (congrArg (fun ψ => Scheme.Modules.Hom.app ψ V) e) s

/-- An isomorphism of `𝒪_W`-modules is bijective on sections. -/
theorem bijective_sectionsKHom {M N : W.Modules} (e : M ≅ N) (V : W.Opens) :
    Function.Bijective (sectionsKHom φ e.hom V) := by
  refine ⟨fun s s' hs => ?_, fun t => ⟨sectionsKHom φ e.inv V t, ?_⟩⟩
  · exact (app_comp_apply e.hom_inv_id V (show Γ(M, V) from s)).symm.trans
      ((congrArg (e.inv.app V).hom hs).trans (app_comp_apply e.hom_inv_id V (show Γ(M, V) from s')))
  · exact app_comp_apply e.inv_hom_id V (show Γ(N, V) from t)

/-- Evaluating a morphism of `𝒪_W`-modules at a section over `V` is additive in the morphism. -/
def homAppAddMonoidHom (M N : W.Modules) (V : W.Opens) (s : Γ(M, V)) : (M ⟶ N) →+ Γ(N, V) :=
  AddMonoidHom.mk' (fun h => h.app V s) fun _ _ => rfl

/-- The projection to a summand of the sum of the inclusions of the summands. -/
theorem biproduct_π_app_toModule_sectionsKHom {J : Type} [Finite J] [DecidableEq J]
    (M : J → W.Modules) [HasBiproduct M] (V : W.Opens)
    (x : DirectSum J fun j => (Stacks.CechKunneth.sectionsK W φ (M j)).obj (op V)) (i : J) :
    (biproduct.π M i).app V
        (DirectSum.toModule k J _ (fun j => sectionsKHom φ (biproduct.ι M j) V) x) = x i := by
  induction x using DirectSum.induction_on with
  | zero => exact (congrArg ((biproduct.π M i).app V).hom (map_zero _)).trans (map_zero _)
  | add x y hx hy =>
    exact (congrArg ((biproduct.π M i).app V).hom (map_add _ x y)).trans
      ((map_add _ _ _).trans (congrArg₂ (· + ·) hx hy))
  | of j m =>
    rw [← DirectSum.lof_eq_of k, DirectSum.toModule_lof, sectionsKHom_apply]
    by_cases hji : j = i
    · subst hji
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
      exact app_comp_apply (biproduct.ι_π_self M j) V (show Γ(M j, V) from m)
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hji)]
      exact app_comp_apply (biproduct.ι_π_ne M hji) V (show Γ(M j, V) from m)

/-- **The sections of a finite biproduct of `𝒪_W`-modules are the direct sum of the sections of
the summands.** -/
theorem bijective_toModule_sectionsKHom_biproduct_ι {J : Type} [Finite J] [DecidableEq J]
    (M : J → W.Modules) [HasBiproduct M] (V : W.Opens) :
    Function.Bijective
      (DirectSum.toModule k J _ fun j => sectionsKHom φ (biproduct.ι M j) V) := by
  have := Fintype.ofFinite J
  refine ⟨fun x y hxy => DFinsupp.ext fun i => ?_, fun t => ?_⟩
  · exact (biproduct_π_app_toModule_sectionsKHom φ M V x i).symm.trans
      ((congrArg ((biproduct.π M i).app V).hom hxy).trans
        (biproduct_π_app_toModule_sectionsKHom φ M V y i))
  · refine ⟨∑ j, DirectSum.lof k J _ j (sectionsKHom φ (biproduct.π M j) V t), ?_⟩
    rw [map_sum]
    have h := congrArg (homAppAddMonoidHom (⨁ M) (⨁ M) V (show Γ(⨁ M, V) from t))
      (biproduct.total (f := M))
    rw [map_sum] at h
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
    rw [DirectSum.toModule_lof]
    rfl

end SectionsK

section Kunneth

attribute [local instance] hasColimits_sheafOfModules_toRingCat
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

open Stacks.CechKunneth (sectionsK baseRingHom boxMap)
open Scheme.Hom (relativeDifferentialForms deRhamBoxModuleIso deRhamBoxSummand)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (g : Y ⟶ Spec (.of k))

/-- **The Künneth map on sections of differential forms**, for opens `U ⊆ X` and `V ⊆ Y`:
`⨁_{a + c = r} Γ(U, Ω^a_{X/k}) ⊗_k Γ(V, Ω^c_{Y/k}) ⟶ Γ(U × V, Ω^r_{X ×_k Y/k})`. -/
def kunnethSectionsMap (r : ℕ) (U : X.Opens) (V : Y.Opens) :
    (DirectSum {ac : ℕ × ℕ // ac.1 + ac.2 = r} fun ac =>
        (hodgeSectionsK f (hodgeScalarsOverField f) ac.1.1).obj (op U) ⊗[k]
          (hodgeSectionsK g (hodgeScalarsOverField g) ac.1.2).obj (op V)) →ₗ[k]
      (hodgeSectionsK (pullback.fst f g ≫ f) (hodgeScalarsOverField (pullback.fst f g ≫ f)) r).obj
        (op (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) :=
  (hodgeSectionsKEquiv (pullback.fst f g ≫ f) (specScalars k) r _).symm.toLinearMap ∘ₗ
    sectionsKHom (baseRingHom (specScalars k) (pullback.fst f g ≫ f))
      (deRhamBoxModuleIso f g r).hom _ ∘ₗ
    DirectSum.toModule k _ _ (fun j => sectionsKHom
      (baseRingHom (specScalars k) (pullback.fst f g ≫ f))
      (biproduct.ι (fun i => (deRhamBoxSummand f g r i).module) j) _) ∘ₗ
    DirectSum.lmap (fun j => ((boxMap (specScalars k) f g
      (relativeDifferentialForms f (j.1.1 : ℤ))
      (relativeDifferentialForms g (j.1.2 : ℤ))).app (op (U, V))).hom) ∘ₗ
    DirectSum.lmap (fun j => (TensorProduct.congr (hodgeSectionsKEquiv f (specScalars k) j.1.1 U)
      (hodgeSectionsKEquiv g (specScalars k) j.1.2 V)).toLinearMap)

/-- The Künneth map on a pure tensor, before evaluating the degreewise Künneth isomorphism: the
image of the section `ω ⊠ η` of `Ω^a_{X/k} ⊠ Ω^c_{Y/k}` under the inclusion of the summand of index
`(a, c)` followed by `AlgebraicGeometry.Scheme.Hom.deRhamBoxModuleIso`. -/
theorem kunnethSectionsMap_lof_tmul_eq_app (r a c : ℕ) (h : a + c = r) (U : X.Opens)
    (V : Y.Opens) (ω : (hodgeSectionsK f (hodgeScalarsOverField f) a).obj (op U))
    (η : (hodgeSectionsK g (hodgeScalarsOverField g) c).obj (op V)) :
    kunnethSectionsMap f g r U V
        (DirectSum.lof k {ac : ℕ × ℕ // ac.1 + ac.2 = r} (fun ac =>
          (hodgeSectionsK f (hodgeScalarsOverField f) ac.1.1).obj (op U) ⊗[k]
            (hodgeSectionsK g (hodgeScalarsOverField g) ac.1.2).obj (op V)) ⟨(a, c), h⟩
          (ω ⊗ₜ η)) =
      (hodgeSectionsKEquiv (pullback.fst f g ≫ f) (specScalars k) r
        (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)).symm
        ((biproduct.ι (fun i => (deRhamBoxSummand f g r i).module) ⟨(a, c), h⟩ ≫
            (deRhamBoxModuleIso f g r).hom).app (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
          (Stacks.CechKunneth.boxSection f g (relativeDifferentialForms f (a : ℤ))
            (relativeDifferentialForms g (c : ℤ)) (U, V) ω η)) := by
  simp only [kunnethSectionsMap, LinearMap.comp_apply]
  erw [LinearMap.comp_apply (DirectSum.lmap _) (DirectSum.lmap _), DirectSum.lmap_lof,
    DirectSum.lmap_lof, DirectSum.toModule_lof]
  rfl

/-- **The Künneth map on a pure tensor**: on the summand of index `(a, c)` it carries `ω ⊗ η`
to `(pr₁^*ω)|_{U × V} ∧ (pr₂^*η)|_{U × V}`, read in degree `r` along `a + c = r`. Here `pr₁^*ω`
is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback` for the square
`pr₁ ≫ f = (pr₁ ≫ f) ≫ 𝟙`, `pr₂^*η` the same for `pr₂ ≫ g = (pr₁ ≫ f) ≫ 𝟙`, and the wedge is
`AlgebraicGeometry.SheafOfModules.formProduct` in `Ω^•_{W/k}`. -/
theorem kunnethSectionsMap_lof_tmul (r a c : ℕ) (h : a + c = r) (U : X.Opens) (V : Y.Opens)
    (ω : (hodgeSectionsK f (hodgeScalarsOverField f) a).obj (op U))
    (η : (hodgeSectionsK g (hodgeScalarsOverField g) c).obj (op V)) :
    kunnethSectionsMap f g r U V
        (DirectSum.lof k {ac : ℕ × ℕ // ac.1 + ac.2 = r} (fun ac =>
          (hodgeSectionsK f (hodgeScalarsOverField f) ac.1.1).obj (op U) ⊗[k]
            (hodgeSectionsK g (hodgeScalarsOverField g) ac.1.2).obj (op V)) ⟨(a, c), h⟩
          (ω ⊗ₜ η)) =
      (eqToHom (congrArg (fun m : ℕ =>
          (Scheme.Hom.deRhamAlgebras (pullback.fst f g ≫ f)).exteriorPower m) h)).val.app
          (op (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))
        (AlgebraicGeometry.SheafOfModules.formProduct
          (Scheme.Hom.deRhamAlgebras (pullback.fst f g ≫ f)) a c
          (op (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))
          ((relativeDifferentialForms (pullback.fst f g ≫ f) (a : ℤ)).presheaf.map
            (homOfLE inf_le_left).op (Scheme.Hom.deRhamBoxLeftPullback f g (a : ℤ) U ω))
          ((relativeDifferentialForms (pullback.fst f g ≫ f) (c : ℤ)).presheaf.map
            (homOfLE inf_le_right).op (Scheme.Hom.deRhamBoxRightPullback f g (c : ℤ) V η))) := by
  refine (kunnethSectionsMap_lof_tmul_eq_app f g r a c h U V ω η).trans ?_
  exact (app_comp_apply (Scheme.Hom.biproduct_ι_comp_deRhamBoxModuleIso_hom f g r ⟨(a, c), h⟩)
    _ _).trans (congrArg ((eqToHom (congrArg (fun m : ℕ =>
      (Scheme.Hom.deRhamAlgebras (pullback.fst f g ≫ f)).exteriorPower m) h)).val.app
      (op (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))).hom
    (Scheme.Hom.prodWedgeHom_deRhamBoxSummandIso_inv_externalTensorSection f g r ⟨(a, c), h⟩
      ω η (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) inf_le_left inf_le_right))

/-- **The Künneth map on a pure tensor, in degree `a + c`**: it carries `ω ⊗ η` in the summand of
index `(a, c)` to `(pr₁^*ω)|_{U × V} ∧ (pr₂^*η)|_{U × V}`. -/
theorem kunnethSectionsMap_lof_tmul_add (a c : ℕ) (U : X.Opens) (V : Y.Opens)
    (ω : (hodgeSectionsK f (hodgeScalarsOverField f) a).obj (op U))
    (η : (hodgeSectionsK g (hodgeScalarsOverField g) c).obj (op V)) :
    kunnethSectionsMap f g (a + c) U V
        (DirectSum.lof k {ac : ℕ × ℕ // ac.1 + ac.2 = a + c} (fun ac =>
          (hodgeSectionsK f (hodgeScalarsOverField f) ac.1.1).obj (op U) ⊗[k]
            (hodgeSectionsK g (hodgeScalarsOverField g) ac.1.2).obj (op V)) ⟨(a, c), rfl⟩
          (ω ⊗ₜ η)) =
      AlgebraicGeometry.SheafOfModules.formProduct
        (Scheme.Hom.deRhamAlgebras (pullback.fst f g ≫ f)) a c
        (op (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))
        ((relativeDifferentialForms (pullback.fst f g ≫ f) (a : ℤ)).presheaf.map
          (homOfLE inf_le_left).op (Scheme.Hom.deRhamBoxLeftPullback f g (a : ℤ) U ω))
        ((relativeDifferentialForms (pullback.fst f g ≫ f) (c : ℤ)).presheaf.map
          (homOfLE inf_le_right).op (Scheme.Hom.deRhamBoxRightPullback f g (c : ℤ) V η)) :=
  kunnethSectionsMap_lof_tmul f g (a + c) a c rfl U V ω η

/-- **The Künneth map on sections of differential forms commutes with restriction**: for opens
`U' ⊆ U` of `X` and `V' ⊆ V` of `Y`, restricting from `U × V` to `U' × V'` after the Künneth map
is the Künneth map after restricting each factor. -/
theorem kunnethSectionsMap_naturality (r : ℕ) {U U' : X.Opens} {V V' : Y.Opens} (hU : U' ≤ U)
    (hV : V' ≤ V) :
    ((hodgeSectionsK (pullback.fst f g ≫ f) (hodgeScalarsOverField (pullback.fst f g ≫ f)) r).map
        (homOfLE (inf_le_inf (Scheme.Hom.preimage_mono (pullback.fst f g) hU)
          (Scheme.Hom.preimage_mono (pullback.snd f g) hV))).op).hom ∘ₗ
        kunnethSectionsMap f g r U V =
      kunnethSectionsMap f g r U' V' ∘ₗ
        DirectSum.lmap (fun j : {ac : ℕ × ℕ // ac.1 + ac.2 = r} => TensorProduct.map
          ((hodgeSectionsK f (hodgeScalarsOverField f) j.1.1).map (homOfLE hU).op).hom
          ((hodgeSectionsK g (hodgeScalarsOverField g) j.1.2).map (homOfLE hV).op).hom) := by
  refine DirectSum.linearMap_ext k fun j => TensorProduct.ext' fun ω η => ?_
  obtain ⟨⟨a, c⟩, h⟩ := j
  have e₁ := DirectSum.lmap_lof (fun j : {ac : ℕ × ℕ // ac.1 + ac.2 = r} => TensorProduct.map
      ((hodgeSectionsK f (hodgeScalarsOverField f) j.1.1).map (homOfLE hU).op).hom
      ((hodgeSectionsK g (hodgeScalarsOverField g) j.1.2).map (homOfLE hV).op).hom)
    ⟨(a, c), h⟩ (ω ⊗ₜ η)
  refine (congrArg ((hodgeSectionsK (pullback.fst f g ≫ f)
      (hodgeScalarsOverField (pullback.fst f g ≫ f)) r).map
        (homOfLE (inf_le_inf (Scheme.Hom.preimage_mono (pullback.fst f g) hU)
          (Scheme.Hom.preimage_mono (pullback.snd f g) hV))).op).hom
      (kunnethSectionsMap_lof_tmul_eq_app f g r a c h U V ω η)).trans ?_
  refine Eq.trans ?_ ((congrArg (kunnethSectionsMap f g r U' V') e₁).trans
    (kunnethSectionsMap_lof_tmul_eq_app f g r a c h U' V' _ _)).symm
  exact (Stacks.Tag01VSPullbackTensor.homApp_presheaf_map
      (biproduct.ι (fun i => (deRhamBoxSummand f g r i).module) ⟨(a, c), h⟩ ≫
        (deRhamBoxModuleIso f g r).hom)
      (homOfLE (inf_le_inf (Scheme.Hom.preimage_mono (pullback.fst f g) hU)
        (Scheme.Hom.preimage_mono (pullback.snd f g) hV))) _).symm.trans
    (congrArg ((biproduct.ι (fun i => (deRhamBoxSummand f g r i).module) ⟨(a, c), h⟩ ≫
        (deRhamBoxModuleIso f g r).hom).app (pullback.fst f g ⁻¹ᵁ U' ⊓ pullback.snd f g ⁻¹ᵁ V'))
      (Stacks.CechKunneth.boxSection_map f g (relativeDifferentialForms f (a : ℤ))
        (relativeDifferentialForms g (c : ℤ)) (Z := (U, V)) (Z' := (U', V'))
        (Stacks.CechKunneth.LatProd.le_mk hU hV) ω η))

/-- The direct sum of bijective linear maps is bijective. -/
private theorem bijective_lmap {R ι : Type*} [Semiring R] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (N i)] [∀ i, Module R (M i)]
    [∀ i, Module R (N i)] {f : ∀ i, M i →ₗ[R] N i} (hf : ∀ i, Function.Bijective (f i)) :
    Function.Bijective (DirectSum.lmap f) := by
  classical
  exact ⟨(DirectSum.lmap_injective f).2 fun i => (hf i).1,
    (DirectSum.lmap_surjective f).2 fun i => (hf i).2⟩

/-- **The Künneth map on sections of differential forms is bijective over a product of affine
opens.** -/
theorem bijective_kunnethSectionsMap (r : ℕ) {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : Function.Bijective (kunnethSectionsMap f g r U V) := by
  have hψ : Function.Bijective (specScalars k) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have : Finite {ac : ℕ × ℕ // ac.1 + ac.2 = r} :=
    inferInstanceAs (Finite (Scheme.Hom.deRhamBoxIndex r))
  have h₁ := bijective_lmap (R := k) fun j : {ac : ℕ × ℕ // ac.1 + ac.2 = r} =>
    (TensorProduct.congr (hodgeSectionsKEquiv f (specScalars k) j.1.1 U)
      (hodgeSectionsKEquiv g (specScalars k) j.1.2 V)).bijective
  have h₂ : Function.Bijective (DirectSum.lmap (fun j : {ac : ℕ × ℕ // ac.1 + ac.2 = r} =>
      ((boxMap (specScalars k) f g (relativeDifferentialForms f (j.1.1 : ℤ))
        (relativeDifferentialForms g (j.1.2 : ℤ))).app (op (U, V))).hom)) :=
    bijective_lmap fun j => by
      have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms f j.1.1
      have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms g j.1.2
      exact Stacks.CechKunneth.bijective_boxMap_app (specScalars k) f g _ _ (U, V) hψ hU hV
  have h₃ := bijective_toModule_sectionsKHom_biproduct_ι
    (baseRingHom (specScalars k) (pullback.fst f g ≫ f))
    (fun i => (deRhamBoxSummand f g r i).module)
    (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
  have h₄ := bijective_sectionsKHom (baseRingHom (specScalars k) (pullback.fst f g ≫ f))
    (deRhamBoxModuleIso f g r) (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)
  exact (hodgeSectionsKEquiv (pullback.fst f g ≫ f) (specScalars k) r _).symm.bijective.comp
    (h₄.comp (h₃.comp (h₂.comp h₁)))

end Kunneth

end Stacks.HodgeWeil

end
