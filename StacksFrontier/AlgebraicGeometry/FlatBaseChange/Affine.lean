module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Pushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degree-zero flat base change over an affine base

For a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `S` and `S'` affine, `g` flat and `f` quasi-compact and quasi-separated, and `F` a
quasi-coherent `𝒪_X`-module, [Stacks, Tag 02KH] part (1) in degree zero says that the
comparison morphism `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange` is an
isomorphism

  `g^* f_* F ⟶ f'_* (g')^* F`.

This file proves that statement for `S = Spec A` and `S' = Spec B`.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine`:
  [Stacks, Tag 02KH] part (1) in degree zero over an affine base: the degree-zero base-change
  comparison is an isomorphism.
* `Stacks.AlgebraicGeometry.FlatBaseChange.bijective_of_tmul_normalisation`: a `B`-linear map
  between two base changes of one `A`-module, compatible with the two structure maps, is
  bijective.
* `Stacks.AlgebraicGeometry.FlatBaseChange.baseModule_pushforward` and `baseModule_id`: the
  `Γ(S, ⊤)`-module structures on global sections obtained by restriction of scalars along
  `appLE ⊤ ⊤` are the intrinsic ones.
* `Stacks.AlgebraicGeometry.FlatBaseChange.exists_linearEquiv_tmul_congr`: transport of a
  normalised base-change isomorphism along an equality of module structures.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isIso_of_bijective_app_top`: a morphism of
  quasi-coherent modules on `Spec R` which is bijective on global sections is an isomorphism.
* `Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs`: the degree-zero
  direct image of a quasi-coherent module along a quasi-compact quasi-separated morphism is
  quasi-coherent ([Stacks, Tag 01XJ] in degree zero).
* `Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pullback_pushforward` and
  `isQuasicoherent_pushforward_pullback`: the source and the target of the comparison morphism
  are quasi-coherent.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChange

/-! ### Two base-change descriptions of one map -/

/-- **Two base-change descriptions of one map.** Let `R ⟶ B` be a ring map and `M` an
`R`-module. Suppose `N₁` and `N₂` are `B`-modules exhibited as base changes of `M` by
`B`-linear isomorphisms `e₁, e₂` out of `B ⊗[R] M`, normalised on pure tensors by maps
`ρ₁ : M → N₁` and `ρ₂ : M → N₂`. Then any `B`-linear map `N₁ → N₂` carrying `ρ₁` to `ρ₂` is
bijective. -/
theorem bijective_of_tmul_normalisation {R B M N₁ N₂ : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [AddCommGroup M] [Module R M] [AddCommGroup N₁] [Module B N₁]
    [AddCommGroup N₂] [Module B N₂] {ρ₁ : M → N₁} {ρ₂ : M → N₂}
    (e₁ : B ⊗[R] M ≃ₗ[B] N₁) (h₁ : ∀ (b : B) (a : M), e₁ (b ⊗ₜ[R] a) = b • ρ₁ a)
    (e₂ : B ⊗[R] M ≃ₗ[B] N₂) (h₂ : ∀ (b : B) (a : M), e₂ (b ⊗ₜ[R] a) = b • ρ₂ a)
    (ψ : N₁ →ₗ[B] N₂) (hψ : ∀ a : M, ψ (ρ₁ a) = ρ₂ a) : Function.Bijective ψ := by
  have key : ∀ x : B ⊗[R] M, ψ (e₁ x) = e₂ x := by
    intro x
    refine TensorProduct.inductionOn x (fun b a => ?_) (fun y z hy hz => ?_)
    · rw [h₁, h₂, map_smul, hψ]
    · rw [map_add, map_add, map_add, hy, hz]
  have hfun : (ψ : N₁ → N₂) = (e₂ : B ⊗[R] M → N₂) ∘ (e₁.symm : N₁ → B ⊗[R] M) := by
    funext y
    simpa using key (e₁.symm y)
  rw [hfun]
  exact e₂.bijective.comp e₁.symm.bijective

/-- A normalised base-change isomorphism `B ⊗[R] M ≃ₗ[B] N` for one choice of the `R`-module
structure on `M` and of the `B`-module structure on `N` gives one for any equal choice. -/
theorem exists_linearEquiv_tmul_congr {R B M N : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [AddCommGroup M] [AddCommGroup N]
    {iM jM : Module R M} (hM : iM = jM) {iN jN : Module B N} (hN : iN = jN) (ρ : M → N)
    (he : letI := iM; letI := iN;
      ∃ e : B ⊗[R] M ≃ₗ[B] N, ∀ (b : B) (a : M), e (b ⊗ₜ[R] a) = b • ρ a) :
    letI := jM; letI := jN;
      ∃ e : B ⊗[R] M ≃ₗ[B] N, ∀ (b : B) (a : M), e (b ⊗ₜ[R] a) = b • ρ a := by
  subst hM hN
  exact he

/-! ### The scalar structures over the base -/

/-- On global sections, `h.appLE ⊤ ⊤` agrees with `h.app ⊤`. -/
theorem appLE_top_apply {X S : Scheme.{u}} (h : X ⟶ S) (r : Γ(S, (⊤ : S.Opens))) :
    (h.appLE ⊤ ⊤ (le_preimage_top h ⊤)).hom r = (h.app ⊤).hom r :=
  congrArg (fun m : Γ(S, ⊤) ⟶ Γ(X, ⊤) => m.hom r) (Scheme.Hom.appLE_eq_app h)

/-- **The base scalar structure on a direct image is the intrinsic one.** For `h : Z ⟶ W` and an
`𝒪_Z`-module `G`, the `Γ(W, ⊤)`-module structure
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule h G ⊤` on `Γ(G, ⊤)` — restriction of
scalars along `h.appLE ⊤ ⊤` — is the structure `Γ(h_* G, ⊤)` carries as the global sections of
an `𝒪_W`-module. -/
theorem baseModule_pushforward {Z W : Scheme.{u}} (h : Z ⟶ W) (G : Z.Modules) :
    (baseModule h G ⊤ : Module Γ(W, (⊤ : W.Opens))
        Γ((Scheme.Modules.pushforward h).obj G, (⊤ : W.Opens))) =
      (inferInstance : Module Γ(W, (⊤ : W.Opens))
        Γ((Scheme.Modules.pushforward h).obj G, (⊤ : W.Opens))) := by
  refine Module.ext (funext fun r => funext fun x : Γ(G, (⊤ : Z.Opens)) => ?_)
  exact congrArg (fun s : Γ(Z, (⊤ : Z.Opens)) => s • x) (appLE_top_apply h r)

/-- **The base scalar structure along the identity is the intrinsic one.** -/
theorem baseModule_id {W : Scheme.{u}} (N : W.Modules) :
    (baseModule (𝟙 W) N ⊤ : Module Γ(W, (⊤ : W.Opens)) Γ(N, (⊤ : W.Opens))) =
      (inferInstance : Module Γ(W, (⊤ : W.Opens)) Γ(N, (⊤ : W.Opens))) := by
  exact baseModule_pushforward (𝟙 W) N

/-! ### Quasi-coherence of the two sides -/

/-- **[Stacks, Tag 01XJ] in degree zero.** The direct image of a quasi-coherent module along a
quasi-compact, quasi-separated morphism of schemes is quasi-coherent. -/
theorem isQuasicoherent_pushforward_of_qcqs {Y Z : Scheme.{u}} (q : Y ⟶ Z) [QuasiCompact q]
    [QuasiSeparated q] (G : Y.Modules) [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward q).obj G).IsQuasicoherent :=
  (Stacks.AlgebraicGeometry.DerivedPushforward.isQuasicoherent_rightDerived_zero_iff q G).mp
    inferInstance

/-- The source `g^* f_* F` of the degree-zero base-change comparison is quasi-coherent, when `f`
is quasi-compact and quasi-separated and `F` is quasi-coherent. -/
theorem isQuasicoherent_pullback_pushforward {S S' X : Scheme.{u}}
    (g : S' ⟶ S) (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pushforward f).obj F)).IsQuasicoherent :=
  have := isQuasicoherent_pushforward_of_qcqs f F
  Stacks.Modules.isQuasicoherent_pullback g _ inferInstance

/-- The target `f'_* (g')^* F` of the degree-zero base-change comparison is quasi-coherent, for
a cartesian square with `f` quasi-compact and quasi-separated and `F` quasi-coherent. -/
theorem isQuasicoherent_pushforward_pullback {S S' X X' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
    (H : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f').obj
      ((Scheme.Modules.pullback g').obj F)).IsQuasicoherent :=
  have : QuasiCompact f' := MorphismProperty.of_isPullback H inferInstance
  have : QuasiSeparated f' := MorphismProperty.of_isPullback H inferInstance
  have := Stacks.Modules.isQuasicoherent_pullback g' F inferInstance
  isQuasicoherent_pushforward_of_qcqs f' _

/-! ### Isomorphism from bijectivity on global sections -/

/-- **Three invertible edges of a commuting square make the fourth invertible.** If
`γ ≫ β = α ≫ ψ` and `α`, `β`, `γ` are isomorphisms then so is `ψ`, with inverse
`inv β ≫ inv γ ≫ α`. -/
theorem isIso_of_isIso_comp_square {C : Type*} [Category C] {P Q M N : C} {ψ : M ⟶ N}
    (α : P ⟶ M) (β : Q ⟶ N) (γ : P ⟶ Q) (hα : IsIso α) (hβ : IsIso β) (hγ : IsIso γ)
    (w : γ ≫ β = α ≫ ψ) : IsIso ψ := by
  refine ⟨inv β ≫ inv γ ≫ α, ?_, ?_⟩
  · rw [← cancel_epi α, Category.comp_id, ← Category.assoc α ψ, ← w]
    simp
  · rw [Category.assoc, Category.assoc, ← w]
    simp

/-- The naturality square of `AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans`, spelled with
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` and `AlgebraicGeometry.tilde.functor` rather than
with the composite functor. -/
theorem fromTildeΓ_naturality {R : CommRingCat.{u}} {M N : (Spec R).Modules} (ψ : M ⟶ N) :
    (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map ψ) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ ψ :=
  (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality ψ

/-- **A morphism of quasi-coherent modules on `Spec R` is an isomorphism as soon as
`moduleSpecΓFunctor` sends it to one.** -/
theorem isIso_of_isIso_moduleSpecΓFunctor_map {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (ψ : M ⟶ N)
    (h : IsIso ((moduleSpecΓFunctor (R := R)).map ψ)) : IsIso ψ :=
  have hγ : IsIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map ψ)) :=
    Functor.map_isIso (tilde.functor R) _
  isIso_of_isIso_comp_square M.fromTildeΓ N.fromTildeΓ
    ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map ψ))
    inferInstance inferInstance hγ (fromTildeΓ_naturality ψ)

/-- **A morphism of quasi-coherent modules on `Spec R` which is bijective on global sections is
an isomorphism.** -/
theorem isIso_of_bijective_app_top {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (ψ : M ⟶ N)
    (h : Function.Bijective (ψ.app ⊤)) : IsIso ψ :=
  isIso_of_isIso_moduleSpecΓFunctor_map ψ ((ConcreteCategory.isIso_iff_bijective _).mpr h)

/-! ### The two sides as base changes of one module -/

/-- The pullback of a global section of `F` along `g'`, read as a global section of
`f'_* (g')^* F`, that is,
`Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom g' F ⊤ ⊤`. -/
def pushforwardPullbackSections {X X' S' : Scheme.{u}} (f' : X' ⟶ S') (g' : X' ⟶ X)
    (F : X.Modules) :
    Γ(F, (⊤ : X.Opens)) →+
      Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F),
        (⊤ : S'.Opens)) :=
  pullbackSectionsHom g' F ⊤ ⊤ (le_preimage_top g' ⊤)

/-- **The source of the comparison is the base change of `Γ(f_* F, ⊤)`.** This is
[Stacks, Tag 02KH] part (2) in degree zero applied to the degenerate cartesian square
`CategoryTheory.IsPullback.of_id_snd` for `g`, with the module `f_* F` on `Spec A`. -/
theorem exists_linearEquiv_sections_pullback_pushforward {A B : CommRingCat.{u}}
    {X : Scheme.{u}} (f : X ⟶ Spec A) (g : Spec B ⟶ Spec A) [Flat g] [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    letI := baseAlgebra g
    ∃ e : Γ(Spec B, ⊤) ⊗[Γ(Spec A, ⊤)]
          Γ((Scheme.Modules.pushforward f).obj F, (⊤ : (Spec A).Opens)) ≃ₗ[Γ(Spec B, ⊤)]
        Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F),
          (⊤ : (Spec B).Opens)),
      ∀ (b : Γ(Spec B, ⊤)) (a : Γ((Scheme.Modules.pushforward f).obj F, (⊤ : (Spec A).Opens))),
        e (b ⊗ₜ[Γ(Spec A, ⊤)] a) =
          b • pullbackSectionsHom g ((Scheme.Modules.pushforward f).obj F) ⊤ ⊤
            (le_preimage_top g ⊤) a := by
  let _ : Algebra Γ(Spec A, (⊤ : (Spec A).Opens)) Γ(Spec B, (⊤ : (Spec B).Opens)) :=
    baseAlgebra g
  have := isQuasicoherent_pushforward_of_qcqs f F
  exact exists_linearEquiv_tmul_congr (baseModule_id _) (baseModule_id _) _
    (exists_linearEquiv_sections_baseChange IsPullback.of_id_snd _)

/-- **The target of the comparison is the base change of `Γ(f_* F, ⊤)`.** This is
[Stacks, Tag 02KH] part (2) in degree zero applied to the square itself. -/
theorem exists_linearEquiv_sections_pushforward_pullback {A B : CommRingCat.{u}}
    {X X' : Scheme.{u}} {f : X ⟶ Spec A} {g : Spec B ⟶ Spec A} {f' : X' ⟶ Spec B}
    {g' : X' ⟶ X} (H : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    letI := baseAlgebra g
    ∃ e : Γ(Spec B, ⊤) ⊗[Γ(Spec A, ⊤)]
          Γ((Scheme.Modules.pushforward f).obj F, (⊤ : (Spec A).Opens)) ≃ₗ[Γ(Spec B, ⊤)]
        Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F),
          (⊤ : (Spec B).Opens)),
      ∀ (b : Γ(Spec B, ⊤)) (a : Γ((Scheme.Modules.pushforward f).obj F, (⊤ : (Spec A).Opens))),
        e (b ⊗ₜ[Γ(Spec A, ⊤)] a) = b • pushforwardPullbackSections f' g' F a := by
  let _ : Algebra Γ(Spec A, (⊤ : (Spec A).Opens)) Γ(Spec B, (⊤ : (Spec B).Opens)) :=
    baseAlgebra g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  exact exists_linearEquiv_tmul_congr (baseModule_pushforward f F)
    (baseModule_pushforward f' ((Scheme.Modules.pullback g').obj F)) _
    (exists_linearEquiv_sections_baseChange H F)

/-! ### Tag 02KH part (1) in degree zero over an affine base -/

/-- The comparison morphism on global sections, as a `Γ(S', ⊤)`-linear map. -/
def pushforwardBaseChangeAppTop {S S' X X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) (F : X.Modules) :
    Γ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F),
        (⊤ : S'.Opens)) →ₗ[Γ(S', ⊤)]
      Γ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F),
        (⊤ : S'.Opens)) where
  toFun y := (pushforwardBaseChange w F).app ⊤ y
  map_add' _ _ := map_add _ _ _
  map_smul' b y := Scheme.Modules.Hom.app_smul (pushforwardBaseChange w F) b y

/-- The comparison morphism carries the pullback of a global section of `f_* F` to the pullback
of the corresponding global section of `F`. -/
theorem pushforwardBaseChangeAppTop_pullbackSectionsHom {S S' X X' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (w : g' ≫ f = f' ≫ g) (F : X.Modules)
    (a : Γ((Scheme.Modules.pushforward f).obj F, (⊤ : S.Opens))) :
    pushforwardBaseChangeAppTop w F
        (pullbackSectionsHom g ((Scheme.Modules.pushforward f).obj F) ⊤ ⊤
          (le_preimage_top g ⊤) a) =
      pushforwardPullbackSections f' g' F a :=
  (congrArg (fun y => (pushforwardBaseChange w F).app ⊤ y)
      (pullbackSectionsHom_top g ((Scheme.Modules.pushforward f).obj F) a)).trans
    ((pushforwardBaseChange_app_top_unit w F a).trans
      (pullbackSectionsHom_top g' F a).symm)

/-- **[Stacks, Tag 02KH] part (1) in degree zero over an affine base.** Let

```
X' --g'--> X
|          |
f'         f
v          v
Spec B --g--> Spec A
```

be a cartesian square of schemes with `g` flat and `f` quasi-compact and quasi-separated, and
let `F` be a quasi-coherent `𝒪_X`-module. Then the degree-zero base-change comparison

  `g^* f_* F ⟶ f'_* (g')^* F`

is an isomorphism.

This is the degree-zero case over an affine base of part (1) of [Stacks, Tag 02KH], which in
every degree and over an arbitrary base is
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_higherBaseChangeMap`. -/
@[ega "III 1.4.15" "q = 0, affine base",
  sga "6 IV 3.1.0" "flat affine base, H^0"]
theorem isIso_pushforwardBaseChange_of_isAffine {A B : CommRingCat.{u}} {X X' : Scheme.{u}}
    {f : X ⟶ Spec A} {g : Spec B ⟶ Spec A} {f' : X' ⟶ Spec B} {g' : X' ⟶ X}
    (H : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] : IsIso (pushforwardBaseChange H.w F) := by
  let _ : Algebra Γ(Spec A, (⊤ : (Spec A).Opens)) Γ(Spec B, (⊤ : (Spec B).Opens)) :=
    baseAlgebra g
  have := isQuasicoherent_pullback_pushforward g f F
  have := isQuasicoherent_pushforward_pullback H F
  obtain ⟨e₁, h₁⟩ := exists_linearEquiv_sections_pullback_pushforward f g F
  obtain ⟨e₂, h₂⟩ := exists_linearEquiv_sections_pushforward_pullback H F
  exact isIso_of_bijective_app_top _
    (bijective_of_tmul_normalisation e₁ h₁ e₂ h₂ (pushforwardBaseChangeAppTop H.w F)
      (pushforwardBaseChangeAppTop_pullbackSectionsHom H.w F))

end Stacks.AlgebraicGeometry.FlatBaseChange

end
