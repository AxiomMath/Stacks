module

public import StacksFrontier.AlgebraicGeometry.Divisors.PullbackTrivialization
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorTrivialization

/-!
# The local equation of a pulled-back section of a tensor product

Let `q : T ⟶ Y` be a morphism of schemes, let `L₁` and `L₂` be invertible `𝒪_Y`-modules and let
`s` be a global section of `L₁ ⊗ L₂`. Over an affine open `V` of `Y` with affine preimage
`q⁻¹V`, trivializations `u₁` of `L₁` and `u₂` of `L₂` give a local equation for `s`, namely the
function `tensorTrivialization L₁ L₂ hV u₁ u₂ (s|_V)` on `V`. This file proves that the pulled
back section `q^*s` of `q^*L₁ ⊗ q^*L₂` — read through the comparison of [Stacks, Tag 01CD] by
`Stacks.PullbackTensorIso.pullbackTensorSection` — has as its local equation over `q⁻¹V`, for
the pulled-back trivializations of `Stacks.Divisors.pullbackTrivialization`, exactly the
pullback of that function.

This is the last ingredient of clause (2) of [Stacks, Tag 0F97]: it is what lets the local
model of the zero scheme of `s` be transported along a base change.

## Main results

* `Stacks.PullbackTensorIso.pullbackTensorSection_resTop` — the restriction to `q⁻¹V` of the
  pullback of a global section of a tensor product is the comparison of Tag 01CD applied to the
  pullback of its restriction to `V`.
* `Stacks.PullbackTensorIso.pullbackSectionHom_tensorSectionsAt` — **the comparison of Tag 01CD
  carries the pullback of a product of two sections over `V` to the product of their pullbacks
  over `q⁻¹V`.** This is
  `Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt` over an arbitrary open
  rather than over `⊤`.
* `Stacks.Divisors.exists_pullbackTensorTrivialization` — **the local equation of the pullback
  of a section of `L₁ ⊗ L₂` is the pullback of its local equation**, for the pulled-back pair of
  trivializations.

## Implementation notes

The two halves of the main result are the two naturality squares of the comparison. Naturality
in the *open* is `PresheafOfModules.naturality_apply` on the comparison together with
`AlgebraicGeometry.pullbackSectionHom_resTop`, and is `pullbackTensorSection_resTop`.
Naturality in the *sections* is the canonicality clause of Tag 01CD,
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul`, which is already stated over an
arbitrary open; what has to be supplied is that the scheme-level pullback of a section over `V`
to the *whole* preimage `q⁻¹V` is the ringed-space `Stacks.RingedSpace.pullbackUnit`, the
restriction map in its definition being the identity. That is
`AlgebraicGeometry.pullbackSectionHom_preimage_self`.

Once both halves are in place nothing about the trivializations is needed beyond the framing
identity `Stacks.Divisors.pullbackTrivialization_symm_one` and semilinearity of
`AlgebraicGeometry.pullbackSectionHom`: a trivialization of a tensor product is determined by
the pure tensor of the two framing sections
(`Stacks.Divisors.tensorTrivialization_symm_apply`), so the identity to prove is an equation
between two sections of `q^*L₁ ⊗ q^*L₂` over `q⁻¹V`, and both sides are the comparison applied
to the same thing.

The proofs are chains of `Eq.trans` and `congrArg` rather than `rw`/`simp` sequences, and the
chains are built by `refine (…).trans ?_`, so that each scalar multiplication appearing in them
comes from the lemma being applied rather than from the text. `Γ(M, U)` and
`M.val.obj (op U)` are definitionally equal and pairwise distinct as terms, and the module
structure the notation `Γ(-, -)` carries is found only at the first spelling; so a term in which
a scalar multiplication on a section of a pullback or of a tensor product has to be elaborated
from a written-out type does not typecheck, and a rewrite whose motive abstracts over one is not
type-correct at the transparency `rw` builds its motive at.

For the same reason the comparison is applied through `AlgebraicGeometry.Scheme.Modules.Hom.app`
rather than through `PresheafOfModules.Hom.app _ (op _)`: the two agree definitionally, but only
the first has `Γ(-, -)` as its source and target, so only it composes with a scalar
multiplication.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **Over the whole preimage of an open, pulling a section back is the unit of `q^* ⊣ q_*`.**
The restriction map in the definition of `AlgebraicGeometry.Scheme.Modules.pullbackSection` is
the identity there, so the scheme-level pullback of a section agrees with the ringed-space
`Stacks.RingedSpace.pullbackUnit` that the canonicality clause of [Stacks, Tag 01CD] is stated
for. -/
theorem pullbackSectionHom_preimage_self {T Y : Scheme.{u}} (q : T ⟶ Y) (M : Y.Modules)
    (V : Y.Opens) (a : Γ(M, V)) :
    pullbackSectionHom q M V (q ⁻¹ᵁ V) le_rfl a =
      Stacks.RingedSpace.pullbackUnit q.toLRSHom.toShHom M (op V) a := by
  show Scheme.Modules.pullbackSection q M V (q ⁻¹ᵁ V) le_rfl a = _
  unfold Scheme.Modules.pullbackSection
  have hid : (homOfLE (le_refl (q ⁻¹ᵁ V))).op = 𝟙 (op (q ⁻¹ᵁ V)) := Subsingleton.elim _ _
  rw [hid]
  simp
  rfl

end AlgebraicGeometry

namespace Stacks.PullbackTensorIso

variable {T Y : Scheme.{u}} (q : T ⟶ Y) (A B : Y.Modules) (V : Y.Opens)

/-- **The pullback of a global section of a tensor product, restricted to `q⁻¹V`.** It is the
comparison of [Stacks, Tag 01CD] over `q⁻¹V` applied to the pullback of the restriction of the
section to `V`. This is naturality of the comparison in the open, together with
`AlgebraicGeometry.pullbackSectionHom_resTop`. -/
theorem pullbackTensorSection_resTop (w : Γ(Stacks.Divisors.tensorModules A B, ⊤)) :
    (Stacks.Divisors.tensorModules ((Scheme.Modules.pullback q).obj A)
          ((Scheme.Modules.pullback q).obj B)).presheaf.map (homOfLE le_top).op
        (pullbackTensorSection q A B w) =
      Scheme.Modules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q A B).hom (q ⁻¹ᵁ V)
        (pullbackSectionHom q (Stacks.Divisors.tensorModules A B) V (q ⁻¹ᵁ V) le_rfl
          ((Stacks.Divisors.tensorModules A B).presheaf.map (homOfLE le_top).op w)) :=
  (PresheafOfModules.naturality_apply
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q A B).hom.val
        (homOfLE (le_top : q ⁻¹ᵁ V ≤ ⊤)).op
        (pullbackGlobalSections q (Stacks.Divisors.tensorModules A B) w)).symm.trans
    (congrArg
      (fun z => Scheme.Modules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q A B).hom (q ⁻¹ᵁ V) z)
      (pullbackSectionHom_resTop q (Stacks.Divisors.tensorModules A B) V w).symm)

/-- **The comparison of [Stacks, Tag 01CD] carries the pullback of a product of two sections
over an open to the product of their pullbacks.** This is
`Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt` over an arbitrary open `V` of
the target rather than over `⊤`; the canonicality clause of the tag,
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul`, is already available there, and what is
supplied here is that the scheme-level pullback of a section to the whole preimage `q⁻¹V` is the
ringed-space one. -/
theorem pullbackSectionHom_tensorSectionsAt (a : Γ(A, V)) (b : Γ(B, V)) :
    Scheme.Modules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q A B).hom (q ⁻¹ᵁ V)
        (pullbackSectionHom q (Stacks.Divisors.tensorModules A B) V (q ⁻¹ᵁ V) le_rfl
          (Stacks.Divisors.tensorSection A B V a b)) =
      Stacks.Divisors.tensorSection ((Scheme.Modules.pullback q).obj A)
        ((Scheme.Modules.pullback q).obj B) (q ⁻¹ᵁ V)
        (pullbackSectionHom q A V (q ⁻¹ᵁ V) le_rfl a)
        (pullbackSectionHom q B V (q ⁻¹ᵁ V) le_rfl b) := by
  have key : ∀ (M : Y.Modules) (x : Γ(M, V)),
      pullbackSectionHom q M V (q ⁻¹ᵁ V) le_rfl x =
        Stacks.RingedSpace.pullbackUnit q.toLRSHom.toShHom M (op V) x :=
    fun M x => pullbackSectionHom_preimage_self q M V x
  rw [key A a, key B b]
  exact (congrArg
      (fun z => PresheafOfModules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q A B).hom.val (op (q ⁻¹ᵁ V)) z)
      (key (Stacks.Divisors.tensorModules A B)
        (Stacks.Divisors.tensorSection A B V a b))).trans
    (Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul q.toLRSHom.toShHom A B (op V) a b)

end Stacks.PullbackTensorIso

namespace Stacks.Divisors

/-- **The local equation of a pulled-back section of a tensor product is the pullback of its
local equation.** Let `L₁` and `L₂` be invertible modules on `Y`, trivialized over an affine
open `V` with affine preimage by `u₁` and `u₂`, and let `s` be a global section of `L₁ ⊗ L₂`.
Then `q^*L₁` and `q^*L₂` carry trivializations over `q⁻¹V` — the pulled-back ones,
`Stacks.Divisors.pullbackTrivialization` — for which the local equation of the pullback of `s`
is the pullback of the local equation of `s`. -/
theorem exists_pullbackTensorTrivialization
    {T Y : Scheme.{u}} (q : T ⟶ Y) (L₁ L₂ : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₁]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L₂]
    (s : Γ(Stacks.Divisors.tensorModules L₁ L₂, ⊤))
    {V : Y.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (q ⁻¹ᵁ V))
    (u₁ : Γ(L₁, V) ≃ₗ[Γ(Y, V)] Γ(Y, V)) (u₂ : Γ(L₂, V) ≃ₗ[Γ(Y, V)] Γ(Y, V)) :
    ∃ (e₁ : Γ((Scheme.Modules.pullback q).obj L₁, q ⁻¹ᵁ V) ≃ₗ[Γ(T, q ⁻¹ᵁ V)] Γ(T, q ⁻¹ᵁ V))
      (e₂ : Γ((Scheme.Modules.pullback q).obj L₂, q ⁻¹ᵁ V) ≃ₗ[Γ(T, q ⁻¹ᵁ V)] Γ(T, q ⁻¹ᵁ V)),
      Stacks.Divisors.tensorTrivialization ((Scheme.Modules.pullback q).obj L₁)
          ((Scheme.Modules.pullback q).obj L₂) hW e₁ e₂
          ((Stacks.Divisors.tensorModules ((Scheme.Modules.pullback q).obj L₁)
              ((Scheme.Modules.pullback q).obj L₂)).presheaf.map (homOfLE le_top).op
            (Stacks.PullbackTensorIso.pullbackTensorSection q L₁ L₂ s)) =
        (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom
          (Stacks.Divisors.tensorTrivialization L₁ L₂ hV u₁ u₂
            ((Stacks.Divisors.tensorModules L₁ L₂).presheaf.map (homOfLE le_top).op s)) := by
  have : L₁.IsQuasicoherent := isQuasicoherent_of_isInvertible L₁
  have : L₂.IsQuasicoherent := isQuasicoherent_of_isInvertible L₂
  refine ⟨pullbackTrivialization q L₁ hV hW u₁, pullbackTrivialization q L₂ hV hW u₂, ?_⟩
  refine (LinearEquiv.eq_symm_apply _).mp ?_
  rw [tensorTrivialization_symm_apply, pullbackTrivialization_symm_one q L₁ hV hW u₁,
    pullbackTrivialization_symm_one q L₂ hV hW u₂]
  have hs : (tensorModules L₁ L₂).presheaf.map (homOfLE le_top).op s =
      tensorTrivialization L₁ L₂ hV u₁ u₂
          ((tensorModules L₁ L₂).presheaf.map (homOfLE le_top).op s) •
        tensorSection L₁ L₂ V (u₁.symm 1) (u₂.symm 1) := by
    have h := eq_smul_symm_one (tensorTrivialization L₁ L₂ hV u₁ u₂)
      ((tensorModules L₁ L₂).presheaf.map (homOfLE le_top).op s)
    rwa [tensorTrivialization_symm_apply, one_smul] at h
  have hpb : pullbackSectionHom q (tensorModules L₁ L₂) V (q ⁻¹ᵁ V) le_rfl
        ((tensorModules L₁ L₂).presheaf.map (homOfLE le_top).op s) =
      (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom
          (tensorTrivialization L₁ L₂ hV u₁ u₂
            ((tensorModules L₁ L₂).presheaf.map (homOfLE le_top).op s)) •
        pullbackSectionHom q (tensorModules L₁ L₂) V (q ⁻¹ᵁ V) le_rfl
          (tensorSection L₁ L₂ V (u₁.symm 1) (u₂.symm 1)) :=
    (congrArg
        (fun z => pullbackSectionHom q (tensorModules L₁ L₂) V (q ⁻¹ᵁ V) le_rfl z) hs).trans
      (pullbackSectionHom_smul q (tensorModules L₁ L₂) V (q ⁻¹ᵁ V) le_rfl _ _)
  refine (Stacks.PullbackTensorIso.pullbackTensorSection_resTop q L₁ L₂ V s).trans ?_
  refine (congrArg
      (fun z => Scheme.Modules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q L₁ L₂).hom (q ⁻¹ᵁ V) z)
      hpb).trans ?_
  refine (Scheme.Modules.Hom.app_smul
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso q L₁ L₂).hom _ _).trans ?_
  exact congrArg _
    (Stacks.PullbackTensorIso.pullbackSectionHom_tensorSectionsAt q L₁ L₂ V
      (u₁.symm 1) (u₂.symm 1))

end Stacks.Divisors

end
