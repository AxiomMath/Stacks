module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing

/-!
# Pulled-back sections generate over a compatible pair of affine opens

Let `f : Y ⟶ X` be a morphism of schemes, `F` a quasi-coherent `𝒪_X`-module, and `U ⊆ X`,
`V ⊆ Y` affine opens with `V ≤ f⁻¹U`.  Then the sections
`AlgebraicGeometry.Scheme.Modules.pullbackSection f F U V hVU a`, for `a` ranging over
`Γ(F, U)`, generate `Γ(f^*F, V)` as a module over `Γ(Y, V)`.

Both statements below come from `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, which
identifies `Γ(f^*F, V)` with `Γ(Y, V) ⊗_{Γ(X, U)} Γ(F, U)`, together with its normalisation
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso_one_tmul`: a linear map out of an
extension of scalars is determined by its values on the elements `1 ⊗ a`
(`ModuleCat.ExtendScalars.hom_ext_one_tmul`), and the comparison carries those to the pulled-back
sections.

**Both affineness hypotheses are needed.**  For `U` affine and `V` arbitrary the statement is
false: the pulled-back sections then generate `f^*F` only as a *sheaf* on `V`, and the
obstruction to generating the module of sections on the nose is the first cohomology over `V` of
the kernel of a presentation of `F|_U`.  So this is the affine-local input to statements about a
site, where local generation becomes generation as a sheaf after refining the Zariski covering of
`V` by affine opens; it is not a statement about sections of a pullback over an arbitrary open.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackSectionRange`: the set of sections of `f^*F` over `V`
  obtained by pulling back the sections of `F` over `U`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.hom_ext_of_pullbackSection`: two `Γ(Y, V)`-linear maps out of
  `Γ(f^*F, V)` which agree on the pulled-back sections are equal.
* `AlgebraicGeometry.Scheme.Modules.span_range_pullbackSection_eq_top`: the pulled-back sections
  of `Γ(F, U)` span `Γ(f^*F, V)` over `Γ(Y, V)`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The set of sections of `f^*F` over `V` obtained by pulling back the sections of `F` over
`U`. -/
public def pullbackSectionRange {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) (U : X.Opens)
    (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U) : Set Γ((Scheme.Modules.pullback f).obj F, V) :=
  Set.range fun a : Γ(F, U) => pullbackSection f F U V hVU a

/-- A pulled-back section belongs to `AlgebraicGeometry.Scheme.Modules.pullbackSectionRange`. -/
public theorem pullbackSection_mem_pullbackSectionRange {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) (U : X.Opens) (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (a : Γ(F, U)) :
    (pullbackSection f F U V hVU a : Γ((Scheme.Modules.pullback f).obj F, V)) ∈
      pullbackSectionRange f F U V hVU :=
  ⟨a, rfl⟩

/-- **Two `Γ(Y, V)`-linear maps out of `Γ(f^*F, V)` agreeing on the pulled-back sections of
`Γ(F, U)` are equal**, for `U ⊆ X` and `V ⊆ Y` affine with `V ≤ f⁻¹U` and `F` quasi-coherent.

Composing with the base-change comparison
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, which is an isomorphism and so may be
cancelled, turns the claim into the equality of two maps out of an extension of scalars; those
are determined by their values on `1 ⊗ a`, which the comparison carries to the pullback of
`a`. -/
public theorem hom_ext_of_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    {P : Type u} [AddCommGroup P] [Module Γ(Y, V) P]
    {α β : Γ((Scheme.Modules.pullback f).obj F, V) →ₗ[Γ(Y, V)] P}
    (h : ∀ a : Γ(F, U), α (pullbackSection f F U V hVU a) = β (pullbackSection f F U V hVU a)) :
    α = β := by
  have key : (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom ≫ ModuleCat.ofHom α =
      (affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom ≫ ModuleCat.ofHom β := by
    refine ModuleCat.ExtendScalars.hom_ext_one_tmul _ fun a => ?_
    show α ((affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom
        ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a)) =
      β ((affinePullbackSectionsBaseChangeIso f F hU hV hVU).hom
        ((1 : Γ(Y, V)) ⊗ₜ[Γ(X, U), (f.appLE U V hVU).hom] a))
    rw [affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU a]
    exact h a
  exact congrArg ModuleCat.Hom.hom
    ((Iso.cancel_iso_hom_left (affinePullbackSectionsBaseChangeIso f F hU hV hVU) _ _).mp key)

/-- **The pulled-back sections of a quasi-coherent module over an affine open generate the
sections of the pullback over an affine open above it.**  For `U ⊆ X` and `V ⊆ Y` affine with
`V ≤ f⁻¹U`, the `Γ(Y, V)`-submodule of `Γ(f^*F, V)` spanned by the sections
`AlgebraicGeometry.Scheme.Modules.pullbackSection f F U V hVU a` is everything.

The quotient map by that submodule and the zero map agree on the pulled-back sections, hence
agree by `AlgebraicGeometry.Scheme.Modules.hom_ext_of_pullbackSection`, so the submodule is the
kernel of the zero map. -/
public theorem span_range_pullbackSection_eq_top {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) :
    Submodule.span Γ(Y, V) (pullbackSectionRange f F U V hVU) = ⊤ := by
  have key : (Submodule.span Γ(Y, V) (pullbackSectionRange f F U V hVU)).mkQ = 0 := by
    refine hom_ext_of_pullbackSection f F hU hV hVU fun a => ?_
    have hmem : (pullbackSection f F U V hVU a : Γ((Scheme.Modules.pullback f).obj F, V)) ∈
        Submodule.span Γ(Y, V) (pullbackSectionRange f F U V hVU) :=
      Submodule.subset_span (pullbackSection_mem_pullbackSectionRange f F U V hVU a)
    have h0 : (Submodule.span Γ(Y, V) (pullbackSectionRange f F U V hVU)).mkQ
        (pullbackSection f F U V hVU a) = 0 :=
      (Submodule.mkQ_apply _ _).trans ((Submodule.Quotient.mk_eq_zero _).2 hmem)
    exact h0
  have hker := Submodule.ker_mkQ (Submodule.span Γ(Y, V) (pullbackSectionRange f F U V hVU))
  rw [key, LinearMap.ker_zero] at hker
  exact hker.symm

end AlgebraicGeometry.Scheme.Modules

end
