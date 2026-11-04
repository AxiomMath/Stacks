module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyLinear
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPushforwardLinear

/-!
# Multiplication by a global function on cohomology, and the scalars it is read through

Conclusion (c) of [Stacks, Tag 0EX3] needs multiplication by a function on the base to be carried
through every step of the computation of the right-hand end of its comparison map. Two of those
steps are purely about scalars rather than about geometry, and they are what this file supplies:
the degree-`n` cohomology of multiplication by a global function **is** multiplication by that
function, and multiplication by a scalar survives both restriction of scalars along a ring map
and transport along an equality of ring maps.

`AlgebraicGeometry.baseScalar` is the multiplication operator of the directory — multiplication
by an element of the base ring of a scheme over `Spec R`, as an element of the centre of the
category of module sheaves — and
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.rightDerivedPlus_pushforward_map_baseScalar`
already says that a higher **direct image** carries it to itself. The statements below are the
same assertion for **global sections** instead of a direct image, which is the functor the
Eilenberg-Watts endofunctor of conclusion (b) ends with, in both indexings of the right derived
functors.

## Main results

* `…TopDegreeBaseChange.rightDerived_moduleGlobalSections_map_baseScalar` and
  `…TopDegreeBaseChange.rightDerivedPlus_moduleGlobalSections_map_baseScalar`: **the cohomology
  of multiplication by a base scalar is multiplication by the image of that scalar in the
  functions on the space**, for Mathlib's `ℕ`-indexed and for the `ℤ`-indexed right derived
  functors.
* `…TopDegreeBaseChange.rightDerivedPlus_moduleGlobalSections_map_baseScalar_comp_toSpecΓ`: the
  same at the structure morphism `(f ≫ Y.toSpecΓ)`, where the scalar is a global function on `Y`
  and its image is its pullback `f^♯ r`. This is the form the computation consumes.
* `…TopDegreeBaseChange.smul_id_restrictScalars`: **multiplication by `a` on a module with its
  scalars restricted along `χ` is multiplication by `χ a`.**
* `…TopDegreeBaseChange.restrictScalars_map_comp_eqToHom`: **transport along an equality of ring
  maps commutes with restriction of scalars of a morphism.**

## Implementation notes

*Why the conclusions are stated with `AlgebraicGeometry.baseScalar` and not with a scalar
action.* The `R`-linear structure on the module sheaves of a scheme over `Spec R` is
`AlgebraicGeometry.modulesLinear`, which is not an instance — it depends on the structure
morphism and not only on the scheme. Stating the hypothesis as `r • 𝟙 M` would therefore need
that structure in scope at every use. `baseScalar` is the multiplication operator itself, and
`(baseScalar R X r).app M = r • 𝟙 M` holds by `CategoryTheory.Category.comp_id`, so the
statements below are usable with no linear structure in scope. This is the discipline of
`rightDerivedPlus_pushforward_map_baseScalar`.

*The target scalar is named by `AlgebraicGeometry.baseRingToSections` rather than by
`algebraMap`.* The two are equal by definition — `Stacks.Cohomology.AffineBase.baseSectionsAlgebra`
is `RingHom.toAlgebra` of `baseRingToSections` at the top open — and naming the ring map keeps
the `Algebra` instance out of the statement for the same reason.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase
open scoped ModuleCat.Algebra

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

section Scalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Multiplication by `a` on a module whose scalars are restricted along `χ` is multiplication
by `χ a`.** Both sides send `x` to `χ a • x`, the left by the definition of the restricted
action. -/
theorem smul_id_restrictScalars (χ : R →+* S) (H : ModuleCat.{u} S) (a : R) :
    a • 𝟙 ((ModuleCat.restrictScalars χ).obj H) =
      (ModuleCat.restrictScalars χ).map ((χ a) • 𝟙 H) :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- **Transport along an equality of ring maps commutes with restriction of scalars.** For equal
ring maps `χ = χ'` and a morphism `t` of `S`-modules, restricting `t` along `χ` and then
transporting is transporting and then restricting along `χ'`: the transport is `eqToHom` of a
`congrArg` in the ring map, as in
`…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections`. -/
theorem restrictScalars_map_comp_eqToHom {χ χ' : R →+* S} (e : χ = χ')
    {H H' : ModuleCat.{u} S} (t : H ⟶ H') :
    (ModuleCat.restrictScalars χ).map t ≫
        eqToHom (congrArg (fun ψ : R →+* S => (ModuleCat.restrictScalars ψ).obj H') e) =
      eqToHom (congrArg (fun ψ : R →+* S => (ModuleCat.restrictScalars ψ).obj H) e) ≫
        (ModuleCat.restrictScalars χ').map t := by
  subst e
  simp

end Scalars

section GlobalSections

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))

/-- **The `ℤ`-indexed cohomology of a scheme over `Spec R` is `R`-linear.** This is
`Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections` transported along the
comparison `Stacks.DerivedIndexing.rightDerivedIso` of the two indexings, as in
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.linear_rightDerivedPlus_pushforward`. -/
theorem linear_rightDerivedPlus_moduleGlobalSections (n : ℕ) :
    ((moduleGlobalSections X.left).rightDerivedPlus (n : ℤ)).Linear R := by
  let := linear_rightDerived_moduleGlobalSections R X n
  exact Functor.linear_of_iso R
    (Stacks.DerivedIndexing.rightDerivedIso (moduleGlobalSections X.left) n)

/-- A linear functor out of the module sheaves carries a base scalar to the scalar it names. -/
private theorem map_baseScalar_app_of_linear {F : X.left.Modules ⥤ ModuleCat.{u} Γ(X.left, ⊤)}
    [F.Linear R] (r : R) (M : X.left.Modules) (c : Γ(X.left, ⊤))
    (hc : AlgebraicGeometry.baseRingToSections R X (op ⊤) r = c) :
    F.map ((AlgebraicGeometry.baseScalar R X r).app M) = c • 𝟙 (F.obj M) := by
  rw [show (AlgebraicGeometry.baseScalar R X r).app M = r • 𝟙 M from (Category.comp_id _).symm]
  exact Eq.trans ((Functor.linear_iff R F).mp inferInstance M r)
    (congrArg (fun z : Γ(X.left, ⊤) => z • 𝟙 (F.obj M)) hc)

/-- **The degree-`n` cohomology of multiplication by a base scalar is multiplication by the image
of that scalar in the functions on the space.** For a scheme `X` over `Spec R`, a module `M` on
it and `r : R`, the degree-`n` cohomology of the endomorphism "multiply by `r`" of `M` is
multiplication by the image of `r` in `Γ(X, ⊤)` on `H^n(X, M)`.

That image is taken as an argument `c` together with its defining equation, as in
`…TopDegreeBaseChange.conjugateRestrict_scalar`: `AlgebraicGeometry.baseRingToSections` lands in
`X.ringCatSheaf.obj.obj (op ⊤)` while the scalar action on `H^n(X, M)` is found over
`Γ(X, ⊤)`, and naming the element lets the consumer supply whichever spelling it has.

This is `Stacks.Cohomology.AffineBase.linear_rightDerived_moduleGlobalSections` read at
`r • 𝟙 M`. -/
theorem rightDerived_moduleGlobalSections_map_baseScalar (n : ℕ) (r : R)
    (M : X.left.Modules) (c : Γ(X.left, ⊤))
    (hc : AlgebraicGeometry.baseRingToSections R X (op ⊤) r = c) :
    ((moduleGlobalSections X.left).rightDerived n).map
        ((AlgebraicGeometry.baseScalar R X r).app M) =
      c • 𝟙 (((moduleGlobalSections X.left).rightDerived n).obj M) := by
  let := linear_rightDerived_moduleGlobalSections R X n
  exact map_baseScalar_app_of_linear R X r M c hc

/-- **The `ℤ`-indexed form of `rightDerived_moduleGlobalSections_map_baseScalar`.** -/
theorem rightDerivedPlus_moduleGlobalSections_map_baseScalar (n : ℕ) (r : R)
    (M : X.left.Modules) (c : Γ(X.left, ⊤))
    (hc : AlgebraicGeometry.baseRingToSections R X (op ⊤) r = c) :
    ((moduleGlobalSections X.left).rightDerivedPlus (n : ℤ)).map
        ((AlgebraicGeometry.baseScalar R X r).app M) =
      c • 𝟙 (((moduleGlobalSections X.left).rightDerivedPlus (n : ℤ)).obj M) := by
  let := linear_rightDerivedPlus_moduleGlobalSections R X n
  exact map_baseScalar_app_of_linear R X r M c hc

end GlobalSections

/-- **The base scalar at the structure morphism `f ≫ Y.toSpecΓ`, read at the top open, is the
pullback of the function.** This is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.baseRingToSections_comp_toSpecΓ` at the top
open, where the restriction map it produces is the identity. -/
theorem baseRingToSections_comp_toSpecΓ_top {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    AlgebraicGeometry.baseRingToSections ↑Γ(Y, ⊤)
        (Over.mk (f ≫ Y.toSpecΓ) : Over (Spec (CommRingCat.of ↑Γ(Y, ⊤)))) (op ⊤) r =
      f.appTop.hom r := by
  refine Eq.trans (SchemeHigherDirectImage.baseRingToSections_comp_toSpecΓ f (op ⊤) r) ?_
  rw [show ((⊤ : X.Opens)).leTop = 𝟙 (⊤ : X.Opens) from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The `ℤ`-indexed cohomology of multiplication by the pullback of a global function is
multiplication by that function's pullback.** For a morphism of schemes `f : X ⟶ Y`, a global
function `r` on `Y` and a module `M` on `X`, the degree-`n` cohomology of multiplication by
`f^♯ r` on `M` is multiplication by `f^♯ r` on `H^n(X, M)`.

The multiplication operator upstairs is `AlgebraicGeometry.baseScalar` for the structure morphism
`f ≫ Y.toSpecΓ`, which is the one
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.preimageScalar` is defined by. -/
theorem rightDerivedPlus_moduleGlobalSections_map_baseScalar_comp_toSpecΓ
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) (r : Γ(Y, ⊤)) (M : X.Modules) :
    ((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).map
        ((AlgebraicGeometry.baseScalar ↑Γ(Y, ⊤)
          (Over.mk (f ≫ Y.toSpecΓ) :
            Over (Spec (CommRingCat.of ↑Γ(Y, ⊤)))) r).app M) =
      (f.appTop.hom r) • 𝟙 (((moduleGlobalSections X).rightDerivedPlus (n : ℤ)).obj M) :=
  rightDerivedPlus_moduleGlobalSections_map_baseScalar ↑Γ(Y, ⊤)
    (Over.mk (f ≫ Y.toSpecΓ) : Over (Spec (CommRingCat.of ↑Γ(Y, ⊤)))) n r M _
    (baseRingToSections_comp_toSpecΓ_top f r)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
