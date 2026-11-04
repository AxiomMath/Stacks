module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksReduced

/-!
# The structure sheaf is an epimorphism onto the sheaf of meromorphic functions

Let `X` be a scheme. Every section of the sheaf `K_X` of meromorphic functions is, locally on an
affine open, a fraction `a/b` with `a` and `b` regular functions and `b` a nonzerodivisor: the
sheaf is the sheafification of the presheaf of objectwise total quotient rings, and on an affine
open that presheaf is the localization of the regular functions at all of their nonzerodivisors.
Consequently the canonical morphism `𝒪_X ⟶ K_X` is an epimorphism of sheaves of rings, for two
ring homomorphisms out of `K_X(V)` which agree on the image of `𝒪_X(V)` agree on `a/b` as well,
the image of `b` being a unit.

## Main results

* `AlgebraicGeometry.exists_isUnit_mul_toTotalQuotientSheaf_eq`: locally every meromorphic
  function is a fraction with unit denominator.
* `AlgebraicGeometry.epi_toTotalQuotientRingCatSheaf`: the canonical morphism `𝒪_X ⟶ K_X` is an
  epimorphism of sheaves of rings.

## Implementation notes

The module-theoretic `SheafOfModules` API indexes modules by sheaves of not necessarily
commutative rings, so the epimorphism proved here is the one between the images of `𝒪_X` and
`K_X` under `sheafCompose` with `forget₂ CommRingCat RingCat`, namely
`AlgebraicGeometry.Scheme.toTotalQuotientRingCatSheaf`. Its sections and restriction maps are
those of `AlgebraicGeometry.Scheme.toTotalQuotientSheaf`, so nothing is lost; the two spellings
are identified by the definitional bridge named `hcarrier` in the proof.

Epimorphicity is tested on sections rather than on stalks: the denominator is inverted on the
nose over an affine open, which makes the cancellation a one-line computation with units, whereas
a stalkwise argument would need the stalks of the *sheafification* to be identified with total
quotient rings — true only under hypotheses on the weakly associated points of `X`, which this
statement does not need.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- **Every meromorphic function is locally a fraction with unit denominator.** Given a section
`s` of `K_X` over an open set `U` and a point `x` of `U`, there is an open `V ∋ x` inside `U` and
regular functions `a` and `b` on `V` whose images in `K_X(V)` satisfy `s · b = a`, with the image
of `b` a unit. This expresses `s` as `a / b` on `V`. -/
theorem exists_isUnit_mul_toTotalQuotientSheaf_eq (X : Scheme.{u}) (U : X.Opens)
    (s : ToType ((totalQuotientSheaf X.sheaf).presheaf.obj (op U))) {x : X} (hx : x ∈ U) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ ∃ a b : Γ(X, V),
      IsUnit ((X.toTotalQuotientSheaf.hom.app (op V)).hom b) ∧
        (totalQuotientSheaf X.sheaf).presheaf.map (homOfLE hVU).op s *
            (X.toTotalQuotientSheaf.hom.app (op V)).hom b =
          (X.toTotalQuotientSheaf.hom.app (op V)).hom a := by
  classical
  have hsurj : ∀ y ∈ U, ∃ (W : X.Opens) (g : W ⟶ U), Presheaf.imageSieve
      (toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf) s g ∧
      y ∈ W :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf) s
  obtain ⟨W, g, hg, hxW⟩ := hsurj x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have hVU : V ≤ U := le_trans hVW g.le
  obtain ⟨t, ht⟩ : Presheaf.imageSieve (toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf) s (homOfLE hVU) :=
    (Presheaf.imageSieve (toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf) s).downward_closed hg (homOfLE hVW)
  let : Algebra Γ(X, V) (X.presheaf.totalQuotientPresheaf.obj (op V)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (op V)).hom.toAlgebra
  have : IsLocalization (nonZeroDivisors Γ(X, V))
      (X.presheaf.totalQuotientPresheaf.obj (op V)) :=
    hV.isLocalization_totalQuotientPresheaf_obj
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, V)) t
  have hα : ∀ r : Γ(X, V), (X.toTotalQuotientSheaf.hom.app (op V)).hom r =
      ((toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op V)).hom
        (algebraMap Γ(X, V) (X.presheaf.totalQuotientPresheaf.obj (op V)) r) := fun _ => rfl
  refine ⟨V, hVU, hxV, a, b.1, ?_, ?_⟩
  · rw [hα]
    exact (IsLocalization.map_units (M := nonZeroDivisors Γ(X, V))
      (X.presheaf.totalQuotientPresheaf.obj (op V)) b).map _
  · have hcarrier : (totalQuotientSheaf X.sheaf).presheaf.map (homOfLE hVU).op s =
        ((toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf).app (op V)).hom t := ht.symm
    rw [hcarrier, hα, hα]
    exact (((toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf).app (op V)).hom.map_mul _ _).symm.trans
      (congrArg _ hab)

/-- **The canonical morphism `𝒪_X ⟶ K_X` is an epimorphism of sheaves of rings.** Two ring
homomorphisms out of `K_X(V)` which agree on the image of `𝒪_X(V)` agree on every fraction
`a / b` with `b` a nonzerodivisor, because the image of `b` is a unit; and every meromorphic
function is locally such a fraction. -/
theorem epi_toTotalQuotientRingCatSheaf (X : Scheme.{u}) :
    Epi X.toTotalQuotientRingCatSheaf := by
  refine ⟨fun {Z} g h w => ?_⟩
  refine CategoryTheory.Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  obtain ⟨U⟩ := U
  refine RingCat.hom_ext (RingHom.ext fun s => ?_)
  refine TopCat.Presheaf.IsSheaf.section_ext (F := Z.obj) Z.property fun x hx => ?_
  obtain ⟨V, hVU, hxV, a, b, hunit, heq⟩ :=
    exists_isUnit_mul_toTotalQuotientSheaf_eq X U s hx
  refine ⟨V, hVU, hxV, ?_⟩
  have hcarrier : X.totalQuotientRingCatSheaf.obj.map (homOfLE hVU).op s =
      (totalQuotientSheaf X.sheaf).presheaf.map (homOfLE hVU).op s := rfl
  have hcancel : ∀ k : X.totalQuotientRingCatSheaf ⟶ Z,
      (k.hom.app (op V)).hom
          ((totalQuotientSheaf X.sheaf).presheaf.map (homOfLE hVU).op s) *
        (k.hom.app (op V)).hom ((X.toTotalQuotientSheaf.hom.app (op V)).hom b) =
      (k.hom.app (op V)).hom ((X.toTotalQuotientSheaf.hom.app (op V)).hom a) := fun k =>
    ((k.hom.app (op V)).hom.map_mul _ _).symm.trans (congrArg _ heq)
  have hw : ∀ r : Γ(X, V), (g.hom.app (op V)).hom
        ((X.toTotalQuotientSheaf.hom.app (op V)).hom r) =
      (h.hom.app (op V)).hom ((X.toTotalQuotientSheaf.hom.app (op V)).hom r) := fun r =>
    congrArg (fun k : X.ringCatSheaf ⟶ Z => (k.hom.app (op V)).hom r) w
  rw [← NatTrans.naturality_apply g.hom (homOfLE hVU).op s,
    ← NatTrans.naturality_apply h.hom (homOfLE hVU).op s, hcarrier]
  refine (hunit.map (g.hom.app (op V)).hom).mul_left_inj.mp ?_
  refine (hcancel g).trans ((hw a).trans ((hcancel h).symm.trans ?_))
  exact congrArg (fun z => (h.hom.app (op V)).hom
    ((totalQuotientSheaf X.sheaf).presheaf.map (homOfLE hVU).op s) * z) (hw b).symm

end AlgebraicGeometry

end
