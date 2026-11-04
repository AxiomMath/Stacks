module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute

/-!
# Dominant morphisms between integral schemes

An integral scheme is irreducible and reduced, so it has a single generic point and its local
rings inject into its function field. For a morphism between integral schemes this collapses
dominance to several equivalent and much more concrete conditions: preservation of the generic
point, injectivity on sections over one — equivalently every — pair of nonempty affine opens,
and injectivity on one — equivalently every — local ring.

## Main results

* `AlgebraicGeometry.tfae_isDominant_of_isIntegral` gives the six equivalent characterizations
  of a dominant morphism between integral schemes.

## Implementation notes

The six entries of the `List.TFAE` are the six numbered conditions in the source. For affine
opens `U ⊆ X` and `V ⊆ Y`, the containment `f(U) ⊆ V` is expressed as `U ≤ f ⁻¹ᵁ V`, and
`f.appLE V U` is the resulting map on rings of sections. The point `y` in the last two
conditions is definitionally the image `f(x)`, as in `f.stalkMap x`.

## References

* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Every point of `X` has affine open neighbourhoods `U ∋ x` and `V ∋ f x` with
`U ≤ f ⁻¹ᵁ V`. -/
public theorem Scheme.Hom.exists_affineOpens_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens), x ∈ U.1 ∧ f x ∈ V.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (V.2.preimage f.continuous)
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hxU, hxV, hUV⟩

/-- If `Y` is integral and the stalk map of `f` at some `x ∈ U` is injective, then so is
`f.appLE V U`. -/
public theorem Scheme.Hom.injective_appLE_of_injective_stalkMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegral Y] {U : X.Opens} {V : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V) {x : X}
    (hxU : x ∈ U) (hx : Function.Injective (f.stalkMap x)) :
    Function.Injective (f.appLE V U hUV) := by
  intro a b hab
  apply germ_injective_of_isIntegral Y (f x) (show f x ∈ V from hUV hxU)
  apply hx
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply,
    ← X.presheaf.germ_res_apply (U := U) (V := f ⁻¹ᵁ V) (homOfLE hUV) x hxU,
    ← X.presheaf.germ_res_apply (U := U) (V := f ⁻¹ᵁ V) (homOfLE hUV) x hxU]
  simpa [Scheme.Hom.appLE] using congrArg (fun z => X.presheaf.germ _ x hxU z) hab

/-- The generic point of an integral scheme lies in every nonempty open. -/
private theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IsIntegral X] {U : X.Opens}
    (hU : Nonempty U) : genericPoint X ∈ U :=
  (genericPoint_spec X).mem_open_set_iff U.2 |>.mpr (by simpa using hU)

/-- A morphism of integral schemes that is injective on sections over some pair of nonempty
affine opens maps the generic point to the generic point. -/
public theorem Scheme.Hom.map_genericPoint_of_injective_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] (U : X.affineOpens) (V : Y.affineOpens)
    (hU : Nonempty U.1) (hV : Nonempty V.1) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (hinj : Function.Injective (f.appLE V.1 U.1 hUV)) :
    f (genericPoint X) = genericPoint Y := by
  have hx := genericPoint_mem_of_nonempty hU
  have hy' := genericPoint_mem_of_nonempty hV
  have hp : V.2.primeIdealOf ⟨f (genericPoint X), hUV hx⟩ =
      V.2.primeIdealOf ⟨genericPoint Y, hy'⟩ := by
    rw [V.2.primeIdealOf_genericPoint,
      ← IsAffineOpen.comap_primeIdealOf_appLE V.1 V.2 U.1 U.2 hUV hx,
      U.2.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine,
      genericPoint_eq_bot_of_affine]
    ext a
    show f.appLE V.1 U.1 hUV a ∈ (⊥ : Ideal Γ(X, U.1)) ↔
      a ∈ (⊥ : Ideal Γ(Y, V.1))
    simpa only [Ideal.mem_bot, map_zero] using (hinj.eq_iff (b := 0) (a := a))
  simpa [V.2.fromSpec_primeIdealOf] using congrArg V.2.fromSpec hp

/-- **Stacks Project, Tag 0CC1.** For a morphism `f : X ⟶ Y` of integral schemes, the
following are equivalent: `f` is dominant; it maps the generic point of `X` to that of `Y`;
the map on sections is injective for some, or for every, pair of nonempty affine opens
`U ⊆ X`, `V ⊆ Y` with `f(U) ⊆ V`; and the map on local rings is injective at some, or at
every, point of `X`. -/
@[stacks 0CC1]
public theorem tfae_isDominant_of_isIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] :
    List.TFAE [
      IsDominant f,
      f (genericPoint X) = genericPoint Y,
      ∃ (U : X.affineOpens) (V : Y.affineOpens)
        (_ : Nonempty U.1) (_ : Nonempty V.1)
        (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        Function.Injective (f.appLE V.1 U.1 hUV),
      ∀ (U : X.affineOpens) (V : Y.affineOpens)
        (_ : Nonempty U.1) (_ : Nonempty V.1)
        (hUV : U.1 ≤ f ⁻¹ᵁ V.1),
        Function.Injective (f.appLE V.1 U.1 hUV),
      ∃ x : X, Function.Injective (f.stalkMap x),
      ∀ x : X, Function.Injective (f.stalkMap x)] := by
  classical
  tfae_have 1 ↔ 2 := by
    rw [isDominant_iff, denseRange_iff_closure_range]
    refine ⟨fun h => ((genericPoint_spec X).image f.continuous).eq
      (by simpa [h] using genericPoint_spec Y), fun h => ?_⟩
    refine (Set.subset_univ _).antisymm ?_
    rw [← (genericPoint_spec Y).def, ← h]
    exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _))
  tfae_have 2 → 4 := by
    intro h U V hU hV hUV
    have hx := genericPoint_mem_of_nonempty hU
    let _ : Field (Y.presheaf.stalk (genericPoint Y)) :=
      inferInstanceAs (Field Y.functionField)
    have : Nontrivial (Y.presheaf.stalk (f (genericPoint X))) := h.symm ▸ inferInstance
    have : IsSimpleRing (Y.presheaf.stalk (f (genericPoint X))) := h.symm ▸ inferInstance
    exact f.injective_appLE_of_injective_stalkMap hUV hx (RingHom.injective _)
  tfae_have 4 → 3 := by
    intro h
    obtain ⟨U, V, hxU, hxV, hUV⟩ := f.exists_affineOpens_le_preimage (Classical.arbitrary X)
    exact ⟨U, V, ⟨⟨_, hxU⟩⟩, ⟨⟨_, hxV⟩⟩, hUV, h U V ⟨⟨_, hxU⟩⟩ ⟨⟨_, hxV⟩⟩ hUV⟩
  tfae_have 3 → 2 := fun ⟨U, V, hU, hV, hUV, hinj⟩ =>
    f.map_genericPoint_of_injective_appLE U V hU hV hUV hinj
  tfae_have 2 → 6 := by
    intro h x
    obtain ⟨U, V, hxU, hxV, hUV⟩ := f.exists_affineOpens_le_preimage x
    apply V.2.stalkMap_injective f x hxV
    intro s hs
    have happ' : f.app V.1 s = 0 :=
      (germ_injective_of_isIntegral X x hxV)
        (by simpa [Scheme.Hom.germ_stalkMap_apply] using hs)
    have happ : f.appLE V.1 U.1 hUV s = 0 := by
      show X.presheaf.map (homOfLE hUV).op (f.app V.1 s) = 0
      rw [happ', map_zero]
    have hs0 : s = 0 := tfae_2_to_4 h U V ⟨⟨x, hxU⟩⟩ ⟨⟨f x, hxV⟩⟩ hUV (by simpa using happ)
    simp [hs0]
  tfae_have 6 → 5 := fun h => ⟨genericPoint X, h _⟩
  tfae_have 5 → 3 := by
    rintro ⟨x, hx⟩
    obtain ⟨U, V, hxU, hxV, hUV⟩ := f.exists_affineOpens_le_preimage x
    exact ⟨U, V, ⟨⟨x, hxU⟩⟩, ⟨⟨f x, hxV⟩⟩, hUV,
      f.injective_appLE_of_injective_stalkMap hUV hxU hx⟩
  tfae_finish

end AlgebraicGeometry
