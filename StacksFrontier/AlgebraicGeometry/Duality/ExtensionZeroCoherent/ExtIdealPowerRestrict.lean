module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplayRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# The restriction map `Ext^i_X(Iⁿ G, F) ⟶ Ext^i_U(G|_U, F|_U)`, and its bijectivity for `i = 0`

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals, `U = X \ V(I)` and `G`, `F` two
`𝒪_X`-modules. This file constructs the canonical map

`Ext^i_X(Iⁿ G, F) ⟶ Ext^i_U(G|_U, F|_U)`

of the core case of [Stacks, Tag 0G2H] — restriction of an `Ext`-class along the open immersion
`U.ι`, followed by the comparison `(Iⁿ G)|_U ≅ G|_U` — shows that these maps form a cocone on
the direct system `n ↦ Ext^i_X(Iⁿ G, F)`, and proves that the resulting map out of the colimit
is bijective **for `i = 0`**, where it is the first display of [Stacks, Tag 01YB] read through
`CategoryTheory.Abelian.Ext.mk₀`.

Bijectivity is stated in the shape a filtered colimit over `ℕ` makes it concrete, and in which
the first display is already available: surjectivity as the existence of a preimage at some
stage `n` (`exists_extIdealPowRestrict_eq`) and injectivity as the vanishing of a class at some
later stage `n + N` (`exists_mk₀_comp_eq_zero_of_extIdealPowRestrict_eq_zero`). No colimit
object appears, so nothing has to be transported between the universe of the morphisms of
`X.Modules` and the universe of `CategoryTheory.HasExt`.

## The restriction of an `Ext`-class

Restriction along an open immersion of schemes is exact —
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_additive` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits`, the colimit half being
instance search from left adjointness — so Mathlib's
`CategoryTheory.Abelian.Ext.mapExactFunctor` applies to it. That is `extRestrict` below, and
with it come, from Mathlib, its compatibility with `CategoryTheory.Abelian.Ext.mk₀`, with
composition, with addition, and with the boundary class
`CategoryTheory.ShortComplex.ShortExact.extClass` of a short exact sequence, the last of which is
the compatibility of the long exact `Ext`-sequences with restriction.

## The degree-zero case

The two halves of the first display are available in the Grothendieck-slice form
(`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_homRestrict_eq` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero_of_homRestrict_eq_zero`), and
`Ext` is about the geometric restriction functor, so each has to be transported across
`AlgebraicGeometry.Scheme.Modules.overEquiv`. Surjectivity is transported in
`StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplayRestrict`; injectivity is
transported here, which needs only that the comparison equivalence is additive and faithful, so
that a morphism with vanishing geometric restriction has vanishing slice restriction.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.extRestrict`: restriction of an `Ext`-class along
  the open immersion `U.ι`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.restrictIdealPowSmulIso`: the comparison
  `(Iⁿ G)|_U ≅ G|_U` in the geometric form.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict`: **the canonical map
  `Ext^i_X(Iⁿ G, F) ⟶ Ext^i_U(G|_U, F|_U)`.**

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.extRestrict_extClass`: restriction commutes with
  the boundary class of a short exact sequence.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.extIdealPowRestrict_mk₀_comp`: the canonical maps
  form a cocone on `n ↦ Ext^i_X(Iⁿ G, F)`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.over_eq_zero_of_restrictFunctor_map_eq_zero` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero_of_restrictFunctor_map_eq_zero`:
  the injectivity assertion of the first display in terms of the geometric restriction functor.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_extIdealPowRestrict_eq` and
  `exists_mk₀_comp_eq_zero_of_extIdealPowRestrict_eq_zero`, in the same namespace:
  **`colim_n Ext^0_X(Iⁿ G, F) = Ext^0_U(G|_U, F|_U)`**, the base case of the induction on `i`.

## Implementation notes

The two `CategoryTheory.HasExt` universes are instance arguments rather than fixed: `X.Modules`
has `HasExt.{u + 1}` from `CategoryTheory.HasDerivedCategory.standard`
(`Stacks.ExtEffacement.hasExt_modules`) and `HasExt.{u}` from the global
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and neither is canonical. Nothing below
needs them to agree, and nothing below fixes one.

`asIso` is applied with its witness positional: `Scheme.Modules` carries
its own `Category` instance whose `Hom` is only definitionally that of `SheafOfModules`, so
instance resolution does not find an `IsIso` hypothesis that is in scope.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H), whose proof reduces to
  the bijectivity of the map constructed here, for all `i ≥ 0`.
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower

universe w w' u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### Restriction of `Ext` along an open immersion -/

section Restrict

variable (U : X.Opens)

/-- Restriction of an `Ext`-class along the open immersion `U.ι`. -/
public def extRestrict [HasExt.{w} X.Modules] [HasExt.{w'} U.toScheme.Modules]
    {A B : X.Modules} {i : ℕ} (ξ : Ext.{w} A B i) :
    Ext.{w'} ((Scheme.Modules.restrictFunctor U.ι).obj A)
      ((Scheme.Modules.restrictFunctor U.ι).obj B) i :=
  ξ.mapExactFunctor (Scheme.Modules.restrictFunctor U.ι)

/-- Restriction along `U.ι` sends the degree-zero class `Ext.mk₀ f` to the degree-zero class of
the restricted morphism. -/
public theorem extRestrict_mk₀ [HasExt.{w} X.Modules] [HasExt.{w'} U.toScheme.Modules]
    {A B : X.Modules} (f : A ⟶ B) :
    extRestrict.{w, w'} U (Ext.mk₀ f) = Ext.mk₀ ((Scheme.Modules.restrictFunctor U.ι).map f) :=
  Ext.mapExactFunctor_mk₀ _ f

/-- Restriction along `U.ι` is compatible with the composition of `Ext`-classes. -/
public theorem extRestrict_comp [HasExt.{w} X.Modules] [HasExt.{w'} U.toScheme.Modules]
    {A B C : X.Modules} {a b c : ℕ} (α : Ext.{w} A B a) (β : Ext.{w} B C b) (h : a + b = c) :
    extRestrict.{w, w'} U (α.comp β h)
      = (extRestrict.{w, w'} U α).comp (extRestrict.{w, w'} U β) h :=
  Ext.mapExactFunctor_comp _ α β h

/-- Restriction along `U.ι` sends the zero class to zero. -/
@[simp] public theorem extRestrict_zero [HasExt.{w} X.Modules] [HasExt.{w'} U.toScheme.Modules]
    (A B : X.Modules) (i : ℕ) : extRestrict.{w, w'} U (0 : Ext.{w} A B i) = 0 :=
  Ext.mapExactFunctor_zero _ A B i

/-- Restriction along `U.ι` is additive. -/
@[simp] public theorem extRestrict_add [HasExt.{w} X.Modules] [HasExt.{w'} U.toScheme.Modules]
    {A B : X.Modules} {i : ℕ} (ξ η : Ext.{w} A B i) :
    extRestrict.{w, w'} U (ξ + η) = extRestrict.{w, w'} U ξ + extRestrict.{w, w'} U η :=
  Ext.mapExactFunctor_add _ A B i ξ η

/-- **Restriction commutes with the boundary class of a short exact sequence.** The connecting
maps of the long exact `Ext`-sequences are composition with `extClass`, so this is the
compatibility of those long exact sequences with restriction to `U`. -/
public theorem extRestrict_extClass [HasExt.{w} X.Modules] [HasExt.{w'} U.toScheme.Modules]
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    extRestrict.{w, w'} U hS.extClass
      = (hS.map_of_exact (Scheme.Modules.restrictFunctor U.ι)).extClass :=
  Ext.mapExactFunctor_extClass _ hS

end Restrict

/-! ### The geometric comparison `(Iⁿ G)|_U ≅ G|_U` -/

section Iso

variable (I : X.IdealSheafData) (U : X.Opens)
  (hU : Disjoint (U : Set X) (I.support : Set X))

/-- **`(Iⁿ G)|_U ≅ G|_U`**, the geometric form of
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulOverIso`. -/
public def restrictIdealPowSmulIso (n : ℕ) (G : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).obj (idealPowSmul I n G) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj G :=
  @asIso _ _ _ _ ((Scheme.Modules.restrictFunctor U.ι).map (idealPowerMultiple I n G).ι)
    (isIso_restrictFunctor_map_idealPowerMultiple_ι I n G hU)

/-- The comparison `(Iⁿ G)|_U ≅ G|_U` is the restriction of the inclusion `Iⁿ G ⟶ G`. -/
@[simp] public theorem restrictIdealPowSmulIso_hom (n : ℕ) (G : X.Modules) :
    (restrictIdealPowSmulIso I U hU n G).hom =
      (Scheme.Modules.restrictFunctor U.ι).map (idealPowerMultiple I n G).ι := rfl

/-- The comparisons `(Iⁿ G)|_U ≅ G|_U` are compatible with the inclusions of the filtration. -/
public theorem restrict_idealPowSmulMap_comp_hom {n m : ℕ} (h : n ≤ m) (G : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (idealPowSmulMap I G h) ≫
        (restrictIdealPowSmulIso I U hU n G).hom =
      (restrictIdealPowSmulIso I U hU m G).hom :=
  ((Scheme.Modules.restrictFunctor U.ι).map_comp _ _).symm.trans
    (congrArg ((Scheme.Modules.restrictFunctor U.ι).map) (idealPowerMultipleMap_comp_ι I G h))

/-- The inverse comparisons are compatible with the inclusions of the filtration. -/
public theorem inv_comp_restrict_idealPowSmulMap {n m : ℕ} (h : n ≤ m) (G : X.Modules) :
    (restrictIdealPowSmulIso I U hU m G).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (idealPowSmulMap I G h) =
      (restrictIdealPowSmulIso I U hU n G).inv := by
  have hf : (Scheme.Modules.restrictFunctor U.ι).map (idealPowSmulMap I G h)
      = (restrictIdealPowSmulIso I U hU m G).hom ≫ (restrictIdealPowSmulIso I U hU n G).inv :=
    (Iso.eq_comp_inv _).mpr (restrict_idealPowSmulMap_comp_hom I U hU h G)
  rw [hf, Iso.inv_hom_id_assoc]

end Iso

/-! ### The canonical map `Ext^i_X(Iⁿ G, F) ⟶ Ext^i_U(G|_U, F|_U)` -/

section Canonical

variable (I : X.IdealSheafData) (U : X.Opens)
  (hU : Disjoint (U : Set X) (I.support : Set X))

/-- **The canonical map `Ext^i_X(Iⁿ G, F) ⟶ Ext^i_U(G|_U, F|_U)`**: restrict the class along
`U.ι` and compose with the inverse of the comparison `(Iⁿ G)|_U ≅ G|_U`.

For `i = 0` this is the `n`-th leg of the cocone of the first display of [Stacks, Tag 01YB],
read through `CategoryTheory.Abelian.Ext.mk₀`. -/
public def extIdealPowRestrict [HasExt.{w} X.Modules] [HasExt.{w'} U.toScheme.Modules]
    {G F : X.Modules} {i n : ℕ} (ξ : Ext.{w} (idealPowSmul I n G) F i) :
    Ext.{w'} ((Scheme.Modules.restrictFunctor U.ι).obj G)
      ((Scheme.Modules.restrictFunctor U.ι).obj F) i :=
  (Ext.mk₀ (restrictIdealPowSmulIso I U hU n G).inv).comp
    (extRestrict.{w, w'} U ξ) (zero_add i)

/-- **The canonical maps form a cocone on the direct system `n ↦ Ext^i_X(Iⁿ G, F)`**: a class
and its image under the transition map `Ext^i_X(Iⁿ G, F) ⟶ Ext^i_X(I^m G, F)` have the same
restriction to `U`. -/
public theorem extIdealPowRestrict_mk₀_comp [HasExt.{w} X.Modules]
    [HasExt.{w'} U.toScheme.Modules] {G F : X.Modules} {i n m : ℕ} (h : n ≤ m)
    (ξ : Ext.{w} (idealPowSmul I n G) F i) :
    extIdealPowRestrict.{w, w'} I U hU
        ((Ext.mk₀ (idealPowSmulMap I G h)).comp ξ (zero_add i)) =
      extIdealPowRestrict.{w, w'} I U hU ξ := by
  rw [extIdealPowRestrict, extRestrict_comp, extRestrict_mk₀, Ext.mk₀_comp_mk₀_assoc,
    inv_comp_restrict_idealPowSmulMap, extIdealPowRestrict]

/-- The canonical map `Ext^i_X(Iⁿ G, F) ⟶ Ext^i_U(G|_U, F|_U)` sends zero to zero. -/
@[simp] public theorem extIdealPowRestrict_zero [HasExt.{w} X.Modules]
    [HasExt.{w'} U.toScheme.Modules] (G F : X.Modules) (i n : ℕ) :
    extIdealPowRestrict.{w, w'} I U hU (0 : Ext.{w} (idealPowSmul I n G) F i) = 0 := by
  rw [extIdealPowRestrict, extRestrict_zero, Ext.comp_zero]

/-- The canonical map `Ext^i_X(Iⁿ G, F) ⟶ Ext^i_U(G|_U, F|_U)` is additive. -/
@[simp] public theorem extIdealPowRestrict_add [HasExt.{w} X.Modules]
    [HasExt.{w'} U.toScheme.Modules] {G F : X.Modules} {i n : ℕ}
    (ξ η : Ext.{w} (idealPowSmul I n G) F i) :
    extIdealPowRestrict.{w, w'} I U hU (ξ + η) =
      extIdealPowRestrict.{w, w'} I U hU ξ + extIdealPowRestrict.{w, w'} I U hU η := by
  rw [extIdealPowRestrict, extRestrict_add, Ext.comp_add, extIdealPowRestrict,
    extIdealPowRestrict]

end Canonical

/-! ### The geometric form of injectivity of the first display -/

section Injectivity

/-- The equivalence comparing the slice restriction with the geometric restriction is additive:
it is an equivalence, hence preserves binary coproducts, hence binary biproducts. -/
public instance overEquiv_functor_additive (U : X.Opens) :
    ((Scheme.Modules.overEquiv U).functor).Additive :=
  letI : PreservesBinaryBiproducts ((Scheme.Modules.overEquiv U).functor) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- **A morphism whose geometric restriction to `U` vanishes has vanishing slice restriction.**
This is the converse direction of
`Stacks.AlgebraicGeometry.IdealPowerColimit.restrictFunctor_map_comp_eq_of_over`, and it is what
turns the injectivity assertion of the first display into its geometric form. -/
public theorem over_eq_zero_of_restrictFunctor_map_eq_zero (U : X.Opens) {M N : X.Modules}
    {a : M ⟶ N} (ha : (Scheme.Modules.restrictFunctor U.ι).map a = 0) :
    a.over U = 0 := by
  have h := overEquivRestrictIso_naturality U a
  rw [ha, Limits.comp_zero] at h
  exact (Functor.map_eq_zero_iff _).mp
    ((Preadditive.IsIso.comp_right_eq_zero (g := (overEquivRestrictIso U N).hom) _).mp h)

/-- **The injectivity assertion of the first display of [Stacks, Tag 01YB], in terms of the
geometric restriction functor.** Let `X` be a Noetherian scheme, `I` a quasi-coherent sheaf of
ideals, `U` the complement of the closed subscheme it cuts out, `G` a coherent and `F` a
quasi-coherent `𝒪_X`-module. A morphism `ψ : Iⁿ G ⟶ F` whose restriction to `U` vanishes already
dies on `I^{n+N} G` for some `N`.

`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero_of_homRestrict_eq_zero` is the
same assertion with the restriction taken in the Grothendieck slice; the content here is only
the transport across `AlgebraicGeometry.Scheme.Modules.overEquiv`. -/
public theorem exists_comp_eq_zero_of_restrictFunctor_map_eq_zero
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) (U : X.Opens)
    (hU : U = I.support.compl) {n : ℕ} {G F : X.Modules} [G.IsCoherent] [F.IsQuasicoherent]
    {ψ : idealPowSmul I n G ⟶ F}
    (hψ : (Scheme.Modules.restrictFunctor U.ι).map ψ = 0) :
    ∃ N : ℕ, (idealPowSmulMap I G (Nat.le_add_right n N) ≫ ψ :
      idealPowSmul I (n + N) G ⟶ F) = 0 := by
  subst hU
  refine exists_comp_eq_zero_of_homRestrict_eq_zero (φ := ψ) ?_
  have hz : homRestrict I (disjoint_supportCompl_support I) ψ =
      (idealPowSmulOverIso I n G (disjoint_supportCompl_support I)).inv ≫ ψ.over _ := rfl
  rw [hz, over_eq_zero_of_restrictFunctor_map_eq_zero _ hψ, Limits.comp_zero]

end Injectivity

/-! ### The case `i = 0` -/

section DegreeZero

/-- Disjointness of an open from the support of `I`, from its description as the complement. -/
public theorem disjoint_support_of_eq_supportCompl {I : X.IdealSheafData} {U : X.Opens}
    (hU : U = I.support.compl) : Disjoint (U : Set X) (I.support : Set X) := by
  rw [hU]; exact disjoint_supportCompl_support I

/-- The canonical map sends the degree-zero class of `ψ` to that of `ψ|_U` precomposed with the
comparison. -/
private theorem extIdealPowRestrict_mk₀ [HasExt.{w} X.Modules] (I : X.IdealSheafData) (U : X.Opens)
    [HasExt.{w'} U.toScheme.Modules] (hU : Disjoint (U : Set X) (I.support : Set X))
    {G F : X.Modules} {n : ℕ}
    (ψ : idealPowSmul I n G ⟶ F) :
    extIdealPowRestrict.{w, w'} I U hU (Ext.mk₀ ψ) = Ext.mk₀
      ((restrictIdealPowSmulIso I U hU n G).inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ψ) := by
  rw [extIdealPowRestrict, extRestrict_mk₀, Ext.mk₀_comp_mk₀]


variable [AlgebraicGeometry.IsNoetherian X] [HasExt.{w} X.Modules]

/-- **Surjectivity of the canonical map in degree `0`.** Every class in
`Ext^0_U(G|_U, F|_U) = Hom_U(G|_U, F|_U)` is the restriction of a class in
`Ext^0_X(Iⁿ G, F) = Hom_X(Iⁿ G, F)` for some `n`. This is the first display of
[Stacks, Tag 01YB] read through `CategoryTheory.Abelian.Ext.mk₀`, and it is the base case of
the induction on `i` for the statement in positive degrees. -/
public theorem exists_extIdealPowRestrict_eq (I : X.IdealSheafData) (U : X.Opens)
    (hU : U = I.support.compl) [HasExt.{w'} U.toScheme.Modules]
    (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent]
    (η : Ext.{w'} ((Scheme.Modules.restrictFunctor U.ι).obj G)
      ((Scheme.Modules.restrictFunctor U.ι).obj F) 0) :
    ∃ (n : ℕ) (ξ : Ext.{w} (idealPowSmul I n G) F 0),
      extIdealPowRestrict.{w, w'} I U (disjoint_support_of_eq_supportCompl hU) ξ = η := by
  obtain ⟨φ, hφ⟩ := (Ext.mk₀_bijective _ _).2 η
  obtain ⟨n, ψ, hψ⟩ := exists_hom_idealPowerMultiple_restrict_eq I U hU G F φ
  refine ⟨n, Ext.mk₀ ψ, ?_⟩
  rw [extIdealPowRestrict_mk₀, ← hψ,
    ← restrictIdealPowSmulIso_hom _ _ (disjoint_support_of_eq_supportCompl hU),
    Iso.inv_hom_id_assoc, hφ]

/-- **Injectivity of the canonical map in degree `0`.** A class in `Ext^0_X(Iⁿ G, F)` restricting
to zero on `U` already dies in `Ext^0_X(I^{n+N} G, F)` for some `N`. Together with
`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_extIdealPowRestrict_eq` this is the
bijectivity of `colim_n Ext^0_X(Iⁿ G, F) ⟶ Ext^0_U(G|_U, F|_U)`. -/
public theorem exists_mk₀_comp_eq_zero_of_extIdealPowRestrict_eq_zero (I : X.IdealSheafData)
    (U : X.Opens) (hU : U = I.support.compl) [HasExt.{w'} U.toScheme.Modules]
    {G F : X.Modules} [G.IsCoherent] [F.IsQuasicoherent] {n : ℕ}
    (ξ : Ext.{w} (idealPowSmul I n G) F 0)
    (hξ : extIdealPowRestrict.{w, w'} I U (disjoint_support_of_eq_supportCompl hU) ξ = 0) :
    ∃ N : ℕ, (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n N))).comp ξ (zero_add 0) = 0 := by
  obtain ⟨ψ, rfl⟩ := (Ext.mk₀_bijective _ _).2 ξ
  rw [extIdealPowRestrict_mk₀, ← Ext.mk₀_zero] at hξ
  have h0 := (Ext.mk₀_bijective _ _).1 hξ
  have h1 : (Scheme.Modules.restrictFunctor U.ι).map ψ = 0 :=
    (Preadditive.IsIso.comp_left_eq_zero
      (f := (restrictIdealPowSmulIso I U
        (disjoint_support_of_eq_supportCompl hU) n G).inv) _).mp h0
  obtain ⟨N, hN⟩ := exists_comp_eq_zero_of_restrictFunctor_map_eq_zero I U hU h1
  exact ⟨N, by rw [Ext.mk₀_comp_mk₀, hN, Ext.mk₀_zero]⟩

end DegreeZero

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
