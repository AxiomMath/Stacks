module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk

/-!
# Torsion-free and dual modules on an integral scheme

Let `X` be a scheme.  The *dual* of an `𝒪_X`-module `F` is the internal Hom
`SheafHom(F, 𝒪_X)`, realized here as the sheaf of modules `dualSheaf F` whose sections over
an open `U` are the morphisms `F|_U ⟶ 𝒪_U` of `𝒪_U`-modules.  A local section of `F` is
*torsion* when its germ at every point of its domain is a torsion element of the stalk, and
`F` is *torsion free* when its only torsion local sections are zero.

The main result is that on an integral scheme a module with a map into a dual module
which is injective on sections is torsion free.  Since a reflexive module is, by definition,
isomorphic to its double dual via the canonical evaluation map, this is the substance of the
first assertion of [Stacks, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2): a reflexive
module on an integral scheme is torsion free.  Neither coherence of `F` nor local
Noetherianity of `X` is used.

## Main definitions

* `dualSheaf F`: the internal-Hom dual `SheafHom(F, 𝒪_X)` of an `𝒪_X`-module.
* `dualPairing F t W x`: the value on a local section `x` of `F` of the component at an object
  `W` of the slice site over `U` of a local section `t` of `dualSheaf F` over `U`.
* `IsTorsionSection F s`: all germs of the local section `s` are torsion elements.
* `IsTorsionFree F`: every torsion local section of `F` vanishes.

## Main results

* `dualSheaf_section_eq_zero`: on an integral scheme, a local section of a dual module that is
  locally annihilated by a function with nonzero germ vanishes.  This is the statement that
  dual modules are torsion free.
* `isTorsionFree_of_injective_toDual`: a module mapping into a dual module by a map injective
  on sections is torsion free, on an integral scheme.

## Implementation notes

The internal Hom is `internalHom` of
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom`,
  whose value at `U` is
literally the module of morphisms `F|_U ⟶ 𝒪_U` over the slice site `Over U`; the sheaf
condition is `internalHom_isSheaf`.  Consequently `dualPairing` is `t.app (op W)` applied to a
section, and its interaction with the module structure and with the restriction maps of
`dualSheaf F` holds by definitional unfolding (`dualPairing_smul`, `dualPairing_map`).

Objects of the slice site over `U` are the opens contained in `U` together with their
inclusion, and `Over.left`/`Over.hom` recover that data, so no translation between `Over U`
and the order on `X.Opens` is needed.

Torsion freeness is stated for sections over every open, including the empty one, where the
torsion condition is vacuous and the unique section is zero because `𝒪_X` is a sheaf.  The
predicates do not assume quasi-coherence; they are the same propositions for a quasi-coherent
module.

The module structure on the stalk of an `𝒪_X`-module over the local ring is
`AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf`, imported from
`StacksFrontier.AlgebraicGeometry.Modules.Stalk`; it only repackages Mathlib's module structure on
the stalk of a presheaf of modules so that instance search finds it for `X.Modules`, where the
structure presheaf appears as `X.ringCatSheaf.obj` rather than as `X.presheaf ⋙ forget₂ _ _`.

## References

* [Stacks Project, Tag 0AVR](https://stacks.math.columbia.edu/tag/0AVR)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0AY2](https://stacks.math.columbia.edu/tag/0AY2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-- The dual `F^∨ = SheafHom(F, 𝒪_X)` of a module on a scheme: the internal Hom from `F` into
the structure sheaf.  Its sections over an open `U` are the morphisms `F|_U ⟶ 𝒪_U` of
`𝒪_U`-modules. -/
-- stacks attribute for 0FNV withheld: Tag 0FNV's `dualSheaf` is a def over
-- `TopCat.Sheaf CommRingCat`, not over `X.Modules`, so this is not the same statement.
-- not over `X.Modules`, so this is not the same statement.
@[ega "0 4.1.5",
  ega "0 5.4.2",
  ega "IV 18.5.1",
  sga "3 I 4.6.5.1",
  sga "3 III 0.6",
  sga "3 VIIA 4.3.3"]
public noncomputable def dualSheaf (F : X.Modules) : X.Modules where
  val := internalHom X.sheaf.obj F.val (SheafOfModules.unit (structureSheaf X.sheaf)).val
  isSheaf := internalHom_isSheaf X.sheaf.obj F.val
    (SheafOfModules.unit (structureSheaf X.sheaf)).val
    (SheafOfModules.unit (structureSheaf X.sheaf)).isSheaf

/-- The value of a local section `t` of `F^∨` over `U` on a local section `x` of `F` over the
open `W.left` lying over `U`. -/
public noncomputable def dualPairing (F : X.Modules) {U : X.Opens} (t : Γ(dualSheaf F, U))
    (W : Over U) (x : Γ(F, W.left)) : Γ(X, W.left) :=
  (t.app (op W)).hom x

/-- A section of the dual all of whose values vanish is zero. -/
public theorem eq_zero_of_dualPairing_eq_zero {F : X.Modules} {U : X.Opens}
    {t : Γ(dualSheaf F, U)}
    (h : ∀ (W : Over U) (x : Γ(F, W.left)), dualPairing F t W x = 0) : t = 0 :=
  PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext (h W.unop))

/-- The `𝒪_X(U)`-action on the sections of `F^∨` over `U` is pointwise multiplication. -/
@[simp] public theorem dualPairing_smul (F : X.Modules) {U : X.Opens} (a : Γ(X, U))
    (t : Γ(dualSheaf F, U)) (W : Over U) (x : Γ(F, W.left)) :
    dualPairing F (a • t) W x = X.presheaf.map W.hom.op a * dualPairing F t W x :=
  rfl

/-- Restricting a section of `F^∨` restricts the corresponding morphism. -/
@[simp] public theorem dualPairing_map (F : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (t : Γ(dualSheaf F, U)) (W : Over V) (x : Γ(F, W.left)) :
    dualPairing F ((dualSheaf F).presheaf.map (homOfLE hVU).op t) W x =
      dualPairing F t (Over.mk (W.hom ≫ homOfLE hVU)) x :=
  rfl

/-- A section of `F^∨` is a morphism, hence compatible with restriction in the source. -/
public theorem dualPairing_naturality (F : X.Modules) {U : X.Opens} (t : Γ(dualSheaf F, U))
    {W W' : Over U} (g : W' ⟶ W) (x : Γ(F, W.left)) :
    dualPairing F t W' (F.presheaf.map g.left.op x) =
      X.presheaf.map g.left.op (dualPairing F t W x) :=
  PresheafOfModules.naturality_apply t (op g) x

/-- A local section of a module on a scheme is *torsion* if its germ at every point of its
domain is a torsion element of the stalk, i.e. is annihilated by a nonzero element of the
local ring. -/
@[stacks 0AVR "part (1)", ega "I 7.4.1" "torsion section"]
public def IsTorsionSection (F : X.Modules) {U : X.Opens} (s : Γ(F, U)) : Prop :=
  ∀ (x : X) (hx : x ∈ U), ∃ r : X.presheaf.stalk x,
    r ≠ 0 ∧ r • F.presheaf.germ U x hx s = 0

/-- A module on a scheme is *torsion free* if every torsion local section vanishes. -/
@[stacks 0AVR "part (2)", ega "I 7.4.1" "torsion free", ega "IV 20.1.5" "quasi-coherent case"]
public def IsTorsionFree (F : X.Modules) : Prop :=
  ∀ (U : X.Opens) (s : Γ(F, U)), IsTorsionSection F s → s = 0

/-- Unfolding of torsion freeness. -/
public theorem isTorsionFree_iff (F : X.Modules) :
    IsTorsionFree F ↔ ∀ (U : X.Opens) (s : Γ(F, U)), IsTorsionSection F s → s = 0 :=
  Iff.rfl

/-- A torsion germ is witnessed by an honest function on a neighbourhood: if the germ of `s`
at `x` is torsion, then on some neighbourhood `W ⊆ U` of `x` there is a function `a` with
nonzero germ at `x` which annihilates `s|_W`. -/
public theorem exists_annihilator_of_isTorsionSection {F : X.Modules} {U : X.Opens}
    {s : Γ(F, U)} {x : X} (hx : x ∈ U)
    (h : ∃ r : X.presheaf.stalk x, r ≠ 0 ∧ r • F.presheaf.germ U x hx s = 0) :
    ∃ (W : X.Opens) (hWU : W ≤ U) (hxW : x ∈ W) (a : Γ(X, W)),
      X.presheaf.germ W x hxW a ≠ 0 ∧ a • F.presheaf.map (homOfLE hWU).op s = 0 := by
  obtain ⟨r, hr, hrs⟩ := h
  obtain ⟨V, hxV, b, hb⟩ := X.presheaf.exists_germ_eq r
  have hxW₀ : x ∈ V ⊓ U := ⟨hxV, hx⟩
  have hW₀U : (V ⊓ U : X.Opens) ≤ U := inf_le_right
  have hW₀V : (V ⊓ U : X.Opens) ≤ V := inf_le_left
  have hgerm : ∀ (W : X.Opens) (hxW : x ∈ W) (hWV : W ≤ V),
      X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hWV).op b) = r := fun W hxW hWV => by
    rw [X.presheaf.germ_res_apply, hb]
  have hzero : F.presheaf.germ (V ⊓ U) x hxW₀
      (X.presheaf.map (homOfLE hW₀V).op b •
        F.presheaf.map (homOfLE hW₀U).op s) = F.presheaf.germ (V ⊓ U) x hxW₀ 0 := by
    refine (F.val.germ_smul x (V ⊓ U) hxW₀ _ _).trans ?_
    erw [hgerm, F.presheaf.germ_res_apply, hrs, map_zero]
  obtain ⟨N, hxN, iN, iN', hN⟩ := F.presheaf.germ_eq x hxW₀ hxW₀ _ (0 : Γ(F, V ⊓ U)) hzero
  have hNzero : F.presheaf.map iN.op
      (X.presheaf.map (homOfLE hW₀V).op b •
        F.presheaf.map (homOfLE hW₀U).op s) = 0 := by
    rw [hN, map_zero]
  have hNW₀ : N ≤ V ⊓ U := leOfHom iN
  have hiN₂ : iN = homOfLE hNW₀ := Subsingleton.elim _ _
  refine ⟨N, le_trans hNW₀ hW₀U, hxN,
    X.presheaf.map (homOfLE (le_trans hNW₀ hW₀V)).op b, ?_, ?_⟩
  · rwa [hgerm]
  · rw [hiN₂, Scheme.Modules.map_smul] at hNzero
    refine Eq.trans ?_ hNzero
    congr 1
    · rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    · rw [← F.presheaf.map_comp_apply]
      rfl

/-- **Dual modules are torsion free.**  On an integral scheme, a local section `t` of a dual
module `F^∨` which is locally annihilated by a function with nonzero germ is zero. -/
public theorem dualSheaf_section_eq_zero [IsIntegral X] (F : X.Modules) {U : X.Opens}
    (t : Γ(dualSheaf F, U))
    (h : ∀ (x : X), x ∈ U → ∃ (W : X.Opens) (hWU : W ≤ U) (hxW : x ∈ W) (a : Γ(X, W)),
      X.presheaf.germ W x hxW a ≠ 0 ∧
        a • (dualSheaf F).presheaf.map (homOfLE hWU).op t = 0) :
    t = 0 := by
  apply eq_zero_of_dualPairing_eq_zero
  intro W x
  have hVU : W.left ≤ U := leOfHom W.hom
  rcases isEmpty_or_nonempty W.left with hVe | ⟨⟨y, hy⟩⟩
  · -- On the empty open the structure sheaf has a unique section.
    have h0 : W.left = ⊥ := by
      rw [← Opens.not_nonempty_iff_eq_bot]
      exact fun hne => hVe.false ⟨hne.some, hne.some_mem⟩
    have : Subsingleton Γ(X, W.left) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty h0)
    exact Subsingleton.elim _ _
  -- Choose a local annihilator around the point `y` of `W.left`.
  obtain ⟨W₀, hW₀U, hyW₀, a, hga, hat⟩ := h y (hVU hy)
  have hyV' : y ∈ W.left ⊓ W₀ := ⟨hy, hyW₀⟩
  have hV'V : (W.left ⊓ W₀ : X.Opens) ≤ W.left := inf_le_left
  have hV'W₀ : (W.left ⊓ W₀ : X.Opens) ≤ W₀ := inf_le_right
  -- Identify the value of `t|_{W₀}` on the restriction of `x` with the restriction of the
  -- value of `t` itself.
  have hpair : dualPairing F ((dualSheaf F).presheaf.map (homOfLE hW₀U).op t)
      (Over.mk (homOfLE hV'W₀)) (F.presheaf.map (homOfLE hV'V).op x) =
      X.presheaf.map (homOfLE hV'V).op (dualPairing F t W x) := by
    rw [dualPairing_map]
    exact dualPairing_naturality F t
      (Over.homMk (homOfLE hV'V) (Subsingleton.elim _ _) :
        (Over.mk ((homOfLE hV'W₀ : (W.left ⊓ W₀ : X.Opens) ⟶ W₀) ≫ homOfLE hW₀U) : Over U) ⟶ W) x
  -- Evaluate the vanishing section `a • t|_{W₀}` on the restriction of `x`.
  have key : X.presheaf.map (homOfLE hV'W₀).op a *
      X.presheaf.map (homOfLE hV'V).op (dualPairing F t W x) = 0 := by
    rw [← hpair]
    change dualPairing F (a • (dualSheaf F).presheaf.map (homOfLE hW₀U).op t)
        (Over.mk (homOfLE hV'W₀)) (F.presheaf.map (homOfLE hV'V).op x) = 0
    rw [hat]
    rfl
  -- Pass to germs at `y`.  The local ring is a domain and `a` has nonzero germ there.
  have hgerm : X.presheaf.germ (W.left ⊓ W₀) y hyV' (X.presheaf.map (homOfLE hV'W₀).op a *
      X.presheaf.map (homOfLE hV'V).op (dualPairing F t W x)) = 0 := by
    rw [key, map_zero]
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at hgerm
  have := (mul_eq_zero.mp hgerm).resolve_left hga
  exact germ_injective_of_isIntegral X y hy (by rw [this, map_zero])

/-- **Stacks, Tag 0AY2 (1), key step.**  On an integral scheme, a module with a map into
a dual module which is injective on sections is torsion free. -/
public theorem isTorsionFree_of_injective_toDual [IsIntegral X] {F G : X.Modules}
    (j : F ⟶ dualSheaf G)
    (hj : ∀ U : X.Opens, Function.Injective (Scheme.Modules.Hom.app j U)) :
    IsTorsionFree F := by
  intro U s hs
  apply hj U
  rw [map_zero]
  refine dualSheaf_section_eq_zero G (Scheme.Modules.Hom.app j U s) ?_
  intro x hx
  obtain ⟨W, hWU, hxW, a, hga, has⟩ := exists_annihilator_of_isTorsionSection hx (hs x hx)
  refine ⟨W, hWU, hxW, a, hga, ?_⟩
  have hnat : (dualSheaf G).presheaf.map (homOfLE hWU).op (Scheme.Modules.Hom.app j U s) =
      Scheme.Modules.Hom.app j W (F.presheaf.map (homOfLE hWU).op s) :=
    (PresheafOfModules.naturality_apply j.val (homOfLE hWU).op s).symm
  rw [hnat, ← Scheme.Modules.Hom.app_smul, has, map_zero]

end Stacks.AlgebraicGeometry.ReflexiveModules
