module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport

/-!
# The stalk of the unit module is the local ring

On a scheme `X` the structure sheaf, read as a sheaf of modules over itself, is
`SheafOfModules.unit X.ringCatSheaf`. Its stalk at a point is taken in `AddCommGrpCat`, because
that is the category the underlying presheaf of a sheaf of modules is valued in, whereas the
local ring `𝒪_{X, x}` is the stalk of `X.presheaf` taken in `CommRingCat`. The two are not the
same object and instance search does not pass between them, so a submodule of the one cannot be
compared with an ideal of the other until they are identified.

This file identifies them, by multiplication by the germ of the unit section: the map
`r ↦ r · 1` from the local ring to the stalk of the unit module is an isomorphism of modules
over the local ring, and it carries the germ of a section of `𝒪_X` to the germ of that same
section read in the unit module.

## Main definitions

* `Stacks.UnitStalk.unitModule`: the structure sheaf as a module over itself, at the declared
  type `AlgebraicGeometry.Scheme.Modules`.
* `Stacks.UnitStalk.one`: the germ at a point of the unit section.
* `Stacks.UnitStalk.unitStalkLinearEquiv`: the identification
  `𝒪_{X, x} ≃ₗ[𝒪_{X, x}] (unit module)_x`.

## Main results

* `Stacks.UnitStalk.unitStalkLinearEquiv_germ`: the identification carries the germ of a section
  of the structure sheaf to the germ of the same section in the unit module. Together with
  surjectivity of germs this determines it.

## Implementation notes

The identification is built in the direction `𝒪_{X, x} ⟶ (unit module)_x` on purpose: in that
direction it is multiplication by a single element, so it is manifestly linear and needs no
choice of germ representatives, whereas the other direction would have to be defined by picking
a representative of each element of the stalk. Both halves of bijectivity are then one germ
computation each: surjectivity because `g · 1 = g` on sections, and injectivity because a
section whose germ vanishes in the unit module restricts to zero on a neighbourhood, and
restriction in the unit module *is* restriction in the structure sheaf — the carriers and the
restriction maps agree definitionally, and only the ambient category differs. That definitional
agreement is recorded as `Stacks.UnitStalk.unitModule_presheaf_map` and is what lets
`TopCat.Presheaf.germ_eq` on one side feed `TopCat.Presheaf.germ_ext` on the other.

The module structure on the stalk of a sheaf of modules over the stalk of the structure sheaf is
Mathlib's `PresheafOfModules.germ_smul` instance, found because `X.ringCatSheaf.obj` is
syntactically `X.presheaf ⋙ forget₂ CommRingCat RingCat`. `unitModule` is an `abbrev` with
declared type `X.Modules` rather than a type ascription on the term, because
`AlgebraicGeometry.Scheme.Modules` is a `def` and instance search re-infers the type from the
term.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.UnitStalk

variable (X : Scheme.{u})

/-- The structure sheaf read as a sheaf of modules over itself, at the declared type
`AlgebraicGeometry.Scheme.Modules`. -/
abbrev unitModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- **Restriction in the unit module is restriction in the structure sheaf.** The two presheaves
have the same sections and the same restriction maps; only the category they are valued in
differs. -/
lemma unitModule_presheaf_map {U V : Opens X} (i : V ⟶ U) (g : Γ(X, U)) :
    (unitModule X).presheaf.map i.op g = X.presheaf.map i.op g := rfl

/-- The germ at `x` of the unit section of the structure sheaf, read in the unit module. -/
def one (x : X) : (unitModule X).presheaf.stalk x :=
  (unitModule X).presheaf.germ ⊤ x (Opens.mem_top x) (1 : Γ(X, ⊤))

/-- The germ of the unit section over any neighbourhood is the germ of the global unit
section. -/
lemma germ_one (x : X) (U : Opens X) (hx : x ∈ U) :
    (unitModule X).presheaf.germ U x hx (1 : Γ(X, U)) = one X x :=
  calc (unitModule X).presheaf.germ U x hx (1 : Γ(X, U))
      = (unitModule X).presheaf.germ U x hx
          ((unitModule X).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(X, ⊤))) :=
        congrArg _ (map_one (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom).symm
    _ = one X x :=
        (unitModule X).presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hx (1 : Γ(X, ⊤))

/-- **Multiplication by the germ of the unit section**, from the local ring to the stalk of the
unit module. -/
def toUnitStalk (x : X) :
    X.presheaf.stalk x →ₗ[X.presheaf.stalk x] (unitModule X).presheaf.stalk x where
  toFun r := r • one X x
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _

/-- **Multiplication by the germ of the unit section carries germs to germs.** -/
lemma toUnitStalk_germ (x : X) (U : Opens X) (hx : x ∈ U) (g : Γ(X, U)) :
    toUnitStalk X x (X.presheaf.germ U x hx g) =
      (unitModule X).presheaf.germ U x hx g := by
  have hsmul : (unitModule X).presheaf.germ U x hx (g • (1 : Γ(X, U))) =
      X.presheaf.germ U x hx g • (unitModule X).presheaf.germ U x hx (1 : Γ(X, U)) :=
    PresheafOfModules.germ_smul (R := X.presheaf) (unitModule X).val x U hx g (1 : Γ(X, U))
  show X.presheaf.germ U x hx g • one X x = _
  rw [← germ_one X x U hx, ← hsmul]
  exact congrArg (ConcreteCategory.hom ((unitModule X).presheaf.germ U x hx)) (mul_one g)

/-- Every element of the stalk of the unit module is a multiple of the germ of the unit
section: it is the germ of some section `g`, and `g · 1 = g`. -/
lemma surjective_toUnitStalk (x : X) : Function.Surjective (toUnitStalk X x) := by
  intro a
  obtain ⟨U, hx, g, hg⟩ := (unitModule X).presheaf.exists_germ_eq a
  exact ⟨X.presheaf.germ U x hx g, (toUnitStalk_germ X x U hx g).trans hg⟩

/-- Multiplication by the germ of the unit section is injective: two sections of the structure
sheaf with the same germ in the unit module agree on a neighbourhood, and restriction in the
unit module is restriction in the structure sheaf. -/
lemma injective_toUnitStalk (x : X) : Function.Injective (toUnitStalk X x) := by
  intro r r' h
  obtain ⟨U, hxU, r₀, hr₀⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hxV, r₁, hr₁⟩ := X.presheaf.exists_germ_eq r'
  rw [← hr₀, ← hr₁, toUnitStalk_germ, toUnitStalk_germ] at h
  obtain ⟨W, hxW, i, j, heq⟩ := (unitModule X).presheaf.germ_eq x hxU hxV r₀ r₁ h
  rw [← hr₀, ← hr₁]
  exact X.presheaf.germ_ext W hxW i j heq

/-- **The stalk of the unit module is the local ring**, by multiplication by the germ of the
unit section. This is the identification that lets a submodule of the stalk of the unit module
be compared with an ideal of the local ring. -/
def unitStalkLinearEquiv (x : X) :
    X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] (unitModule X).presheaf.stalk x :=
  LinearEquiv.ofBijective (toUnitStalk X x)
    ⟨injective_toUnitStalk X x, surjective_toUnitStalk X x⟩

/-- The identification carries the germ of a section of the structure sheaf to the germ of the
same section read in the unit module. -/
lemma unitStalkLinearEquiv_germ (x : X) (U : Opens X) (hx : x ∈ U) (g : Γ(X, U)) :
    unitStalkLinearEquiv X x (X.presheaf.germ U x hx g) =
      (unitModule X).presheaf.germ U x hx g :=
  toUnitStalk_germ X x U hx g

end Stacks.UnitStalk

end
