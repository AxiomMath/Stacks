module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.LinearCombination
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Problem Description

Stacks project Tag 04BP (Lemma 18.33.9, "Modules on Sites").

Throughout, `C` is a site (a category equipped with a Grothendieck topology `J`) and
`φ : O₁ → O₂` is a homomorphism of sheaves of (commutative) rings on `C`. All maps
below are maps of sheaves on `C`, i.e. they are given on local sections compatibly
with restriction.

We are given a square-zero extension: a short exact sequence of sheaves of
`O₁`-modules
  `0 → F → A →[π] O₂ → 0`,
where `A` is a sheaf of `O₁`-algebras, `π` is a surjective homomorphism of sheaves of
`O₁`-algebras, `F = Ker(π)` is a square-zero ideal of `A`, and `F` carries the
induced `O₂`-module structure (Definition 2).

The lemma states: fixing a section `s : O₂ → A` of `π` (a homomorphism of sheaves of
`O₁`-algebras with `π ∘ s = id`), the map `D ↦ s + D` is a bijection from the set of
`φ`-derivations `Der_{O₁}(O₂, F)` to the set of sections of `π`, with inverse
`s' ↦ s' - s`. In particular the set of sections is a torsor under
`Der_{O₁}(O₂, F)`.

## Formalization approach (sheaf level)

We model sheaves of commutative rings on the site `C` as functors `Cᵒᵖ ⥤ CommRingCat`
(presheaves of commutative rings) together with the sheaf condition for the
underlying presheaf of types (`CategoryTheory.Presheaf.IsSheaf J`). Morphisms of
sheaves of rings are natural transformations: the naturality square is *exactly* the
compatibility with restriction maps. This keeps the site `C`, the restriction maps,
and the sheaf condition genuinely present in the formalization, and every map below
is a map of sheaves (a natural transformation), not merely a ring homomorphism of a
single ring of global sections.

* A *sheaf of `O₁`-algebras* is a sheaf of commutative rings `A` together with a
  structure morphism `η : O₁ ⟶ A` of sheaves of rings. `O₂` is a sheaf of
  `O₁`-algebras via `φ`. A *homomorphism of sheaves of `O₁`-algebras* `g : X ⟶ Y` is
  a morphism of sheaves of rings with `ηX ≫ g = ηY` (equivalently: a natural
  transformation that is objectwise a ring hom and commutes with the structure maps
  from `O₁`).
* `F = Ker(π)` is taken objectwise: `F.obj U = RingHom.ker (π.app U)`, an ideal of
  `A.obj U`. The restriction maps of `A` carry `F` into itself (naturality of `π`).
* The `O₂`-module structure on `F` (Definition 2) is recorded as part of the data,
  *characterized* by its defining property `h • τ = ã * τ` for any local lift `ã` of
  `h` along `π` (the lift may only exist locally, which is exactly why this is the
  appropriate sheaf-level formulation), together with restriction-compatibility.
* A `φ`-derivation `D : O₂ → F` (Stacks Tag 04BK / Definition 18.33.1) is given by
  objectwise additive maps `D U : O₂.obj U → F.obj U` that satisfy the Leibniz rule
  (with the `O₂`-action of Definition 2), annihilate the image of `φ`, and are
  compatible with restriction.
-/

namespace Stacks.Sites.SquareZeroExtension

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The sheaf condition for a presheaf of commutative rings `O`: its underlying
presheaf of types is a sheaf for the topology `J`. -/
def IsSheafOfRings (O : Cᵒᵖ ⥤ CommRingCat.{u}) : Prop :=
  Presheaf.IsSheaf J (O ⋙ forget CommRingCat)

/-! ## The square-zero extension as a sheaf-level datum -/

/-- The setup of Tag 04BP, as sheaves on the site `(C, J)`.

It bundles:
* sheaves of commutative rings `O₁`, `O₂`, `A` (as functors `Cᵒᵖ ⥤ CommRingCat`,
  each satisfying the sheaf condition for `J`);
* the homomorphism of sheaves of rings `φ : O₁ ⟶ O₂`;
* structure morphisms `η₂ : O₁ ⟶ O₂` and `ηA : O₁ ⟶ A` making `O₂` and `A` sheaves of
  `O₁`-algebras, with `η₂ = φ`;
* a surjective homomorphism of sheaves of `O₁`-algebras `π : A ⟶ O₂`
  (`π` is `O₁`-linear via `ηA ≫ π = φ`, and locally surjective, i.e. its image is
  `J`-locally everything — encoded by the existence of local lifts `Lift`);
* the square-zero condition on `F = Ker(π)`;
* the induced `O₂`-module structure on `F` (Definition 2), recorded objectwise via a
  scalar action `act` characterized by `act h τ = ã * τ` for any local lift `ã` of `h`,
  and compatible with restriction.

All naturality squares (`φ.naturality`, `π.naturality`, ...) are the
restriction-compatibility conditions for the corresponding maps of sheaves. -/
@[ega "III 5.4.6"]
structure SqZeroExt where
  /-- The sheaf of commutative rings `O₁`. -/
  O₁ : Cᵒᵖ ⥤ CommRingCat.{u}
  /-- The sheaf of commutative rings `O₂`. -/
  O₂ : Cᵒᵖ ⥤ CommRingCat.{u}
  /-- The sheaf of commutative rings `A`. -/
  A : Cᵒᵖ ⥤ CommRingCat.{u}
  isSheaf_O₁ : IsSheafOfRings J O₁
  isSheaf_O₂ : IsSheafOfRings J O₂
  isSheaf_A : IsSheafOfRings J A
  /-- The homomorphism of sheaves of rings `φ : O₁ ⟶ O₂`. -/
  φ : O₁ ⟶ O₂
  /-- The structure morphism `ηA : O₁ ⟶ A` making `A` a sheaf of `O₁`-algebras. -/
  ηA : O₁ ⟶ A
  /-- The surjection `π : A ⟶ O₂`, a homomorphism of sheaves of rings. -/
  π : A ⟶ O₂
  /-- `π` is `O₁`-linear, i.e. commutes with the structure maps: `ηA ≫ π = φ`.
  This says `π` is a homomorphism of sheaves of `O₁`-algebras. -/
  ηA_comp_π : ηA ≫ π = φ
  /-- `π` is surjective as a map of sheaves: for every object `U` and every local
  section `h : O₂.obj (op U)`, there is a covering sieve `S ∈ J U` such that on each
  member `f : V ⟶ U` of the covering the restriction of `h` lifts along `π`, i.e.
  there is `a : A.obj (op V)` with `π a = h|_V`.  (This is the sheaf-level meaning of
  surjectivity: lifts exist locally, not necessarily globally — a `J`-local condition,
  not objectwise function surjectivity.) -/
  locally_surjective : ∀ (U : C) (h : O₂.obj (Opposite.op U)),
    ∃ S ∈ J U, ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
      ∃ a : A.obj (Opposite.op V),
        (π.app (Opposite.op V)).hom a = (O₂.map (Quiver.Hom.op f)).hom h
  /-- The square-zero condition: for all `U` and all `x, y` in `F.obj U = Ker(π.app U)`,
  the product `x * y` vanishes in `A.obj U`. -/
  sq_zero : ∀ (U : Cᵒᵖ) (x y : A.obj U),
    (π.app U).hom x = 0 → (π.app U).hom y = 0 → x * y = 0
  /-- Definition 2 (the `O₂`-module structure on `F`), recorded objectwise: for each
  object `U`, a scalar action of `O₂.obj U` on the ideal `F.obj U = Ker(π.app U)`.
  We store it as a map sending `h : O₂.obj U` and `τ ∈ F.obj U` to an element of `A`
  (in the ideal). -/
  act : ∀ (U : Cᵒᵖ) (_ : O₂.obj U) (_ : A.obj U), A.obj U
  /-- The action lands in `F = Ker(π)`. -/
  act_mem : ∀ (U : Cᵒᵖ) (h : O₂.obj U) (τ : A.obj U),
    (π.app U).hom τ = 0 → (π.app U).hom (act U h τ) = 0
  /-- Definition 2, characterizing property: `h • τ = ã * τ` in `A` for *any* local
  lift `ã` of `h` along `π` (`π ã = h`). Well-definedness (independence of the lift)
  is a consequence of the square-zero condition, but we record the characterization
  directly since lifts need only exist locally. -/
  act_spec : ∀ (U : Cᵒᵖ) (h : O₂.obj U) (τ : A.obj U), (π.app U).hom τ = 0 →
    ∀ a : A.obj U, (π.app U).hom a = h → act U h τ = a * τ
  /-- Restriction-compatibility (naturality) of the action: the restriction maps of
  `A` and `O₂` intertwine the `O₂`-action on `F`. -/
  act_naturality : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (h : O₂.obj U) (τ : A.obj U),
    (A.map f).hom (act U h τ) = act V ((O₂.map f).hom h) ((A.map f).hom τ)

variable {J}
variable (E : SqZeroExt J)

/-! ## Basic consequences -/

/-- The ideal `F.obj U = Ker(π.app U)` of `A.obj U`. -/
def SqZeroExt.F (U : Cᵒᵖ) : Ideal (E.A.obj U) := RingHom.ker (E.π.app U).hom

/-- A local section `a` of `A` lies in `F.obj U` iff `π a = 0`. -/
@[simp] theorem SqZeroExt.mem_F_iff {U : Cᵒᵖ} {a : E.A.obj U} :
    a ∈ E.F U ↔ (E.π.app U).hom a = 0 := RingHom.mem_ker

/-- The restriction maps of `A` carry `F` into `F` (naturality of `π`): this is the
statement that `F = Ker(π)` is a *sub-sheaf* of `A`, with restriction maps induced
from those of `A`. -/
theorem SqZeroExt.map_mem_F {U V : Cᵒᵖ} (f : U ⟶ V) {a : E.A.obj U} (ha : a ∈ E.F U) :
    (E.A.map f).hom a ∈ E.F V := by
  rw [SqZeroExt.mem_F_iff] at ha ⊢
  have hn : (E.π.app V).hom ((E.A.map f).hom a)
      = (E.O₂.map f).hom ((E.π.app U).hom a) := by
    have h := E.π.naturality f
    have h := congrArg (fun g => (CommRingCat.Hom.hom g) a) h
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h ⊢
    exact h
  rw [hn, ha, map_zero]

/-- π applied to a structure-map section equals φ, pointwise (`O₁`-linearity of π). -/
theorem SqZeroExt.π_ηA {U : Cᵒᵖ} (g : E.O₁.obj U) :
    (E.π.app U).hom ((E.ηA.app U).hom g) = (E.φ.app U).hom g := by
  simpa using congrArg (fun t : E.O₁ ⟶ E.O₂ => (t.app U).hom g) E.ηA_comp_π

/-- Definition 2 well-definedness, restated as a lemma (a consequence of square-zero):
if `a` and `b` are two lifts of the same `h`, then `a * τ = b * τ` for `τ ∈ F`. -/
theorem SqZeroExt.lift_mul_eq {U : Cᵒᵖ} {a b : E.A.obj U}
    (h : (E.π.app U).hom a = (E.π.app U).hom b) {τ : E.A.obj U} (hτ : τ ∈ E.F U) :
    a * τ = b * τ := by
  have hmem : (a - b) ∈ E.F U := by
    rw [SqZeroExt.mem_F_iff, map_sub, h, sub_self]
  rw [SqZeroExt.mem_F_iff] at hmem hτ
  linear_combination E.sq_zero U (a - b) τ hmem hτ

/-! ## Definition 3: sections of `π` -/

/-- Definition 3: a *section of `π`* is a homomorphism of sheaves of `O₁`-algebras
`s : O₂ ⟶ A` (a morphism of sheaves of rings commuting with the structure maps from
`O₁`, i.e. `φ ≫ s = ηA`) such that `s ≫ π = 𝟙 O₂`, i.e. `π ∘ s = id`.

As a natural transformation, `s` is automatically compatible with restriction. -/
structure SqZeroExt.Section where
  /-- The underlying morphism of sheaves of rings `s : O₂ ⟶ A`. -/
  hom : E.O₂ ⟶ E.A
  /-- `s` commutes with the structure maps from `O₁`: `φ ≫ s = ηA`. -/
  comp_struct : E.φ ≫ hom = E.ηA
  /-- `π ∘ s = id`. -/
  comp_π : hom ≫ E.π = 𝟙 E.O₂

namespace SqZeroExt.Section

variable {E}

/-- A section `s`, applied to a local section `a : O₂.obj U`. -/
def app (s : E.Section) (U : Cᵒᵖ) (a : E.O₂.obj U) : E.A.obj U := (s.hom.app U).hom a

/-- `π (s a) = a` for a section `s` of `π` and a local section `a` of `O₂`. -/
theorem comp_π_app (s : E.Section) (U : Cᵒᵖ) (a : E.O₂.obj U) :
    (E.π.app U).hom (s.app U a) = a := by
  simpa [SqZeroExt.Section.app] using
    congrArg (fun t : E.O₂ ⟶ E.O₂ => (t.app U).hom a) s.comp_π

/-- `s (φ g) = ηA g` for a section `s` of `π` and a local section `g` of `O₁`. -/
theorem comp_struct_app (s : E.Section) (U : Cᵒᵖ) (g : E.O₁.obj U) :
    (s.hom.app U).hom ((E.φ.app U).hom g) = (E.ηA.app U).hom g := by
  simpa only [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] using congrArg (fun t : E.O₁ ⟶ E.A => (t.app U).hom g) s.comp_struct

/-- A section `s` of `π` commutes with the restriction maps. -/
theorem hom_naturality_apply (s : E.Section) {U V : Cᵒᵖ} (g : U ⟶ V) (a : E.O₂.obj U) :
    (s.hom.app V).hom ((E.O₂.map g).hom a) = (E.A.map g).hom ((s.hom.app U).hom a) := by
  simp

end SqZeroExt.Section

/-- The `O₂`-action on `F` is multiplication by `s h`, for any section `s` of `π`. -/
theorem SqZeroExt.act_eq_mul (s : E.Section) {U : Cᵒᵖ} (h : E.O₂.obj U) {τ : E.A.obj U}
    (hτ : τ ∈ E.F U) : E.act U h τ = s.app U h * τ :=
  E.act_spec U h τ (E.mem_F_iff.mp hτ) _ (s.comp_π_app U h)

/-- Leibniz expansion `(s a + x) * (s b + y)` for `x, y ∈ F`, using that `F` is square-zero. -/
private theorem SqZeroExt.add_mul_add_act (s : E.Section) {U : Cᵒᵖ} (a b : E.O₂.obj U)
    {x y : E.A.obj U} (hx : x ∈ E.F U) (hy : y ∈ E.F U) :
    (s.app U a + x) * (s.app U b + y) =
      s.app U a * s.app U b + (E.act U a y + E.act U b x) := by
  rw [E.act_eq_mul s a hy, E.act_eq_mul s b hx]
  linear_combination E.sq_zero U x y (E.mem_F_iff.mp hx) (E.mem_F_iff.mp hy)

/-! ## Definition 4: `φ`-derivations -/

/-- Definition 4: a *`φ`-derivation* (`O₁`-derivation) `D : O₂ → F` is a map of
sheaves of sets given objectwise by additive maps `D U : O₂.obj U → F.obj U` that
1. are additive;
2. annihilate the image of `φ`: `D(φ g) = 0`;
3. satisfy the Leibniz rule `D(ab) = a·D(b) + b·D(a)` (with the `O₂`-action of
   Definition 2, recorded in `E.act`);
and are compatible with restriction (naturality).

We store the values as elements of `A` (in the ideal `F`), with `toFun_mem`
witnessing that they lie in `F`. -/
structure SqZeroExt.Derivation where
  /-- The objectwise function `O₂.obj U → A.obj U`. -/
  toFun : ∀ (U : Cᵒᵖ), E.O₂.obj U → E.A.obj U
  /-- Each value lies in `F = Ker(π)`. -/
  toFun_mem : ∀ (U : Cᵒᵖ) (a : E.O₂.obj U), toFun U a ∈ E.F U
  /-- Additivity. -/
  map_add : ∀ (U : Cᵒᵖ) (a b : E.O₂.obj U), toFun U (a + b) = toFun U a + toFun U b
  /-- Annihilation of the image of `φ`. -/
  map_φ : ∀ (U : Cᵒᵖ) (g : E.O₁.obj U), toFun U ((E.φ.app U).hom g) = 0
  /-- Leibniz rule, using the `O₂`-action `E.act` of Definition 2. -/
  leibniz : ∀ (U : Cᵒᵖ) (a b : E.O₂.obj U),
    toFun U (a * b) = E.act U a (toFun U b) + E.act U b (toFun U a)
  /-- Restriction-compatibility (naturality): `D` commutes with restriction maps. -/
  naturality : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (a : E.O₂.obj U),
    (E.A.map f).hom (toFun U a) = toFun V ((E.O₂.map f).hom a)

/-! ## Definition 5: the maps `s + D` and `s' - s` -/

/-- The map `s + D : O₂ → A`, `(s + D)(a) := s(a) + D(a)` (objectwise), using the
inclusion `F ↪ A` to regard `D(a)` as a local section of `A`.  A priori this is just
an objectwise function; Statement 1 asserts it underlies a section of `π`. -/
def SqZeroExt.addDeriv (s : E.Section) (D : E.Derivation) (U : Cᵒᵖ) (a : E.O₂.obj U) :
    E.A.obj U :=
  s.app U a + D.toFun U a

/-- The map `s' - s : O₂ → F`, `(s' - s)(a) := s'(a) - s(a)` (objectwise). Since
`π(s'(a) - s(a)) = a - a = 0`, this lands in `F = Ker(π)`. -/
def SqZeroExt.subSection (s s' : E.Section) (U : Cᵒᵖ) (a : E.O₂.obj U) : E.A.obj U :=
  s'.app U a - s.app U a

/-- For sections `s`, `s'` of `π`, each value `s'(a) - s(a)` lies in `F = Ker(π)`. -/
theorem SqZeroExt.subSection_mem (s s' : E.Section) (U : Cᵒᵖ) (a : E.O₂.obj U) :
    E.subSection s s' U a ∈ E.F U := by
  rw [SqZeroExt.mem_F_iff, SqZeroExt.subSection, map_sub,
    s'.comp_π_app U a, s.comp_π_app U a, sub_self]

/-- `D 1 = 0`: indeed `1 = φ 1` and `D` annihilates the image of `φ`. -/
theorem SqZeroExt.Derivation.map_one (D : E.Derivation) (U : Cᵒᵖ) :
    D.toFun U 1 = 0 := by
  simpa using D.map_φ U 1

/-! ## Main Statement(s) -/

/-- **Statement 1.** For every `φ`-derivation `D`, the map `s + D : O₂ → A`
(Definition 5) is again a section of `π`: it underlies a homomorphism of sheaves of
`O₁`-algebras with `π ∘ (s + D) = id`.

We express this by producing a `Section` whose objectwise function is `s + D`. -/
@[stacks 04BP, ega "0 20.1.3" "action of Der"]
theorem statement₁ (s : E.Section) (D : E.Derivation) :
    ∃ s' : E.Section, ∀ (U : Cᵒᵖ) (a : E.O₂.obj U), s'.app U a = E.addDeriv s D U a := by
  have hD U a : (E.π.app U).hom (D.toFun U a) = 0 := E.mem_F_iff.mp (D.toFun_mem U a)
  let hom : E.O₂ ⟶ E.A :=
    { app U := CommRingCat.ofHom
        { toFun := E.addDeriv s D U
          map_one' := by simp [SqZeroExt.addDeriv, SqZeroExt.Section.app, D.map_one]
          map_mul' a b := by
            simp only [SqZeroExt.addDeriv, D.leibniz]
            rw [E.add_mul_add_act s a b (D.toFun_mem U a) (D.toFun_mem U b)]
            simp only [SqZeroExt.Section.app, map_mul]
          map_zero' := by
            simpa [SqZeroExt.addDeriv, SqZeroExt.Section.app] using D.map_add U 0 0
          map_add' a b := by
            simp only [SqZeroExt.addDeriv, SqZeroExt.Section.app, map_add, D.map_add]
            ring }
      naturality U V g := by
        ext a
        change E.addDeriv s D V ((E.O₂.map g).hom a) = (E.A.map g).hom (E.addDeriv s D U a)
        simp only [SqZeroExt.addDeriv, SqZeroExt.Section.app, map_add,
          s.hom_naturality_apply, D.naturality] }
  refine ⟨⟨hom, ?_, ?_⟩, fun _ _ => rfl⟩
  · ext U g
    change E.addDeriv s D U ((E.φ.app U).hom g) = (E.ηA.app U).hom g
    simp only [SqZeroExt.addDeriv, D.map_φ, add_zero]
    exact s.comp_struct_app U g
  · ext U a
    change (E.π.app U).hom (E.addDeriv s D U a) = a
    simp only [SqZeroExt.addDeriv, map_add, hD, s.comp_π_app, add_zero]

/-- **Statement 2 (existence).** For every section `s'` of `π`, the map
`D := s' - s : O₂ → F` (Definition 5) is a `φ`-derivation.

We express this by producing a `Derivation` whose objectwise function is `s' - s`. -/
theorem statement₂_exists (s s' : E.Section) :
    ∃ D : E.Derivation, ∀ (U : Cᵒᵖ) (a : E.O₂.obj U), D.toFun U a = E.subSection s s' U a := by
  refine ⟨{ toFun := E.subSection s s'
            toFun_mem := E.subSection_mem s s'
            map_add := fun U a b => ?_
            map_φ := fun U g => ?_
            leibniz := fun U a b => ?_
            naturality := fun U V g a => ?_ }, fun _ _ => rfl⟩
  · simp only [SqZeroExt.subSection, SqZeroExt.Section.app, map_add]
    ring
  · simp only [SqZeroExt.subSection, SqZeroExt.Section.app, s.comp_struct_app,
      s'.comp_struct_app, sub_self]
  · have h := E.add_mul_add_act s a b (E.subSection_mem s s' U a) (E.subSection_mem s s' U b)
    simp only [SqZeroExt.subSection, SqZeroExt.Section.app, map_mul, add_sub_cancel] at h ⊢
    linear_combination h
  · simp only [SqZeroExt.subSection, SqZeroExt.Section.app, map_sub,
      s.hom_naturality_apply, s'.hom_naturality_apply]

/-- Two sections are equal iff they agree on all local sections. -/
theorem SqZeroExt.Section.ext {s₁ s₂ : E.Section}
    (h : ∀ (U : Cᵒᵖ) (a : E.O₂.obj U), s₁.app U a = s₂.app U a) : s₁ = s₂ := by
  obtain ⟨hom₁⟩ := s₁
  obtain ⟨hom₂⟩ := s₂
  obtain rfl : hom₁ = hom₂ := by
    ext U a
    exact h U a
  rfl

/-- Two derivations are equal iff they agree on all local sections. -/
theorem SqZeroExt.Derivation.ext {D₁ D₂ : E.Derivation}
    (h : ∀ (U : Cᵒᵖ) (a : E.O₂.obj U), D₁.toFun U a = D₂.toFun U a) : D₁ = D₂ := by
  obtain ⟨t₁⟩ := D₁
  obtain ⟨t₂⟩ := D₂
  obtain rfl : t₁ = t₂ := funext fun U => funext (h U)
  rfl

/-- **Statement 2 (the bijection / torsor).** Fixing a section `s`, the map
`D ↦ s + D` is a bijection from `φ`-derivations to sections of `π`, with inverse
`s' ↦ s' - s`.  We package the bijection as an explicit `Equiv` between
`Der_{O₁}(O₂, F)` and the sections of `π`, characterized on underlying objectwise
functions by `s + D` and `s' - s`.  This exhibits the set of sections of `π` as a
torsor under (an affine space over) `Der_{O₁}(O₂, F)`. -/
@[stacks 04BP, ega "0 20.1.3" "section case (u = id)"]
theorem statement₂_bijection (s : E.Section) :
    ∃ e : E.Derivation ≃ E.Section,
      (∀ (D : E.Derivation) (U : Cᵒᵖ) (a : E.O₂.obj U),
        (e D).app U a = E.addDeriv s D U a) ∧
      (∀ (s' : E.Section) (U : Cᵒᵖ) (a : E.O₂.obj U),
        (e.symm s').toFun U a = E.subSection s s' U a) := by
  have toFun_spec := fun D => (statement₁ E s D).choose_spec
  have invFun_spec := fun s' => (statement₂_exists E s s').choose_spec
  refine ⟨⟨fun D => (statement₁ E s D).choose, fun s' => (statement₂_exists E s s').choose,
    fun D => ?_, fun s' => ?_⟩, toFun_spec, invFun_spec⟩
  · refine SqZeroExt.Derivation.ext E fun U a => ?_
    rw [invFun_spec, SqZeroExt.subSection, toFun_spec, SqZeroExt.addDeriv]
    ring
  · refine SqZeroExt.Section.ext E fun U a => ?_
    rw [toFun_spec, SqZeroExt.addDeriv, invFun_spec, SqZeroExt.subSection]
    ring

end Stacks.Sites.SquareZeroExtension
