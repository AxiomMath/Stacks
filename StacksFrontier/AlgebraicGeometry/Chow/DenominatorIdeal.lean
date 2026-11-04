module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorIdeal.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.BasicOpenVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.Topology.Sheaves.Modules.Support

/-!
# The ideal sheaf of denominators of a meromorphic section

Let `X` be a scheme, let `L` be a sheaf of `𝒪_X`-modules and let `s` be a meromorphic section
of `L`, that is, a global section of `K_X(L) = K_X ⊗_{𝒪_X} L`. The *denominators* of `s` are
the sections `f` of `𝒪_X` with `f s` a regular section of `L`:
`I(V) = {f ∈ 𝒪_X(V) | f s ∈ L(V)}`. Since `L` maps to `K_X(L)` and `s` induces a morphism
`𝒪_X ⟶ K_X(L)`, this family of submodules is the fibre product of those two morphisms, and
that fibre product is the definition used here. Its two projections are the inclusion of the
denominators in `𝒪_X` and multiplication by `s`, landing in `L`.

Multiplication by `s` is injective on the denominators as soon as `s` is a regular meromorphic
section; this needs no invertibility of `L`, and no hypothesis relating the denominators to the
affine-local ideal data.

## Main definitions

* `AlgebraicGeometry.Scheme.totalQuotientRingCatSheaf` and
  `AlgebraicGeometry.Scheme.toTotalQuotientRingCatSheaf`: the sheaf of total quotient rings and
  the morphism to it from the structure sheaf, as sheaves of (not necessarily commutative)
  rings — the form in which the `SheafOfModules` API indexes modules, matching Mathlib's
  `AlgebraicGeometry.Scheme.ringCatSheaf` for the structure sheaf.
* `AlgebraicGeometry.meromorphicSectionSheafRestrict`: the sheaf `K_X(L)` of meromorphic
  sections of `L`, read as a sheaf of `𝒪_X`-modules by restriction of scalars.
* `AlgebraicGeometry.toMeromorphicSectionSheafRestrict`: the canonical morphism
  `L ⟶ K_X(L)`, the unit of extension of scalars along `𝒪_X ⟶ K_X`, written down explicitly so
  that it can be computed on sections.
* `AlgebraicGeometry.mulMeromorphicSection`: the morphism `𝒪_X ⟶ K_X(L)` given by
  multiplication by a meromorphic section `s`.
* `AlgebraicGeometry.denominatorIdealSheaf`: the sheaf of denominators of `s`, as the fibre
  product of the previous two morphisms, with projections
  `AlgebraicGeometry.denominatorIdealSheafι` to `𝒪_X` and
  `AlgebraicGeometry.denominatorIdealSheafMul` to `L`.
* `AlgebraicGeometry.denominatorIdealSheafData`: the denominators presented in the
  affine-local ideal-sheaf interface, as the largest ideal sheaf contained in the affine
  ideals cut out by the inclusion.

## Main results

* `AlgebraicGeometry.toMeromorphicSectionSheafRestrict_app` computes the morphism
  `L ⟶ K_X(L)` on sections: it sends `l` to the image of `1 ⊗ l` under sheafification.
* `AlgebraicGeometry.denominatorIdealSheaf_sections` is the denominator rule: a section `f` of
  `𝒪_X` over an open set is a denominator exactly when `f s` comes from a section of `L` there.
* `AlgebraicGeometry.mono_mulMeromorphicSection`: for a regular meromorphic section `s`,
  multiplication by `s` embeds the structure sheaf into `K_X(L)`.
* `AlgebraicGeometry.mono_denominatorIdealSheafMul`: for a regular meromorphic section `s`,
  multiplication by `s` embeds the sheaf of denominators into `L`.
* `AlgebraicGeometry.mono_denominatorIdealSheafι_of_mono`: the inclusion of the denominators
  in `𝒪_X` is injective as soon as `L ⟶ K_X(L)` is.

## Implementation notes

The morphism `L ⟶ K_X(L)` is the unit of extension of scalars, but it is *not* defined as the unit
of the library's `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`: that
adjunction is assembled with `Classical.choice` from `Stacks.PresheafOfModules.ChangeOfRings`,
whose presheaf-level adjunction is stated as a `Nonempty`, so its unit cannot be computed on
sections, and nothing elementwise about the sheaf of denominators would be provable. Instead the
same morphism is written down directly, as the image of the identity under the two explicit
hom-equivalences (`PresheafOfModules.sheafificationHomEquiv` and
`Stacks.PresheafOfModules.ChangeOfRings.unitHom`) lifted along the fully faithful forgetful
functor; `AlgebraicGeometry.toMeromorphicSectionSheafRestrict_app` is then true by `rfl`.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P1](https://stacks.math.columbia.edu/tag/02P1)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The sheaf of total quotient rings of a scheme as a sheaf of (not necessarily commutative)
rings. This is the form in which the `SheafOfModules` API indexes modules, and it is the
counterpart for `AlgebraicGeometry.totalQuotientSheaf` of `AlgebraicGeometry.Scheme.ringCatSheaf`
for the structure sheaf. -/
abbrev Scheme.totalQuotientRingCatSheaf : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj
    (_root_.AlgebraicGeometry.totalQuotientSheaf X.sheaf)

/-- The canonical morphism from the structure sheaf to the sheaf of total quotient rings, as a
morphism of sheaves of (not necessarily commutative) rings. -/
abbrev Scheme.toTotalQuotientRingCatSheaf : X.ringCatSheaf ⟶ X.totalQuotientRingCatSheaf :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).map
    (_root_.AlgebraicGeometry.toTotalQuotientSheaf X.sheaf)

variable {X}

/-- The sheaf `K_X(L)` of meromorphic sections of `L`, read as a sheaf of `𝒪_X`-modules by
restricting scalars along `𝒪_X ⟶ K_X`. The module `L` maps to it by
`AlgebraicGeometry.toMeromorphicSectionSheafRestrict`. -/
abbrev meromorphicSectionSheafRestrict (L : SheafOfModules.{u} X.ringCatSheaf) :
    SheafOfModules.{u} X.ringCatSheaf :=
  (SheafOfModules.restrictScalars X.toTotalQuotientRingCatSheaf).obj
    (meromorphicSectionSheaf X.sheaf L)

/-- The canonical morphism `L ⟶ K_X(L)` of sheaves of `𝒪_X`-modules: the unit of extension of
scalars along `𝒪_X ⟶ K_X`. It sends a section `l` of `L` to the section `1 ⊗ l` of the
sheafification of the sectionwise tensor product; see
`AlgebraicGeometry.toMeromorphicSectionSheafRestrict_app`. -/
def toMeromorphicSectionSheafRestrict (L : SheafOfModules.{u} X.ringCatSheaf) :
    L ⟶ meromorphicSectionSheafRestrict L :=
  (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).preimage
    (Stacks.PresheafOfModules.ChangeOfRings.unitHom (_root_.AlgebraicGeometry.toTotalQuotientSheaf
      X.sheaf).hom
      (PresheafOfModules.sheafificationHomEquiv (𝟙 X.totalQuotientRingCatSheaf.obj)
        (𝟙 (meromorphicSectionSheaf X.sheaf L))))

/-- Multiplication by a meromorphic section `s` of `L`, as a morphism `𝒪_X ⟶ K_X(L)` of
sheaves of `𝒪_X`-modules. On the sections over an open set it sends `f` to `f s`. -/
def mulMeromorphicSection (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    SheafOfModules.unit X.ringCatSheaf ⟶ meromorphicSectionSheafRestrict L :=
  (meromorphicSectionSheafRestrict L).unitHomEquiv.symm s

/-- The sheaf of denominators of a meromorphic section `s` of `L`: the fibre product of
multiplication by `s` and of the inclusion of `L` in the sheaf of meromorphic sections. Its
sections over an open set `V` are the pairs `(f, t)` with `f ∈ 𝒪_X(V)`, `t ∈ L(V)` and
`f s = t` in `K_X(L)(V)`, so they are exactly the denominators of `s` on `V`. -/
@[ega "IV 20.2.14"]
def denominatorIdealSheaf (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) : SheafOfModules.{u} X.ringCatSheaf :=
  pullback (mulMeromorphicSection L s) (toMeromorphicSectionSheafRestrict L)

/-- The inclusion of the sheaf of denominators of `s` in the structure sheaf. -/
def denominatorIdealSheafι (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    denominatorIdealSheaf L s ⟶ SheafOfModules.unit X.ringCatSheaf :=
  pullback.fst _ _

/-- Multiplication by `s` on the sheaf of denominators of `s`, landing in `L`. -/
def denominatorIdealSheafMul (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) : denominatorIdealSheaf L s ⟶ L :=
  pullback.snd _ _

/-- The denominators of `s` presented in the affine-local ideal-sheaf interface: the largest
ideal sheaf contained in the ideals of `Γ(X, U)`, for `U` affine, cut out by the inclusion of
the sheaf of denominators in the structure sheaf. -/
def denominatorIdealSheafData (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦
    ((denominatorIdealSheafι L s).val.app (op U.1)).hom.range

/-- The sheaf of denominators of `s`, presented as a sheaf of modules on the underlying ringed
space, which is the form its support is computed in. -/
abbrev denominatorIdealModuleSheaf (L : SheafOfModules.{u} X.ringCatSheaf)
    (s : MeromorphicSection X.sheaf L) :
    RingedSpace.ModuleSheaf.{u} X.toRingedSpace :=
  SheafOfModules.moduleSheafOfModules (denominatorIdealSheaf L s)

section Sections

variable (L : SheafOfModules.{u} X.ringCatSheaf) (s : MeromorphicSection X.sheaf L)

/-- The morphism `L ⟶ K_X(L)` sends a section `l` of `L` over an open set `V` to the image of
the pure tensor `1 ⊗ l` under the sheafification map of the sectionwise tensor product. -/
theorem toMeromorphicSectionSheafRestrict_app (V : (Opens X)ᵒᵖ) (l : L.val.obj V) :
    ((toMeromorphicSectionSheafRestrict L).val.app V).hom l =
      letI := ((_root_.AlgebraicGeometry.toTotalQuotientSheaf X.sheaf).hom.app V).hom.toAlgebra
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
              (_root_.AlgebraicGeometry.toTotalQuotientSheaf X.sheaf).hom).obj
            L.val).presheaf).app V).hom
        ((1 : (_root_.AlgebraicGeometry.totalQuotientSheaf X.sheaf).obj.obj V) ⊗ₜ l) := rfl

/-- Multiplication by a meromorphic section, as a morphism out of the structure sheaf, is
multiplication by it as a morphism out of the sheaf of total quotient rings, precomposed with
the canonical map `𝒪_X(V) → K_X(V)`. -/
theorem mulMeromorphicSection_app (V : (Opens X)ᵒᵖ)
    (f : (SheafOfModules.unit X.ringCatSheaf).val.obj V) :
    ((mulMeromorphicSection L s).val.app V).hom f =
      (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app V).hom
        ((X.toTotalQuotientRingCatSheaf.hom.app V).hom f) := rfl

/-- **The denominator rule.** A section `f` of the structure sheaf over an open set `V` is a
denominator of the meromorphic section `s` exactly when `f s` is the image of a section of `L`
over `V`; that is, exactly when `f s ∈ L(V)`. -/
theorem denominatorIdealSheaf_sections (V : Opens X)
    (f : (SheafOfModules.unit X.ringCatSheaf).val.obj (op V)) :
    (∃ d : (denominatorIdealSheaf L s).val.obj (op V),
        ((denominatorIdealSheafι L s).val.app (op V)).hom d = f) ↔
      ∃ t : L.val.obj (op V),
        ((mulMeromorphicSection L s).val.app (op V)).hom f =
          ((toMeromorphicSectionSheafRestrict L).val.app (op V)).hom t :=
  SheafOfModules.exists_pullback_fst_eq_iff _ _ (op V) f

end Sections

section Regular

variable {L : SheafOfModules.{u} X.ringCatSheaf} {s : MeromorphicSection X.sheaf L}

/-- Multiplication by a regular meromorphic section of `L` embeds the structure sheaf in the
sheaf of meromorphic sections of `L`. -/
theorem mono_mulMeromorphicSection (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Mono (mulMeromorphicSection L s) := by
  rw [SheafOfModules.mono_iff_forall_app_injective]
  intro V
  have h : Function.Injective
      ((((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app V).hom) :=
    (SheafOfModules.mono_iff_forall_app_injective _).mp hs V
  intro f g hfg
  exact toTotalQuotientSheaf_app_injective X V.unop (h hfg)

/-- Multiplication by a regular meromorphic section `s` of `L` embeds the sheaf of denominators
of `s` in `L`. -/
theorem mono_denominatorIdealSheafMul (hs : IsRegularMeromorphicSection X.sheaf L s) :
    Mono (denominatorIdealSheafMul L s) :=
  have := mono_mulMeromorphicSection hs
  pullback.snd_of_mono

/-- The inclusion of the sheaf of denominators of `s` in the structure sheaf is injective as
soon as `L ⟶ K_X(L)` is. -/
theorem mono_denominatorIdealSheafι_of_mono
    (h : Mono (toMeromorphicSectionSheafRestrict L)) :
    Mono (denominatorIdealSheafι L s) :=
  have := h
  pullback.fst_of_mono

end Regular

end AlgebraicGeometry
