module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.IntegralCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RestrictionOfScalars

/-!
# Forgetting to integral coefficients through restriction of coefficients

Restricting the coefficients of an étale module sheaf along `φ : Λ₁ → Λ₂` and then forgetting to
integral coefficients is forgetting to integral coefficients directly -- but only up to a
canonical isomorphism, never on the nose.

## Main results

* `Stacks.EtaleCohomology.intCastRingHom_eq_comp`
* `Stacks.EtaleCohomology.etaleRestrictForgetToIntIso`

## Implementation notes

The mathematical content is one line, and it reads as a triviality: there is exactly ONE ring map
`ℤ → Λ₂` (`RingHom.ext_int`), so the one factoring through `Λ₁` is the canonical one.  Everything
else here is the work of saying that in a form Lean accepts.

**This is not a `rfl`, for a reason that recurs throughout this development.** The two composites
have literally the same underlying sheaves; they differ only in which `Module ℤ` structure sits on
the sections -- `Λ₁` acting through `φ` and then restricted, versus `ℤ` acting directly.  Those
are *equal*, `Module ℤ M` being a subsingleton, and that is precisely the situation in which no
rewriting works: `exact` and `show` fail on the mismatch, `convert` bottoms out in `HEq` with the
carriers provably equal, and `rw [Subsingleton.elim ..]` cannot place its equation because the
goal's instance is an already-elaborated term rather than the literal `inferInstance`.  What gets
through is an argument that never mentions the instance, and Mathlib supplies exactly that:
`ModuleCat.restrictScalarsComp'` is built from an `AddEquiv` which is `rfl` on the carrier with
scalar compatibility supplied by hand, and its components satisfy `hom x = x` by `rfl`.

The *lifting* to sheaves, by contrast, is definitional: `sheafCompose J (F ⋙ G)` and
`sheafCompose J F ⋙ sheafCompose J G` are equal by `rfl` here, so the difficulty is confined to the
`Module ℤ` layer and does not propagate.  The iso is therefore assembled componentwise, each
component being the whiskered module-level iso carried across the fully faithful
`CategoryTheory.sheafToPresheaf`.

**Five reasons reusable-looking lemmas do not apply here**, collected because together
they are a short checklist:

1. *Smallness.*  The statement assumes `[SmallCategory C]`; the small étale site is large and only
   essentially small, so it is excluded outright.
2. *Collapsed universes.*  The statement pins the site's object and hom universes to one another,
   or the coefficient universe to the site's (`{C : Type u} [Category.{u} C]`,
   `RingedSite.{u, u, u}`), while étale sheaves live at a module universe strictly above the
   site's.  For 1 and 2 the collapse is in the *specialisation*: the generic form it was
   specialised from is usually public and at independent universes, often in the same file, so
   look there before restating anything.
3. *An over-strong hypothesis in an otherwise general lemma.*  `Type*`-generic, no universe
   coupling, and still inapplicable because it carries a hypothesis its proof barely needs --
   `Dualizing.isIso_of_isIso_mapDerivedCategory_map` requires `[F.Full]` and uses fullness at
   exactly one step.  This is the mode that fools someone who has learned 1 and 2, because the
   check is not "are the universes free" but "does this hypothesis hold for *my* functor".
4. *"On the nose" asserted in prose.*  That two functors agree definitionally is a claim about
   syntax; the only check distinguishing it from "provably equal" is to write `rfl` and build.
   Between two Mathlib spellings of one `ℤ`-linear structure, assume an instance path.
5. *Blaming the content for a lifting failure.*  When a lifted identity will not close, probe
   whether the lifting is definitional before assuming the content is at fault.  Here the lifting
   was free and the content was not -- the reverse of the guess.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)

/-- **There is only one ring map `ℤ → Λ₂`**, so the one factoring through `Λ₁` is the canonical
one.  This reads as a triviality and is the entire mathematical content of the identification
below. -/
theorem intCastRingHom_eq_comp :
    (Int.castRingHom Λ₂) = φ.comp (Int.castRingHom Λ₁) :=
  RingHom.ext_int _ _

/-- Restricting `Λ₂`-modules to `ℤ` is restricting along `φ` and then to `ℤ`, at the level of
module categories.  Identity on elements, which is what makes it usable at all. -/
abbrev restrictScalarsIntComp :
    ModuleCat.restrictScalars.{max (u + 1) r, 0, r} (Int.castRingHom Λ₂) ≅
      ModuleCat.restrictScalars.{max (u + 1) r} φ ⋙
        ModuleCat.restrictScalars.{max (u + 1) r, 0, r} (Int.castRingHom Λ₁) :=
  ModuleCat.restrictScalarsComp'.{max (u + 1) r} (Int.castRingHom Λ₁) φ (Int.castRingHom Λ₂)
    (intCastRingHom_eq_comp φ)

/-- **Forgetting an étale module sheaf to integral coefficients through restriction of
coefficients is forgetting to integral coefficients.**  Canonically isomorphic, not equal: see
the module docstring. -/
def etaleRestrictForgetToIntIso (X : Scheme.{u}) :
    etaleModuleForgetToInt.{u, r} Λ₂ X ≅
      etaleModuleRestrictScalarsUniv.{u, r} φ X ⋙ etaleModuleForgetToInt.{u, r} Λ₁ X :=
  NatIso.ofComponents
    (fun P =>
      { hom := ⟨Functor.whiskerLeft P.val (restrictScalarsIntComp.{u, r} φ).hom⟩
        inv := ⟨Functor.whiskerLeft P.val (restrictScalarsIntComp.{u, r} φ).inv⟩
        hom_inv_id := by aesop_cat
        inv_hom_id := by aesop_cat })
    (fun f => by aesop_cat)

end Stacks.EtaleCohomology

end
