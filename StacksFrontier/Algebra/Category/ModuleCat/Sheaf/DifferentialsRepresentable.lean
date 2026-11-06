module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Representability of derivations of sheaves of rings

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a small site. Derivations
of `O₂` over `O₁` with values in a sheaf of `O₂`-modules form a covariant functor, and this
file shows that functor is corepresented by a sheaf of modules, the sheaf of relative
differentials, constructed as the sheafification of the sectionwise Kähler differentials.

## Main definitions

* `moduleOfDifferentials` is the representing sheaf of modules: the sheafification of the
  presheaf of sectionwise Kähler differentials.
* `universalDerivation` is its universal relative derivation.
* `presheafDifferentialsEquiv` packages Mathlib's universal property of the presheaf of
  sectionwise Kähler differentials as a bijection.

## Main results

* `universalDerivation_isUniversal` is Tag 04BL in unique-factorization form: every
  relative derivation with values in a sheaf of modules factors through the universal
  derivation by a unique morphism. This is exactly a corepresentation of the functor
  sending a sheaf of modules to the type of its relative derivations.

## Implementation notes

Representability is stated by its universal element, as a unique factorization through the
universal derivation. Since the factorization is by a morphism of sheaves of modules and is
unique, this is precisely a corepresentation of the derivations functor, in the covariant
convention the source uses for its representability claim.

The representing object is the sheafification of Mathlib's
`PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'`, the presheaf whose
sections on `U` are the Kähler differentials of `O₂(U)` over `O₁(U)`. Its universal property
is Mathlib's `isUniversal'` transported along the sheafification adjunction, so this realizes
the explicit construction of the source rather than an abstract existence argument.

The site is a small category and the coefficient modules live in the same universe as the
rings. This is forced by the construction rather than chosen: sectionwise Kähler
differentials of a `CommRingCat.{u}`-valued sheaf of rings are `u`-sized, so sheafifying
them yields a `SheafOfModules.{u}`. Corepresenting derivations valued in strictly larger
sheaves of modules would need a universe lift of a sheaf of modules, which Mathlib does not
provide.

## References

* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Sheaves.Differentials

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- A sheaf of commutative rings, regarded as a sheaf of rings. -/
noncomputable abbrev underlyingRingSheaf (O : Sheaf J CommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O

variable (O₁ O₂ : Sheaf J CommRingCat.{u}) (φ : O₁ ⟶ O₂)

/-- Relative derivations of `O₂` over `O₁` with values in a sheaf of `O₂`-modules,
expressed on the underlying presheaf of modules. -/
abbrev SheafDerivation (F : SheafOfModules.{u} (underlyingRingSheaf O₂)) :=
  PresheafOfModulesOfCommRing.Derivation' F.val φ.hom

/-- The sheaf of relative differentials: the sheafification of the presheaf whose sections
on `U` are the Kähler differentials of `O₂(U)` over `O₁(U)`. -/
noncomputable def moduleOfDifferentials :
    SheafOfModules.{u} (underlyingRingSheaf O₂) :=
  (PresheafOfModules.sheafification (𝟙 (underlyingRingSheaf O₂).obj)).obj
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)

/-- The universal relative derivation into the sheaf of relative differentials: the
sectionwise differential followed by the unit of sheafification. -/
noncomputable def universalDerivation :
    SheafDerivation O₁ O₂ φ (moduleOfDifferentials O₁ O₂ φ) :=
  (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction
      (J := J) (𝟙 (underlyingRingSheaf O₂).obj)).unit.app
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom))

/-- The universal property of Mathlib's presheaf of sectionwise Kähler differentials, as a
bijection between morphisms out of it and relative derivations. -/
noncomputable def presheafDifferentialsEquiv
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ' : S ⟶ R)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ' ⟶ M) ≃
      PresheafOfModulesOfCommRing.Derivation' M φ' where
  toFun f := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ').postcomp f
  invFun := (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').desc
  left_inv _ :=
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').postcomp_injective _ _
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').fac _)
  right_inv := (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ').fac

/-- Every relative derivation with values in a sheaf of modules factors through the universal
derivation by a unique morphism of sheaves of modules. -/
@[stacks 04BL,
  stacks 0619 "the factorization D = d o theta of a derivation through the universal derivation"]
theorem universalDerivation_isUniversal
    (F : SheafOfModules.{u} (underlyingRingSheaf O₂))
    (D : SheafDerivation O₁ O₂ φ F) :
    ∃! f : moduleOfDifferentials O₁ O₂ φ ⟶ F,
      (universalDerivation O₁ O₂ φ).postcomp f.val = D := by
  set e := (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (underlyingRingSheaf O₂).obj) (P :=
      PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)
    (F := F)).trans (presheafDifferentialsEquiv φ.hom _) with he
  have key (f : moduleOfDifferentials O₁ O₂ φ ⟶ F) :
      e f = (universalDerivation O₁ O₂ φ).postcomp f.val := by
    ext U x
    rfl
  exact ⟨e.symm D, (key _).symm.trans (e.apply_symm_apply D),
    fun f hf ↦ (Equiv.eq_symm_apply e).mpr ((key f).trans hf)⟩

end Stacks.Sheaves.Differentials

end
