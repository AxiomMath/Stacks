module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.GlobalSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections are sections over a terminal object, and so are their derived functors

Let `J` be a Grothendieck topology on a category `C` admitting a global sections functor
`Sheaf.Γ J A`, the right adjoint of the constant sheaf functor, and let `T` be a terminal object
of `C`. Then the restriction map `Γ(F) ⟶ F(T)` of `CategoryTheory.Sheaf.ΓRes` is an isomorphism,
naturally in the sheaf `F`: global sections are a limit of the sections of `F` over the objects
of `C` (`CategoryTheory.Sheaf.isLimitConeΓ`), and `op T` is an initial index of that limit, so
the projection to it is invertible.

Passing to complexes, this identifies the two *unbounded* derived functors: the total right
derived functor `RΓ(-)` of global sections and the total right derived functor `RΓ(T, -)` of
sections over `T` are isomorphic as functors `D(Sh(J, A)) ⥤ D(A)`, and the comparison is
degreewise an isomorphism on hypercohomology. This is what lets a statement proved about
hypercohomology over an object of the site be read as a statement about hypercohomology in the
sense of `CategoryTheory.Sheaf.Γ`, and conversely.

Mathlib's `CategoryTheory.Sheaf.ΓNatIsoSheafSections` already identifies the two functors on a
site that *has* a terminal object. What is added here is that the identification is the
canonical restriction map — which needs only `IsTerminal T`, not `HasTerminal C` — and the
derived and degreewise consequences, which are not about `Sheaf.Γ` alone.

## Main definitions

* `Stacks.Cohomology.mapHomotopyCategoryNatIso`: the isomorphism induced on homotopy categories
  of cochain complexes by an isomorphism of additive functors.
* `Stacks.Cohomology.homotopyGlobalSectionsNatIsoSectionsAtTerminal`: degreewise global sections
  of a complex of sheaves are its degreewise sections over a terminal object, after the
  localization to the derived category of the coefficients.
* `Stacks.Cohomology.derivedGlobalSectionsNatIsoSectionsAtTerminal`: **`RΓ(-) ≅ RΓ(T, -)`** on
  the unbounded derived category.
* `Stacks.Cohomology.hypercohomologyGlobalSectionsNatIsoAtTerminal` and
  `Stacks.Cohomology.hypercohomologyGlobalSectionsIsoAtTerminal`: the degree-`n` consequence, as
  a natural isomorphism of functors and at a single object of the derived category.

## Main results

* `Stacks.Cohomology.isIso_ΓRes_of_isTerminal` and
  `Stacks.Cohomology.isIso_natTransΓRes_of_isTerminal`: **restriction to a terminal object is an
  isomorphism on global sections**, at a sheaf and as a natural transformation.
* `Stacks.Cohomology.hasRightDerivedFunctor_sectionsAtTerminal_of_globalSections` and its
  converse: the two derivations exist under the same hypothesis, since they derive isomorphic
  functors.

## Implementation notes

Nothing here carries a Stacks attribute: this is infrastructure comparing two spellings of the
same functor.

The derived statements are stated for the explicit `Functor.totalRightDerived` of
`mapHomotopyCategory ⋙ DerivedCategory.Qh`, which is the spelling the unbounded derived
global-sections functors of this repository use, rather than for any one of the named
abbreviations built on it; that way a consumer whose derivation hypothesis is phrased with
either functor can quote them.

The existence of the two derivations is an instance argument rather than a hypothesis, and the
two implications between them are recorded separately instead of as one `Iff`, because they are
consumed as instance-providing lemmas.

The two additivity instances are stated for an arbitrary site and arbitrary coefficients, which
is what the comparison needs. The repository's existing instances of the same two facts are
narrower and do not apply here: `Stacks.Cohomology.DerivedLowerShriek.additive_abelianSections`
asks the site to be a small category with coefficients in `AddCommGrpCat` in the site's own
universe, and the additivity instances for `CategoryTheory.Sheaf.Γ` are each attached to one
site.

## References

* [Stacks Project, Tag 013R](https://stacks.math.columbia.edu/tag/013R)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

universe w₁ w₂ v u v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology

/-! ### An isomorphism of additive functors, on homotopy categories -/

section MapHomotopyCategory

variable {V₁ : Type u₃} [Category.{v₃} V₁] [Preadditive V₁]
  {V₂ : Type u₄} [Category.{v₄} V₂] [Preadditive V₂]
  {ι : Type*} {F G : V₁ ⥤ V₂} [F.Additive] [G.Additive]

/-- The isomorphism induced on homotopy categories of complexes by an isomorphism `e : F ≅ G` of
additive functors: the degreewise actions of `e.hom` and `e.inv` are mutually inverse, because
`CategoryTheory.NatTrans.mapHomotopyCategory` is functorial. -/
def mapHomotopyCategoryNatIso (e : F ≅ G) (c : ComplexShape ι) :
    F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory e.hom c
  inv := NatTrans.mapHomotopyCategory e.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id]

end MapHomotopyCategory

/-! ### Restriction to a terminal object, on global sections -/

section Sections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [HasWeakSheafify J A] [HasGlobalSectionsFunctor J A]

/-- Sections over an object of the site are an additive functor on sheaves: addition of
morphisms of sheaves is computed on the underlying presheaves, hence componentwise. -/
instance additive_sheafSections_obj [Preadditive A] (U : Cᵒᵖ) :
    ((sheafSections J A).obj U).Additive where
  map_add := rfl

variable {T : C} (hT : IsTerminal T)

include hT

/-- **Restriction to a terminal object is an isomorphism on global sections.** The restriction
maps out of the global sections of `F` form a limit cone over the presheaf underlying `F`
(`CategoryTheory.Sheaf.isLimitConeΓ`), and `op T` is an initial object of the index category
`Cᵒᵖ`, so the projection of a limit to it is invertible. -/
@[sga "3 IV 4.3.17" "special case"]
theorem isIso_ΓRes_of_isTerminal (F : Sheaf J A) : IsIso (F.ΓRes (op T)) :=
  (Sheaf.isLimitConeΓ F).isIso_π_app_of_isInitial (op T) (initialOpOfTerminal hT)

/-- **The global sections functor is the functor of sections over a terminal object**, through
the canonical restriction `CategoryTheory.Sheaf.natTransΓRes`. -/
theorem isIso_natTransΓRes_of_isTerminal : IsIso (Sheaf.natTransΓRes J A (op T)) :=
  have (F : Sheaf J A) : IsIso ((Sheaf.natTransΓRes J A (op T)).app F) :=
    isIso_ΓRes_of_isTerminal J A hT F
  NatIso.isIso_of_isIso_app _

/-- Global sections are sections over a terminal object, as an isomorphism of functors whose
forward direction is the canonical restriction. -/
def ΓNatIsoSectionsAtTerminal : Sheaf.Γ J A ≅ (sheafSections J A).obj (op T) :=
  haveI := isIso_natTransΓRes_of_isTerminal J A hT
  asIso (Sheaf.natTransΓRes J A (op T))

/-- The forward direction of `ΓNatIsoSectionsAtTerminal` is the restriction
`CategoryTheory.Sheaf.natTransΓRes` to the terminal object. -/
@[simp]
lemma ΓNatIsoSectionsAtTerminal_hom :
    (ΓNatIsoSectionsAtTerminal J A hT).hom = Sheaf.natTransΓRes J A (op T) :=
  rfl

end Sections

/-! ### Derived global sections and derived sections over a terminal object -/

section Derived

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u₂) [Category.{v₂} A] [Abelian A] [HasSheafify J A]
  [HasGlobalSectionsFunctor J A] [HasDerivedCategory.{w₂} A]
  [HasDerivedCategory.{w₁} (Sheaf J A)]

/-- The global sections functor is additive: it is a right adjoint, so it preserves binary
products. -/
instance additive_Γ : (Sheaf.Γ J A).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {T : C} (hT : IsTerminal T)

include hT

/-- **Degreewise global sections of a complex of sheaves are its degreewise sections over a
terminal object**, as functors on the homotopy category of cochain complexes followed by the
localization to the derived category of the coefficients. This is the comparison that the two
unbounded derivations are taken of. -/
def homotopyGlobalSectionsNatIsoSectionsAtTerminal :
    (Sheaf.Γ J A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      ((sheafSections J A).obj (op T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  Functor.isoWhiskerRight
    (mapHomotopyCategoryNatIso (ΓNatIsoSectionsAtTerminal J A hT) (ComplexShape.up ℤ))
    DerivedCategory.Qh

/-- If unbounded derived global sections exist, so do unbounded derived sections over a terminal
object: the two functors being derived are isomorphic. -/
theorem hasRightDerivedFunctor_sectionsAtTerminal_of_globalSections
    [((Sheaf.Γ J A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))] :
    (((sheafSections J A).obj (op T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) :=
  (Functor.hasRightDerivedFunctor_iff_of_iso
    (homotopyGlobalSectionsNatIsoSectionsAtTerminal J A hT) _).1 inferInstance

/-- If unbounded derived sections over a terminal object exist, so do unbounded derived global
sections: the two functors being derived are isomorphic. -/
theorem hasRightDerivedFunctor_globalSections_of_sectionsAtTerminal
    [(((sheafSections J A).obj (op T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))] :
    ((Sheaf.Γ J A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) :=
  (Functor.hasRightDerivedFunctor_iff_of_iso
    (homotopyGlobalSectionsNatIsoSectionsAtTerminal J A hT) _).2 inferInstance

variable [((Sheaf.Γ J A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))]
  [(((sheafSections J A).obj (op T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).HasRightDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))]

/-- **Unbounded derived global sections are unbounded derived sections over a terminal object**,
`RΓ(-) ≅ RΓ(T, -)` as functors `D(Sh(J, A)) ⥤ D(A)`: both are right derived functors of
isomorphic functors on the homotopy category, and a right derived functor is unique up to a
canonical isomorphism. -/
def derivedGlobalSectionsNatIsoSectionsAtTerminal :
    ((Sheaf.Γ J A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) ≅
      (((sheafSections J A).obj (op T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) :=
  Functor.rightDerivedNatIso _ _
    (Functor.totalRightDerivedUnit _ DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)))
    (Functor.totalRightDerivedUnit _ DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))
    (homotopyGlobalSectionsNatIsoSectionsAtTerminal J A hT)

/-- **Hypercohomology computed with global sections is hypercohomology over a terminal object**,
in every degree and naturally in the complex. -/
def hypercohomologyGlobalSectionsNatIsoAtTerminal (n : ℤ) :
    ((Sheaf.Γ J A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) ⋙
        DerivedCategory.homologyFunctor A n ≅
      (((sheafSections J A).obj (op T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ)) ⋙
        DerivedCategory.homologyFunctor A n :=
  Functor.isoWhiskerRight (derivedGlobalSectionsNatIsoSectionsAtTerminal J A hT)
    (DerivedCategory.homologyFunctor A n)

/-- The degree-`n` hypercohomology of a complex of sheaves, computed as the homology of its
derived global sections, is its degree-`n` hypercohomology over a terminal object. -/
def hypercohomologyGlobalSectionsIsoAtTerminal (n : ℤ) (K : DerivedCategory (Sheaf J A)) :
    (DerivedCategory.homologyFunctor A n).obj
        (((((Sheaf.Γ J A).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))).obj K)) ≅
      (DerivedCategory.homologyFunctor A n).obj
        (((((sheafSections J A).obj (op T)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso (Sheaf J A) (ComplexShape.up ℤ))).obj K) :=
  (hypercohomologyGlobalSectionsNatIsoAtTerminal J A hT n).app K

end Derived

end Stacks.Cohomology

end
