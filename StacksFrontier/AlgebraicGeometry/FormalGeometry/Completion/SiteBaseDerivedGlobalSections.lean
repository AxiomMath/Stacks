module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CohomologyAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SliceDerivedSections

/-!
# `RΓ(X, -)` of a scheme over `A` and `RΓ(𝒞, -)` of its small Zariski site agree

The `A`-linear derived global sections of a scheme `f : X ⟶ Spec A` are written in this library in
two unrelated ways:

* `AlgebraicGeometry.derivedGlobalSectionsOver f`, the total right derived functor of
  `ℱ ↦ Γ(X, ℱ)` read as an `A`-module along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.RingedSite.derivedGlobalSectionsOverUnbounded` at the ringed site
  `opensRingedSite X.sheaf`, the total right derived functor of
  `ℱ ↦ Hom_𝒪(𝒪, ℱ)` read as an `A`-module along a ring map `A ⟶ Γ(𝒞, 𝒪)` into the compatible
  families of local sections; this is the functor of [Stacks, Tags 0BLX and 0CQI].

This file identifies them.

## Main definitions

* `AlgebraicGeometry.RingedSite.terminalSectionsRingHom`: a section of `𝒪` over a terminal object
  of the site, read as a compatible family of local sections, as a ring map.
* `Stacks.Algebraization.baseSiteRingHom`: the ring map `A ⟶ Γ(𝒞, 𝒪_X)` which makes the structure
  sheaf of the small Zariski site of `X` a sheaf of `A`-algebras, for `f : X ⟶ Spec A`.
* `Stacks.Algebraization.globalSectionsOverSiteIso`: **`Hom_𝒪(𝒪, -) ≅ Γ(X, -)`** as `A`-linear
  functors, the underived comparison.
* `Stacks.Algebraization.derivedGlobalSectionsOverSiteIso`: **`RΓ(𝒞, -) ≅ RΓ(X, -)`**, the derived
  comparison.

## Implementation notes

The underived comparison is two steps. `Hom_𝒪(𝒪, ℱ)` is `Γ(T, ℱ)` for a terminal object `T`, which
is `AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIsoSectionsTerminal`; and `⊤` is terminal
in the site of opens, where `Γ(⊤, -)` is global sections on the nose. The scalars match because
the ring map into the compatible families is built from the one into `Γ(X, ⊤)` by restricting
along the unique arrow to `⊤`, so evaluating it at `⊤` returns the original map — that is
`AlgebraicGeometry.RingedSite.sectionsEval_comp_terminalSectionsRingHom`.

The derived comparison is then the uniqueness of total right derived functors,
`CategoryTheory.Functor.rightDerivedNatIso`: both functors are right derived along
`DerivedCategory.Qh` of the two isomorphic functors `K(Mod 𝒪_X) ⥤ D(A)` that the underived
comparison induces, and the isomorphism of those is
`CategoryTheory.Functor.mapHomotopyCategoryNatIso` whiskered with `Qh`.

`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (Stacks.SheafOfModules.opensRingedSite
X.sheaf).O))` and `X.Modules` are the same category, the two spellings of the sheaf of rings being
definitionally equal; so the two functors have literally the same source, and the morphism
property and localization functor of the two right derivations agree.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (opensRingedSite)
open scoped IsMulCommutative

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafCompose_forget₂_ringCat

section Terminal

variable (X : RingedSite.{u, u, u}) {T : X.C} (hT : IsTerminal T)

/-- **A section of `𝒪` over a terminal object of the site, read as a compatible family of local
sections**, as a ring map `𝒪(T) ⟶ Γ(𝒞, 𝒪)`. Its value over an object `V` is the restriction of the
section along the unique arrow `V ⟶ T`.

This is the ring map which makes `𝒪` a sheaf of `𝒪(T)`-algebras; on the site of opens of a ringed
space, with `T = ⊤`, it is the map which reads a global function as a compatible family. -/
def terminalSectionsRingHom :
    sectionRing X T →+*
      RingCat.sectionsSubring ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj where
  toFun b :=
    ⟨(Stacks.SheafOfModules.terminalSection ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) T hT
        b).val,
      (Stacks.SheafOfModules.terminalSection ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) T hT
        b).property⟩
  map_one' := by ext V; exact map_one _
  map_mul' _ _ := by ext V; exact map_mul _ _ _
  map_zero' := by ext V; exact map_zero _
  map_add' _ _ := by ext V; exact map_add _ _ _

/-- **The compatible family attached to a section over a terminal object has that section as its
value there**: restricting along the identity changes nothing. -/
theorem sectionsEval_comp_terminalSectionsRingHom :
    (sectionsEval (X := X) (op T)).comp (terminalSectionsRingHom X hT) =
      RingHom.id (sectionRing X T) := by
  refine RingHom.ext (fun b => ?_)
  change ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map (hT.from T).op b = b
  rw [show hT.from T = 𝟙 T from hT.hom_ext _ _, op_id,
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map_id]
  rfl

/-- The two readings of a section over a terminal object as a global section of `𝒪` — through
`AlgebraicGeometry.RingedSite.terminalSectionsRingHom` and through
`AlgebraicGeometry.RingedSite.globalSectionOfTerminalSection` — agree. -/
theorem globalSectionOfSections_terminalSectionsRingHom (b : sectionRing X T) :
    globalSectionOfSections (X := X) (terminalSectionsRingHom X hT b) =
      globalSectionOfTerminalSection (X := X) hT b := by
  refine (Presheaf.globalSectionsEquivSections _).injective (Subtype.ext (funext fun V => ?_))
  exact (globalSectionVal_globalSectionOfSections _ V).trans
    (globalSectionVal_globalSectionOfTerminalSection (X := X) hT b V).symm

end Terminal

end AlgebraicGeometry.RingedSite

namespace Stacks.Algebraization

open AlgebraicGeometry.RingedSite

attribute [local instance 100000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The structure sheaf of the small Zariski site of `X` as a sheaf of `A`-algebras**, for a
scheme `f : X ⟶ Spec A` over `A`: the ring map `A ⟶ Γ(𝒞, 𝒪_X)` into the compatible families of
local sections obtained from `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` by restricting a global function along
the inclusions of the open sets. -/
def baseSiteRingHom :
    A →+* RingCat.sectionsSubring
      ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O)).obj :=
  (terminalSectionsRingHom (opensRingedSite X.sheaf)
      (T := (⊤ : Opens X)) isTerminalTop).comp
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

/-- Evaluating `Stacks.Algebraization.baseSiteRingHom` at the terminal open returns the ring map
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` it was built from. -/
theorem sectionsEval_comp_baseSiteRingHom :
    (sectionsEval (X := opensRingedSite X.sheaf)
        (op (⊤ : Opens X))).comp (baseSiteRingHom f) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom :=
  RingHom.ext fun a =>
    RingHom.congr_fun (sectionsEval_comp_terminalSectionsRingHom (opensRingedSite X.sheaf)
      (T := (⊤ : Opens X)) isTerminalTop) (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a)

/-- **`Γ(X, -)` read on the small Zariski site**: the `A`-linear global sections
`Hom_{𝒪_X}(𝒪_X, -)` of the ringed site `𝒞` of `X`, ascribed as a functor out of `X.Modules`.

The two spellings of the category of `𝒪_X`-modules — `X.Modules` and
`SheafOfModules ((Stacks.SheafOfModules.Tensor.ringSheaf (opensRingedSite X.sheaf).O))` — are
definitionally equal but not syntactically so. -/
def siteGlobalSections : X.Modules ⥤ ModuleCat.{u} A :=
  moduleGlobalSectionsOver (opensRingedSite X.sheaf) A (baseSiteRingHom f)

/-- The `A`-linear global sections functor `Stacks.Algebraization.siteGlobalSections` is
additive. -/
instance siteGlobalSections_additive : (siteGlobalSections f).Additive :=
  moduleGlobalSectionsOver_additive (opensRingedSite X.sheaf) A (baseSiteRingHom f)

/-- **`RΓ(𝒞, -)` read on the small Zariski site**: the `A`-linear unbounded derived global
sections of the ringed site of `X`, ascribed as a functor out of `D(𝒪_X)`. -/
def siteDerivedGlobalSections :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  derivedGlobalSectionsOverUnbounded (opensRingedSite X.sheaf) A (baseSiteRingHom f)

/-- The comparison exhibiting `Stacks.Algebraization.siteDerivedGlobalSections` as the total right
derived functor of `Stacks.Algebraization.siteGlobalSections`. -/
def siteDerivedGlobalSectionsUnit :
    (siteGlobalSections f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ siteDerivedGlobalSections f :=
  derivedGlobalSectionsOverUnboundedUnit (opensRingedSite X.sheaf) A (baseSiteRingHom f)

/-- `Stacks.Algebraization.siteDerivedGlobalSections` is the total right derived functor of
`Stacks.Algebraization.siteGlobalSections` with respect to the quasi-isomorphisms, via
`Stacks.Algebraization.siteDerivedGlobalSectionsUnit`. -/
instance siteDerivedGlobalSections_isRightDerivedFunctor :
    (siteDerivedGlobalSections f).IsRightDerivedFunctor (siteDerivedGlobalSectionsUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
  derivedGlobalSectionsOverUnbounded_isRightDerivedFunctor (opensRingedSite X.sheaf) A
    (baseSiteRingHom f)

/-- **`Hom_{𝒪_X}(𝒪_X, -) ≅ Γ(X, -)` as `A`-linear functors.** The `A`-linear global sections of
the small Zariski site of `X`, taken along `Stacks.Algebraization.baseSiteRingHom`, are the
`A`-linear global sections `AlgebraicGeometry.globalSectionsOver f` of the scheme.

`⊤` is terminal in the site of opens, so `Hom_𝒪(𝒪, -)` is `Γ(⊤, -)` by
`AlgebraicGeometry.RingedSite.moduleGlobalSectionsOverIsoSectionsTerminal`, and the scalars match
by `Stacks.Algebraization.sectionsEval_comp_baseSiteRingHom`. -/
def globalSectionsOverSiteIso :
    siteGlobalSections f ≅ _root_.AlgebraicGeometry.globalSectionsOver f :=
  moduleGlobalSectionsOverIsoSectionsTerminal (opensRingedSite X.sheaf) A
      (baseSiteRingHom f) (T := (⊤ : Opens X)) isTerminalTop ≪≫
    eqToIso (by rw [sectionsEval_comp_baseSiteRingHom f]; rfl)

/-- **`RΓ(𝒞, -) ≅ RΓ(X, -)`.** The `A`-linear unbounded derived global sections of the small
Zariski site of `X`, taken along `Stacks.Algebraization.baseSiteRingHom`, are the `A`-linear
unbounded derived global sections `AlgebraicGeometry.derivedGlobalSectionsOver f` of the scheme
over `A`.

Both are total right derived functors along `DerivedCategory.Qh` of the two isomorphic functors
`K(Mod 𝒪_X) ⥤ D(A)` induced by `Stacks.Algebraization.globalSectionsOverSiteIso`, so they are
identified by the uniqueness of right derived functors. -/
def derivedGlobalSectionsOverSiteIso :
    siteDerivedGlobalSections f ≅ _root_.AlgebraicGeometry.derivedGlobalSectionsOver f :=
  Functor.rightDerivedNatIso _ _ (siteDerivedGlobalSectionsUnit f)
    (_root_.AlgebraicGeometry.derivedGlobalSectionsOverUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryNatIso (globalSectionsOverSiteIso f) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- `Stacks.Algebraization.siteDerivedGlobalSections` is, by definition, the `A`-linear unbounded
derived global sections functor of the ringed site of `X` along
`Stacks.Algebraization.baseSiteRingHom`. -/
theorem siteDerivedGlobalSections_eq :
    siteDerivedGlobalSections f =
      derivedGlobalSectionsOverUnbounded (opensRingedSite X.sheaf) A (baseSiteRingHom f) :=
  rfl

end Stacks.Algebraization

end
