module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.GlobalSections

/-!
# Restriction of crystalline cohomology to a divided power thickening

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `(U, T, δ)` of the small
crystalline site `Cris(X/S)`.  A presheaf `F` on `Cris(X/S)` restricts to a presheaf `F_T` on the
Zariski site of the ambient scheme `T`, by `F_T(W) = F(U ∩ W, W, δ|_W)`; the restrictions of
`(U, T, δ)` to the opens of `T` are again objects of `Cris(X/S)`, so this restriction is the
composition of `F` with the functor `W ↦ (U ∩ W, W, δ|_W)`.  A morphism `f : T → T'` of
`Cris(X/S)` induces the comparison `f`-map `F_{T'} ⟶ f_* F_T` of [Stacks, Tag 07IP].

Global sections restrict to `T`: a global section of `F` is a family of sections compatible with
every morphism of `Cris(X/S)`, so its value at `(U, T, δ)` is a section of `F_T` over all of `T`,
and this value is compatible with the Zariski restriction maps of `F_T` and with the comparison
maps of `F`.  This underived restriction is the degree-zero shadow of the restriction of global
cohomology classes to `T` used in the construction of [Stacks, Equation 07LP]; the map of the
equation itself, in the derived category, is `...SmallSite.crystallineToAmbientDeRham` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Equation07LP.lean`, and the derived
restriction it uses is `...SmallSite.CrystallineThickening.derivedGlobalSectionsToAmbient` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AmbientRestrictionDerived.lean`.

## Main definitions

Everything below lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`.

* `CrystallineThickening.restrictOpenFunctorMap` — the restrictions of a morphism of `Cris(X/S)`
  over the opens of the ambient scheme of its target, as a natural transformation of the
  restriction functors `CrystallineThickening.restrictOpenFunctor`.
* `restriction` — the restriction `F_T` of a presheaf on `Cris(X/S)` to the ambient scheme of an
  object, and `restrictionFMap` the comparison `f`-map `F_{T'} ⟶ f_* F_T` of [Stacks, Tag 07IP].
* `deRhamRestriction` — the restriction of the global sections of `F` to the sections of `F_T`
  over `T`, for a presheaf with values in an arbitrary category whose global sections are
  computed by a limit.
* `globalSectionsRestriction` — the same map for a presheaf of sets, with global sections in the
  sense of [Stacks, Tag 06UN].

## Main results

* `restriction_comp_ι` — the restriction to `T` of the presheaf that a presheaf on `CRIS(X/S)`
  induces on `Cris(X/S)` is its restriction to `T` as a presheaf on `CRIS(X/S)`; through this the
  comparison isomorphism of [Stacks, Tag 07IZ] identifies the restriction of `Ω_{X/S}` to `T` with
  the divided power differentials `Ω_{T/S,δ}` for objects of the small site.
* `deRhamRestriction_restriction_map` and `globalSectionsRestriction_restriction_map` — the
  restriction of a global section to `T` restricts further, over an open `W` of `T`, to its
  restriction to the object `(U ∩ W, W, δ|_W)`.
* `deRhamRestriction_restrictionFMap` and `globalSectionsRestriction_restrictionFMap` — the
  restriction of a global section to `T'`, compared along a morphism `f : T → T'` of `Cris(X/S)`
  by the `f`-map of [Stacks, Tag 07IP], is its restriction to `T`.  This is what makes the
  comparison map canonical.
* `limMap_deRhamRestriction` — the restriction is natural in `F`.

## Implementation notes

Global sections of a presheaf `F` on a site are its limit, which for a presheaf of sets is the
hom-set out of the final presheaf of [Stacks, Tag 06UN]; `deRhamRestriction` therefore assumes
`HasLimit F`, a hypothesis on the ambient category and not on the mathematics, while
`globalSectionsRestriction` assumes nothing and is stated with the library's `06UN` global
sections.

The restrictions of an object of `Cris(X/S)` to the opens of its ambient scheme are those of the
underlying object of `CRIS(X/S)`, taken in `Cris(X/S)` by
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor`;
composed with the inclusion they are the original functor definitionally, which is what makes
`restriction_comp_ι` hold by `rfl`.

## References

* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
* [Stacks Project, Tag 07LP](https://stacks.math.columbia.edu/tag/07LP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe w v u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CohomologyRestriction

namespace CrystallineThickening

variable {S : GlobalCrystallineSituation.{u}}

/-- **The restrictions of a morphism of `Cris(X/S)` over the opens of the ambient scheme of its
target**, as a natural transformation of functors from those opens to `Cris(X/S)`. -/
def restrictOpenFunctorMap {A B : CrystallineThickening S} (g : A ⟶ B) :
    Opens.map g.hom.targetHom.hom.base ⋙ CrystallineThickening.restrictOpenFunctor A ⟶
      CrystallineThickening.restrictOpenFunctor B where
  app W := CrystallineThickening.restrictOpenMap g W
  naturality _ _ i := ObjectProperty.hom_ext (Thickening.IsCrystalline (S := S))
    (Thickening.restrictOpenLE_restrictOpenMap g.hom (leOfHom i))

/-- The component of `restrictOpenFunctorMap g` at an open `W` is the restriction of `g` over
`W`. -/
@[simp]
theorem restrictOpenFunctorMap_app {A B : CrystallineThickening S} (g : A ⟶ B)
    (W : B.obj.thickening.target.scheme.Opens) :
    (restrictOpenFunctorMap g).app W = CrystallineThickening.restrictOpenMap g W := rfl

end CrystallineThickening

section Restriction

variable {S : GlobalCrystallineSituation.{u}} {𝒜 : Type v} [Category.{w} 𝒜]
  (F : (CrystallineThickening S)ᵒᵖ ⥤ 𝒜)

/-- **The restriction `F_T` of a presheaf on `Cris(X/S)` to the ambient scheme of an object.**  Its
sections over an open `W` of `T` are the sections of `F` over the restriction
`(U ∩ W, W, δ|_W)`. -/
abbrev restriction (A : CrystallineThickening S) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ 𝒜 :=
  (CrystallineThickening.restrictOpenFunctor A).op ⋙ F

/-- The sections of `F_T` over an open `W` of `T` are the sections of `F` over the restriction of
the object to `W`. -/
theorem restriction_obj (A : CrystallineThickening S)
    (W : A.obj.thickening.target.scheme.Opens) :
    (restriction F A).obj (op W) = F.obj (op (A.restrictOpen W)) := rfl

/-- The restriction map of `F_T` along an inclusion `W ≤ W'` of opens of `T` is `F` applied to the
inclusion of the corresponding restrictions of the object. -/
theorem restriction_map (A : CrystallineThickening S)
    {W W' : A.obj.thickening.target.scheme.Opens} (h : W ≤ W') :
    (restriction F A).map (homOfLE h).op =
      F.map (CrystallineThickening.restrictOpenLE A h).op := rfl

/-- **Stacks Project, Tag 07IP.**  The `f`-map from the restriction of a presheaf on `Cris(X/S)` to
the ambient scheme of the target of a morphism `f` of `Cris(X/S)` to its restriction to the ambient
scheme of the source: over an open `W` of the target it is the presheaf applied to the restriction
of `f` over `W`. -/
@[stacks 07IP "the f-map on the small crystalline site, for presheaves"]
def restrictionFMap {A B : CrystallineThickening S} (g : A ⟶ B) :
    restriction F B ⟶ g.hom.targetHom.hom.base _* restriction F A :=
  Functor.whiskerRight (NatTrans.op (CrystallineThickening.restrictOpenFunctorMap g)) F

/-- The component of the `f`-map at an open `W` of the target is `F` applied to the restriction of
`f` over `W`. -/
@[simp]
theorem restrictionFMap_app {A B : CrystallineThickening S} (g : A ⟶ B)
    (W : B.obj.thickening.target.scheme.Opens) :
    (restrictionFMap F g).app (op W) =
      F.map (CrystallineThickening.restrictOpenMap g W).op := rfl

end Restriction

section BigComparison

variable {S : GlobalCrystallineSituation.{u}} {𝒜 : Type v} [Category.{u} 𝒜]

/-- **The restriction to `T` of the presheaf induced on `Cris(X/S)` by a presheaf on `CRIS(X/S)` is
its restriction to `T` as a presheaf on `CRIS(X/S)`.**  Both are the presheaf evaluated on the
restrictions of the object to the opens of its ambient scheme. -/
theorem restriction_comp_ι (G : (Thickening S)ᵒᵖ ⥤ 𝒜) (A : CrystallineThickening S) :
    restriction ((CrystallineThickening.ι S).op ⋙ G) A = Thickening.restriction G A.obj := rfl

end BigComparison

section DeRhamRestriction

variable {S : GlobalCrystallineSituation.{u}} {𝒜 : Type v} [Category.{w} 𝒜]
  (F : (CrystallineThickening S)ᵒᵖ ⥤ 𝒜) [HasLimit F]

/-- **The restriction of global sections to an object of `Cris(X/S)`**, the underived map
`Γ(Cris(X/S), F) ⟶ Γ(T, F_T)` restricting a global section of a presheaf on `Cris(X/S)` to the
sections over `T` of its restriction `F_T`, for an object `(U, T, δ)` of `Cris(X/S)`; global
sections are the limit.  The map of [Stacks, Equation 07LP] itself, in the derived category, is
`...SmallSite.crystallineToAmbientDeRham` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Equation07LP.lean`. -/
def deRhamRestriction (A : CrystallineThickening S) :
    limit F ⟶ (restriction F A).obj (op ⊤) :=
  limit.π F (op (A.restrictOpen ⊤))

/-- **The restriction of a global section to `T` restricts further, over an open `W` of `T`, to its
restriction to `(U ∩ W, W, δ|_W)`.** -/
@[reassoc]
theorem deRhamRestriction_restriction_map (A : CrystallineThickening S)
    (W : A.obj.thickening.target.scheme.Opens) :
    deRhamRestriction F A ≫ (restriction F A).map (homOfLE (le_top : W ≤ ⊤)).op =
      limit.π F (op (A.restrictOpen W)) :=
  limit.w F (CrystallineThickening.restrictOpenLE A (le_top : W ≤ ⊤)).op

/-- **The restriction of a global section to `T'`, compared along a morphism `f : T → T'` of
`Cris(X/S)` by the `f`-map of Tag 07IP, is its restriction to `T`.**  This is the compatibility
that makes the comparison map of Equation 07LP canonical. -/
@[reassoc]
theorem deRhamRestriction_restrictionFMap {A B : CrystallineThickening S} (g : A ⟶ B) :
    deRhamRestriction F B ≫ (restrictionFMap F g).app (op ⊤) =
      limit.π F (op (A.restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ ⊤))) :=
  limit.w F (CrystallineThickening.restrictOpenMap g ⊤).op

/-- **The comparison map of Equation 07LP is natural in the presheaf.** -/
theorem limMap_deRhamRestriction {G : (CrystallineThickening S)ᵒᵖ ⥤ 𝒜} [HasLimit G]
    (φ : F ⟶ G) (A : CrystallineThickening S) :
    limMap φ ≫ deRhamRestriction G A =
      deRhamRestriction F A ≫ φ.app (op (A.restrictOpen ⊤)) :=
  limMap_π φ (op (A.restrictOpen ⊤))

end DeRhamRestriction

section GlobalSections

variable {S : GlobalCrystallineSituation.{u}}
  (F : (CrystallineThickening S)ᵒᵖ ⥤ Type w) (A : CrystallineThickening S)

/-- **The restriction of global sections to an object of `Cris(X/S)`, for a presheaf of sets.**
The map `Γ(Cris(X/S), F) ⟶ Γ(T, F_T)` sending a global section of `F`, in the sense of Tag 06UN, to
its value at the object `(U, T, δ)`, a section of `F_T` over all of `T`. -/
def globalSectionsRestriction :
    Presheaf.globalSections F → (restriction F A).obj (op ⊤) :=
  fun s ↦ (Presheaf.globalSectionsEquivSections F s).val (op (A.restrictOpen ⊤))

/-- **The restriction of a global section of a presheaf of sets to `T` restricts further, over an
open `W` of `T`, to its value at `(U ∩ W, W, δ|_W)`.** -/
theorem globalSectionsRestriction_restriction_map
    (W : A.obj.thickening.target.scheme.Opens) (s : Presheaf.globalSections F) :
    (restriction F A).map (homOfLE (le_top : W ≤ ⊤)).op (globalSectionsRestriction F A s) =
      (Presheaf.globalSectionsEquivSections F s).val (op (A.restrictOpen W)) :=
  (Presheaf.globalSectionsEquivSections F s).property
    (CrystallineThickening.restrictOpenLE A (le_top : W ≤ ⊤)).op

/-- **The restriction of a global section of a presheaf of sets to `T'`, compared along a morphism
`f : T → T'` of `Cris(X/S)` by the `f`-map of Tag 07IP, is its value at `T`.** -/
theorem globalSectionsRestriction_restrictionFMap {B : CrystallineThickening S} (g : A ⟶ B)
    (s : Presheaf.globalSections F) :
    (restrictionFMap F g).app (op ⊤) (globalSectionsRestriction F B s) =
      (Presheaf.globalSectionsEquivSections F s).val
        (op (A.restrictOpen (g.hom.targetHom.hom ⁻¹ᵁ ⊤))) :=
  (Presheaf.globalSectionsEquivSections F s).property
    (CrystallineThickening.restrictOpenMap g ⊤).op

end GlobalSections

end CohomologyRestriction

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
