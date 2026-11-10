module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Module-valued cohomology of the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  This file constructs the cohomology of
a sheaf of `𝒪_{X/S}`-modules on the small crystalline site *valued in modules over the base
ring* `A = Γ(S, 𝒪_S)`: the graded modules `H^j(Cris(X/S), M)` and the derived object
`RΓ(Cris(X/S), M)` of `D⁺(Mod_A)`.  That is the shape in which the chapter's base change,
perfectness and Frobenius statements are written — [Stacks, Tag 07MU], [Stacks, Tag 07MX],
[Stacks, Tag 07MY], [Stacks, Tag 07N5] all assert something about `RΓ(Cris(X/S), F)` *as an
object of `D(A)`*, and none of them can be stated about an abelian group.

## Universes

The universe bookkeeping is the whole difficulty, so it is set out explicitly.  For a situation
`S : GlobalCrystallineSituation.{u}`:

| object | universe |
| --- | --- |
| the objects of `Cris(X/S)`, i.e. `CrystallineThickening S` | `Type (u + 1)` |
| the morphisms of `Cris(X/S)` | `Type u` |
| the sections `Γ(T, 𝒪_T)` of the structure sheaf, i.e. `structureSheaf S` | `RingCat.{u}` |
| **the sections of a module**, i.e. `SheafOfModules.{u + 1} (structureSheaf S)` | `Type (u + 1)` |
| the underlying abelian sheaf of such a module | `AddCommGrpCat.{u + 1}` |
| the base ring `A = Γ(S, 𝒪_S)` | `Type u` |
| the ring `Γ(Cris(X/S), 𝒪_{X/S})` of compatible sections | `Type (u + 1)` |
| `H^j(Cris(X/S), M)` and the terms of `RΓ(Cris(X/S), M)` | `ModuleCat.{u + 1} A` |
| the morphisms of the derived categories | `Type (u + 2)` |

The one choice being made is in the fourth row, and it is forced.  A module over
`SmallSite.structureSheaf` with its sections in `Type u` has its underlying abelian sheaf in
`AddCommGrpCat.{u}`, where sheafification on `Cris(X/S)` is unavailable — the criterion
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` asks `max (u+1) u ≤ u`, i.e.
`UnivLE.{u + 1, u}` — so there is no abelian category to derive anything in.  Raising the
*module* universe to `u + 1` while leaving the *ring* universe at `u` repairs this and nothing
else has to move: the structure sheaf is unchanged, so these are modules over the same
`𝒪_{X/S}` that the rest of the chapter uses, and the underlying abelian sheaf lands in
`AddCommGrpCat.{u + 1}`, which is exactly the coefficient category of the abelian-valued
`SmallSite/Cohomology.lean`.  This is the arrangement that
`Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_moduleRestrictionSheaf_over`
already uses for the global presentations it needs.

Raising the ring universe instead would have changed `𝒪_{X/S}`, and lowering the module universe
is the state of affairs the paragraph above rules out.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `ModuleSheaf` — the category of sheaves of `𝒪_{X/S}`-modules on `Cris(X/S)` at the raised
  module universe, `SheafOfModules.{u + 1} (structureSheaf S)`.
* `toAbelianSheaf` — the underlying abelian sheaf of such a module, landing in
  `Sheaf (smallTopology S) AddCommGrpCat.{u + 1}`, the coefficient category of the
  abelian-valued theory of `SmallSite/Cohomology.lean`.
* `crystallineSectionRing` — the ring `Γ(Cris(X/S), 𝒪_{X/S})` of compatible families of sections
  of the structure sheaf.
* `baseRingHom` — the canonical ring map `A = Γ(S, 𝒪_S) ⟶ Γ(Cris(X/S), 𝒪_{X/S})`, given on an
  object `(U, T, δ)` by the structure morphism `T ⟶ S`.  This is why `A` acts on everything in
  sight.
* `baseSmul` and `baseSmulRingHom` — multiplication by an element of `A` on a sheaf of
  `𝒪_{X/S}`-modules, and the ring map `A ⟶ End M` it assembles into.
* `moduleGlobalSections` — global sections of a module, as a module over
  `Γ(Cris(X/S), 𝒪_{X/S})`, and `baseModuleGlobalSections` the same as a module over `A`.
* `moduleCohomologyFunctor` and `moduleCohomology` — **`H^j(Cris(X/S), M)` as an `A`-module**,
  the `j`-th right derived functor of `baseModuleGlobalSections`.
* `derivedModuleGlobalSectionsFunctor` and `derivedModuleGlobalSections` —
  **`RΓ(Cris(X/S), M)` in `D⁺(Mod_A)`**.
* `hasDerivedCategoryModuleSheaf`, `hasDerivedCategoryModuleCat` — the two derived category
  models the above are stated against, at the universe `u + 2`.

## Main results

* `instWEqualsLocallyBijectiveAddCommGrpCat`, `instAbelianModuleSheaf`,
  `instEnoughInjectivesModuleSheaf` — the raised-universe module category is abelian and has
  enough injectives, so derived functors out of it exist.  Together with the `HasSheafify`
  instance of `SmallSite/Cohomology.lean` these are the hypotheses the construction needs.
* `homologyDerivedModuleGlobalSectionsIso` — **the derived and the graded module-valued theories
  agree**, `H^j(RΓ(Cris(X/S), M)) ≅ H^j(Cris(X/S), M)` as `A`-modules, naturally in `M`.
* `toModuleCohomologyZero` — the degree-zero comparison `Γ(Cris(X/S), -) ⟶ H^0(Cris(X/S), -)`.
* `moduleGlobalSections_obj_carrier`, `baseModuleGlobalSections_obj_carrier` — the underlying
  type of the global sections of `M`, at either scalar ring, is the set of compatible families
  of sections of `M`; restriction of scalars along `baseRingHom` changes only the action.
* `baseSmul_val_app` — an element of `A` acts on the sections of `M` over `(U, T, δ)` as its
  pullback to `Γ(T, 𝒪_T)`.
* `isZero_moduleCohomology_of_injective` and
  `isZero_homology_derivedModuleGlobalSections_of_injective` — the higher cohomology of an
  injective module vanishes, graded and in the derived category.

## What is and is not proved

What is proved is that sheaves of `𝒪_{X/S}`-modules at the raised universe form an abelian
category with enough injectives; that `A` acts on every such module by `𝒪_{X/S}`-linear
endomorphisms, so that their global sections are a module over `Γ(Cris(X/S), 𝒪_{X/S})` and over
`A`; that the graded cohomology modules `H^j(Cris(X/S), M)` and the derived object
`RΓ(Cris(X/S), M) ∈ D⁺(Mod_A)` therefore exist and are functorial; and that the derived and the
graded module-valued theories agree degreewise.

What is **not** proved here:

* **The degree-zero comparison is a map, not an isomorphism — in this file.**
  `toModuleCohomologyZero` is `Γ(Cris(X/S), -) ⟶ H^0(Cris(X/S), -)`, and upgrading it to an
  isomorphism is `CategoryTheory.Functor.rightDerivedZeroIsoSelf`, whose hypothesis is left
  exactness of `baseModuleGlobalSections`.  That hypothesis is available, but from a
  comparison this file does not import:
  `...SmallSite.preservesFiniteLimits_baseModuleGlobalSections` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/VanishingTransfer.lean` gets it by
  identifying the module-valued global sections with the abelian-valued ones, which are a right
  adjoint, and `...SmallSite.moduleCohomologyZeroIso` there is the resulting isomorphism.  The
  library's own proof of the left exactness,
  `Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor_ringUniverse`, goes
  through corepresentability by `CategoryTheory.SheafOfModules.unit`, which is an object of
  `SheafOfModules.{u} (structureSheaf S)` — the module universe *equal to* the ring universe —
  and so is not an object of the category used here.  This is the one price of leaving the
  structure sheaf's rings in `Type u`; raising them to `RingCat.{u + 1}` as well would recover
  it, at the cost that the modules would then be modules over a universe lift of `𝒪_{X/S}` and
  not over the `𝒪_{X/S}` that the rest of the chapter uses, which is the worse trade.

* **The comparison with the abelian-valued cohomology is not proved in this file**; it is
  proved elsewhere.  `toAbelianSheaf` names the underlying abelian sheaf of a module, so
  `Crystalline.GlobalCrystallineSituation.SmallSite.cohomology S ((toAbelianSheaf S).obj M) j`
  is a statement about the same `M`, and the assertion that it agrees with
  `moduleCohomology S M j` after forgetting the `A`-action is [Stacks, Tag 03FD].  The
  repository's `ModuleSheafCohomology.globalSectionsComparisonIso` is **not** available here:
  that declaration is stated under `[SmallCategory C]`, while `Cris(X/S)` has its objects in
  `Type (u + 1)` and its morphisms in `Type u` and is therefore not small.  This is the same
  failure of smallness that keeps `Stacks.Cohomology.CompositeRightDerived.RGammaSite` out of
  `SmallSite/DerivedGlobalSections.lean`, and it is a hypothesis of that particular form of the
  comparison, not anything about the crystalline site.  The general `δ`-functor construction
  behind it, `ModuleSheafCohomology.comparisonIso`, has no smallness hypothesis, and
  `...SmallSite.abelianComparisonIso` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleCohomologyComparison.lean`
  instantiates it at these universes; `...SmallSite.isZero_moduleCohomology_iff` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/VanishingTransfer.lean` then says that
  `moduleCohomology S M j` vanishes exactly when the abelian-valued right derived global sections
  of `(toAbelianSheaf S).obj M` do.  Nothing *in this file* depends on the comparison.
* The two theories do, however, have the *same* coefficient data, which is the point of the
  universe choice above: `toAbelianSheaf` lands in `AddCommGrpCat.{u + 1}`, so the
  `SmallSite.cohomology` of the underlying abelian sheaf of a module is defined, with no
  universe lifting, and is the object the comparison would be about.  Had the modules been left
  in `Type u` there would have been nothing to compare them to.
* The derived tensor product is available.  It is
  `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`
  (`StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean:1463`), instantiated for this chapter
  as
  `...SmallSite.derivedBaseChangeTensor` in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/DerivedTensorBaseChange.lean`.  Condition
  (5) of [Stacks, Tag 07MU] — flatness of `F'` — is rendered as
  `...SmallSite.IsFlatModule` in `SmallSite/BaseChangeIsomorphism.lean`, and [Stacks, Tag 07MU]
  itself **is** stated there, with all seven of its conditions, as
  `...SmallSite.IsBaseChangeIso07MU`.  It is not *proved*, and carries no
  attribute.  No perfectness predicate is applied to `RΓ(Cris(X/S), M)`, so [Stacks, Tag 07MX]
  and [Stacks, Tag 07MY] remain unstated here.
* The higher direct image `R^i f_{cris, *}` of modules is available too.  It is
  `...SmallSite.higherCrisModuleDirectImage` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisModuleDirectImage.lean`, a functor
  `ModuleSheaf S ⥤ ModuleSheaf S'` over this chapter's own `structureSheaf` — not over a universe
  lift, `Stacks.Modules.sheafRingULiftEquiv` being an isomorphism of categories that changes
  neither sections nor morphisms.  [Stacks, Tag 07MP] and [Stacks, Tag 07MQ] are what it is about,
  as modules and not merely as abelian sheaves, and both are stated as predicates:
  `Crystalline.GlobalCrystallineSituation.SmallSite.Quasicoherence07MP` and `...Boundedness07MQ`
  of `SmallSite/CrisModuleDirectImage.lean`, stated against `higherCrisModuleDirectImage`
  directly, so neither needs a universe-lift circumlocution.  Neither is proved: both reduce,
  through formula (07MK) of [Stacks, Tag 07MJ] and the distinguished triangle of
  [Stacks, Tag 07ML], to [Stacks, Tag 07LG], which is
  `...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
  `SmallSite/CrystalDeRhamComputesCohomology.lean`; the reduction itself is not carried out.

  The statements in `CrisModuleDirectImage.lean` ask for quasi-coherence alone, which is this
  library's spelling of "crystal in quasi-coherent modules".  They do not also carry
  `IsSheafCrystal F` beside `F.IsQuasicoherentOnSite`: that is condition (2) of
  [Stacks, Tag 07IT] standing next to condition (1), and since the library has only one half of
  one implication of that tag (`CrystalsModules/QuasicoherentImpliesLocal.lean`, big site only),
  it would be an extra hypothesis in Lean and make each statement cover strictly fewer modules
  than its tag.
* Nothing here carries a `@[stacks]` attribute.  Module-valued cohomology is infrastructure, in
  the same way that `SmallSite.derivedGlobalSections` is; the numbered assertions of the source
  that consume it are stated elsewhere.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (S : GlobalCrystallineSituation.{u})

/-! ### The modules, one universe up -/

/-- Sheafification of abelian presheaves on the small crystalline site inverts exactly the
locally bijective morphisms, with the coefficients at the universe `u + 1` of the objects of the
site.  Together with the `HasSheafify` instance of `SmallSite/Cohomology.lean` this is what makes
the sheaves of `𝒪_{X/S}`-modules with sections in `Type (u + 1)` an abelian category. -/
instance instWEqualsLocallyBijectiveAddCommGrpCat :
    (smallTopology S).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u + 1} _

/-- **The category of sheaves of `𝒪_{X/S}`-modules on the small crystalline site**, with the
sections of a module in `Type (u + 1)` and the sections of the structure sheaf left in `Type u`.
The raised module universe is forced: see the universe table in the module docstring. -/
abbrev ModuleSheaf := SheafOfModules.{u + 1} (structureSheaf S)

/-- **The underlying abelian sheaf of a sheaf of `𝒪_{X/S}`-modules.**  It lands in
`AddCommGrpCat.{u + 1}`, the coefficient category of the abelian-valued
`Crystalline.GlobalCrystallineSituation.SmallSite.cohomology`, so the graded theory is
defined on the image of this functor. -/
abbrev toAbelianSheaf :
    ModuleSheaf S ⥤ Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf.{u + 1} (structureSheaf S)

/-- **Sheaves of `𝒪_{X/S}`-modules on the small crystalline site form an abelian category** at the
raised module universe.  This is `SheafOfModules.instAbelian`, whose two hypotheses are the
`HasSheafify` of `SmallSite/Cohomology.lean` and
`instWEqualsLocallyBijectiveAddCommGrpCat`. -/
instance instAbelianModuleSheaf : Abelian (ModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian.{u + 1, u, u, u} (structureSheaf S)

/-- **Sheaves of `𝒪_{X/S}`-modules on the small crystalline site have enough injectives**, so
their cohomology can be computed by injective resolutions.  They form a Grothendieck abelian
category at the universe `u + 1`, by
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives`, whose ambient universe
`max (u + 1) u u u` is `u + 1`. -/
@[sga "4½ Etat_0 6.2" "special case"]
instance instEnoughInjectivesModuleSheaf : EnoughInjectives (ModuleSheaf S) :=
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives.{u + 1, u, u, u} (structureSheaf S)

/-! ### The two scalar rings -/

/-- The ring `Γ(Cris(X/S), 𝒪_{X/S})` of compatible families of sections of the structure sheaf of
the small crystalline site.  Its elements are families `(a_{(U,T,δ)} ∈ Γ(T, 𝒪_T))` compatible with
every morphism of `Cris(X/S)`; since the objects of the site form a `Type (u + 1)`, so does this
ring. -/
abbrev crystallineSectionRing :=
  Stacks.Cohomology.SiteModules.GlobalSectionRing (structureSheaf S)

/-- **The base ring `A = Γ(S, 𝒪_S)` acts on the small crystalline site**: the canonical ring map
`Γ(S, 𝒪_S) ⟶ Γ(Cris(X/S), 𝒪_{X/S})` sends `a` to the family whose value at `(U, T, δ)` is the
pullback of `a` along the structure morphism `T ⟶ S`.  Compatibility of that family is
`Crystalline.GlobalCrystallineSituation.Thickening.Hom.base_naturality`: a morphism of
`Cris(X/S)` commutes with the structure morphisms to `S`.

This is the map through which every `A`-linear statement of the chapter acquires its scalars. -/
def baseRingHom : Γ(S.S.scheme, ⊤) →+* ↥(crystallineSectionRing S) where
  toFun a :=
    ⟨fun A => (Scheme.Γ.map A.unop.obj.toBase.hom.op).hom a, by
      intro A B f
      have h := congrArg
        (fun g : B.unop.obj.thickening.target ⟶ S.S => (Scheme.Γ.map g.hom.op).hom a)
        f.unop.hom.base_naturality
      change (Scheme.Γ.map f.unop.hom.targetHom.hom.op).hom
          ((Scheme.Γ.map A.unop.obj.toBase.hom.op).hom a) =
        (Scheme.Γ.map B.unop.obj.toBase.hom.op).hom a
      calc
        _ = (Scheme.Γ.map (f.unop.hom.targetHom.hom ≫ A.unop.obj.toBase.hom).op).hom a := by
              rw [op_comp, Functor.map_comp]
              rfl
        _ = _ := by simpa only [DividedPowerScheme.Hom.comp_hom] using h⟩
  map_one' := Subtype.ext <| funext fun A => map_one (Scheme.Γ.map A.unop.obj.toBase.hom.op).hom
  map_mul' a b :=
    Subtype.ext <| funext fun A => map_mul (Scheme.Γ.map A.unop.obj.toBase.hom.op).hom a b
  map_zero' := Subtype.ext <| funext fun A => map_zero (Scheme.Γ.map A.unop.obj.toBase.hom.op).hom
  map_add' a b :=
    Subtype.ext <| funext fun A => map_add (Scheme.Γ.map A.unop.obj.toBase.hom.op).hom a b

/-- The section of `baseRingHom S a` on a thickening `A` is the pullback of `a` along the
structure map of `A` to the base. -/
@[simp]
theorem baseRingHom_apply_val (a : Γ(S.S.scheme, ⊤)) (A : (CrystallineThickening S)ᵒᵖ) :
    (baseRingHom S a).val A = (Scheme.Γ.map A.unop.obj.toBase.hom.op).hom a := rfl

/-- The rings of sections of the structure sheaf of the small crystalline site are commutative:
they are the rings of global sections of the ambient schemes.  This instance is not found through
`forget₂ CommRingCat RingCat`, so it is supplied, exactly as
`AlgebraicGeometry.Scheme.isMulCommutative_ringCatSheaf` is for a scheme. -/
instance isMulCommutative_structureSheaf (X : (CrystallineThickening S)ᵒᵖ) :
    IsMulCommutative ((structureSheaf S).obj.obj X) :=
  ⟨⟨fun a b =>
    mul_comm (G := Γ(X.unop.obj.thickening.target.scheme, ⊤)) a b⟩⟩

/-- **Multiplication by an element of the base ring `A = Γ(S, 𝒪_S)` on a sheaf of
`𝒪_{X/S}`-modules.**  The element acts through `baseRingHom`, section by section. -/
def baseSmul (a : Γ(S.S.scheme, ⊤)) (M : ModuleSheaf S) : M ⟶ M :=
  Stacks.Cohomology.SiteModules.globalSmul (structureSheaf S) (baseRingHom S a) M

/-- **The base ring `A = Γ(S, 𝒪_S)` acts on every sheaf of `𝒪_{X/S}`-modules by `𝒪_{X/S}`-linear
endomorphisms**, as a ring homomorphism `A ⟶ End M`.

This is the source of every `A`-linear structure in this file, and — because any additive functor
carries a ring map into `End M` to one into the endomorphisms of its value — it is also what puts
an `A`-action on the *abelian-valued* `Crystalline.GlobalCrystallineSituation.SmallSite.cohomology`
of the underlying abelian sheaf `(toAbelianSheaf S).obj M`.  So the two theories act by the same
scalars even where they are not identified; see the module docstring. -/
def baseSmulRingHom (M : ModuleSheaf S) : Γ(S.S.scheme, ⊤) →+* End M where
  toFun a := End.of (baseSmul S a M)
  map_one' := by
    ext1
    change baseSmul S 1 M = 𝟙 M
    rw [baseSmul, map_one]
    exact Stacks.Cohomology.SiteModules.globalSmul_one (structureSheaf S) M
  map_mul' a b := by
    ext1
    change baseSmul S (a * b) M = baseSmul S b M ≫ baseSmul S a M
    rw [baseSmul, baseSmul, baseSmul, mul_comm, map_mul]
    exact Stacks.Cohomology.SiteModules.globalSmul_mul (structureSheaf S)
      (baseRingHom S b) (baseRingHom S a) M
  map_zero' := by
    ext1
    change baseSmul S 0 M = 0
    rw [baseSmul, map_zero]
    exact Stacks.Cohomology.SiteModules.globalSmul_zero (structureSheaf S) M
  map_add' a b := by
    ext1
    change baseSmul S (a + b) M = baseSmul S a M + baseSmul S b M
    rw [baseSmul, baseSmul, baseSmul, map_add]
    exact Stacks.Cohomology.SiteModules.globalSmul_add (structureSheaf S)
      (baseRingHom S a) (baseRingHom S b) M

/-- An element of the base ring acts on the sections of a module over an object `(U, T, δ)` of
`Cris(X/S)` as its pullback to `Γ(T, 𝒪_T)`. -/
theorem baseSmul_val_app (a : Γ(S.S.scheme, ⊤)) (M : ModuleSheaf S)
    (X : (CrystallineThickening S)ᵒᵖ) (x : M.val.obj X) :
    (baseSmul S a M).val.app X x = (baseRingHom S a).val X • x :=
  Stacks.Cohomology.SiteModules.globalSmul_app (structureSheaf S) (baseRingHom S a) M X x

/-! ### Global sections -/

/-- **The global sections `Γ(Cris(X/S), M)` of a sheaf of `𝒪_{X/S}`-modules**, as a module over
the ring `Γ(Cris(X/S), 𝒪_{X/S})` of compatible sections of the structure sheaf. -/
abbrev moduleGlobalSections :
    ModuleSheaf S ⥤ ModuleCat.{u + 1} ↥(crystallineSectionRing S) :=
  Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u + 1} (structureSheaf S)

/-- **The global sections `Γ(Cris(X/S), M)` of a sheaf of `𝒪_{X/S}`-modules, as an `A`-module**,
the scalars restricted along `baseRingHom`.  This is the functor whose right derived functors are
the module-valued crystalline cohomology. -/
abbrev baseModuleGlobalSections : ModuleSheaf S ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  moduleGlobalSections S ⋙ ModuleCat.restrictScalars (baseRingHom S)

/-- Global sections of `M` over `Γ(Cris(X/S), 𝒪_{X/S})` are the compatible families of sections
of `M`. -/
theorem moduleGlobalSections_obj_carrier (M : ModuleSheaf S) :
    ((moduleGlobalSections S).obj M : Type (u + 1)) = M.sections := rfl

/-- Restriction of scalars along `baseRingHom` changes only the action: the underlying type of
`Γ(Cris(X/S), M)` as an `A`-module is still the compatible families of sections of `M`. -/
theorem baseModuleGlobalSections_obj_carrier (M : ModuleSheaf S) :
    ((baseModuleGlobalSections S).obj M : Type (u + 1)) = M.sections := rfl

/-! ### `H^j(Cris(X/S), -)` -/

/-- **The `j`-th module-valued crystalline cohomology functor `H^j(Cris(X/S), -)`**, the `j`-th
right derived functor of the `A`-module-valued global sections.  Its values are `A`-modules, which
is the form [Stacks, Tag 07MU], [Stacks, Tag 07MX], [Stacks, Tag 07MY] and [Stacks, Tag 07N5] are
stated in. -/
def moduleCohomologyFunctor (j : ℕ) :
    ModuleSheaf S ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  (baseModuleGlobalSections S).rightDerived j

/-- **The cohomology `H^j(Cris(X/S), M)` of a sheaf of `𝒪_{X/S}`-modules, as an `A`-module.** -/
abbrev moduleCohomology (M : ModuleSheaf S) (j : ℕ) : ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  (moduleCohomologyFunctor S j).obj M

/-- **The degree-zero comparison: global sections map to `H^0(Cris(X/S), -)`.**  This is
`CategoryTheory.Functor.toRightDerivedZero`, which exists for any additive functor; it is an
isomorphism exactly when `baseModuleGlobalSections` is left exact, which is not available at the
raised module universe (see the module docstring). -/
def toModuleCohomologyZero : baseModuleGlobalSections S ⟶ moduleCohomologyFunctor S 0 :=
  (baseModuleGlobalSections S).toRightDerivedZero

/-- The higher cohomology of an injective sheaf of `𝒪_{X/S}`-modules vanishes. -/
theorem isZero_moduleCohomology_of_injective (M : ModuleSheaf S) [Injective M] (j : ℕ) :
    IsZero (moduleCohomology S M (j + 1)) :=
  (baseModuleGlobalSections S).isZero_rightDerived_obj_injective_succ j M

/-! ### `RΓ(Cris(X/S), -)` -/

section Model

/-- **A derived category of the sheaves of `𝒪_{X/S}`-modules exists**, with its morphisms in
`Type (u + 2)`.  `CategoryTheory.HasDerivedCategory.standard` applies to any abelian category with
no smallness hypothesis, and places the morphisms of the localized category in the universe of the
objects of the category being localized, here `u + 2`. -/
@[instance_reducible]
def hasDerivedCategoryModuleSheaf : HasDerivedCategory.{u + 2} (ModuleSheaf S) :=
  HasDerivedCategory.standard _

/-- **A derived category of `A`-modules exists**, with its morphisms in `Type (u + 2)`.  This is
the target model for `derivedModuleGlobalSectionsFunctor`, so that `RΓ(Cris(X/S), -)` is an object
of `D⁺(Mod_A)`. -/
@[instance_reducible]
def hasDerivedCategoryModuleCat :
    HasDerivedCategory.{u + 2} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  HasDerivedCategory.standard _

end Model

section RGamma

variable [HasDerivedCategory.{w} (ModuleSheaf S)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **The derived global sections `RΓ(Cris(X/S), -)` of sheaves of `𝒪_{X/S}`-modules**, as a
functor between bounded below derived categories, landing in the derived category of `A`-modules.
It is the right derived functor of `baseModuleGlobalSections`, which is additive and has enough
injectives available on its source by `instEnoughInjectivesModuleSheaf`. -/
def derivedModuleGlobalSectionsFunctor :
    DerivedCategory.Plus (ModuleSheaf S) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (baseModuleGlobalSections S).rightDerivedFunctorPlus

/-- **`RΓ(Cris(X/S), M) ∈ D⁺(Mod_A)` for a single sheaf of `𝒪_{X/S}`-modules `M`**: the module
placed in degree zero, then derived global sections.  This is the object [Stacks, Tag 07MU],
[Stacks, Tag 07MX], [Stacks, Tag 07MY] and [Stacks, Tag 07N5] are statements about; its
cohomology objects are the graded modules `moduleCohomology`, by
`homologyDerivedModuleGlobalSectionsIso`. -/
def derivedModuleGlobalSections :
    ModuleSheaf S ⥤ DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0 ⋙ derivedModuleGlobalSectionsFunctor S

/-- Taking the degree-`j` cohomology of `RΓ(Cris(X/S), -)` is the `ℤ`-indexed right derived
functor of the `A`-module-valued global sections, by definition of the latter. -/
theorem derivedModuleGlobalSections_comp_homologyFunctor (j : ℤ) :
    derivedModuleGlobalSections S ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) j =
      (baseModuleGlobalSections S).rightDerivedPlus j :=
  rfl

/-- **The derived and the graded module-valued crystalline theories agree**:
`H^j(RΓ(Cris(X/S), M)) ≅ H^j(Cris(X/S), M)` as `A`-modules, naturally in `M`.

The cohomology of `RΓ` is the `ℤ`-indexed right derived functor of global sections, which agrees
with Mathlib's `ℕ`-indexed one by `Stacks.DerivedIndexing.rightDerivedIso`; the `ℕ`-indexed one is
`moduleCohomologyFunctor` by definition. -/
def homologyDerivedModuleGlobalSectionsIso (j : ℕ) :
    derivedModuleGlobalSections S ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ) ≅
      moduleCohomologyFunctor S j :=
  (Stacks.DerivedIndexing.rightDerivedIso (baseModuleGlobalSections S) j).symm

/-- `H^j(RΓ(Cris(X/S), M)) ≅ H^j(Cris(X/S), M)` at a fixed sheaf of `𝒪_{X/S}`-modules. -/
def homologyDerivedModuleGlobalSectionsIsoObj (M : ModuleSheaf S) (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
        ((derivedModuleGlobalSections S).obj M) ≅
      moduleCohomology S M j :=
  (homologyDerivedModuleGlobalSectionsIso S j).app M

/-- **`RΓ(Cris(X/S), M)` of an injective sheaf of `𝒪_{X/S}`-modules is concentrated in degree
zero.**  This is the derived-category form of `isZero_moduleCohomology_of_injective`. -/
theorem isZero_homology_derivedModuleGlobalSections_of_injective
    (M : ModuleSheaf S) [Injective M] (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) j).obj ((derivedModuleGlobalSections S).obj M)) :=
  Functor.isZero_rightDerivedPlus_obj_injective (baseModuleGlobalSections S) j hj M

end RGamma

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
