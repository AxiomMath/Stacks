module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology

/-!
# Derived global sections across the inclusion `i : Cris(X/S) ⟶ CRIS(X/S)`, at module coefficients

Fix a global crystalline situation `(p, (S, I, γ), X)` and let
`i : Cris(X/S) ⥤ CRIS(X/S)` be the inclusion of the small crystalline site into the big one,
which is fully faithful, continuous and cocontinuous ([Stacks, Tag 07IJ]).  This file proves, for
a sheaf `M` of `𝒪_{X/S}`-modules on `Cris(X/S)`,

`RΓ(Cris(X/S), M) ≅ RΓ(CRIS(X/S), R i_* M)`,

in the bounded below derived categories of `A`-modules, `A = Γ(S, 𝒪_S)`; the comparison is
assembled from its two components, each proved separately:

1. **`i_*` on modules preserves injective objects**
   (`preservesInjectiveObjects_moduleDirectImageι`);
2. **`Γ(CRIS(X/S), i_* M) ≅ Γ(Cris(X/S), M)`**, `A`-linearly and naturally in `M`
   (`moduleDirectImageιGlobalSectionsIso`).

## Which leg of the retraction this is, and why the other one is closed

The inclusion sits in an adjoint triple `i_! ⊣ i^{-1} ⊣ i_*` on sheaves of modules.  Three routes
to the first arrow of [Stacks, Tag 07N5] run through the left-hand adjunction, and all three are
**false**: they need the module-level lower shriek `i_!` to be exact, and
`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LowerShriekNotLeftExact.lean` exhibits a functor of
sites that is continuous, cocontinuous, fully faithful and final, whose image covers the target
site, with the identity structure map — every formal property this inclusion has — and whose
module-level lower shriek does not preserve the monomorphism `𝟙 + 𝟙` of the structure sheaf.
"`i^{-1}` preserves injectives" is equivalent to exactness of `i_!`, so it is closed too; see the
module documentation of `SmallSite/LowerShriekModules.lean`.

What this file uses is the **right-hand** adjunction, and the asymmetry is the whole point:
`i^{-1}` on sheaves of modules is restriction along `i.op` with no extension of scalars, so it is
exact *unconditionally* (`preservesFiniteLimits_moduleRestrictι`), and therefore its right adjoint
`i_*` preserves injective objects.  No flatness, no affineness, no hypothesis on the situation.

## How the two components are proved

`i_*` is `Stacks.SheafOfModules.directImage`, the pointwise right Kan extension along `i.op` of the
underlying presheaf of modules, which is a sheaf because `i` is cocontinuous; `i^{-1}` is
`Stacks.SheafOfModules.pushforward₀`, and `SheafOfModules.pushforward₀DirectImageAdjunction` is the
adjunction between them.  Both land in the chapter's own categories
`Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf` and `...BigModuleSheaf`, with no
universe lift of the structure sheaf: the ring-universe detour of
`SmallSite/CrisModuleDirectImage.lean` is needed only because
`Stacks.SheafOfModules.pushforwardCocontinuous` builds the Kan extension at `RingCat`-valued
coefficients, and the construction used here forms it on presheaves of modules instead.

Component 1 is then [Stacks, Tag 015Z]: a right adjoint whose left adjoint preserves monomorphisms
preserves injective objects.

Component 2 factors through the counit.  `i` is fully faithful, so the counit `i^{-1}i_* ⟶ id` is
invertible (`moduleDirectImageιCounitIso`, from
`SheafOfModules.isIso_pushforward0DirectImageAdjunction_counit`), and it remains to compare
`Γ(CRIS(X/S), N)` with `Γ(Cris(X/S), i^{-1}N)` for every sheaf of modules `N` on the big site.
That comparison is *restriction of a compatible family of sections*, `restrictSections`, and it is
bijective — `restrictSections_bijective` — for exactly the two reasons the abelian statement
`...SmallSite.smallRestrictionGlobalSectionsIso` has: the objects of `Cris(X/S)` cover the final
object of the topos of `CRIS(X/S)` (`...CrystallineThickening.coversTop_ι`), which gives
separatedness through `CategoryTheory.GrothendieckTopology.CoversTop.sections_ext`; and the objects
of `Cris(X/S)` under a fixed object of `CRIS(X/S)` form a cofiltered-or-empty category
(`...SmallSite.isCofilteredOrEmpty_structuredArrow_ι`, [Stacks, Tag 07I9]), which makes the family
of restrictions compatible, so that
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible.section_` glues it.  Both steps are
run on the sheaf of *types* underlying `N`, which is a sheaf by
`CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf`.  The map is `A`-linear because the two base
scalars agree along the inclusion, `bigBaseRingHom_val_ι`, which holds on the nose.

The assembly is [Stacks, Tag 015M] in the form
`Stacks.Cohomology.DerivedPushforwardSections.compIso`: `i_*` carries an injective module to an
injective module, and an injective object is right acyclic for any additive functor
(`CategoryTheory.Functor.rightAcyclic_of_injective`), so no left exactness of the module-valued
global sections is needed here.  It is available where it is needed:
`...SmallSite.preservesFiniteLimits_baseModuleGlobalSections` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/VanishingTransfer.lean` gets it from the
identification of the module-valued global sections with the abelian-valued ones, which are a
right adjoint.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `moduleRestrictι` — `i^{-1} : Mod(𝒪_{X/S} on CRIS(X/S)) ⥤ Mod(𝒪_{X/S} on Cris(X/S))`.
* `moduleDirectImageι` — **`i_* : Mod(𝒪_{X/S} on Cris(X/S)) ⥤ Mod(𝒪_{X/S} on CRIS(X/S))`**.
* `moduleDirectImageιAdjunction` — `i^{-1} ⊣ i_*` on sheaves of modules.
* `bigCrystallineSectionRing`, `bigBaseRingHom`, `bigModuleGlobalSections` and
  `bigBaseModuleGlobalSections` — `Γ(CRIS(X/S), 𝒪_{X/S})`, the action of `A = Γ(S, 𝒪_S)` on it,
  and the global sections of a sheaf of modules on the big site over each of the two rings.
* `restrictSections` — restriction of a global section along the inclusion.
* `derivedBigModuleGlobalSectionsFunctor` and `derivedModuleDirectImageι` —
  `RΓ(CRIS(X/S), -)` and `R i_*` at module coefficients.

## Main results

* `preservesFiniteLimits_moduleRestrictι` — **`i^{-1}` on modules is left exact**, with no
  hypothesis; this is what the whole file turns on.
* `preservesInjectiveObjects_moduleDirectImageι` — **component (1): `i_*` on modules preserves
  injective objects.**
* `moduleDirectImageιCounitIso` — `i^{-1}i_* = id` on modules.
* `restrictSections_bijective` and `restrictModuleGlobalSectionsIso` —
  **`Γ(CRIS(X/S), N) ≅ Γ(Cris(X/S), i^{-1}N)`**, the module-level form of
  `...SmallSite.smallRestrictionGlobalSectionsIso`.
* `moduleDirectImageιGlobalSectionsIso` — **component (2): `Γ(CRIS(X/S), i_* M) ≅
  Γ(Cris(X/S), M)`.**
* `derivedModuleGlobalSectionsFunctorIsoDirectImage`, with its single-sheaf form
  `derivedModuleGlobalSectionsIsoDirectImage` and its single-object form
  `derivedModuleGlobalSectionsObjIsoDirectImage` — **the comparison of derived global sections
  across the inclusion, at module coefficients.**
* `moduleDirectImageι_obj_val_obj` — the sections of `i_* M` over an object of `CRIS(X/S)` are the
  compatible families of sections of `M` indexed by the objects of `Cris(X/S)` over it, so the
  construction is pinned down pointwise.

## What is and is not proved

What is proved is unconditional in the situation: no affineness, no quasi-coherence, no hypothesis
on `p` beyond those already in a `GlobalCrystallineSituation`, and no appeal to
[Stacks, Tag 07HP].  The comparison is of the derived functors of the chapter's own module-valued
global sections, `...SmallSite.baseModuleGlobalSections`, whose right derived functors are
`...SmallSite.moduleCohomologyFunctor`, the `A`-modules that [Stacks, Tag 07N5] is stated in terms
of.

The comparison running the *other* way across the retraction, namely

`RΓ(CRIS(X/S), F) ≅ RΓ(Cris(X/S), i^{-1}F)` for `F` a sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)`,

is **not** in this file.  What is here is its underived half,
`restrictModuleGlobalSectionsIso`.  Its derived half needs `Γ(Cris(X/S), -)`-acyclicity of
`i^{-1}I` for `I` an injective sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` — preservation of
injectives by `i^{-1}` would do and is closed, being equivalent to exactness of `i_!`, while
acyclicity itself is strictly weaker — and that acyclicity is
`...SmallSite.rightAcyclic_moduleRestrictι_obj` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleRestrictionAcyclicity.lean`, where the
derived comparison `...SmallSite.derivedRestrictModuleGlobalSectionsObjIso` is assembled from it
and from `restrictModuleGlobalSectionsIso`.  The route taken there uses no module-level `i_!`: it
crosses to abelian coefficients by [Stacks, Tag 03FD] on each of the two sites and runs Leray for
the retraction there, where clause (6) of [Stacks, Tag 07IJ] is proved.

Nothing here identifies the module-valued `i_*` with the abelian `...SmallSite.bigDirectImage` on
underlying abelian sheaves.  Both are right Kan extensions along `i.op`, but of different objects
— a presheaf of modules and a presheaf of abelian groups — so the identification is the canonical
comparison `PresheafOfModules.directImageRanIso` and not an equality; it is not needed for
anything below and is not stated.

**No `@[stacks]` attribute is placed.**  [Stacks, Tag 07IJ] is registered clause by clause in this
development, and no clause of it asserts the existence of a right adjoint to `i^{-1}` on sheaves of
modules; [Stacks, Tag 07N5] has no registration and two earlier ones were withdrawn as
over-claims, and the comparison proved here is not a clause of that tag either.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v₁ v₂ v₃ u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### `i^{-1}` and `i_*` on sheaves of modules -/

/-- **`i^{-1}` on sheaves of `𝒪_{X/S}`-modules**: restriction along the inclusion
`i : Cris(X/S) ⥤ CRIS(X/S)` of the small crystalline site into the big one.

This is `Stacks.SheafOfModules.pushforward₀`, the strict form of the restriction in which the
structure sheaf of the source is the inverse image of that of the target *on the nose* — which it
is here, `...SmallSite.inverseImageRing_eq_structureSheaf`, so no restriction of scalars occurs and
the sections are untouched.  It agrees with the chapter's `...SmallSite.crisRestrictModules` by
`crisRestrictModulesIsoModuleRestrictι`. -/
def moduleRestrictι : BigModuleSheaf S ⥤ ModuleSheaf S :=
  SheafOfModules.pushforward₀.{u, u} (CrystallineThickening.ι S) (smallTopology S) (topology S)
    (crystallineStructureSheaf S)

/-- **`i_*` on sheaves of `𝒪_{X/S}`-modules**, the direct image along the inclusion
`i : Cris(X/S) ⥤ CRIS(X/S)`.

It is `Stacks.SheafOfModules.directImage`: the underlying presheaf of modules is the pointwise
right Kan extension along `i.op`, whose value over an object of `CRIS(X/S)` is the module of
compatible families of sections of `M` indexed by the objects of `Cris(X/S)` over it
(`moduleDirectImageι_obj_val_obj`), and that presheaf is a sheaf because the inclusion is
cocontinuous.  Unlike `...SmallSite.bigModuleDirectImage` of
`SmallSite/CrisModuleDirectImage.lean` it needs no universe lift of the structure sheaf: the Kan
extension is formed on presheaves of modules, not on presheaves of rings. -/
def moduleDirectImageι : ModuleSheaf S ⥤ BigModuleSheaf S :=
  SheafOfModules.directImage.{u, u} (CrystallineThickening.ι S) (smallTopology S) (topology S)
    (crystallineStructureSheaf S)

/-- **`i^{-1} ⊣ i_*` on sheaves of `𝒪_{X/S}`-modules**, the right-hand adjunction of the adjoint
triple `i_! ⊣ i^{-1} ⊣ i_*`; the left-hand one is
`...SmallSite.moduleLowerShriekAdjunction`. -/
def moduleDirectImageιAdjunction : moduleRestrictι S ⊣ moduleDirectImageι S :=
  SheafOfModules.pushforward₀DirectImageAdjunction.{u, u} (CrystallineThickening.ι S)
    (smallTopology S) (topology S) (crystallineStructureSheaf S)

/-- **`i^{-1}` is the chapter's restriction of modules.**  `...SmallSite.crisRestrictModules` is
`SheafOfModules.pushforward` along the identity comparison of structure sheaves, which is the
strict restriction followed by restriction of scalars along an identity; the two differ by that
restriction of scalars and by nothing else. -/
def crisRestrictModulesIsoModuleRestrictι : crisRestrictModules.{u + 1} S ≅ moduleRestrictι S :=
  SheafOfModules.pushforwardIdIsoPushforward₀.{u, u} (CrystallineThickening.ι S)
    (smallTopology S) (topology S) (crystallineStructureSheaf S)

/-- `i^{-1}` on modules is additive: it leaves the sections alone, so addition of morphisms is
computed in the same groups on both sides. -/
instance additive_moduleRestrictι : (moduleRestrictι S).Additive where
  map_add := rfl

/-- **`i^{-1}` on sheaves of modules is left exact**, with no hypothesis whatever.  It is a direct
image of sheaves of modules along a continuous functor of sites, hence a right adjoint; this is
the left exact half of [Stacks, Tag 04BD](2), transported along
`crisRestrictModulesIsoModuleRestrictι`.

This is the asymmetry the file turns on: the *other* leg of the retraction, the module-level
`i_!`, is not left exact, and not for want of a proof — see the module documentation. -/
instance preservesFiniteLimits_moduleRestrictι : PreservesFiniteLimits (moduleRestrictι S) :=
  haveI := SheafOfModules.preservesFiniteLimits_pushforward.{u + 1} (crisInclusionStructureHom S)
  preservesFiniteLimits_of_natIso (crisRestrictModulesIsoModuleRestrictι S)

/-- `i_*` on modules is additive, being a right adjoint between additive categories. -/
instance additive_moduleDirectImageι : (moduleDirectImageι S).Additive :=
  (moduleDirectImageιAdjunction S).right_adjoint_additive

/-- **`i_*` on sheaves of `𝒪_{X/S}`-modules preserves injective objects.**  This is
[Stacks, Tag 015Z]: a right adjoint whose left adjoint preserves monomorphisms carries injective
objects to injective objects, and the left adjoint here is `i^{-1}`, which is left exact by
`preservesFiniteLimits_moduleRestrictι` and hence preserves monomorphisms.

It is the first component of the comparison of derived global sections across the inclusion, and
it is unconditional.  The analogous statement for `i^{-1}` is **false**, being equivalent to
exactness of the module-level `i_!`; see the module documentation. -/
theorem preservesInjectiveObjects_moduleDirectImageι :
    (moduleDirectImageι S).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (moduleDirectImageιAdjunction S)

/-- The counit of `i^{-1} ⊣ i_*` on modules is invertible, the inclusion of sites being fully
faithful: over an object of the image the index category of the right Kan extension has the
identity index as an initial object. -/
instance isIso_moduleDirectImageιAdjunction_counit :
    IsIso (moduleDirectImageιAdjunction S).counit :=
  SheafOfModules.isIso_pushforward0DirectImageAdjunction_counit.{u, u}
    (CrystallineThickening.ι S) (smallTopology S) (topology S) (crystallineStructureSheaf S)

/-- **`i^{-1}i_* = id` on sheaves of `𝒪_{X/S}`-modules**, the counit of `i^{-1} ⊣ i_*` as an
isomorphism of functors.  It is the counterpart of `...SmallSite`
`.isIso_moduleLowerShriekAdjunction_unit` on the other side of the adjoint triple, and the two are
equivalent to one another. -/
def moduleDirectImageιCounitIso :
    moduleDirectImageι S ⋙ moduleRestrictι S ≅ 𝟭 (ModuleSheaf S) :=
  asIso (moduleDirectImageιAdjunction S).counit

/-! ### Global sections of modules on the big crystalline site -/

/-- The ring `Γ(CRIS(X/S), 𝒪_{X/S})` of compatible families of sections of the structure sheaf of
the big crystalline site, the big-site twin of `...SmallSite.crystallineSectionRing`. -/
abbrev bigCrystallineSectionRing :=
  Stacks.Cohomology.SiteModules.GlobalSectionRing (crystallineStructureSheaf S)

/-- **The base ring `A = Γ(S, 𝒪_S)` acts on the big crystalline site**: the canonical ring map
`Γ(S, 𝒪_S) ⟶ Γ(CRIS(X/S), 𝒪_{X/S})` sends `a` to the family whose value at `(U, T, δ)` is the
pullback of `a` along the structure morphism `T ⟶ S`.  Compatibility of that family is
`...Thickening.Hom.base_naturality`.

This is `...SmallSite.baseRingHom` with the small site replaced by the big one, and the two agree
along the inclusion by `bigBaseRingHom_val_ι`. -/
def bigBaseRingHom : Γ(S.S.scheme, ⊤) →+* ↥(bigCrystallineSectionRing S) where
  toFun a :=
    ⟨fun A => (Scheme.Γ.map A.unop.toBase.hom.op).hom a, by
      intro A B f
      have h := congrArg
        (fun g : B.unop.thickening.target ⟶ S.S => (Scheme.Γ.map g.hom.op).hom a)
        f.unop.base_naturality
      change (Scheme.Γ.map f.unop.targetHom.hom.op).hom
          ((Scheme.Γ.map A.unop.toBase.hom.op).hom a) =
        (Scheme.Γ.map B.unop.toBase.hom.op).hom a
      calc
        _ = (Scheme.Γ.map (f.unop.targetHom.hom ≫ A.unop.toBase.hom).op).hom a := by
              rw [op_comp, Functor.map_comp]
              rfl
        _ = _ := by simpa only [DividedPowerScheme.Hom.comp_hom] using h⟩
  map_one' := Subtype.ext <| funext fun A => map_one (Scheme.Γ.map A.unop.toBase.hom.op).hom
  map_mul' a b := Subtype.ext <| funext fun A => map_mul (Scheme.Γ.map A.unop.toBase.hom.op).hom a b
  map_zero' := Subtype.ext <| funext fun A => map_zero (Scheme.Γ.map A.unop.toBase.hom.op).hom
  map_add' a b := Subtype.ext <| funext fun A => map_add (Scheme.Γ.map A.unop.toBase.hom.op).hom a b

/-- The value of the base scalar attached to `a` at an object of `CRIS(X/S)` is the pullback of
`a` along the structure morphism of its ambient scheme. -/
@[simp]
theorem bigBaseRingHom_apply_val (a : Γ(S.S.scheme, ⊤)) (A : (Thickening S)ᵒᵖ) :
    (bigBaseRingHom S a).val A = (Scheme.Γ.map A.unop.toBase.hom.op).hom a := rfl

/-- **The two base scalars agree along the inclusion**, on the nose: an object of `Cris(X/S)` and
its image in `CRIS(X/S)` have the same ambient scheme and the same structure morphism to `S`.
This is what makes restriction of global sections `A`-linear. -/
theorem bigBaseRingHom_val_ι (a : Γ(S.S.scheme, ⊤)) (A : (CrystallineThickening S)ᵒᵖ) :
    (bigBaseRingHom S a).val (op ((CrystallineThickening.ι S).obj A.unop)) =
      (baseRingHom S a).val A := rfl

/-- **The global sections `Γ(CRIS(X/S), N)` of a sheaf of `𝒪_{X/S}`-modules on the big crystalline
site**, as a module over `Γ(CRIS(X/S), 𝒪_{X/S})`. -/
abbrev bigModuleGlobalSections :
    BigModuleSheaf S ⥤ ModuleCat.{u + 1} ↥(bigCrystallineSectionRing S) :=
  Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u + 1}
    (crystallineStructureSheaf S)

/-- **`Γ(CRIS(X/S), N)` as an `A`-module**, the scalars restricted along `bigBaseRingHom`.  This is
the functor whose right derived functors the comparison below is about, and it is the big-site twin
of `...SmallSite.baseModuleGlobalSections`. -/
abbrev bigBaseModuleGlobalSections : BigModuleSheaf S ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  bigModuleGlobalSections S ⋙ ModuleCat.restrictScalars (bigBaseRingHom S)

/-! ### Restriction of global sections along the inclusion -/

/-- **The presheaf of sets of sections of a sheaf of modules on `CRIS(X/S)` is a sheaf.**  The
forgetful functor of abelian groups preserves limits of the size of the big crystalline site, so
this is `CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf`.  It is the form in which the covering
statement and the gluing lemma below consume the sheaf condition. -/
theorem isSheafType_bigModule (N : BigModuleSheaf S) :
    Presheaf.IsSheaf (topology S)
      (N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ N.isSheaf

/-- **Restriction of a global section along the inclusion**: a compatible family of sections of a
sheaf of modules on `CRIS(X/S)` read only at the objects of `Cris(X/S)`.  Compatibility is
inherited, the morphisms of `Cris(X/S)` being morphisms of `CRIS(X/S)`. -/
def restrictSections (N : BigModuleSheaf S) (x : N.sections) :
    ((moduleRestrictι S).obj N).sections :=
  ⟨fun A => x.val (op ((CrystallineThickening.ι S).obj A.unop)),
    fun f => x.property ((CrystallineThickening.ι S).map f.unop).op⟩

/-- **Restriction of global sections is injective.**  The objects of `Cris(X/S)` cover the final
object of the topos of `CRIS(X/S)` — `...CrystallineThickening.coversTop_ι`, the step
[Stacks, Tag 07IJ] omits in general — so two compatible families agreeing on them agree, by
`CategoryTheory.GrothendieckTopology.CoversTop.sections_ext`. -/
theorem restrictSections_injective (N : BigModuleSheaf S) :
    Function.Injective (restrictSections S N) := by
  intro x y hxy
  refine (CrystallineThickening.coversTop_ι S).sections_ext
    ⟨_, isSheafType_bigModule S N⟩ fun A => ?_
  exact congrArg (fun t : ((moduleRestrictι S).obj N).sections => t.val (op A)) hxy

/-- **Restriction of global sections is surjective.**  A compatible family of sections over
`Cris(X/S)` is a compatible family of elements on the objects of `Cris(X/S)` in the sense of
`CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`: two morphisms out of an object
of `CRIS(X/S)` to objects of `Cris(X/S)` factor through a common object of `Cris(X/S)`, by
`...SmallSite.isCofilteredOrEmpty_structuredArrow_ι`, which is [Stacks, Tag 07I9] in the form
[Stacks, Tag 00X6] uses it.  The covering `...CrystallineThickening.coversTop_ι` then amalgamates
the family to a section over all of `CRIS(X/S)`. -/
theorem restrictSections_surjective (N : BigModuleSheaf S) :
    Function.Surjective (restrictSections S N) := by
  intro t
  set F := N.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  have hcomp : (show Presheaf.FamilyOfElementsOnObjects F (CrystallineThickening.ι S).obj from
      fun A => t.val (op A)).IsCompatible := by
    intro Z i j f g
    obtain ⟨W, a, b, -⟩ := (isCofilteredOrEmpty_structuredArrow_ι S Z).cone_objs
      (StructuredArrow.mk f) (StructuredArrow.mk g)
    have hf' : W.hom ≫ (CrystallineThickening.ι S).map a.right = f := StructuredArrow.w a
    have hg' : W.hom ≫ (CrystallineThickening.ι S).map b.right = g := StructuredArrow.w b
    rw [← hf', ← hg', op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg _ ((t.property a.right.op).trans (t.property b.right.op).symm)
  exact ⟨hcomp.section_ (CrystallineThickening.coversTop_ι S) (isSheafType_bigModule S N),
    Subtype.ext <| funext fun A =>
      hcomp.section_apply (CrystallineThickening.coversTop_ι S) (isSheafType_bigModule S N) A.unop⟩

/-- **The global sections of a sheaf of modules on `CRIS(X/S)` are already computed over
`Cris(X/S)`:** restriction along the inclusion is bijective.  This is the module-level form of
`...SmallSite.isIso_limitPre_ι`, and like it the statement fails for presheaves, in general no
object of `Cris(X/S)` receiving a morphism from a given object of `CRIS(X/S)` at all. -/
theorem restrictSections_bijective (N : BigModuleSheaf S) :
    Function.Bijective (restrictSections S N) :=
  ⟨restrictSections_injective S N, restrictSections_surjective S N⟩

/-- Restriction of global sections is `A`-linear: the two base scalars agree along the inclusion
by `bigBaseRingHom_val_ι`, and the action on global sections is the sectionwise one. -/
def restrictSectionsLinearMap (N : BigModuleSheaf S) :
    ((bigBaseModuleGlobalSections S).obj N) →ₗ[Γ(S.S.scheme, ⊤)]
      ((baseModuleGlobalSections S).obj ((moduleRestrictι S).obj N)) where
  toFun := restrictSections S N
  map_add' _ _ := Subtype.ext <| funext fun _ => rfl
  map_smul' _ _ := Subtype.ext <| funext fun _ => rfl

/-- **`Γ(CRIS(X/S), N) ≅ Γ(Cris(X/S), i^{-1}N)` as `A`-modules**, at a fixed sheaf of modules on
the big crystalline site. -/
def restrictSectionsLinearEquiv (N : BigModuleSheaf S) :
    ((bigBaseModuleGlobalSections S).obj N) ≃ₗ[Γ(S.S.scheme, ⊤)]
      ((baseModuleGlobalSections S).obj ((moduleRestrictι S).obj N)) :=
  LinearEquiv.ofBijective (restrictSectionsLinearMap S N) (restrictSections_bijective S N)

/-- **`Γ(CRIS(X/S), N) ≅ Γ(Cris(X/S), i^{-1}N)`**, naturally in the sheaf of `𝒪_{X/S}`-modules `N`
on the big crystalline site and `A`-linearly: restricting to the small crystalline site loses no
global section.

This is the module-level form of `...SmallSite.smallRestrictionGlobalSectionsIso`, and it is the
underived half of the arrow of [Stacks, Tag 07N5] that is completed in
`SmallSite/ModuleRestrictionAcyclicity.lean`; see the module documentation. -/
def restrictModuleGlobalSectionsIso :
    bigBaseModuleGlobalSections S ≅ moduleRestrictι S ⋙ baseModuleGlobalSections S :=
  NatIso.ofComponents (fun N => (restrictSectionsLinearEquiv S N).toModuleIso)
    (by intros; ext; rfl)

/-- **`Γ(CRIS(X/S), i_* M) ≅ Γ(Cris(X/S), M)`**, naturally in the sheaf of `𝒪_{X/S}`-modules `M`
on the small crystalline site and `A`-linearly: the second component of the comparison of derived
global sections across the inclusion.

It is `restrictModuleGlobalSectionsIso` at `i_* M` followed by `i^{-1}i_* = id`, that is
`moduleDirectImageιCounitIso`. -/
def moduleDirectImageιGlobalSectionsIso :
    moduleDirectImageι S ⋙ bigBaseModuleGlobalSections S ≅ baseModuleGlobalSections S :=
  Functor.isoWhiskerLeft (moduleDirectImageι S) (restrictModuleGlobalSectionsIso S) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDirectImageιCounitIso S) (baseModuleGlobalSections S) ≪≫
    (baseModuleGlobalSections S).leftUnitor

/-! ### The comparison of derived global sections -/

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **A derived category of the sheaves of `𝒪_{X/S}`-modules on the big crystalline site exists**,
with its morphisms in `Type (u + 2)`; the big-site twin of
`...SmallSite.hasDerivedCategoryModuleSheaf`.  It is not registered as a global instance,
following the repository's convention for `HasDerivedCategory`. -/
@[instance_reducible]
def hasDerivedCategoryBigModuleSheaf : HasDerivedCategory.{u + 2} (BigModuleSheaf S) :=
  HasDerivedCategory.standard _

section Derived

variable [HasDerivedCategory.{v₁} (ModuleSheaf S)] [HasDerivedCategory.{v₂} (BigModuleSheaf S)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **`RΓ(CRIS(X/S), -)` on sheaves of `𝒪_{X/S}`-modules**, as a functor between bounded below
derived categories: the right derived functor of `bigBaseModuleGlobalSections`, which is additive
and has enough injectives available on its source by `...SmallSite`
`.instEnoughInjectivesBigModuleSheaf`. -/
def derivedBigModuleGlobalSectionsFunctor :
    DerivedCategory.Plus (BigModuleSheaf S) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (bigBaseModuleGlobalSections S).rightDerivedFunctorPlus

/-- **`R i_*` on sheaves of `𝒪_{X/S}`-modules**, the right derived functor of the direct image
along the inclusion. -/
def derivedModuleDirectImageι :
    DerivedCategory.Plus (ModuleSheaf S) ⥤ DerivedCategory.Plus (BigModuleSheaf S) :=
  (moduleDirectImageι S).rightDerivedFunctorPlus

omit [HasDerivedCategory (ModuleSheaf S)] in
/-- **`i_*` carries an injective sheaf of `𝒪_{X/S}`-modules to a `Γ(CRIS(X/S), -)`-acyclic one.**
It carries it to an *injective* sheaf of modules, by
`preservesInjectiveObjects_moduleDirectImageι`, and an injective object is right acyclic for any
additive functor whose bounded below right derived functor exists,
`CategoryTheory.Functor.rightAcyclic_of_injective`.

No left exactness of the global sections is needed here, which is why this holds before
`...SmallSite.preservesFiniteLimits_baseModuleGlobalSections` of `SmallSite/VanishingTransfer.lean`
is in scope. -/
theorem rightAcyclic_moduleDirectImageι_obj (I : ModuleSheaf S) (hI : Injective I) :
    (bigBaseModuleGlobalSections S).rightAcyclic ((moduleDirectImageι S).obj I) := by
  have : Injective I := hI
  have := preservesInjectiveObjects_moduleDirectImageι S
  have : Injective ((moduleDirectImageι S).obj I) :=
    (moduleDirectImageι S).injective_obj I
  exact Functor.rightAcyclic_of_injective _ _

/-- **The comparison of derived global sections across the inclusion, at module coefficients:**
`RΓ(Cris(X/S), -) ≅ R i_* ⋙ RΓ(CRIS(X/S), -)` as functors between bounded below derived
categories.

This is [Stacks, Tag 015M] for the two components proved above: the underived comparison
`moduleDirectImageιGlobalSectionsIso` identifies the source with the right derived functor of
`i_* ⋙ Γ(CRIS(X/S), -)`, and `rightAcyclic_moduleDirectImageι_obj` splits that derived functor
through `R i_*`. -/
def derivedModuleGlobalSectionsFunctorIsoDirectImage :
    (baseModuleGlobalSections S).rightDerivedFunctorPlus ≅
      derivedModuleDirectImageι S ⋙ derivedBigModuleGlobalSectionsFunctor S :=
  (Functor.rightDerivedFunctorPlusNatIso (moduleDirectImageιGlobalSectionsIso S)).symm ≪≫
    Stacks.Cohomology.DerivedPushforwardSections.compIso (moduleDirectImageι S)
      (bigBaseModuleGlobalSections S) (rightAcyclic_moduleDirectImageι_obj S)

/-- **`RΓ(Cris(X/S), M) ≅ RΓ(CRIS(X/S), R i_* M)`**, naturally in the sheaf of `𝒪_{X/S}`-modules
`M` placed in degree zero: the form in which the comparison is applied to a single module. -/
def derivedModuleGlobalSectionsIsoDirectImage :
    derivedModuleGlobalSections S ≅
      DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0 ⋙
        derivedModuleDirectImageι S ⋙ derivedBigModuleGlobalSectionsFunctor S :=
  Functor.isoWhiskerLeft _ (derivedModuleGlobalSectionsFunctorIsoDirectImage S)

/-- **`RΓ(Cris(X/S), M) ≅ RΓ(CRIS(X/S), R i_* M)`** at a fixed sheaf of `𝒪_{X/S}`-modules `M`. -/
def derivedModuleGlobalSectionsObjIsoDirectImage (M : ModuleSheaf S) :
    (derivedModuleGlobalSections S).obj M ≅
      (derivedBigModuleGlobalSectionsFunctor S).obj
        ((derivedModuleDirectImageι S).obj
          ((DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0).obj M)) :=
  (derivedModuleGlobalSectionsIsoDirectImage S).app M

end Derived

/-- **The sections of `i_* M` over an object of `CRIS(X/S)`** are the compatible families of
sections of `M` indexed by the objects of `Cris(X/S)` over it, so the construction is pinned down
pointwise and is not vacuous. -/
theorem moduleDirectImageι_obj_val_obj (M : ModuleSheaf S) (V : (Thickening S)ᵒᵖ) :
    (((moduleDirectImageι S).obj M).val.obj V : Type (u + 1)) =
      ↥(PresheafOfModules.directImageSections.{u, u} (CrystallineThickening.ι S)
        (crystallineStructureSheaf S).obj M.val V) :=
  rfl

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
