module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.FiniteLocallyFreeCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# Comparing the two module universes on the small crystalline site

The chapter carries sheaves of `𝒪_{X/S}`-modules on the small crystalline site at two different
module universes, and the predicates of [Stacks, Tag 07IS] and [Stacks, Tag 07IU] on one hand and
the cohomology functors on the other were, until this file, stated at different ones:

* the crystal and quasi-coherence predicates — `IsSheafCrystal`,
  `Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent`,
  `SheafOfModules.IsQuasicoherentOnSite` and
  `Crystalline.GlobalCrystallineSituation.SmallSite.IsFiniteLocallyFreeQuasicoherentCrystal` —
  are stated for `SheafOfModules.{u} (structureSheaf S)`, the module sections in `Type u`, the
  same universe as the sections of the structure sheaf;
* the cohomology — `Crystalline.GlobalCrystallineSituation.SmallSite.moduleCohomology` and
  `Crystalline.GlobalCrystallineSituation.SmallSite.derivedModuleGlobalSections` — is stated for
  `Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf`, that is
  `SheafOfModules.{u + 1} (structureSheaf S)`, the module sections in `Type (u + 1)`, because
  sheafification of `AddCommGrpCat.{u}`-valued presheaves on `Cris(X/S)` is unavailable.

So "a crystal in quasi-coherent `𝒪_{X/S}`-modules" and "the cohomology of a module" could not be
said of the same object.  This file closes that gap.

## Universes

The universe bookkeeping is the whole difficulty, so every object is placed explicitly.  For a
situation `S : GlobalCrystallineSituation.{u}`:

| object | universe |
| --- | --- |
| the objects of `Cris(X/S)`, i.e. `CrystallineThickening S` | `Type (u + 1)` |
| the morphisms of `Cris(X/S)` | `Type u` |
| the sections of the structure sheaf, i.e. `structureSheaf S` | `RingCat.{u}` |
| the opens of the ambient scheme `T` of an object | `Type u`, with morphisms in `Type u` |
| the restricted structure sheaf `𝒪_T`, i.e. `Thickening.ringRestrictionSheaf` | `RingCat.{u}` |
| the modules the **predicates** use, `SheafOfModules.{u} (structureSheaf S)` | `Type u` |
| the modules the **cohomology** is stated for, `ModuleSheaf S` | `Type (u + 1)` |
| the base ring `A = Γ(S, 𝒪_S)` | `Type u` |
| `H^j(Cris(X/S), -)` and the terms of `RΓ(Cris(X/S), -)` | `ModuleCat.{u + 1} A` |
| the morphisms of the derived categories | `Type (u + 2)` |

The route taken is the **universe-lifting comparison functor**
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULift`, which raises only the module
sections, from `Type u` to `Type (u + 1)`, leaving the site, the structure sheaf and the base ring
where they are.  It is `SheafOfModules.uliftForPresentationFunctor` at the universe parameters
`{u + 1, u, u, u, u + 1}` — site objects, site morphisms, ring sections, module sections, lift —
and its value on `F` has `ULift.{u + 1} (F(U, T, δ))` for its sections over `(U, T, δ)`.

With it, `H^j(Cris(X/S), F)` and `RΓ(Cris(X/S), F)` are available for a module `F` at the
*predicates'* universe, as
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULiftCohomology` and
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleULiftDerivedGlobalSections`, and the
hypotheses of [Stacks, Tag 07IS] and [Stacks, Tag 07IU] are the existing predicates applied to
`F` itself, unchanged and unweakened.

Three of the four predicates are *also* restated at the raised universe, in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf`, so that they can be said of a
`ModuleSheaf S` directly; the fourth, the crystal condition, provably cannot be — see *What is
and is not proved*.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `moduleULift` — **the universe-lifting comparison functor**
  `SheafOfModules.{u} (structureSheaf S) ⥤ ModuleSheaf S`.
* `moduleULiftCohomologyFunctor` and `moduleULiftCohomology` — **`H^j(Cris(X/S), F)` as an
  `A`-module, for `F` a sheaf of `𝒪_{X/S}`-modules at the universe the chapter's predicates are
  stated at.**
* `moduleULiftDerivedGlobalSectionsFunctor` and `moduleULiftDerivedGlobalSections` —
  **`RΓ(Cris(X/S), F) ∈ D⁺(Mod_A)` for such an `F`.**
* `ModuleSheaf.IsLocallyQuasiCoherent` — [Stacks, Tag 07IS] local quasi-coherence, restated for
  `SheafOfModules.{u + 1} (structureSheaf S)`.
* `ModuleSheaf.IsFiniteLocallyFreeQuasicoherentCrystal` — [Stacks, Tag 07IU], crystals in finite
  locally free modules, restated for `SheafOfModules.{u + 1} (structureSheaf S)`.

Quasi-coherence and finite local freeness need *no* restatement: `SheafOfModules`
`.IsQuasicoherentOnSite` and `SheafOfModules.IsFiniteLocallyFreeOnSite` are already polymorphic
in the module universe, with the site, the ring and the module sections in independent universes,
so they apply to a `ModuleSheaf S` as they stand.

## Main results

* `toAbelianSheaf_obj_moduleULift` — **the abelian sheaf underlying the lift of `F` is the
  abelian sheaf `Crystalline.GlobalCrystallineSituation.SmallSite.abelianSheaf` of `F` that the
  chapter's abelian-valued statements already use**, by `rfl`.  This is what makes the lift the
  right avatar of `F`: the module-valued `H^j(Cris(X/S), moduleULift F)` and the abelian-valued
  `Crystalline.GlobalCrystallineSituation.SmallSite.cohomology S (abelianSheaf F) j` of
  [Stacks, Tag 07LF] are statements about one and the same abelian sheaf.
* `isQuasicoherentOnSite_moduleULift`, `isLocallyQuasiCoherent_moduleULift`,
  `isFiniteLocallyFreeOnSite_moduleULift` and
  `isFiniteLocallyFreeQuasicoherentCrystal_moduleULift` — **the three transferable
  predicates transfer along the comparison functor**, so a module satisfying them at the
  predicates' universe satisfies the restated form at the cohomology's universe.
* `moduleULift` is full and faithful, `full_moduleULift` and `faithful_moduleULift`.
* `homologyModuleULiftDerivedGlobalSectionsIso` — `H^j(RΓ(Cris(X/S), F)) ≅ H^j(Cris(X/S), F)`
  for `F` at the predicates' universe, the lifted form of
  `Crystalline.GlobalCrystallineSituation.SmallSite.homologyDerivedModuleGlobalSectionsIso`.
* `isFiniteFree_uliftForPresentation` — finite freeness of a sheaf of modules on any site is
  carried by a universe lift of its sections.  Stated generically; it is the ingredient the
  finite-locally-free transfer needs and the library did not have it.

## What is and is not proved

What is proved is that `H^i(Cris(X/S), F) = 0` **is now a well-formed Lean statement for `F` a
crystal in quasi-coherent `𝒪_{X/S}`-modules**: the hypothesis is
`SheafOfModules.IsQuasicoherentOnSite F` together with
`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal F` for
`F : SheafOfModules.{u} (structureSheaf S)` — the library's predicates, verbatim — and the
conclusion is `CategoryTheory.Limits.IsZero (moduleULiftCohomology S F i)`.  Likewise
`RΓ(Cris(X/S), F)` is `moduleULiftDerivedGlobalSections S F`, an object of `D⁺(Mod_A)`, so the
perfectness assertions have an object to be about.  Nothing below asserts any such vanishing or
perfectness; this file supplies only the objects and the predicate transfers.

What is **not** proved:

* **The crystal condition cannot be restated at the raised module universe**, and this is a hard
  obstruction, not an omission.  `IsSheafCrystal` is the assertion that the comparison maps
  `c_f : f^* F_{T'} ⟶ F_T` of *sheaves* of `𝒪_T`-modules are isomorphisms, and `f^*` is
  `SheafOfModules.pullback`, which is defined as a left adjoint of
  `SheafOfModules.pushforward` and exists only where that adjoint does.  The existence is
  `PresheafOfModules.pullbackObjIsDefined_eq_top`, whose proof presents a presheaf of modules as
  a cokernel of a map between coproducts of the free presheaves on Yoneda presheaves,
  `PresheafOfModules.free` being available only with the module sections in the universe of the
  *site* and of the *coefficient rings*; accordingly that instance is stated for
  `{C D : Type u} [SmallCategory C] [SmallCategory D]`, `R : Dᵒᵖ ⥤ RingCat.{u}` and
  `PresheafOfModules.{u}`, with all three universes equal.  Here the site is the Zariski site of
  the ambient scheme `T` of an object, whose opens and whose morphisms are in `Type u`, and the
  coefficient sheaf is `Thickening.ringRestrictionSheaf`, with sections in `Type u`; so the
  pullback exists at module universe `u` and at no other.  Raising the opens to `Type (u + 1)`
  would force the rings up with them, and the crystal condition would then be a condition on
  modules over a universe lift of `𝒪_T` rather than over `𝒪_T` — a different statement, which is
  the trade the module documentation of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ModuleCohomology.lean` already rejects for
  `𝒪_{X/S}`.  This is why the comparison *functor* is the route taken and not the restatement of
  every predicate: the crystal condition has to stay at the module universe `u`, and
  `moduleULift` is what lets the cohomology be taken of an object it applies to.
* **The comparison functor is not proved exact**, so no comparison of the cohomology of `F` with
  the cohomology of `moduleULift F` is claimed — indeed the former is not defined.  Exactness of
  `SheafOfModules.uliftForPresentationFunctor` is available as
  `SheafOfModules.preservesFiniteLimits_uliftForPresentationFunctor` together with
  `SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor'`, but both assume
  `HasSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat.{u}` on the site, which on
  `Cris(X/S)` is exactly what is unavailable and is the reason the module universe had to be
  raised in the first place.  What is proved instead, and is what the vanishing statements need,
  is that the lift is fully faithful and that its underlying abelian sheaf is the one the
  chapter's abelian-valued theory already uses: universe lifting of abelian groups is an
  equivalence onto a full subcategory and carries the zero group to the zero group, so a
  vanishing statement about the lift says what it should, exactly as recorded in the module
  documentation of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineCohomology.lean`.
* **No comparison with the big crystalline site** is made.  The predicates on `CRIS(X/S)` are
  stated for `SheafOfModules.{u} (crystallineStructureSheaf S)`, and
  `Crystalline.GlobalCrystallineSituation.SmallSite.restrictSheafOfModules` carries a module
  there to one on `Cris(X/S)` at the same universe, so `moduleULift` composed with it serves the
  big site as well; that composite is not named here, having no consumer.
* Nothing here carries a `@[stacks]` attribute.  The universe comparison is infrastructure, like
  the module-valued cohomology it serves; the numbered assertions of the source that consume it —
  [Stacks, Tag 07MR], [Stacks, Tag 07MX], [Stacks, Tag 07MY] — need Krull dimension, the Zariski
  comparison and a derived tensor product besides, and are stated nowhere in the library.

## References

* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe w w' u₁ v₁ r m t u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Finite freeness is carried by a universe lift of the sections

This is generic: it is about an arbitrary sheaf of modules on an arbitrary site, and is recorded
here because it is what `isFiniteLocallyFreeOnSite_moduleULift` needs and the library does not
have it. -/

/-- **Finite freeness of a sheaf of modules is carried by a universe lift of its sections.**
`SheafOfModules.IsFiniteFree` compares the module with a finite free model through linear
equivalences natural in the object of the site, and the model lives in the universe of the
coefficient rings, so it is left untouched: the equivalences are composed with
`ULift.moduleEquiv` instead. -/
theorem isFiniteFree_uliftForPresentation {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}} {F : SheafOfModules.{m} R}
    (h : SheafOfModules.IsFiniteFree R F) :
    SheafOfModules.IsFiniteFree R (SheafOfModules.uliftForPresentation.{u₁, v₁, r, m, t} F) := by
  obtain ⟨n, M, ι, hι, e, he⟩ := h
  exact ⟨n, M, ι, hι, fun U ↦ (e U).trans ULift.moduleEquiv.symm,
    fun g x ↦ congrArg ULift.up (he g x)⟩

/-! ### The comparison functor -/

variable (S : GlobalCrystallineSituation.{u})

/-- **The universe-lifting comparison functor for sheaves of `𝒪_{X/S}`-modules on the small
crystalline site**, from the module universe `u` at which the chapter's crystal and
quasi-coherence predicates are stated to the module universe `u + 1` at which its cohomology is.
Only the module sections move: the site, the structure sheaf `𝒪_{X/S}` and the base ring
`A = Γ(S, 𝒪_S)` are unchanged, and the sections of the value over an object `(U, T, δ)` are
`ULift.{u + 1} (F(U, T, δ))`.

The universe parameters of `SheafOfModules.uliftForPresentationFunctor` are, in order, the
objects and the morphisms of the site, the sections of the coefficient ring sheaf, the sections
of the module and the universe lifted into: `u + 1`, `u`, `u`, `u`, `u + 1`. -/
def moduleULift : SheafOfModules.{u} (structureSheaf S) ⥤ ModuleSheaf S :=
  SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u + 1}

/-- The sections of the lift of `F` over an object of `Cris(X/S)` are the universe lift of the
sections of `F` there. -/
theorem moduleULift_obj_val_obj_carrier (F : SheafOfModules.{u} (structureSheaf S))
    (A : (CrystallineThickening S)ᵒᵖ) :
    (((moduleULift S).obj F).val.obj A : Type (u + 1)) = ULift.{u + 1} (F.val.obj A) := rfl

/-- The lift of a morphism `f : F ⟶ G` acts on the lifted sections over an object of
`Cris(X/S)` as `f` acts on the underlying sections. -/
@[simp]
theorem moduleULift_map_val_app_apply {F G : SheafOfModules.{u} (structureSheaf S)} (f : F ⟶ G)
    (A : (CrystallineThickening S)ᵒᵖ) (x : ULift.{u + 1} (F.val.obj A)) :
    ((moduleULift S).map f).val.app A x = ULift.up (f.val.app A x.down) := rfl

/-- **The comparison functor is full.**  A morphism between the lifts is the lift of a morphism,
`ULift` being an equivalence onto a full subcategory. -/
instance full_moduleULift : (moduleULift S).Full :=
  SheafOfModules.full_uliftForPresentationFunctor (structureSheaf S)

/-- **The comparison functor is faithful**: two morphisms with the same lift are equal. -/
instance faithful_moduleULift : (moduleULift S).Faithful :=
  SheafOfModules.faithful_uliftForPresentationFunctor (structureSheaf S)

/-- **The abelian sheaf underlying the lift of `F` is the abelian sheaf of `F` that the chapter's
abelian-valued statements already use.**  Both are the underlying abelian presheaf of `F`
composed with `AddCommGrpCat.uliftFunctor`, so the module-valued cohomology of `moduleULift F`
and the abelian-valued `Crystalline.GlobalCrystallineSituation.SmallSite.cohomology` of
`Crystalline.GlobalCrystallineSituation.SmallSite.abelianSheaf F` — the sheaf whose vanishing
[Stacks, Tag 07LF] asserts — are statements about one and the same abelian sheaf on
`Cris(X/S)`. -/
theorem toAbelianSheaf_obj_moduleULift (F : SheafOfModules.{u} (structureSheaf S)) :
    (toAbelianSheaf S).obj ((moduleULift S).obj F) = abelianSheaf F := rfl

/-! ### `H^j(Cris(X/S), F)` for a module at the predicates' universe -/

/-- **The `j`-th module-valued crystalline cohomology of a sheaf of `𝒪_{X/S}`-modules at the
module universe `u`**, as a functor: lift the module, then take
`Crystalline.GlobalCrystallineSituation.SmallSite.moduleCohomologyFunctor`.  Its values are
`A`-modules for `A = Γ(S, 𝒪_S)`. -/
def moduleULiftCohomologyFunctor (j : ℕ) :
    SheafOfModules.{u} (structureSheaf S) ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  moduleULift S ⋙ moduleCohomologyFunctor S j

/-- **`H^j(Cris(X/S), F)` as an `A`-module, for `F` a sheaf of `𝒪_{X/S}`-modules at the universe
the chapter's crystal and quasi-coherence predicates are stated at.**  This is the object whose
vanishing [Stacks, Tag 07MR] asserts. -/
abbrev moduleULiftCohomology (F : SheafOfModules.{u} (structureSheaf S)) (j : ℕ) :
    ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  (moduleULiftCohomologyFunctor S j).obj F

/-- The cohomology of `F` is the cohomology of its lift, by definition of
`moduleULiftCohomologyFunctor`. -/
theorem moduleULiftCohomology_eq (F : SheafOfModules.{u} (structureSheaf S)) (j : ℕ) :
    moduleULiftCohomology S F j = moduleCohomology S ((moduleULift S).obj F) j := rfl

/-- The higher cohomology of a sheaf of `𝒪_{X/S}`-modules whose lift is injective vanishes. -/
theorem isZero_moduleULiftCohomology_of_injective
    (F : SheafOfModules.{u} (structureSheaf S)) [Injective ((moduleULift S).obj F)] (j : ℕ) :
    IsZero (moduleULiftCohomology S F (j + 1)) :=
  isZero_moduleCohomology_of_injective S _ j

/-! ### `RΓ(Cris(X/S), F)` for a module at the predicates' universe -/

section RGamma

variable [HasDerivedCategory.{w} (ModuleSheaf S)]
  [HasDerivedCategory.{w'} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **The derived global sections `RΓ(Cris(X/S), -)` of sheaves of `𝒪_{X/S}`-modules at the
module universe `u`**, landing in the bounded below derived category of `A`-modules: lift the
module, then apply
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedModuleGlobalSectionsFunctor`. -/
def moduleULiftDerivedGlobalSectionsFunctor :
    SheafOfModules.{u} (structureSheaf S) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  moduleULift S ⋙ derivedModuleGlobalSections S

/-- **`RΓ(Cris(X/S), F) ∈ D⁺(Mod_A)` for `F` a sheaf of `𝒪_{X/S}`-modules at the universe the
chapter's crystal and quasi-coherence predicates are stated at.**  This is the object
[Stacks, Tag 07MX] and [Stacks, Tag 07MY] assert to be perfect. -/
abbrev moduleULiftDerivedGlobalSections (F : SheafOfModules.{u} (structureSheaf S)) :
    DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  (moduleULiftDerivedGlobalSectionsFunctor S).obj F

/-- **`H^j(RΓ(Cris(X/S), F)) ≅ H^j(Cris(X/S), F)` as `A`-modules**, for `F` at the predicates'
universe: the derived and the graded theories agree there because they agree at the raised
universe, which is
`Crystalline.GlobalCrystallineSituation.SmallSite.homologyDerivedModuleGlobalSectionsIsoObj`. -/
def homologyModuleULiftDerivedGlobalSectionsIso (F : SheafOfModules.{u} (structureSheaf S))
    (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) (j : ℤ)).obj
        (moduleULiftDerivedGlobalSections S F) ≅
      moduleULiftCohomology S F j :=
  homologyDerivedModuleGlobalSectionsIsoObj S ((moduleULift S).obj F) j

end RGamma

/-! ### The predicates at the raised module universe

`SheafOfModules.IsQuasicoherentOnSite` and `SheafOfModules.IsFiniteLocallyFreeOnSite` are already
polymorphic in the module universe and are not restated. -/

namespace ModuleSheaf

variable {S}

/-- **Stacks Project, Tag 07IS, at the raised module universe.**  A sheaf of `𝒪_{X/S}`-modules on
the small crystalline site *with its sections in `Type (u + 1)`* is *locally quasi-coherent* when
for every object `(U, T, δ)` of `Cris(X/S)` the restriction `F_T` is a quasi-coherent
`𝒪_T`-module.  This is the transcription of
`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent`, which is stated for
`SheafOfModules.{u} (structureSheaf S)`; nothing but the module universe changes, the restriction
being a pushforward of presheaves of modules and `SheafOfModules.IsQuasicoherentOnSite` being
polymorphic in the module universe.

The restricted module is a module over the restriction of the structure sheaf of the *big*
crystalline site to the ambient scheme of the underlying object, that being the very same
presheaf of rings, exactly as in the unlifted definition. -/
def IsLocallyQuasiCoherent (M : SmallSite.ModuleSheaf S) : Prop :=
  ∀ A : CrystallineThickening S,
    ∃ h : Presheaf.IsSheaf (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      ((PresheafOfModules.pushforward₀
          (ObjectProperty.lift (Thickening.IsCrystalline (S := S)) A.obj.restrictOpenFunctor
            fun W ↦ Thickening.isCrystalline_restrictOpen A.property W)
          (crisRing S)).obj (M.val : PresheafOfModules.{u + 1} (crisRing S))).presheaf,
      SheafOfModules.IsQuasicoherentOnSite
        (⟨(PresheafOfModules.pushforward₀
              (ObjectProperty.lift (Thickening.IsCrystalline (S := S)) A.obj.restrictOpenFunctor
                fun W ↦ Thickening.isCrystalline_restrictOpen A.property W)
              (crisRing S)).obj (M.val : PresheafOfModules.{u + 1} (crisRing S)), h⟩ :
          SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf A.obj))

/-- **Stacks Project, Tag 07IU, at the raised module universe.**  A *crystal in finite locally
free modules* on the small crystalline site, for a sheaf of `𝒪_{X/S}`-modules with its sections
in `Type (u + 1)`: quasi-coherent, which is condition (1) of [Stacks, Tag 07IT] and is what it is
for the module to be a crystal in quasi-coherent modules, and finite locally free.  This is the
transcription of
`Crystalline.GlobalCrystallineSituation.SmallSite.IsFiniteLocallyFreeQuasicoherentCrystal`; both
conjuncts are the general predicates for a sheaf of modules on a site and are already polymorphic
in the module universe, so only the universe of the module changes. -/
structure IsFiniteLocallyFreeQuasicoherentCrystal (M : SmallSite.ModuleSheaf S) : Prop where
  /-- The module is quasi-coherent, which is what it is for it to be a crystal in quasi-coherent
  modules. -/
  isQuasicoherentOnSite : M.IsQuasicoherentOnSite
  /-- The module is finite locally free. -/
  isFiniteLocallyFree : SheafOfModules.IsFiniteLocallyFreeOnSite M

end ModuleSheaf

/-! ### Transfer of the predicates along the comparison functor -/

variable {S}

/-- **Quasi-coherence transfers along the comparison functor.**  Raising the universe of the
sections commutes with restriction to a slice site, so the covering on whose members the module
is globally presented serves for the lift as well; this is
`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`. -/
theorem isQuasicoherentOnSite_moduleULift {F : SheafOfModules.{u} (structureSheaf S)}
    (h : F.IsQuasicoherentOnSite) : ((moduleULift S).obj F).IsQuasicoherentOnSite :=
  SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{u + 1, u, u, u, u + 1} h

/-- **Finite local freeness transfers along the comparison functor.**  On the members of a
covering on which `F` is finite free, the lift is finite free with the same finite free model,
by `isFiniteFree_uliftForPresentation`. -/
theorem isFiniteLocallyFreeOnSite_moduleULift {F : SheafOfModules.{u} (structureSheaf S)}
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    SheafOfModules.IsFiniteLocallyFreeOnSite ((moduleULift S).obj F) := by
  intro U
  obtain ⟨I, V, f, hcover, hfree⟩ := h U
  exact ⟨I, V, f, hcover,
    fun i ↦ isFiniteFree_uliftForPresentation.{u + 1, u, u, u, u + 1} (hfree i)⟩

/-- **Local quasi-coherence transfers along the comparison functor.**  The restriction to the
ambient scheme of an object of the lift of `F` *is* the universe lift of the restriction of `F`,
the two being the same presheaf of modules, so the quasi-coherence of the restriction is carried
across by `SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'` on the Zariski site of the
ambient scheme. -/
theorem isLocallyQuasiCoherent_moduleULift
    {F : SheafOfModules.{u} (structureSheaf S)} (h : IsLocallyQuasiCoherent F) :
    ModuleSheaf.IsLocallyQuasiCoherent ((moduleULift S).obj F) := by
  intro A
  obtain ⟨hsh, hqc⟩ := h A
  exact ⟨(SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
      (⟨_, hsh⟩ : SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj))).isSheaf,
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{u, u, u, u, u + 1} hqc⟩

/-- **Being a crystal in finite locally free modules transfers along the comparison functor**, so
the hypothesis of [Stacks, Tag 07MX] and [Stacks, Tag 07MY] on a module at the predicates'
universe gives the restated hypothesis on its lift, the module whose
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedModuleGlobalSections` those remarks
assert to be perfect. -/
theorem isFiniteLocallyFreeQuasicoherentCrystal_moduleULift
    {F : SheafOfModules.{u} (structureSheaf S)}
    (h : IsFiniteLocallyFreeQuasicoherentCrystal F) :
    ModuleSheaf.IsFiniteLocallyFreeQuasicoherentCrystal ((moduleULift S).obj F) where
  isQuasicoherentOnSite := isQuasicoherentOnSite_moduleULift h.isQuasicoherentOnSite
  isFiniteLocallyFree := isFiniteLocallyFreeOnSite_moduleULift h.isFiniteLocallyFree

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
