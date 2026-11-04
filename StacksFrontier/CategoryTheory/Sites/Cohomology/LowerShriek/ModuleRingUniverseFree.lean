module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ModuleDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtendScalarsAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 07AC for modules, with the structure sheaf's universe free of the module universe

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `O_D` be a sheaf of rings
on `D` and set `O_C = g^{-1} O_D`.  The generators of `Mod(O_C)` used by
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedExistence.lean` — direct sums of
`j_{U!} O_U`, spelled through `SheafOfModules.unit` — have their sections in the universe of the
sections of `O_C`, and generate only under a `Small` hypothesis on `C`.  That is one universe
too few for the lisse-étale and flat-fppf sites of **Stacks 0787**: their objects lie in
`Type (u+1)` and their morphisms in `Type u`, so the Čech computation of **Stacks 0D6X** forces
the module sections into `Type (u+1)`, while the structure sheaf of **Stacks 06TV** has its
sections in `Type u`.

This file supplies the generators, and the module-level acyclicity input of **Stacks 03FD** at
them, in the namespace `Stacks.Cohomology.DerivedLowerShriek.FreeRingUniverse`, with the ring
universe `r` a free variable and the module sections in `Type (max u₁ v₁ r t)`, a universe which
contains the objects of `C`, so that no smallness hypothesis is needed.  Nothing already on the
library is altered.

## Main definitions

* `...FreeRingUniverse.IsSumOfExtensionByZeroUnits`: the class of direct sums of the generators
  `j_{U!} O_U`, taken at the sheafified-free-module spelling
  `Stacks.SheafOfModules.extensionByZeroUnit`.  This is the one place where the spelling has to
  change: the spelling of
  `Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnit` is `SheafOfModules.pullback` applied
  to `SheafOfModules.unit (R.over U)`, and Mathlib's `SheafOfModules.unit` has its sections in
  the universe of the *ring*, so that spelling cannot be written at a larger module universe at
  all.
* `...FreeRingUniverse.sectionModuleObject`: the second spelling of `j_{U!} O_U`, the sheafified
  extension of scalars of the free abelian presheaf on the universe-lifted representable, whose
  corepresentation of sections over `U` is additive.

## Main results

* `...FreeRingUniverse.exists_epi_isSumOfExtensionByZeroUnits`: the generators generate.
* `...FreeRingUniverse.subsingleton_ext_extensionByZeroUnit_of_abelian`: **Stacks 03FD** at the
  generators.
These are consumed by `...FreeRingUniverse.lowerShriekModules_acyclic_of_abelian` in
`ModuleRingUniverseFreeDerived.lean`, **the acyclicity statement of Stacks 07AC for modules**.

## Implementation notes

The three ingredients that had to exist at split universes already do:

* `Stacks.SheafOfModules.extensionByZeroUnit` and its corepresentation of sections
  `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv` (**Stacks 0G1V**) are stated with the
  objects, the morphisms, the ring values and the module sections in four independent universes.
* `Stacks.SheafOfModules.tensorSheafHomIso` is the additive corepresentation of sections by the
  sheafified extension of scalars, with the ring universe free.
* `Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree` is the acyclicity input of
  **Stacks 03FD** with the ring universe free.

So the only work here is to thread them together.

Because the module universe `max u₁ v₁ r t` contains the universe of the objects of `C`, the
index type `Σ V : C, M(V)` of the generating family already lies in the module universe and no
`Small.{·} C` hypothesis is needed, unlike in
`Stacks.Cohomology.DerivedLowerShriek.exists_epi_isSumOfExtensionByZeroUnits`.

The three global instances of `Stacks.Cohomology.SiteModules` are switched off for this file.
They are stated at the module universe `max u v r w`, a join of four variables of which only
three are pinned by the arguments, so instance search for a category of modules whose universe
is a join of four *other* variables leaves the fourth as an unsolvable universe metavariable and
dies with a stuck universe constraint — which is what made `M ⊞ N` fail to elaborate here. The
erasure is confined to this file, and the instances actually used are Mathlib's, at the universe
pinned by the `HasSheafify` hypothesis. The same erasure is made for the same reason in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisSections.lean`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0D6X](https://stacks.math.columbia.edu/tag/0D6X)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

universe t r v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek.FreeRingUniverse

section Generators

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u₁ v₁ r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ r t}]
  (R : Sheaf J RingCat.{r}) (U : C)

/-- The class of direct sums of the generators `j_{U!} O_U`, at the sheafified-free-module
spelling `Stacks.SheafOfModules.extensionByZeroUnit`, whose module universe is independent of
the universe of the sections of `O_C`. -/
def IsSumOfExtensionByZeroUnits :
    ObjectProperty (SheafOfModules.{max u₁ v₁ r t} R) := fun M =>
  ∃ (ι : Type max u₁ v₁ r t) (V : ι → C),
    Nonempty ((∐ fun i : ι =>
      Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R (V i)) ≅ M)

/-- The class of direct sums of the generators contains a zero object: the direct sum over the
empty index family is initial, hence zero. -/
instance containsZero_isSumOfExtensionByZeroUnits :
    (IsSumOfExtensionByZeroUnits.{t} J R).ContainsZero := by
  let V₀ : PEmpty.{max u₁ v₁ r t + 1} → C := fun i => nomatch i
  let E : PEmpty.{max u₁ v₁ r t + 1} → SheafOfModules.{max u₁ v₁ r t} R := fun i =>
    Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R (V₀ i)
  exact ⟨∐ E, (IsInitial.ofUniqueHom (fun Y => Sigma.desc (fun i => isEmptyElim i))
    (fun Y m => Sigma.hom_ext _ _ (fun i => isEmptyElim i))).isZero,
    ⟨PEmpty.{max u₁ v₁ r t + 1}, V₀, ⟨Iso.refl _⟩⟩⟩

/-- The class of direct sums of the generators is closed under binary direct sums: concatenate
the two index families. -/
lemma isSumOfExtensionByZeroUnits_biprod {M N : SheafOfModules.{max u₁ v₁ r t} R}
    (hM : IsSumOfExtensionByZeroUnits.{t} J R M)
    (hN : IsSumOfExtensionByZeroUnits.{t} J R N) :
    IsSumOfExtensionByZeroUnits.{t} J R (M ⊞ N) := by
  obtain ⟨ι, V, ⟨eM⟩⟩ := hM
  obtain ⟨κ, W, ⟨eN⟩⟩ := hN
  refine ⟨ι ⊕ κ, Sum.elim V W, ?_⟩
  let F : ι → SheafOfModules.{max u₁ v₁ r t} R := fun i =>
    Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R (V i)
  let H : κ → SheafOfModules.{max u₁ v₁ r t} R := fun j =>
    Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R (W j)
  let e : Discrete.functor (fun i : ι ⊕ κ =>
        Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R (Sum.elim V W i)) ≅
      Discrete.functor (Sum.elim F H) :=
    Discrete.natIso fun i => eqToIso (by rcases i with ⟨_ | _⟩ <;> rfl)
  exact ⟨HasColimit.isoOfNatIso e ≪≫
    (coproductIsCoproduct (Sum.elim F H)).coconePointUniqueUpToIso
      (Cofan.combPairIsColimit (coproductIsCoproduct F) (coproductIsCoproduct H)
        (coprodIsCoprod (∐ F) (∐ H))) ≪≫
    (biprod.isoCoprod (∐ F) (∐ H)).symm ≪≫ biprod.mapIso eM eN⟩

/-- **The generators generate.** Every sheaf of modules receives an epimorphism from a direct
sum of the `j_{U!} O_U`, indexed by the pairs `(V, x)` of an object of `C` and a section of the
module over it; the component at `(V, x)` is the morphism `j_{V!} O_V ⟶ M` that **Stacks 0G1V**
identifies with `x`.

The index type lies in the module universe already, that universe containing the objects of `C`,
so no smallness hypothesis is needed. -/
@[sga "4 IV 11.3.3" "special case"]
theorem exists_epi_isSumOfExtensionByZeroUnits (M : SheafOfModules.{max u₁ v₁ r t} R) :
    ∃ (N : SheafOfModules.{max u₁ v₁ r t} R)
      (_ : IsSumOfExtensionByZeroUnits.{t} J R N) (p : N ⟶ M), Epi p := by
  classical
  let σ : Type max u₁ v₁ r t := Σ V : C, ToType (M.val.obj (op V))
  refine ⟨∐ fun i : σ =>
      Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R i.1,
    ⟨σ, fun i => i.1, ⟨Iso.refl _⟩⟩,
    Sigma.desc fun i =>
      (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, r, t} R i.1 M).symm i.2, ⟨?_⟩⟩
  intro N f g h
  have key (i : σ) : f.val.app (op i.1) i.2 = g.val.app (op i.1) i.2 := by
    have hh := Sigma.ι
      (fun i : σ => Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R i.1) i ≫= h
    simp only [Sigma.ι_desc_assoc] at hh
    have he := congrArg
      (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, r, t} R i.1 N) hh
    rwa [Stacks.SheafOfModules.extensionByZeroUnitHomEquiv_naturality,
      Stacks.SheafOfModules.extensionByZeroUnitHomEquiv_naturality,
      Equiv.apply_symm_apply] at he
  apply (SheafOfModules.toSheaf R).map_injective
  ext Y x
  exact key ⟨Y.unop, x⟩

/-! ### The two spellings of the generator -/

/-- **`j_{U!} O_U`, spelled as a sheafified extension of scalars.** The free abelian presheaf on
the universe-lifted presheaf represented by `U`, tensored up to an `O_C`-module presheaf and
sheafified.  It corepresents the sections over `U` *additively*, which is what the `Ext`
comparison of **Stacks 03FD** consumes; see
`Stacks.SheafOfModules.tensorSheafHomIso`.

The universe of the sections of `R` is free of the module universe. -/
abbrev sectionModuleObject : SheafOfModules.{max u₁ v₁ r t} R :=
  (PresheafOfModules.sheafification.{max u₁ v₁ r t} (𝟙 R.obj)).obj
    (Stacks.SheafOfModules.tensorPresheaf.{u₁, v₁, max u₁ v₁ t, r} R.obj
      (uliftYoneda.{max u₁ v₁ r t}.obj U ⋙ AddCommGrpCat.free))

/-- **Morphisms out of `j_{U!} O_U` are the morphisms out of `j_{U!} ℤ_U` of abelian sheaves.**
Both are the sections over `U`, by **Stacks 0G1V** on modules and on abelian sheaves. -/
def extensionByZeroUnitHomEquivAb (M : SheafOfModules.{max u₁ v₁ r t} R) :
    (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R U ⟶ M) ≃
      (extensionByZeroUnitAb.{max u₁ v₁ r t} J U ⟶ (SheafOfModules.toSheaf R).obj M) :=
  (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, r, t} R U M).trans
    (extensionByZeroUnitAbHomEquiv.{max u₁ v₁ r t} J U
      ((SheafOfModules.toSheaf R).obj M)).symm

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ r t}] in
/-- The identification of the two kinds of morphism out of `j_{U!}` is natural in the module:
both sides are the restriction of a section over `U`. -/
theorem extensionByZeroUnitHomEquivAb_naturality
    {M N : SheafOfModules.{max u₁ v₁ r t} R}
    (φ : Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R U ⟶ M) (g : M ⟶ N) :
    extensionByZeroUnitHomEquivAb.{t} J R U N (φ ≫ g) =
      extensionByZeroUnitHomEquivAb.{t} J R U M φ ≫ (SheafOfModules.toSheaf R).map g := by
  have h1 : ∀ (P : SheafOfModules.{max u₁ v₁ r t} R)
      (ψ : Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R U ⟶ P),
      extensionByZeroUnitAbHomEquiv.{max u₁ v₁ r t} J U ((SheafOfModules.toSheaf R).obj P)
          (extensionByZeroUnitHomEquivAb.{t} J R U P ψ) =
        Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{u₁, v₁, r, t} R U P ψ :=
    fun P ψ => (extensionByZeroUnitAbHomEquiv.{max u₁ v₁ r t} J U
      ((SheafOfModules.toSheaf R).obj P)).apply_symm_apply _
  apply (extensionByZeroUnitAbHomEquiv.{max u₁ v₁ r t} J U
    ((SheafOfModules.toSheaf R).obj N)).injective
  rw [extensionByZeroUnitAbHomEquiv_naturality.{max u₁ v₁ r t} J _
      ((SheafOfModules.toSheaf R).map g), h1, h1]
  exact Stacks.SheafOfModules.extensionByZeroUnitHomEquiv_naturality.{u₁, v₁, r, t} R U φ g

/-- The corepresentation of sections over `U` by `j_{U!} O_U`, read against the abelian
generator, as an isomorphism of functors to types. -/
def extensionByZeroUnitCoyonedaIso :
    coyoneda.obj (op (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R U)) ≅
      SheafOfModules.toSheaf R ⋙
        coyoneda.obj (op (extensionByZeroUnitAb.{max u₁ v₁ r t} J U)) :=
  NatIso.ofComponents (fun M => Equiv.toIso (extensionByZeroUnitHomEquivAb.{t} J R U M))
    (fun {M N} g => by
      ext φ
      exact extensionByZeroUnitHomEquivAb_naturality.{t} J R U φ g)

/-- **Morphisms out of the sheafified extension of scalars are the sections over `U`**,
additively.  This is `Stacks.SheafOfModules.tensorSheafHomIso` at the free abelian presheaf on
the universe-lifted representable. -/
def sectionModuleObjectCorepresentation :
    preadditiveCoyoneda.obj (op (sectionModuleObject.{t} J R U)) ≅
      SheafOfModules.toSheaf R ⋙
        preadditiveCoyoneda.obj (op (extensionByZeroUnitAb.{max u₁ v₁ r t} J U)) :=
  Stacks.SheafOfModules.tensorSheafHomIso.{max u₁ v₁ t, r, v₁, u₁} J R
    (uliftYoneda.{max u₁ v₁ r t}.obj U ⋙ AddCommGrpCat.free)

/-- **The two spellings of `j_{U!} O_U` agree.** Both corepresent the sections over `U`, so they
are isomorphic by uniqueness of a corepresenting object. -/
def extensionByZeroUnitIsoSectionModuleObject :
    Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R U ≅
      sectionModuleObject.{t} J R U :=
  (Coyoneda.fullyFaithful.preimageIso
    (extensionByZeroUnitCoyonedaIso.{t} J R U ≪≫
      (Functor.isoWhiskerRight (sectionModuleObjectCorepresentation.{t} J R U)
        (forget AddCommGrpCat.{max u₁ v₁ r t})).symm)).unop.symm

section Ext

variable [EnoughInjectives (SheafOfModules.{max u₁ v₁ r t} R)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u₁ v₁ r t})]
  [HasExt.{max u₁ v₁ r t} (SheafOfModules.{max u₁ v₁ r t} R)]
  [HasExt.{max u₁ v₁ r t} (Sheaf J AddCommGrpCat.{max u₁ v₁ r t})]

omit [EnoughInjectives (SheafOfModules.{max u₁ v₁ r t} R)]
  [HasExt.{max u₁ v₁ r t} (SheafOfModules.{max u₁ v₁ r t} R)] in
/-- **The acyclicity input of Stacks 03FD at the generators.** The underlying abelian sheaf of
an injective `O_C`-module has vanishing positive-degree `Ext` against `j_{U!} ℤ_U`, the latter
being the sheafification of a sectionwise torsion-free abelian presheaf. -/
theorem ext_eq_zero_extensionByZeroUnitAb_toSheaf
    (I : SheafOfModules.{max u₁ v₁ r t} R) [Injective I] (n : ℕ)
    (e : Ext.{max u₁ v₁ r t} (extensionByZeroUnitAb.{max u₁ v₁ r t} J U)
      ((SheafOfModules.toSheaf R).obj I) (n + 1)) :
    e = 0 :=
  Stacks.SheafOfModules.ext_eq_zero_of_isTorsionFree.{max u₁ v₁ r t, max u₁ v₁ t, r, v₁, u₁}
    J R I _
    (ModuleSheafCohomology.isTorsionFree_sheafify J
      (uliftYoneda.{max u₁ v₁ r t}.obj U ⋙ AddCommGrpCat.free) (fun point => by
        change Module.IsTorsionFree ℤ
          (FreeAbelianGroup (ULift.{max u₁ v₁ r t} (point.unop ⟶ U)))
        exact Module.Flat.isTorsionFree)) n e

/-- **Stacks 03FD at the generators.** For every `O_C`-module `M`, the positive-degree `Ext`
groups out of `j_{U!} O_U` in `Mod(O_C)` are those out of `j_{U!} ℤ_U` in `Ab(C)` against the
underlying abelian sheaf of `M`.  So the module-level vanishing follows from the abelian-sheaf
one, which is the form the Čech computation of **Stacks 0D6X** provides. -/
theorem subsingleton_ext_extensionByZeroUnit_of_abelian
    (M : SheafOfModules.{max u₁ v₁ r t} R)
    (hM : ∀ n : ℕ, 0 < n →
      Subsingleton (Ext.{max u₁ v₁ r t} (extensionByZeroUnitAb.{max u₁ v₁ r t} J U)
        ((SheafOfModules.toSheaf R).obj M) n))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Ext.{max u₁ v₁ r t}
      (Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, r, t} R U) M n) := by
  have hcomp := (ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R)
    (extensionByZeroUnitAb.{max u₁ v₁ r t} J U) (sectionModuleObject.{t} J R U)
    (fun I _ m e => ext_eq_zero_extensionByZeroUnitAb_toSheaf.{t} J R U I m e)
    (sectionModuleObjectCorepresentation.{t} J R U) n).app M
  exact Stacks.Cohomology.subsingleton_ext_of_iso
    (extensionByZeroUnitIsoSectionModuleObject.{t} J R U) n
    (hcomp.addCommGroupIsoToAddEquiv.subsingleton_congr.mpr (hM n hn))

end Ext

end Generators

end Stacks.Cohomology.DerivedLowerShriek.FreeRingUniverse

end
