module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Lower shriek of modules carries `j_{U!} O_U` to `j_{u(U)!} O_{u(U)}`

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, let `g` be the corresponding
morphism of topoi, let `O_D` be a sheaf of rings on `D` and let `O_C = g^{-1} O_D`. Among the
assertions of **Stacks 07AC** is the displayed chain

`Lg_!(j_{U!} O_U) = g_! j_{U!} O_U = j_{u(U)!} O_{u(U)}`

for an object `U` of `C`, where `j_{U!}` and `j_{u(U)!}` are the extensions by zero of
**Stacks 03DI** along the localization morphisms `C/U ⟶ C` and `D/u(U) ⟶ D`.

This file proves the **second equality**, on sheaves of modules, with nothing assumed beyond the
hypotheses of Stacks 07AC itself:

`g_! (j_{U!} O_U) ≅ j_{u(U)!} O_{u(U)}`,

for the module-level lower shriek `Stacks.SheafOfModules.lowerShriek` of **Stacks 0797** that
Stacks 07AC is about. The proof is pure corepresentability and uses no geometry: morphisms out of
`g_! (j_{U!} O_U)` are, by the adjunction `g_! ⊣ g^*` of Stacks 0797 followed by **Stacks 0G1V**
on `(C, J)`, the sections of `g^* F` over `U`, which are the sections of `F` over `u(U)` on the
nose, restriction of modules along `u` being precomposition with `uᵒᵖ`; and morphisms out of
`j_{u(U)!} O_{u(U)}` are the sections over `u(U)` by Stacks 0G1V on `(D, K)`. Two objects
corepresenting the same functor are isomorphic.

`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ExtensionByZeroLowerShriek.lean` is the
same statement for abelian sheaves, with `ℤ_U` in place of `O_U`; neither file is a consequence
of the other, the two adjunctions being different.

## What is *not* proved here

The first equality of the displayed chain, and with it the existence and adjointness of `Lg_!`,
are not proved here: they need the acyclicity statement of Stacks 0794 for `g_!`, which the source
deduces from the vanishing `H^p(U, g^{-1} I) = 0` of **Stacks 0D6X** for an injective
`O_D`-module `I`. That is done in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/ModuleDerivedLowerShriek.lean`, where
Stacks 07AC is registered in full, using the isomorphism below for the second equality.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekExtensionByZeroUnitHomEquiv`: morphisms out of
  `g_! (j_{U!} O_U)` are the sections over `u(U)`.
* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekExtensionByZeroUnitIso`: Stacks 07AC, the
  second equality of the displayed chain, `g_! (j_{U!} O_U) ≅ j_{u(U)!} O_{u(U)}`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekExtensionByZeroUnitHomEquiv_naturality`:
  naturality of the first in the sheaf of modules on `(D, K)`.

## Implementation notes

The sheaf of rings and the module sections lie in one universe `w`, as in
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroUnitSections.lean`, whose form of
Stacks 0G1V is used on both sites and is stated that way; the two sites and their morphisms keep
independent universes, related to `w` only by `UnivLE`. That is a narrowing of universes relative
to Stacks 07AC and of nothing else.

Existence of the extension-by-zero functors — the left adjoints of restriction along
`Over.forget V` for the slices of the two sites — is carried as an instance hypothesis for the
same reason as in
`StacksFrontier/CategoryTheory/Sites/Modules/ExtensionByZeroUnitSections.lean`: Mathlib
constructs them only for a small
site whose module sections lie in the universe of the site, and on such a site each hypothesis is
discharged by instance search, so every statement below specialises to its single-universe form
verbatim. These are the objects `j_{V!}` that Stacks 07AC's displayed chain is about, cited there
from Stacks 03DI; nothing mathematical is assumed about them.

## References

* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ v₂ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (u : C ⥤ D) [u.IsContinuous J K] [u.IsCocontinuous J K] (O : Sheaf K RingCat.{w})
  [UnivLE.{v₁, w}] [UnivLE.{v₂, w}] [UnivLE.{u₁, w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, (SheafOfModules.pushforward.{w} (F := Over.forget V)
    (𝟙 ((Stacks.SheafOfModules.inverseImageRing J K u O).over V) :
      (Stacks.SheafOfModules.inverseImageRing J K u O).over V ⟶
        (Stacks.SheafOfModules.inverseImageRing J K u O).over V)).IsRightAdjoint]
  [∀ W : D, (SheafOfModules.pushforward.{w} (F := Over.forget W)
    (𝟙 (O.over W) : O.over W ⟶ O.over W)).IsRightAdjoint]

/-- **Morphisms out of `g_! (j_{U!} O_U)` are the sections over `u(U)`.** The adjunction
`g_! ⊣ g^*` of Stacks 0797 turns them into morphisms out of `j_{U!} O_U` on `(C, J)`, which are
the sections of `g^* F` over `U` by Stacks 0G1V; and the underlying presheaf of modules of a
restriction along `u` is precomposition with `uᵒᵖ`, so those are the sections over `u(U)`. -/
def lowerShriekExtensionByZeroUnitHomEquiv (V : C) (F : SheafOfModules.{w} O) :
    ((Stacks.SheafOfModules.lowerShriek.{w} J K u O).obj
        (extensionByZeroUnit (Stacks.SheafOfModules.inverseImageRing J K u O) V) ⟶ F) ≃
      (F.val.obj (op (u.obj V)) : Type w) :=
  ((Stacks.SheafOfModules.lowerShriekAdjunction.{w} J K u O).homEquiv _ _).trans
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} J
      (Stacks.SheafOfModules.inverseImageRing J K u O) V
      ((Stacks.SheafOfModules.inverseImage.{w} J K u O).obj F))

omit [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : D, (SheafOfModules.pushforward.{w} (F := Over.forget W)
    (𝟙 (O.over W) : O.over W ⟶ O.over W)).IsRightAdjoint] in
/-- Naturality of `lowerShriekExtensionByZeroUnitHomEquiv` in the sheaf of modules on `(D, K)`:
postcomposing a morphism out of `g_! (j_{U!} O_U)` with `g` acts on the corresponding section
over `u(U)` through `g`. -/
theorem lowerShriekExtensionByZeroUnitHomEquiv_naturality {V : C}
    {F G : SheafOfModules.{w} O}
    (f : (Stacks.SheafOfModules.lowerShriek.{w} J K u O).obj
      (extensionByZeroUnit (Stacks.SheafOfModules.inverseImageRing J K u O) V) ⟶ F)
    (g : F ⟶ G) :
    lowerShriekExtensionByZeroUnitHomEquiv J K u O V G (f ≫ g) =
      ((SheafOfModules.evaluation O (op (u.obj V))).map g)
        (lowerShriekExtensionByZeroUnitHomEquiv J K u O V F f) := by
  have h1 : (Stacks.SheafOfModules.lowerShriekAdjunction.{w} J K u O).homEquiv
        (extensionByZeroUnit (Stacks.SheafOfModules.inverseImageRing J K u O) V) G (f ≫ g) =
      (Stacks.SheafOfModules.lowerShriekAdjunction.{w} J K u O).homEquiv
        (extensionByZeroUnit (Stacks.SheafOfModules.inverseImageRing J K u O) V) F f ≫
        (Stacks.SheafOfModules.inverseImage.{w} J K u O).map g :=
    (Stacks.SheafOfModules.lowerShriekAdjunction.{w} J K u O).homEquiv_naturality_right _ _
  exact (congrArg (fun a => Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} J
      (Stacks.SheafOfModules.inverseImageRing J K u O) V
      ((Stacks.SheafOfModules.inverseImage.{w} J K u O).obj G) a) h1).trans
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality.{w} J
      (Stacks.SheafOfModules.inverseImageRing J K u O) V
      ((Stacks.SheafOfModules.lowerShriekAdjunction.{w} J K u O).homEquiv
        (extensionByZeroUnit (Stacks.SheafOfModules.inverseImageRing J K u O) V) F f)
      ((Stacks.SheafOfModules.inverseImage.{w} J K u O).map g))

/-- **Stacks 07AC, the second equality of its displayed chain, on sheaves of modules.** For a
continuous and cocontinuous functor of sites `u : C ⥤ D`, a sheaf of rings `O_D` on `D`,
`O_C = g^{-1} O_D` and every object `U` of `C`,

`g_! (j_{U!} O_U) ≅ j_{u(U)!} O_{u(U)}`.

Both sides corepresent the sections over `u(U)` — the left by
`lowerShriekExtensionByZeroUnitHomEquiv`, the right by Stacks 0G1V on `(D, K)` — so each of the
two universal sections names a morphism to the other object, and the two naturality statements
identify the composites with the identities. -/
def lowerShriekExtensionByZeroUnitIso (V : C) :
    (Stacks.SheafOfModules.lowerShriek.{w} J K u O).obj
        (extensionByZeroUnit (Stacks.SheafOfModules.inverseImageRing J K u O) V) ≅
      extensionByZeroUnit O (u.obj V) where
  hom := (lowerShriekExtensionByZeroUnitHomEquiv J K u O V _).symm
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} K O (u.obj V) _ (𝟙 _))
  inv := (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} K O (u.obj V) _).symm
    (lowerShriekExtensionByZeroUnitHomEquiv J K u O V _ (𝟙 _))
  hom_inv_id := by
    apply (lowerShriekExtensionByZeroUnitHomEquiv J K u O V _).injective
    rw [lowerShriekExtensionByZeroUnitHomEquiv_naturality, Equiv.apply_symm_apply,
      ← Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Category.id_comp, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv.{w} K O
      (u.obj V) _).injective
    rw [Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality,
      Equiv.apply_symm_apply, ← lowerShriekExtensionByZeroUnitHomEquiv_naturality,
      Category.id_comp, Equiv.apply_symm_apply]

end Stacks.Cohomology.DerivedLowerShriek

end
