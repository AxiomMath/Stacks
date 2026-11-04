module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.AbelianDerivedExistence

/-!
# Lower shriek carries a free abelian sheaf on an object to the free abelian sheaf on its image

Let `u : C ⥤ D` be a continuous functor of sites whose restriction functor `g⁻¹` on abelian
sheaves admits a left adjoint `g_!`. For an object `U` of `C` write `j_{U!} ℤ_U` for the free
abelian sheaf on the presheaf represented by `U`, which is `Stacks 0G1V`'s corepresenting object
for sections over `U`. Then

`g_! (j_{U!} ℤ_U) ≅ j_{u(U)!} ℤ_{u(U)}`.

The proof is pure corepresentability and needs nothing of the geometry: morphisms out of
`g_! (j_{U!} ℤ_U)` are, by the adjunction `g_! ⊣ g⁻¹` followed by `Stacks 0G1V` on `(C, J)`,
the sections of the restriction over `U`, which are the sections over `u(U)` on the nose; and
morphisms out of `j_{u(U)!} ℤ_{u(U)}` are the sections over `u(U)` by `Stacks 0G1V` on `(D, K)`.
Two objects corepresenting the same functor are isomorphic.

## Why this statement

The identification `g_! ℤ_C ≅ ℤ_D` of the constant sheaves — the degree-zero content of
**Stacks 0H0Z** — is available in this library only through
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso`, which asks for terminal
objects of *both* sites with `u` carrying one to the other. That route is closed for the
flat-fppf and lisse-étale subsites of an algebraic stack: neither they nor the ambient site has a
terminal object as soon as the stack has a nontrivial automorphism, by
`CategoryTheory.Functor.IsFiberedInGroupoids.not_isTerminal_of_faithful_of_ne_id`.

The statement below is the terminal-object-free replacement: it is the same identification run on
the generators `j_{U!} ℤ_U` of `Ab(C)` rather than on the constant sheaf, and it holds for every
object `U` with no hypothesis beyond continuity of `u` and the existence of `g_!`. On a site with
a terminal object `e` the constant sheaf is `j_{e!} ℤ_e`, so `lowerShriekConstantSheafIso` is the
instance `U = e` of it; off such a site it is what the source's own proof of Stacks 0H0Z uses,
`Lg_!` being computed by resolutions whose terms are direct sums of these generators
(`Stacks.Cohomology.DerivedLowerShriek.IsSumOfExtensionByZeroUnitsAb`).

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekExtensionByZeroUnitAbHomEquiv`: morphisms out
  of `g_! (j_{U!} ℤ_U)` are the sections over `u(U)`.
* `Stacks.Cohomology.DerivedLowerShriek.abelianLowerShriekExtensionByZeroUnitAbIso`:
  `g_! (j_{U!} ℤ_U) ≅ j_{u(U)!} ℤ_{u(U)}`.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.lowerShriekExtensionByZeroUnitAbHomEquiv_naturality`:
  naturality of the first in the abelian sheaf on `(D, K)`.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{max v w}` for both sites, which forces the two sites
to have their morphisms in one universe `v`; that is the shape of the geometric sites this is
for, whose objects live one universe above their morphisms. Objects are left in independent
universes `u₁`, `u₂`.

Cocontinuity of `u` is not assumed: the adjunction `g_! ⊣ g⁻¹` of
`Stacks.Cohomology.DerivedLowerShriek.abelianAdjunction` needs only continuity together with the
existence of the left adjoint.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁ u₂

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (u : C ⥤ D)
  [u.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{max v w}] [HasSheafify K AddCommGrpCat.{max v w}]
  [(u.sheafPushforwardContinuous AddCommGrpCat.{max v w} J K).IsRightAdjoint]

/-- **Morphisms out of `g_! (j_{U!} ℤ_U)` are the sections over `u(U)`.** The adjunction
`g_! ⊣ g⁻¹` turns them into morphisms out of `j_{U!} ℤ_U` on `(C, J)`, which are the sections of
the restriction over `U` by Stacks 0G1V; and the underlying presheaf of a restriction is
precomposition with `uᵒᵖ`, so those are the sections over `u(U)`. -/
def lowerShriekExtensionByZeroUnitAbHomEquiv (U : C) (F : Sheaf K AddCommGrpCat.{max v w}) :
    ((abelianLowerShriek.{w} J K u).obj (extensionByZeroUnitAb.{w} J U) ⟶ F) ≃
      F.obj.obj (op (u.obj U)) :=
  ((abelianAdjunction.{w} J K u).homEquiv _ _).trans
    (extensionByZeroUnitAbHomEquiv.{w} J U ((abelianRestriction.{w} J K u).obj F))

omit [HasSheafify K AddCommGrpCat.{max v w}] in
/-- Naturality of `lowerShriekExtensionByZeroUnitAbHomEquiv` in the abelian sheaf on `(D, K)`:
postcomposing a morphism out of `g_! (j_{U!} ℤ_U)` with `g` acts on the corresponding section
over `u(U)` through `g`. -/
lemma lowerShriekExtensionByZeroUnitAbHomEquiv_naturality {U : C}
    {F G : Sheaf K AddCommGrpCat.{max v w}}
    (f : (abelianLowerShriek.{w} J K u).obj (extensionByZeroUnitAb.{w} J U) ⟶ F) (g : F ⟶ G) :
    lowerShriekExtensionByZeroUnitAbHomEquiv.{w} J K u U G (f ≫ g) =
      g.hom.app (op (u.obj U))
        (lowerShriekExtensionByZeroUnitAbHomEquiv.{w} J K u U F f) := by
  have h1 : (abelianAdjunction.{w} J K u).homEquiv (extensionByZeroUnitAb.{w} J U) G (f ≫ g) =
      (abelianAdjunction.{w} J K u).homEquiv (extensionByZeroUnitAb.{w} J U) F f ≫
        (abelianRestriction.{w} J K u).map g :=
    (abelianAdjunction.{w} J K u).homEquiv_naturality_right _ _
  exact (congrArg (fun a => extensionByZeroUnitAbHomEquiv.{w} J U
      ((abelianRestriction.{w} J K u).obj G) a) h1).trans
    (extensionByZeroUnitAbHomEquiv_naturality.{w} J
      ((abelianAdjunction.{w} J K u).homEquiv (extensionByZeroUnitAb.{w} J U) F f)
      ((abelianRestriction.{w} J K u).map g))

/-- **Lower shriek carries the free abelian sheaf on an object to the free abelian sheaf on its
image**: for every object `U` of `C`,

`g_! (j_{U!} ℤ_U) ≅ j_{u(U)!} ℤ_{u(U)}`.

Both sides corepresent the sections over `u(U)` — the left by
`lowerShriekExtensionByZeroUnitAbHomEquiv`, the right by Stacks 0G1V on `(D, K)` — so each of the
two universal sections names a morphism to the other object, and the two naturality statements
identify the composites with the identities.

This is the generator form of the comparison `g_! ℤ_C ≅ ℤ_D` of the constant sheaves that the
proof of **Stacks 0H0Z** rests on, and unlike
`Stacks.Cohomology.BiggerSiteGlobal.lowerShriekConstantSheafIso` it needs no terminal object in
either site. -/
def abelianLowerShriekExtensionByZeroUnitAbIso (U : C) :
    (abelianLowerShriek.{w} J K u).obj (extensionByZeroUnitAb.{w} J U) ≅
      extensionByZeroUnitAb.{w} K (u.obj U) where
  hom := (lowerShriekExtensionByZeroUnitAbHomEquiv.{w} J K u U _).symm
    (extensionByZeroUnitAbHomEquiv.{w} K (u.obj U) _ (𝟙 _))
  inv := (extensionByZeroUnitAbHomEquiv.{w} K (u.obj U) _).symm
    (lowerShriekExtensionByZeroUnitAbHomEquiv.{w} J K u U _ (𝟙 _))
  hom_inv_id := by
    apply (lowerShriekExtensionByZeroUnitAbHomEquiv.{w} J K u U _).injective
    rw [lowerShriekExtensionByZeroUnitAbHomEquiv_naturality, Equiv.apply_symm_apply,
      ← extensionByZeroUnitAbHomEquiv_naturality, Category.id_comp, Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (extensionByZeroUnitAbHomEquiv.{w} K (u.obj U) _).injective
    rw [extensionByZeroUnitAbHomEquiv_naturality, Equiv.apply_symm_apply,
      ← lowerShriekExtensionByZeroUnitAbHomEquiv_naturality, Category.id_comp,
      Equiv.apply_symm_apply]

end Stacks.Cohomology.DerivedLowerShriek

end
