module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubobjectLocalization

/-!
# Restricting modules and their global sections to an open of `X`

For `V` an open of `X`, `Crystalline.GlobalCrystallineSituation.openSubspace S V` is the
crystalline situation `V/S`: the same divided power base, the same prime, the space `V`. This
file restricts sheaves of modules and their global sections from `Cris(X/S)` to `Cris(V/S)`, and
compares the module-valued cohomology of the two.

The inclusion `V ⟶ X` over the identity of `S` is an instance of change of divided power base,
`...SmallSite.smallChangeBaseModulePullback` and `...SmallSite.baseChangeGlobalSectionsTrans`,
for the identity of the base and the open immersion `V ⟶ X`, with compatibility datum
`...openSubspace_changeBase_condition`. Since the morphism of bases is `𝟙 S.S`, the ring map
`A' ⟶ A` of `...SmallSite.baseChangeRingHom` is the identity, and the comparison of global
sections is a transformation of functors valued in `Mod_A` for the single ring `A = Γ(S, 𝒪_S)`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `openSubspaceModuleRestriction`: the restriction of a sheaf of `𝒪_{X/S}`-modules to
  `Cris(V/S)`, with its sections computed by `openSubspaceModuleRestriction_obj_val_obj`; it is
  exact.
* `openSubspaceRestrictScalarsIdIso`: restriction of scalars along the base ring map of
  `openSubspace` is the identity functor.
* `openSubspaceGlobalSectionsTrans`: the restriction of global sections, a transformation
  `Γ(Cris(X/S), -) ⟶ Γ(Cris(V/S), -|_V)` of functors valued in `A`-modules.
* `openSubspaceCohomologyTrans`: its `j`-th right derived functor, a comparison out of
  `H^j(Cris(X/S), -)`.

## Main results

* `openSubspace_baseChangeRingHom_eq_id`: the base ring map of `openSubspace` is the identity of
  `A = Γ(S, 𝒪_S)`.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (V : S.X.Opens)

/-! ### The restriction of modules -/

/-- **The restriction of a sheaf of `𝒪_{X/S}`-modules to `Cris(V/S)`**, for `V` an open of `X`:
the sections over an object `(U, T, δ)` of `Cris(V/S)` are the sections of the module over the
same `(U, T, δ)` read in `Cris(X/S)`. -/
def openSubspaceModuleRestriction : ModuleSheaf S ⥤ ModuleSheaf (openSubspace S V) :=
  smallChangeBaseModulePullback (openSubspace S V) S (𝟙 S.S) V.ι
    (openSubspace_changeBase_condition S V)

/-- The sections of the restriction of `F` over an object of `Cris(V/S)` are the sections of `F`
over the image of that object in `Cris(X/S)`. -/
theorem openSubspaceModuleRestriction_obj_val_obj (F : ModuleSheaf S)
    (A : (CrystallineThickening (openSubspace S V))ᵒᵖ) :
    (((openSubspaceModuleRestriction S V).obj F).val.obj A : Type (u + 1)) =
      (F.val.obj (op ((smallChangeBase (openSubspace S V) S (𝟙 S.S) V.ι
        (openSubspace_changeBase_condition S V)).obj A.unop)) : Type (u + 1)) :=
  rfl

/-- Restriction to an open of `X` is additive, acting on sections by restriction. -/
instance openSubspaceModuleRestriction_additive :
    (openSubspaceModuleRestriction S V).Additive :=
  inferInstanceAs (smallChangeBaseModulePullback (openSubspace S V) S (𝟙 S.S) V.ι
    (openSubspace_changeBase_condition S V)).Additive

/-- Restriction to an open of `X` preserves finite limits. -/
instance openSubspaceModuleRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (openSubspaceModuleRestriction S V) :=
  inferInstanceAs (PreservesFiniteLimits (smallChangeBaseModulePullback (openSubspace S V) S
    (𝟙 S.S) V.ι (openSubspace_changeBase_condition S V)))

/-- Restriction to an open of `X` preserves finite colimits. -/
instance openSubspaceModuleRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (openSubspaceModuleRestriction S V) :=
  inferInstanceAs (PreservesFiniteColimits (smallChangeBaseModulePullback (openSubspace S V) S
    (𝟙 S.S) V.ι (openSubspace_changeBase_condition S V)))

/-! ### The scalars do not change -/

/-- **Restricting to an open of `X` does not change the base ring**: the ring map `A' ⟶ A` over
which the comparison on global sections of [Stacks, Tag 07MS] is semilinear is the identity of
`A = Γ(S, 𝒪_S)`. -/
theorem openSubspace_baseChangeRingHom_eq_id :
    baseChangeRingHom (S := openSubspace S V) (S' := S) (𝟙 S.S) =
      RingHom.id Γ(S.S.scheme, ⊤) :=
  baseChangeRingHom_id S

/-- Restriction of scalars along the base ring map of `openSubspace` is the identity functor. -/
def openSubspaceRestrictScalarsIdIso :
    ModuleCat.restrictScalars.{u + 1}
        (baseChangeRingHom (S := openSubspace S V) (S' := S) (𝟙 S.S)) ≅
      𝟭 (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :=
  ModuleCat.restrictScalarsId' _ (openSubspace_baseChangeRingHom_eq_id S V)

/-! ### The comparison on global sections and on cohomology -/

/-- **The restriction of global sections to an open of `X`**:

`Γ(Cris(X/S), F) ⟶ Γ(Cris(V/S), F|_V)`,

natural in `F` and `A`-linear, for the one ring `A = Γ(S, 𝒪_S)` acting on both sides. -/
def openSubspaceGlobalSectionsTrans :
    baseModuleGlobalSections S ⟶
      openSubspaceModuleRestriction S V ⋙ baseModuleGlobalSections (openSubspace S V) :=
  baseChangeGlobalSectionsTrans (openSubspace S V) S (𝟙 S.S) V.ι
      (openSubspace_changeBase_condition S V) ≫
    Functor.whiskerLeft
      (openSubspaceModuleRestriction S V ⋙ baseModuleGlobalSections (openSubspace S V))
      (openSubspaceRestrictScalarsIdIso S V).hom

/-- **The comparison of cohomology of `Cris(X/S)` with that of `Cris(V/S)`**, in degree `j`: the
`j`-th right derived functor of `openSubspaceGlobalSectionsTrans`, a transformation

`H^j(Cris(X/S), -) ⟶ R^j(Γ(Cris(V/S), -) ∘ restriction)`

of functors `ModuleSheaf S ⥤ Mod_A`, whose target is the right derived functor of the
composite. -/
def openSubspaceCohomologyTrans (j : ℕ) :
    moduleCohomologyFunctor S j ⟶
      (openSubspaceModuleRestriction S V ⋙
        baseModuleGlobalSections (openSubspace S V)).rightDerived j :=
  NatTrans.rightDerived (openSubspaceGlobalSectionsTrans S V) j

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
