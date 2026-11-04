module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FiniteTypeDegreeZero
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Generators.LocalSpanFiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite type modules on a scheme: restriction, locality, and closed immersions

This file collects what Stacks 09UM(2) needs about `SheafOfModules.IsFiniteType` for sheaves of
modules on a scheme: it is inherited by restriction to an open subscheme, it is local on the
scheme, and it is preserved and reflected by pushforward along a closed immersion.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLocallySurjective_c`: the map on structure sheaves of a
  closed immersion of schemes is locally surjective, because it is surjective on sections over
  every affine open.
* `AlgebraicGeometry.Scheme.Modules.isFiniteType_restrict`: finite type is inherited by
  restriction to an open subscheme.
* `AlgebraicGeometry.Scheme.Modules.localSpan_of_restrict` and
  `AlgebraicGeometry.Scheme.Modules.isFiniteType_of_isFiniteType_restrict`: finite type is local
  on the scheme.
* `AlgebraicGeometry.Scheme.Modules.isFiniteType_pushforward_iff`: **Stacks 01C4** for a closed
  immersion of schemes.
* `AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_singleFunctor_zero_iff`:
  the local condition of Stacks 09UI in degree `0` for a sheaf of modules placed in degree zero
  is finiteness of type of its restriction. This is Stacks 09V9(1) combined with Stacks 01C4, and
  it is the per-pair content of Stacks 09UM(2).

## Implementation notes

A closed immersion of schemes is surjective on sections over an affine open
(`AlgebraicGeometry.Scheme.Hom.app_surjective`), and the affine opens form a basis, so the map on
structure sheaves is locally surjective in the sense of
`CategoryTheory.Presheaf.IsLocallySurjective`. That is the hypothesis under which Stacks 01C4
holds, and it is strictly stronger than the map being an epimorphism of sheaves of rings.

Stacks 01C4 is formalized for the section-and-local-span form of finite type, and
`Stacks.RingedSpace.isFiniteType_iff_localSpan` identifies that form with Mathlib's
`SheafOfModules.IsFiniteType`; `AlgebraicGeometry.Scheme.Modules.isFiniteType_pushforward_iff` is
the composition of the two, read at the scheme-level spelling
`AlgebraicGeometry.Scheme.Modules.pushforward`, which is
`RingedSpaceModuleAdjunction.modulePushforward` of the underlying morphism of ringed spaces.

Locality is proved in the section-and-local-span form, where it is a statement about sections and
needs no comparison of restriction functors: the sections of `ℱ|_U` over an open `W` of `U` *are*
the sections of `ℱ` over the image of `W`, so a family of locally spanning sections on `U`
transports to one on `X` once the scalars are moved along the isomorphism
`AlgebraicGeometry.Scheme.Hom.appIso`.

Restriction to an open subscheme is isomorphic to pullback
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), so the fact that pullback
preserves finite type — Stacks 01B6,
`AlgebraicGeometry.SheafOfModules.pullback_isFiniteType` — gives it for restriction.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 17.9.5 (01C4)](https://stacks.math.columbia.edu/tag/01C4)
* [The Stacks Project, Lemma 17.9.2 (01B6)](https://stacks.math.columbia.edu/tag/01B6)
* [The Stacks Project, Lemma 36.60.11 (09V9)](https://stacks.math.columbia.edu/tag/09V9)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.8 (09UM)](https://stacks.math.columbia.edu/tag/09UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-! ### The structure sheaf map of a closed immersion -/

/-- **The map on structure sheaves of a closed immersion of schemes is locally surjective.** It is
surjective on sections over every affine open (`AlgebraicGeometry.Scheme.Hom.app_surjective`), and
the affine opens form a basis of the target. -/
public theorem isLocallySurjective_c {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (i.toLRSHom.toShHom).hom.c := by
  have h : TopCat.Presheaf.IsLocallySurjective i.toLRSHom.c := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U t x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, hVU, i.app_surjective V hV _, hxV⟩
  exact h

/-! ### Restriction to an open subscheme -/

/-- **Finite type is inherited by restriction to an open subscheme**, restriction being
isomorphic to pullback and pullback preserving finite type by Stacks 01B6. -/
public theorem isFiniteType_restrict {X : Scheme.{u}} (F : X.Modules) (hF : F.IsFiniteType)
    (U : X.Opens) : ((restrictFunctor U.ι).obj F).IsFiniteType := by
  have h1 : ((pullback U.ι).obj F).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType U.ι.toLRSHom.toShHom F
  exact SheafOfModules.IsFiniteType.of_iso (R := U.toScheme.ringCatSheaf) h1
    ((restrictFunctorIsoPullback U.ι).app F).symm

/-! ### Locality -/

/-- **A family of locally spanning sections of `ℱ|_X'` transports to one of `ℱ`**, for
`i : X' ⟶ Y` an open immersion. The sections of `ℱ|_X'` over an open `W` of `X'` are the sections
of `ℱ` over the image of `W`, and every open of `Y` contained in the image of `i` is the image of
an open of `X'`, so the only thing to move is the scalars, along
`AlgebraicGeometry.Scheme.Hom.appIso`. -/
public theorem localSpan_of_restrict {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]
    (F : Y.Modules) (x : X)
    (h : Stacks.RingedSpace.IsFiniteType
      (⟨((restrictFunctor i).obj F).val, ((restrictFunctor i).obj F).isSheaf⟩ :
        AlgebraicGeometry.RingedSpace.ModuleSheaf X.toRingedSpace)) :
    ∃ (U : Y.Opens) (_ : i.base x ∈ U) (n : ℕ) (s : Fin n → F.val.obj (op U)),
      ∀ (V : Y.Opens) (hVU : V ≤ U) (t : F.val.obj (op V)) (y : Y), y ∈ V →
        ∃ (W : Y.Opens) (hWV : W ≤ V), y ∈ W ∧
          F.val.map (homOfLE hWV).op t ∈
            Submodule.span (Y.ringCatSheaf.obj.obj (op W))
              (Set.range fun j => F.val.map (homOfLE (hWV.trans hVU)).op (s j)) := by
  obtain ⟨U, hx, n, s, hs⟩ := h x
  refine ⟨i ''ᵁ U, (i.apply_mem_image_iff).mpr hx, n, s, ?_⟩
  intro V hVU
  have heq : i ''ᵁ (i ⁻¹ᵁ V) = V := by
    rw [i.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr (hVU.trans (i.image_le_opensRange U))
  obtain ⟨V', rfl⟩ : ∃ V' : X.Opens, i ''ᵁ V' = V := ⟨i ⁻¹ᵁ V, heq⟩
  intro t y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hVU' : V' ≤ U := (i.image_le_image_iff _ _).mp hVU
  obtain ⟨W, hWV, hzW, ht⟩ := hs V' hVU' t z hz
  refine ⟨i ''ᵁ W, i.image_mono hWV, (i.apply_mem_image_iff).mpr hzW, ?_⟩
  set P := Submodule.span (Y.ringCatSheaf.obj.obj (op (i ''ᵁ W)))
    (Set.range fun j => F.val.map (homOfLE ((i.image_mono hWV).trans hVU)).op (s j))
  have hspan : ∀ a : ((restrictFunctor i).obj F).val.obj (op W),
      a ∈ Submodule.span (X.ringCatSheaf.obj.obj (op W))
        (Set.range fun j => ((restrictFunctor i).obj F).val.map
          (homOfLE (hWV.trans hVU')).op (s j)) → a ∈ P := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact Submodule.subset_span ha
    | zero => exact Submodule.zero_mem P
    | add _ _ _ _ ha' hb' => exact Submodule.add_mem P ha' hb'
    | smul r a ha ha' => exact Submodule.smul_mem P ((i.appIso W).inv.hom r) ha'
  exact hspan _ ht

/-- **Finite type is local on a scheme.** If the restriction of `ℱ` to each member of an open
cover is of finite type, so is `ℱ`.

Both sides are read in the section-and-local-span form through
`Stacks.RingedSpace.isFiniteType_iff_localSpan`, where the statement is about sections and
`AlgebraicGeometry.Scheme.Modules.localSpan_of_restrict` applies. -/
public theorem isFiniteType_of_isFiniteType_restrict {X : Scheme.{u}} (F : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : (⨆ j, U j) = ⊤)
    (h : ∀ j, ((restrictFunctor (U j).ι).obj F).IsFiniteType) : F.IsFiniteType := by
  refine Stacks.RingedSpace.isFiniteType_of_localSpan F fun x => ?_
  obtain ⟨j, hxj⟩ := Opens.mem_iSup.mp (hU ▸ Opens.mem_top x)
  exact localSpan_of_restrict (U j).ι F ⟨x, hxj⟩
    (Stacks.RingedSpace.localSpan_of_isFiniteType _ (h j))

/-! ### Stacks 01C4 for a closed immersion of schemes -/

/-- **Stacks 01C4 for a closed immersion of schemes.** A sheaf of modules on the source is of
finite type if and only if its direct image is.

The `stacks` attribute sits on the ringed-space form
`Stacks.RingedSpace.isFiniteType_modulePushforward_iff`, which is the tag's own generality; this
is its specialization to schemes, where the surjectivity hypothesis on the structure-sheaf map is
automatic. -/
public theorem isFiniteType_pushforward_iff {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (F : Z.Modules) :
    ((pushforward i).obj F).IsFiniteType ↔ F.IsFiniteType := by
  have := isLocallySurjective_c i
  exact Stacks.RingedSpace.isFiniteType_modulePushforward_iff' i.toLRSHom.toShHom
    i.isClosedEmbedding F

/-! ### The local condition of Stacks 09UI in degree zero -/

attribute [local instance] HasDerivedCategory.standard

/-- **The local condition of Stacks 09UI in degree `0` for a sheaf of modules is finiteness of
type.** For a closed immersion `i` out of an open subscheme `U` of `X`, the derived pushforward
along `i` of the restriction of `ℱ` to `U`, placed in degree zero, is `0`-pseudo-coherent exactly
when `ℱ|_U` is of finite type.

Pushing forward along a closed immersion and restricting to an open subscheme are both exact, so
both carry a module placed in degree zero to a module placed in degree zero; by Stacks 09V9(1)
the condition is then finiteness of type of `i_*(ℱ|_U)`, and by Stacks 01C4 that is finiteness of
type of `ℱ|_U`. -/
public theorem isPseudoCoherentFromAfterPushforward_singleFunctor_zero_iff {X Y : Scheme.{u}}
    (U : X.Opens) (i : (U : Scheme.{u}) ⟶ Y) [IsClosedImmersion i] (F : X.Modules) :
    IsPseudoCoherentFromAfterPushforward i
        ((restrictFunctor U.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) 0 ↔
      ((restrictFunctor U.ι).obj F).IsFiniteType := by
  rw [isPseudoCoherentFromAfterPushforward_iff, ← isFiniteType_pushforward_iff i]
  refine Iff.trans ?_
    (RingedSpace.isPseudoCoherentFrom_singleFunctor_zero_iff_isFiniteType.{u, u + 1} _)
  let e := (pushforward i).mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategorySingleFunctor (restrictFunctor U.ι) 0).app F) ≪≫
    (Functor.mapDerivedCategorySingleFunctor (pushforward i) 0).app ((restrictFunctor U.ι).obj F)
  exact ⟨fun h => h.of_iso e, fun h => h.of_iso e.symm⟩

end AlgebraicGeometry.Scheme.Modules

end
