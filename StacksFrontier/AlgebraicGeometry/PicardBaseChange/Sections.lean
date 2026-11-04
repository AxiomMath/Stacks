module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeData
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.Topology.Sheaves.Modules.Invertible

/-!
# Global sections of an invertible module trivialized by a faithfully flat base change

Let `X` be a quasi-compact, quasi-separated scheme over a ring `A`, let `φ : A →+* B` be
faithfully flat, and let `L` be an invertible `𝒪_X`-module whose pullback to `X_B` is trivial.
Tag 0CDX asserts, among other things, that `Γ(X, L)` is then an invertible module over
`Γ(X, 𝒪_X)`. This file proves that clause.

Its three ingredients are now all available:

* `Γ(X, 𝒪_X) → Γ(X_B, 𝒪_{X_B})` is faithfully flat —
  `Stacks.AlgebraicGeometry.PicardBaseChange.faithfullyFlat_appTop_pullback_fst`;
* `Γ(X, L)` base changes to `Γ(X_B, L_B)` along it — degree-zero flat base change for a
  quasi-coherent module,
  `Stacks.AlgebraicGeometry.SectionsBaseChange.isBaseChange_appTop_pullbackSections`;
* invertibility of a module descends along a faithfully flat ring map —
  `Module.Invertible.of_trivial_baseChange_of_faithfullyFlat`.

## Main definitions

* `Stacks.AlgebraicGeometry.PicardBaseChange.unitModule`: the structure sheaf as an
  `𝒪_Y`-module, spelled at `Y.Modules` so that the module structure on its sections is found by
  instance search.
* `Stacks.AlgebraicGeometry.PicardBaseChange.pullbackAppTopLinear`: pulling a global section
  back, as a `Γ(X, 𝒪_X)`-linear map `Γ(X, L) → Γ(Y, p^* L)`.

## Main results

* `Stacks.AlgebraicGeometry.PicardBaseChange.nonempty_linearEquiv_appTop_of_isTrivial`: a trivial
  `𝒪_Y`-module has `Γ(Y, L) ≃ₗ[Γ(Y, 𝒪_Y)] Γ(Y, 𝒪_Y)`.
* `Stacks.AlgebraicGeometry.PicardBaseChange.invertible_appTop_of_isTrivial`: the general form,
  for any cartesian square with affine bases.
* `Stacks.AlgebraicGeometry.PicardBaseChange`
  `.invertible_globalSections_of_faithfullyFlat_trivialization`:
  **Tag 0CDX, the clause about the global sections of the sheaf.**

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a plain `def`, so instance search does not see through it;
`unitModule` is an `abbrev` at `Y.Modules` for this reason, and it is what
makes `Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤)` carry its `Γ(Y, ⊤)`-module structure. Without
it the triviality hypothesis cannot be read on sections at all.

The `Γ(X, 𝒪_X)`-algebra structure on `Γ(Y, 𝒪_Y)` and the `Γ(X, 𝒪_X)`-module structure on
`Γ(Y, p^* L)` are restrictions of scalars along `p` and are not instances; the general form takes
the algebra structure as a hypothesis pinned by its algebra map, and builds the module structure
from `Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule`.

The hypotheses are those of the Chapter 33 decomposition of Tag 0CDX, with Tag 01CS's
`IsInvertible` and `IsTrivial` read as `AlgebraicGeometry.SheafOfModules.IsInvertible` and
`AlgebraicGeometry.SheafOfModules.IsTrivial`, and the ringed-space pullback
`RingedSpaceModuleAdjunction.modulePullback p.toLRSHom.toShHom` read as
`AlgebraicGeometry.Scheme.Modules.pullback p`, to which it is equal by `rfl`.

Only this one clause of Tag 0CDX is proved here. The clause for the inverse tensor power is in
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/InverseSections.lean`; it needs **no** comparison between the pullback of a tensor power and the
tensor power of the pullback — the binary Tag 01CD comparison and the defining iteration of
Tag 01CU suffice. The clause about the canonical multiplication is in
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/MulIsomorphism.lean`, transcribed with Tag 01CU's coherent multiplication
in `StacksFrontier/AlgebraicGeometry/PicardBaseChange/CoherentMul.lean`; the
compatibility of that multiplication with base change is available and is proved there. The tag
is part-qualified exactly as the decomposition qualifies it, with one site per clause.

## References

* [Stacks Project, Tag 0CDX](https://stacks.math.columbia.edu/tag/0CDX)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 058S](https://stacks.math.columbia.edu/tag/058S)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.SectionsBaseChange

namespace Stacks.AlgebraicGeometry.PicardBaseChange

/-- The structure sheaf as an `𝒪_Y`-module, spelled at `Y.Modules`. The spelling matters:
`AlgebraicGeometry.Scheme.Modules` is a plain `def`, so the module structure on
`Γ(SheafOfModules.unit Y.ringCatSheaf, U)` is not found by instance search, while the one on
`Γ(unitModule Y, U)` is. -/
abbrev unitModule (Y : Scheme.{u}) : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

/-- **A trivial module has free global sections of rank one.** -/
theorem nonempty_linearEquiv_appTop_of_isTrivial (Y : Scheme.{u}) (L : Y.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsTrivial Y.presheaf Y.ringCatSheaf.property L) :
    Nonempty (Γ(L, (⊤ : Y.Opens)) ≃ₗ[Γ(Y, ⊤)] Γ(Y, ⊤)) := by
  obtain ⟨e⟩ := hL
  let e' : L ≅ unitModule Y := e
  have hiso : Function.Bijective (e'.hom.app (⊤ : Y.Opens)) :=
    ConcreteCategory.bijective_of_isIso _
  exact ⟨LinearEquiv.ofBijective
    { toFun := fun a => ((e'.hom.app (⊤ : Y.Opens)).hom a : Γ(Y, ⊤))
      map_add' := fun a b => (e'.hom.app (⊤ : Y.Opens)).hom.map_add a b
      map_smul' := fun r a => Scheme.Modules.Hom.app_smul e'.hom r a } hiso⟩

/-- Over the whole space, `AlgebraicGeometry.Scheme.Hom.appLE` is
`AlgebraicGeometry.Scheme.Hom.app`. -/
theorem appLE_top_top {X Y : Scheme.{u}} (p : Y ⟶ X) :
    p.appLE ⊤ ⊤ (le_preimage_top p ⊤) = p.app ⊤ := by
  simp [Scheme.Hom.app_eq_appLE]

/-- **Pulling a global section back, as a linear map** over the global functions of the target.
-/
def pullbackAppTopLinear {X Y : Scheme.{u}} (p : Y ⟶ X) (L : X.Modules) :
    letI := baseModule p ((Scheme.Modules.pullback p).obj L) ⊤
    Γ(L, ⊤) →ₗ[Γ(X, ⊤)] Γ((Scheme.Modules.pullback p).obj L, ⊤) :=
  letI := baseModule p ((Scheme.Modules.pullback p).obj L) ⊤
  { toFun := pullbackSectionsHom p L ⊤ ⊤ (le_preimage_top p ⊤)
    map_add' := (pullbackSectionsHom p L ⊤ ⊤ (le_preimage_top p ⊤)).map_add
    map_smul' := fun r a => by
      change pullbackSectionsHom p L ⊤ ⊤ (le_preimage_top p ⊤) (r • a) =
        (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom r •
          pullbackSectionsHom p L ⊤ ⊤ (le_preimage_top p ⊤) a
      rw [pullbackSectionsHom_top, pullbackSectionsHom_top, appLE_top_top,
        pullbackUnitSections_smul]
      rfl }

/-- **Invertibility of the global sections descends from a trivializing faithfully flat base
change.** This is Tag 0CDX's clause about the global sections of the sheaf, for an arbitrary
cartesian square with affine bases. -/
theorem invertible_appTop_of_isTrivial
    {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
    (H : IsPullback p k iX q) [IsAffine S] [IsAffine T] [Flat q]
    [CompactSpace X] [QuasiSeparatedSpace X] (L : X.Modules) [L.IsQuasicoherent]
    [Algebra Γ(X, ⊤) Γ(Y, ⊤)]
    (halg : ∀ r, algebraMap Γ(X, ⊤) Γ(Y, ⊤) r = (p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom r)
    [Module.FaithfullyFlat Γ(X, ⊤) Γ(Y, ⊤)]
    (hL : AlgebraicGeometry.SheafOfModules.IsTrivial Y.presheaf Y.ringCatSheaf.property
      ((Scheme.Modules.pullback p).obj L)) :
    Module.Invertible Γ(X, ⊤) Γ(L, ⊤) := by
  let modXG : Module Γ(X, ⊤) Γ((Scheme.Modules.pullback p).obj L, ⊤) :=
    baseModule p ((Scheme.Modules.pullback p).obj L) ⊤
  have towerXYG : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ((Scheme.Modules.pullback p).obj L, ⊤) :=
    Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
      ((p.appLE ⊤ ⊤ (le_preimage_top p ⊤)).hom) (fun _ _ => rfl) (fun a => (halg a).symm)
  have hbc : IsBaseChange Γ(Y, ⊤) (pullbackAppTopLinear p L) :=
    isBaseChange_appTop_pullbackSections H L halg _ (fun _ => rfl)
  exact Module.Invertible.of_trivial_baseChange_of_faithfullyFlat _ hbc
    (nonempty_linearEquiv_appTop_of_isTrivial _ _ hL)

/-- **Stacks Project, Tag 0CDX, the clause about the global sections of the sheaf.** For a
quasi-compact, quasi-separated scheme `X` over `A`, a faithfully flat ring map `φ : A →+* B` and
an invertible `𝒪_X`-module `L` whose pullback to `X_B` is trivial, the global sections `Γ(X, L)`
form an invertible module over the global functions `Γ(X, 𝒪_X)`. -/
@[stacks 0CDX "global sections of the sheaf"]
theorem invertible_globalSections_of_faithfullyFlat_trivialization
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.FaithfullyFlat)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules)
    [hinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hL : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf
      (Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).ringCatSheaf.property
      ((Scheme.Modules.pullback
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj L)) :
    Module.Invertible Γ(X, ⊤) Γ(L, ⊤) := by
  have hinv' : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
    X.ringCatSheaf.property L := hinv
  have hLqc : L.IsQuasicoherent := AlgebraicGeometry.isQuasicoherent_of_isInvertible L
  have hq : Flat (Spec.map (CommRingCat.ofHom φ)) := Flat.SpecMap_iff.mpr hφ.flat
  let algXY : Algebra Γ(X, ⊤) Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appTop.hom.toAlgebra
  have halg : ∀ r, algebraMap Γ(X, ⊤)
      Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) r =
      ((Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ))).appLE ⊤ ⊤
        (le_preimage_top _ ⊤)).hom r := by
    intro r
    rw [appLE_top_top]
    rfl
  have hff : Module.FaithfullyFlat Γ(X, ⊤)
      Γ(Limits.pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    faithfullyFlat_appTop_pullback_fst hφ f
  exact invertible_appTop_of_isTrivial
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom φ))) L halg hL

end Stacks.AlgebraicGeometry.PicardBaseChange

end
