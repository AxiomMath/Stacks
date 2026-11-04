module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleFiniteness.FiniteType

/-!
# Coherence of a module on a scheme is local on an open cover

A module on a locally Noetherian scheme whose restriction to each member of an open covering is
coherent is coherent. This is the globalisation step of [Stacks, Tag 01XZ] that the statement of
`Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae` does not provide: condition (5) of
that list speaks of `Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn`, a condition on
*affine* opens, while the coverings produced by local constructions — for instance the covering
on which a perfect complex has a strictly perfect model — are by arbitrary opens.

## Main results

* `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_restrict`: the restriction of a
  coherent module along an open immersion is coherent.
* `Stacks.AlgebraicGeometry.PerfectCohomology.isFiniteTildeOn_of_isCoherent_restrict`: on an
  affine open, coherence of the restriction gives condition (4) of [Stacks, Tag 01XZ].
* `Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_cover_restrict`: **coherence is
  local on an open covering of a locally Noetherian scheme.**

## Implementation notes

`Stacks.SheafOfModules.isCoherent_of_coversTop` glues the *slice-site* form
`Stacks.SheafOfModules.IsCoherentOn`, which is not the form a restriction along an open
immersion produces; the route taken here is instead through condition (4) of [Stacks, Tag 01XZ],
which is about `AlgebraicGeometry.Scheme.Modules.restrict` and so matches.

`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde` already builds the isomorphism of
condition (4), but assumes the module quasi-coherent on the whole scheme, which is not available
before the globalisation; `restrictIsoSpecTildeOfLocal` is the same isomorphism with that
hypothesis replaced by quasi-coherence of the restriction alone, which is all its proof uses.

`isFiniteType_of_iso` and `isQuasicoherent_of_iso` below are aliases of
`AlgebraicGeometry.isFiniteType_of_iso` and `Stacks.Descent.isQuasicoherent_of_iso`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules

universe u

namespace Stacks.AlgebraicGeometry.PerfectCohomology

/-! ### Transport of the two halves of coherence -/

/-- Being of finite type is invariant under isomorphism, with the hypothesis explicit. -/
alias isFiniteType_of_iso := AlgebraicGeometry.isFiniteType_of_iso

/-- Quasi-coherence is invariant under isomorphism, with the hypothesis explicit. -/
alias isQuasicoherent_of_iso := Stacks.Descent.isQuasicoherent_of_iso

/-- The pullback of a module of finite type is of finite type. -/
theorem isFiniteType_pullback {Y Z : Scheme.{u}} (f : Z ⟶ Y) (M : Y.Modules)
    (h : M.IsFiniteType) : ((Scheme.Modules.pullback f).obj M).IsFiniteType :=
  @SheafOfModules.pullback_isFiniteType _ _ f.toLRSHom.toShHom M h

/-- The restriction of a module of finite type along an open immersion is of finite type. -/
theorem isFiniteType_restrict {Y Z : Scheme.{u}} (f : Z ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (h : M.IsFiniteType) : (M.restrict f).IsFiniteType :=
  isFiniteType_of_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm
    (isFiniteType_pullback f M h)

/-! ### Coherence transported along isomorphisms and restrictions -/

/-- Coherence is invariant under isomorphism, with the hypothesis explicit. -/
theorem isCoherent_of_iso {Y : Scheme.{u}} [IsLocallyNoetherian Y] {M N : Y.Modules}
    (e : M ≅ N) (h : M.IsCoherent) : N.IsCoherent := by
  have := h
  obtain ⟨hq, hft⟩ := CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M
  have := isQuasicoherent_of_iso e hq
  have := isFiniteType_of_iso e hft
  exact CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType N

/-- The restriction of a coherent module along an open immersion is quasi-coherent and of finite
type. -/
private theorem isQuasicoherent_and_isFiniteType_restrict {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (h : M.IsCoherent) :
    (M.restrict f).IsQuasicoherent ∧ (M.restrict f).IsFiniteType := by
  have := h
  obtain ⟨hq, hft⟩ := CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M
  have := hq
  exact ⟨Scheme.Modules.isQuasicoherent_restrictFunctor f M, isFiniteType_restrict f M hft⟩

/-- **The restriction of a coherent module along an open immersion is coherent.** Coherence on a
locally Noetherian scheme is quasi-coherence together with finite type, and restriction along an
open immersion preserves both. -/
theorem isCoherent_restrict {Y Z : Scheme.{u}} [IsLocallyNoetherian Y] (f : Z ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (h : M.IsCoherent) : (M.restrict f).IsCoherent := by
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isOpenImmersion f
  obtain ⟨_, _⟩ := isQuasicoherent_and_isFiniteType_restrict f M h
  exact CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType (M.restrict f)

/-! ### Condition (4) of Tag 01XZ from coherence of the restriction -/

/-- **`F|_V` is the `tilde` of `Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hV`** as soon
as `F|_V`, read on `Spec Γ(X, V)`, is quasi-coherent. This is
`Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSpecTilde` with its global quasi-coherence
hypothesis weakened to the one its proof uses. -/
noncomputable def restrictIsoSpecTildeOfLocal {X : Scheme.{u}} (F : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (hq : (CoherentTFAE.specRestrict F hV).IsQuasicoherent) :
    F.restrict V.ι ≅
      (Scheme.Modules.pullback hV.isoSpec.hom).obj (tilde (CoherentTFAE.specModule F hV)) :=
  have := hq
  (CoherentTFAE.restrictIsoSelf hV.isoSpec (F.restrict V.ι)).symm ≪≫
    (Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapIso
      (asIso (CoherentTFAE.specRestrict F hV).fromTildeΓ).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback hV.isoSpec.hom).app _

/-- **Coherence of `F|_V` for `V` an affine open gives condition (4) of [Stacks, Tag 01XZ] at
`V`.** Coherence of the restriction makes it quasi-coherent and of finite type; read on
`Spec Γ(X, V)` it is then the `tilde` of its module of global sections, and that module is
finite because the `tilde` is of finite type. -/
theorem isFiniteTildeOn_of_isCoherent_restrict {X : Scheme.{u}} (F : X.Modules) {V : X.Opens}
    (hV : IsAffineOpen V) (h : (F.restrict V.ι).IsCoherent) :
    CoherentTFAE.IsFiniteTildeOn F V hV := by
  obtain ⟨hqs, hfts⟩ := isQuasicoherent_and_isFiniteType_restrict hV.isoSpec.inv
    (F.restrict V.ι) h
  have := hqs
  have htilde : (tilde (CoherentTFAE.specModule F hV)).IsFiniteType :=
    isFiniteType_of_iso (asIso (CoherentTFAE.specRestrict F hV).fromTildeΓ).symm hfts
  exact ⟨CoherentTFAE.specModule F hV, (tilde_isFiniteType_iff _).1 htilde,
    ⟨restrictIsoSpecTildeOfLocal F hV hqs⟩⟩

/-! ### Coherence is local on an open covering -/

/-- The affine opens lying inside some member of an open covering form an open covering. -/
theorem isOpenCover_affineOpens_subordinate {X : Scheme.{u}} {I : Type u} (U : I → X.Opens)
    (hU : IsOpenCover U) :
    IsOpenCover
      (fun j : (i : I) × {V : X.Opens // IsAffineOpen V ∧ V ≤ U i} => (j.2.1 : X.Opens)) := by
  refine IsOpenCover.mk ?_
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hU.iSup_eq_top ▸ Opens.mem_top x)
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hxi
  exact Opens.mem_iSup.mpr ⟨⟨i, ⟨W, hW, hWU⟩⟩, hxW⟩

/-- **Coherence is local on an open covering of a locally Noetherian scheme.** The affine opens
inside the members of the covering again cover the scheme, coherence restricts to them, and on
an affine open coherence of the restriction is condition (4) of [Stacks, Tag 01XZ]; condition
(5) then gives coherence on the whole scheme. -/
theorem isCoherent_of_cover_restrict {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : IsOpenCover U)
    (h : ∀ i, (F.restrict (U i).ι).IsCoherent) : F.IsCoherent := by
  refine CoherenceCriteria.isCoherent_of_exists_affineOpenCover_isFiniteTildeOn F
    ⟨(i : I) × {V : X.Opens // IsAffineOpen V ∧ V ≤ U i}, fun j => (j.2.1 : X.Opens),
      isOpenCover_affineOpens_subordinate U hU, fun j => ⟨j.2.2.1, ?_⟩⟩
  obtain ⟨i, ⟨V, hV, hVU⟩⟩ := j
  have hrestr : ((F.restrict (U i).ι).restrict (X.homOfLE hVU)).IsCoherent :=
    isCoherent_restrict (X.homOfLE hVU) (F.restrict (U i).ι) (h i)
  refine isFiniteTildeOn_of_isCoherent_restrict F hV (isCoherent_of_iso ?_ hrestr)
  exact ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVU) (U i).ι).app F).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVU)).app F

end Stacks.AlgebraicGeometry.PerfectCohomology

end
