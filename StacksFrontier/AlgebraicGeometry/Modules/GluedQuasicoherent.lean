module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentLocal
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeLocal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison

/-!
# A sheaf glued from quasi-coherent charts is quasi-coherent

Stacks 00AM glues a family of sheaves of `𝒪_S`-modules `N i`, compared over the overlaps of a
family of opens `U i`, into a single sheaf of modules on `S`. The construction records the
comparison of the glued sheaf with the `N i` only on *sections*
(`Stacks.SheafOfModules.OModuleGlueData.chartIso`). This file upgrades that to an isomorphism in
the category of sheaves of modules on the open subscheme `U i`, and deduces that the glued sheaf is
quasi-coherent as soon as each `N i` is quasi-coherent on its own chart.

Both facts are what a construction of a quasi-coherent sheaf by glueing actually needs: the
quasi-coherence of the result is not part of 00AM, and the section comparison alone is not enough
to get it, because quasi-coherence is local on the base in the form
`Stacks.Modules.isQuasicoherent_of_restrict`, which asks for an isomorphism of *sheaves* on each
member of the cover.

## Main definitions

* `Stacks.SheafOfModules.OModuleGlueData.ofModulesRestrictIso`: the glued sheaf restricted to a
  member of the cover is isomorphic, in `(U i).toScheme.Modules`, to the `i`-th member of the
  datum restricted there.

## Main results

* `Stacks.SheafOfModules.isQuasicoherent_gluedModules_ofModules`: if the family of opens covers
  `S` and each member of the datum is quasi-coherent after restriction to its chart, the glued
  sheaf of modules is quasi-coherent.
* `Stacks.SheafOfModules.isFiniteType_gluedModules_ofModules`: the same for being of finite type.
* `Stacks.SheafOfModules.isCoherent_gluedModules_ofModules`: on a locally Noetherian scheme, a
  sheaf glued from charts that are quasi-coherent and of finite type is coherent.

## Implementation notes

The isomorphism is assembled component by component from the section comparison at the open
`(U i).ι ''ᵁ V` of `S`, for `V` an open of the open subscheme; no statement here transports along
an identification of opens, because the sections of a restricted sheaf of modules over `V` are by
construction the sections over `(U i).ι ''ᵁ V` — only the *ring* of scalars changes, which is what
the `ModuleCat.restrictScalars` wrapper records. Naturality is
`OModuleGlueData.chartLinearEquiv_restrict`, i.e. the statement that the section comparison
commutes with restriction.

The datum is taken in the form `OModuleGlueData.ofModules`, rather than as an arbitrary
`OModuleGlueData`, because only then is the `i`-th member of the datum definitionally the sheaf
`N i` read on the opens contained in `U i`, which is what makes the component isomorphisms
typecheck without transport.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {S : Scheme.{u}} {ι : Type u} {U : ι → S.Opens}

namespace OModuleGlueData

/-- The glued sheaf of modules, restricted to a member of the cover, is isomorphic to the member
of the glueing datum it was glued from, restricted there. This is
`OModuleGlueData.chartIso` assembled into an isomorphism of sheaves of modules on
`(U i).toScheme`. -/
public def ofModulesRestrictIso (N : ι → S.Modules)
    (t : ∀ (i j : ι) {V : S.Opens} (_hi : V ≤ U i) (_hj : V ≤ U j),
      (N i).val.obj (op V) ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))] (N j).val.obj (op V))
    (tm : ∀ (i j : ι) {V W : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : ToType ((N i).val.obj (op V))),
      t i j (hWV.trans hi) (hWV.trans hj) ((N i).val.map (homOfLE hWV).op s)
        = (N j).val.map (homOfLE hWV).op (t i j hi hj s))
    (tt : ∀ (i j k : ι) {V : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : ToType ((N i).val.obj (op V))),
      t j k hj hk (t i j hi hj s) = t i k hi hk s)
    (i : ι) :
    (ofModules (U := U) N t tm tt).gluedModules.restrict (U i).ι ≅ (N i).restrict (U i).ι :=
  Scheme.Modules.fullyFaithfulToPresheafOfModules.preimageIso
    (PresheafOfModules.isoMk
      (fun V => (ModuleCat.restrictScalars (((U i).ι.appIso V.unop).inv).hom).mapIso
        ((ofModules (U := U) N t tm tt).chartIso i ((U i).ι_image_le V.unop)))
      (by
        intro V W g
        refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
        exact (ofModules (U := U) N t tm tt).chartLinearEquiv_restrict i
          ((U i).ι_image_le V.unop) (Scheme.Hom.image_mono _ (leOfHom g.unop)) s))

end OModuleGlueData

/-- **A sheaf of modules glued from quasi-coherent charts is quasi-coherent.** If the opens `U i`
cover the scheme and each member of a glueing datum of sheaves of modules is quasi-coherent after
restriction to its own chart, then the sheaf of modules glued from the datum is quasi-coherent. -/
public theorem isQuasicoherent_gluedModules_ofModules (hU : iSup U = ⊤) (N : ι → S.Modules)
    (t : ∀ (i j : ι) {V : S.Opens} (_hi : V ≤ U i) (_hj : V ≤ U j),
      (N i).val.obj (op V) ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))] (N j).val.obj (op V))
    (tm : ∀ (i j : ι) {V W : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : ToType ((N i).val.obj (op V))),
      t i j (hWV.trans hi) (hWV.trans hj) ((N i).val.map (homOfLE hWV).op s)
        = (N j).val.map (homOfLE hWV).op (t i j hi hj s))
    (tt : ∀ (i j k : ι) {V : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : ToType ((N i).val.obj (op V))),
      t j k hj hk (t i j hi hj s) = t i k hi hk s)
    (hN : ∀ i, ((N i).restrict (U i).ι).IsQuasicoherent) :
    (OModuleGlueData.ofModules (U := U) N t tm tt).gluedModules.IsQuasicoherent := by
  refine Stacks.Modules.isQuasicoherent_of_restrict _ U hU fun i => ?_
  exact Stacks.Descent.isQuasicoherent_of_iso
    (OModuleGlueData.ofModulesRestrictIso N t tm tt i).symm (hN i)

/-- **A sheaf of modules glued from charts of finite type is of finite type.** -/
public theorem isFiniteType_gluedModules_ofModules (hU : iSup U = ⊤) (N : ι → S.Modules)
    (t : ∀ (i j : ι) {V : S.Opens} (_hi : V ≤ U i) (_hj : V ≤ U j),
      (N i).val.obj (op V) ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))] (N j).val.obj (op V))
    (tm : ∀ (i j : ι) {V W : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : ToType ((N i).val.obj (op V))),
      t i j (hWV.trans hi) (hWV.trans hj) ((N i).val.map (homOfLE hWV).op s)
        = (N j).val.map (homOfLE hWV).op (t i j hi hj s))
    (tt : ∀ (i j k : ι) {V : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : ToType ((N i).val.obj (op V))),
      t j k hj hk (t i j hi hj s) = t i k hi hk s)
    (hN : ∀ i, ((N i).restrict (U i).ι).IsFiniteType) :
    (OModuleGlueData.ofModules (U := U) N t tm tt).gluedModules.IsFiniteType := by
  refine AlgebraicGeometry.isFiniteType_of_restrict _ U hU fun i => ?_
  exact Stacks.Coherent.isFiniteType_of_iso_local
    (OModuleGlueData.ofModulesRestrictIso N t tm tt i).symm (hN i)

/-- **A sheaf of modules on a locally Noetherian scheme glued from coherent charts is coherent.**
Precisely: if each member of the glueing datum is quasi-coherent and of finite type after
restriction to its own chart, the glued sheaf is coherent. This is the form in which a
construction by glueing produces a coherent sheaf: quasi-coherence and finite type are each local
on the base, and on a locally Noetherian scheme their conjunction is coherence (Tag 01XZ). -/
public theorem isCoherent_gluedModules_ofModules [IsLocallyNoetherian S] (hU : iSup U = ⊤)
    (N : ι → S.Modules)
    (t : ∀ (i j : ι) {V : S.Opens} (_hi : V ≤ U i) (_hj : V ≤ U j),
      (N i).val.obj (op V) ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))] (N j).val.obj (op V))
    (tm : ∀ (i j : ι) {V W : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hWV : W ≤ V)
      (s : ToType ((N i).val.obj (op V))),
      t i j (hWV.trans hi) (hWV.trans hj) ((N i).val.map (homOfLE hWV).op s)
        = (N j).val.map (homOfLE hWV).op (t i j hi hj s))
    (tt : ∀ (i j k : ι) {V : S.Opens} (hi : V ≤ U i) (hj : V ≤ U j) (hk : V ≤ U k)
      (s : ToType ((N i).val.obj (op V))),
      t j k hj hk (t i j hi hj s) = t i k hi hk s)
    (hq : ∀ i, ((N i).restrict (U i).ι).IsQuasicoherent)
    (hf : ∀ i, ((N i).restrict (U i).ι).IsFiniteType) :
    _root_.SheafOfModules.IsCoherent
      (OModuleGlueData.ofModules (U := U) N t tm tt).gluedModules := by
  have := isQuasicoherent_gluedModules_ofModules hU N t tm tt hq
  have := isFiniteType_gluedModules_ofModules hU N t tm tt hf
  exact Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_of_isQuasicoherent_of_isFiniteType
    _

end Stacks.SheafOfModules

end
