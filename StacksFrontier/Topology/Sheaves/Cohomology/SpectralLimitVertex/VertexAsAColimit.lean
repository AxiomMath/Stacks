module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ComparisonReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.GermPullbackSystem
public import StacksFrontier.Topology.Spectral.AsDirectedInverseLimit

/-!
# Step 2 of Tag 0A37 over the vertex of an abstract cone, and the factorization of base change

`StacksDraft.Ch20.Sec16.Tag0A37PullSystem` exhibits the sheaf on the vertex of a limiting cone of
abelian sheafed spaces as the colimit `colimₖ pₖ⁻¹Fₖ` of the germ-model inverse images, as an
actual colimit cocone.  This file draws the two consequences that the colimit-comparison clauses
of Tag 0A37 need.

**First**, the space underlying the vertex is a *spectral space*: it is homeomorphic to the
concrete inverse limit `S.invLim`, which is spectral by Stacks 0A2Z, and spectrality transports
along a homeomorphism.  With that, abelian Stacks 01FF — which asks only that the ambient space
be prespectral and quasi-separated — applies to the system on the abstract vertex, and **step 2
of the Stacks factorization becomes available there in every degree, with no reference to
`S.invLim` at all**.  That was impossible before the vertex carried a system of sheaves with a
colimit.

**Second**, the `k`-th cone projection factors as `colegMor k ≫ pullProj k`: base change to the
vertex, whose target carries `pₖ⁻¹Fₖ`, followed by the morphism whose sheaf component is the
`k`-th leg of the comparison cocone.  Applying `spaceCohomologyMap_comp` to that factorization
splits the base-change map on cohomology as

  `Hᑫ(U, Fₖ) ⟶ Hᑫ(pₖ⁻¹U, pₖ⁻¹Fₖ) ⟶ Hᑫ(pₖ⁻¹U, c.pt.sheaf)`,

whose second factor is the `k`-th component of the source of `vertexComparison`.

## Main definitions

* `SpectralAbelianSheafSystem.conePointIso`: the homeomorphism from the space underlying `c.pt`
  to `S.invLim`.
* `SpectralAbelianSheafSystem.vertexColimitIso` and `SpectralAbelianSheafSystem.vertexComparison`:
  the identification of `c.pt.sheaf` with `colimₖ pₖ⁻¹Fₖ`, and the comparison of step 2.
* `SpectralAbelianSheafSystem.pullSpace`, `pullProj`, `colegMor`: the vertex carrying `pₖ⁻¹Fₖ` and
  the two morphisms of abelian sheafed spaces that the `k`-th cone projection factors into.

## Main results

* `SpectralAbelianSheafSystem.spectralSpace_conePoint`: **the space underlying the vertex of a
  limiting cone is spectral**.
* `SpectralAbelianSheafSystem.isSpectralMap_projFun` and `isCompact_legPreimage`: the cone
  projections are spectral maps, so `pᵢ⁻¹U` is quasi-compact for `U` a quasi-compact open of a
  stage.
* `SpectralAbelianSheafSystem.isIso_colimit_post_H'functor_pullSystem` and
  `isIso_vertexComparison`: **step 2 of the factorization of Tag 0A37, over the vertex of an
  abstract cone, in every degree and unconditionally**, with
  `isIso_vertexComparison_stageOpen` at the open carried by the stage clause's open cone.
* `SpectralAbelianSheafSystem.colegMor_comp_pullProj` and `spaceCohomologyMap_leg_eq`: **the
  factorization of the cone projection and of the base-change map on cohomology**.

## Implementation notes

`pullSpace` is written as a structure literal rather than as `SheafedSpaceLimit.reseat`, and as
an `abbrev`.  `reseat` is a semireducible `def`, so instance search — which works at `instances`
transparency — cannot see that the carrier of `reseat c H hH` is the space underlying `c.pt`, and
the `Additive` instance for sections over an open of that space is then not found.  Writing the
carrier field out makes the projection reduce.

`isIso_vertexComparison` is stated through a plain isomorphism of colimit vertices rather than by
transporting the colimit cocone along `Cocone.functoriality`: the latter forces the elaborator to
identify `(Cocone.functoriality F G).obj X` with `G.mapCocone X`, which exhausts the heartbeat
budget on these cocones. The instance `IsIso ((H'functor U q).map _)` likewise has to be seated
as a named `have` through `Functor.mapIso`.

## References

* [Stacks Project, Tag 0A2Z](https://stacks.math.columbia.edu/tag/0A2Z)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

open Stacks.Cohomology Stacks.Cohomology.SpectralLimit
open Stacks.Cohomology.SpectralLimit.SheafedSpaceLimit

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- **The space underlying the vertex of a limiting cone is the inverse limit of the stages.**
`SheafedSpace.forget` is a right adjoint (`SheafedSpaceLimit.isRightAdjoint_forget`), so it
carries `c` to a limiting cone of spaces; `S.invLim` is `Limits.limit S.baseDiagram` with the
limit cone, and two limiting cones of one diagram have canonically isomorphic vertices. -/
def conePointIso (c : Cone S.E) (hc : IsLimit c) : (c.pt : TopCat.{u}) ≅ S.invLim :=
  (SheafedSpaceLimit.isLimit_mapCone_forget hc).conePointUniqueUpToIso
    (limit.isLimit S.typeSystem.diagram.F)

/-- The isomorphism of `conePointIso` commutes with the projections. -/
lemma conePointIso_hom_comp_proj (c : Cone S.E) (hc : IsLimit c) (i : J) :
    (conePointIso S c hc).hom ≫ S.typeSystem.diagram.proj i = (c.π.app i).hom.base :=
  (SheafedSpaceLimit.isLimit_mapCone_forget hc).conePointUniqueUpToIso_hom_comp
    (limit.isLimit S.typeSystem.diagram.F) i

/-- **The space underlying the vertex of a limiting cone of abelian spectral sheafed spaces is a
spectral space.**  The inverse limit of a cofiltered diagram of spectral spaces with spectral
transition maps is spectral (Stacks 0A2Z, `spectralDiagram_invLimit_spectralSpace`), and being a
spectral space transports along a homeomorphism (`SpectralSpace.of_homeomorph`).

This is what makes the fixed-space theory available on the *abstract* vertex: it supplies the
`PrespectralSpace` and `QuasiSeparatedSpace` hypotheses of abelian Stacks 01FF with no reference
to the concrete limit `S.invLim`. -/
theorem spectralSpace_conePoint (c : Cone S.E) (hc : IsLimit c) :
    SpectralSpace ((c.pt : TopCat.{u}) : Type u) :=
  have : SpectralSpace ((S.invLim : TopCat.{u}) : Type u) :=
    spectralDiagram_invLimit_spectralSpace S.typeSystem.diagram
  SpectralSpace.of_homeomorph (TopCat.homeoOfIso (conePointIso S c hc))

/-- **The base map of a cone projection is a spectral map.**  It is the projection out of the
inverse limit, which is spectral by Stacks 0A2Z, precomposed with the homeomorphism of
`conePointIso`. -/
theorem isSpectralMap_projFun (c : Cone S.E) (hc : IsLimit c) (i : J) :
    IsSpectralMap (SheafedSpaceLimit.projFun c i) := by
  set e := TopCat.homeoOfIso (conePointIso S c hc)
  have he : IsSpectralMap e := ⟨e.continuous, fun _ _ hs => e.isCompact_preimage.2 hs⟩
  have hfun : SheafedSpaceLimit.projFun c i = S.typeSystem.diagram.projFun i ∘ e := by
    funext x
    exact (ConcreteCategory.congr_hom (conePointIso_hom_comp_proj S c hc i) x).symm
  rw [hfun]
  exact (spectralDiagram_proj_isSpectralMap S.typeSystem.diagram i).comp he

/-- **The inverse image on the vertex of a quasi-compact open of a stage is quasi-compact.**
This is the quasi-compactness hypothesis of abelian Stacks 01FF at the open `pᵢ⁻¹U` carried by
the open cone of the stage clause of Tag 0A37. -/
theorem isCompact_legPreimage (c : Cone S.E) (hc : IsLimit c) (i : J)
    (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) :
    IsCompact ((Opens.map (c.π.app i).hom.base).obj U).1 :=
  (isSpectralMap_projFun S c hc i).isCompact_preimage_of_isOpen U.isOpen hU

/-- **Step 2 of the Stacks factorization, over the vertex of an abstract cone, in every degree
and unconditionally**: for a quasi-compact open `U` of the vertex,
`colimₖ Hᑫ(U, pₖ⁻¹Fₖ) ⟶ Hᑫ(U, colimₖ pₖ⁻¹Fₖ)` is an isomorphism.

This is abelian Stacks 01FF (`AbelianSpectral.isIso_colimit_post_H'functor_of_isCompact`, itself
unconditional given abelian Stacks 01EW) applied to `SheafedSpaceLimit.pullSystem`.  Its
two space hypotheses come from `spectralSpace_conePoint`, and the index `Jᵒᵖ` is filtered because
`J` is cofiltered.  **Nothing here routes through the concrete limit `S.invLim`**:
`SheafedSpaceLimit.isColimitPullCocone` supplies the system of sheaves on the abstract vertex
that 01FF is applied to. -/
theorem isIso_colimit_post_H'functor_pullSystem (c : Cone S.E) (hc : IsLimit c)
    (U : Opens ((c.pt : TopCat.{u}) : Type u)) (hU : IsCompact U.1) (q : ℕ) :
    IsIso (colimit.post (SheafedSpaceLimit.pullSystem c)
      (AbelianColimit.H'functor U q)) :=
  have : SpectralSpace ((c.pt : TopCat.{u}) : Type u) := spectralSpace_conePoint S c hc
  AbelianSpectral.isIso_colimit_post_H'functor_of_isCompact U hU
    (SheafedSpaceLimit.pullSystem c) q

/-- **The sheaf on the vertex is the colimit of the germ-model inverse images**, as an
isomorphism: the two colimit cocones `colimit.cocone (pullSystem c)` and `pullCocone c` have
canonically isomorphic vertices. -/
def vertexColimitIso (c : Cone S.E) (hc : IsLimit c) :
    colimit (SheafedSpaceLimit.pullSystem c) ≅ c.pt.sheaf :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (SheafedSpaceLimit.pullSystem c))
    (SheafedSpaceLimit.isColimitPullCocone c hc)

/-- **The comparison of Tag 0A37's step 2 on the abstract vertex**:
`colimₖ Hᑫ(U, pₖ⁻¹Fₖ) ⟶ Hᑫ(U, c.pt.sheaf)`, the canonical map out of the colimit followed by the
identification of `colimₖ pₖ⁻¹Fₖ` with the sheaf on the vertex. -/
def vertexComparison (c : Cone S.E) (hc : IsLimit c)
    (U : Opens ((c.pt : TopCat.{u}) : Type u)) (q : ℕ) :
    colimit (SheafedSpaceLimit.pullSystem c ⋙ AbelianColimit.H'functor U q) ⟶
      Sheaf.H'.{u, u, u} c.pt.sheaf q U :=
  colimit.post (SheafedSpaceLimit.pullSystem c) (AbelianColimit.H'functor U q) ≫
    (AbelianColimit.H'functor U q).map (vertexColimitIso S c hc).hom

/-- **The comparison of step 2 on the abstract vertex is an isomorphism** over every
quasi-compact open of the vertex and in every degree: a composite of
`isIso_colimit_post_H'functor_pullSystem` with the image of an isomorphism. -/
theorem isIso_vertexComparison (c : Cone S.E) (hc : IsLimit c)
    (U : Opens ((c.pt : TopCat.{u}) : Type u)) (hU : IsCompact U.1) (q : ℕ) :
    IsIso (vertexComparison S c hc U q) := by
  have := isIso_colimit_post_H'functor_pullSystem S c hc U hU q
  have : IsIso ((AbelianColimit.H'functor U q).map (vertexColimitIso S c hc).hom) :=
    inferInstanceAs
      (IsIso ((AbelianColimit.H'functor U q).mapIso (vertexColimitIso S c hc)).hom)
  exact IsIso.comp_isIso

/-- **Step 2 at the open carried by the open cone of the stage clause of Tag 0A37.**  The open is
`pᵢ⁻¹U` for a quasi-compact open `U` of the stage `Xᵢ`, which is `(S.stageOpenCone c i U).pt`,
and it is quasi-compact by `isCompact_legPreimage`. -/
theorem isIso_vertexComparison_stageOpen (c : Cone S.E) (hc : IsLimit c) (i : J)
    (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (q : ℕ) :
    IsIso (vertexComparison S c hc (S.stageOpenCone c i U).pt q) :=
  isIso_vertexComparison S c hc _ (isCompact_legPreimage S c hc i U hU) q

/-! ### Gap 2: the base-change arrow factors through the germ model -/

/-- **The vertex carrying the germ-model inverse image `pₖ⁻¹Fₖ`**, as an abelian sheafed space.
This is `SheafedSpaceLimit.reseat` of `pullSheaf c k`, written as a structure literal so that the
carrier is reducibly the space underlying `c.pt` and the instances of the fixed-space cohomology
API are found on it. -/
abbrev pullSpace (c : Cone S.E) (k : J) :
    SheafedSpace.{u + 1, u, u} AddCommGrpCat.{u} where
  carrier := (c.pt : TopCat.{u})
  presheaf := (SheafedSpaceLimit.pullSheaf c k).presheaf
  IsSheaf := (SheafedSpaceLimit.pullSheaf c k).2

/-- **Base change to the vertex, as a morphism of abelian sheafed spaces**
`(c.pt, pₖ⁻¹Fₖ) ⟶ (Xₖ, Fₖ)`: the base map is the `k`-th cone projection and the sheaf component
is the unit of the germ model. -/
def pullProj (c : Cone S.E) (k : J) : pullSpace S c k ⟶ S.E.obj k :=
  SheafedSpaceLimit.leg c (SheafedSpaceLimit.pullSheaf c k).presheaf
    (SheafedSpaceLimit.pullSheaf c k).2 k
    (GermPullback.toPushforwardPresheaf (c.π.app k).hom.base (S.E.obj k).presheaf)

/-- **The `k`-th leg of the comparison cocone, as a morphism of abelian sheafed spaces**
`c.pt ⟶ (c.pt, pₖ⁻¹Fₖ)`: the base map is the identity and the sheaf component is
`SheafedSpaceLimit.coleg`. -/
def colegMor (c : Cone S.E) (k : J) : c.pt ⟶ pullSpace S c k :=
  InducedCategory.homMk { base := 𝟙 _, c := SheafedSpaceLimit.coleg c k }

/-- **The `k`-th cone projection factors through the germ model**: it is `colegMor` followed by
`pullProj`.  The base maps are equal on the nose (`𝟙 ≫ f = f` is `rfl` in `TopCat`) so no
transport is involved, and the sheaf components agree by
`GermPullback.toPushforwardPresheaf_comp_mapOut` — which is exactly the statement that `coleg` is
the morphism out of the germ model adjoint to the projection's sheaf component. -/
lemma colegMor_comp_pullProj (c : Cone S.E) (k : J) :
    colegMor S c k ≫ pullProj S c k = c.π.app k :=
  InducedCategory.hom_ext (AlgebraicGeometry.PresheafedSpace.hext _ _ rfl
    (heq_of_eq (GermPullback.toPushforwardPresheaf_comp_mapOut (c.π.app k).hom.base
      (c.π.app k).hom.c c.pt.IsSheaf)))

/-- **The base-change map on cohomology along a cone projection factors as base change to the
vertex followed by the map induced by `coleg`.**  Together with `IsCohomologyMap.eq`, which pins
the arrows of any `CohomologyCocone` to `spaceCohomologyMap`, this is what identifies the legs
`D.ι` of a presentation of the cohomology cocone of Tag 0A37 with arrows factoring through
`Hᑫ(pₖ⁻¹U, pₖ⁻¹Fₖ)` — the source of the comparison `vertexComparison`.

It is `spaceCohomologyMap_comp` applied to `colegMor_comp_pullProj`.  The three compatibility
hypotheses are all `le_rfl`: the base maps of `pullProj` and of the projection agree on the nose,
and the base map of `colegMor` is the identity. -/
theorem spaceCohomologyMap_leg_eq (c : Cone S.E) (k : J)
    (V : Opens (S.E.obj k)) (W : Opens (c.pt : TopCat.{u}))
    (h : W ≤ (Opens.map (c.π.app k).hom.base).obj V) (p : ℕ)
    (e₃ : Sheaf.H'.{u, u, u} (S.E.obj k).sheaf p V ≅
      ((sections.{u, u} (S.E.obj k) V).rightDerived p).obj (S.E.obj k).sheaf)
    (e₂ : Sheaf.H'.{u, u, u} (pullSpace S c k).sheaf p W ≅
      ((sections.{u, u} (pullSpace S c k) W).rightDerived p).obj (pullSpace S c k).sheaf)
    (e₁ : Sheaf.H'.{u, u, u} c.pt.sheaf p W ≅
      ((sections.{u, u} c.pt W).rightDerived p).obj c.pt.sheaf) :
    spaceCohomologyMap (c.π.app k) V W h p e₃ e₁ =
      spaceCohomologyMap (pullProj S c k) V W h p e₃ e₂ ≫
        spaceCohomologyMap (colegMor S c k) W W le_rfl p e₂ e₁ := by
  rw [spaceCohomologyMap_congr (colegMor_comp_pullProj S c k).symm V W h h p e₃ e₁]
  exact spaceCohomologyMap_comp (colegMor S c k) (pullProj S c k) V W W h le_rfl h p e₃ e₂ e₁

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end
