module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ComparisonOfDeltaFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.DegeneracyOfTheInjectiveCase

/-!
# Stacks 0A37: cohomology on a cofiltered limit of spectral spaces, in every degree

Let `X = lim Xᵢ` be a cofiltered limit of spectral spaces with spectral transition maps, let
`𝓕ᵢ` be abelian sheaves on `Xᵢ` with compatible `f_a`-maps, and let `𝓕 = colim pᵢ⁻¹𝓕ᵢ` on `X`.
This is encoded as a `SpectralAbelianSheafSystem` together with a limiting cone `c` of its diagram
of abelian sheafed spaces. For a stage `i` and a quasi-compact open `Uᵢ ⊆ Xᵢ`,
`SpectralAbelianSheafSystem.isIso_comparison` proves
`colim_{a : j → i} Hᵖ(f_a⁻¹(Uᵢ), 𝓕ⱼ) = Hᵖ(pᵢ⁻¹(Uᵢ), 𝓕)` for every `p ≥ 0`, and
`SpectralAbelianSheafSystem.isIso_comparison_global` proves `Hᵖ(X, 𝓕) = colim Hᵖ(Xᵢ, 𝓕ᵢ)`.

## Main results

* `CohomologyCocone.isColimitOfIsColimit`: whether a presentation of the cohomology cocone is a
  colimit cocone does not depend on the presentation, since the arrows of every presentation are
  the maps on right-derived sections prescribed by injective resolutions.
* `SpectralAbelianSheafSystem.isColimit_transferCocone`: a presentation over one limiting cone
  gives a presentation over any isomorphic cone, along the map on cohomology induced by the
  isomorphism of vertices.
* `SpectralAbelianSheafSystem.isIso_comparison` and `…_global`: **Stacks 0A37.** The
  quasi-compact-open statement is the invertibility of the comparison of δ-functors on systems,
  `SpectralDiagram.AbelianSystem.isIso_comparisonDelta_app`, read on the canonical presentation
  over the vertex cone and carried to `c` and to an arbitrary presentation; the global statement
  is the case `Uᵢ = Xᵢ` (`SpectralAbelianSheafSystem.isIso_comparison_global_of_stage`).
* `SpectralAbelianSheafSystem.nonempty_and_isIso_comparison` and `…_global`: the same two
  statements together with the existence of a presentation of the cohomology cocone.
* `SpectralAbelianSheafSystem.quasiCompactOpenColimitComparison`: the same statement, in the
  form of the proposition `SpectralAbelianSheafSystem.QuasiCompactOpenColimitComparison`.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cohomology.SpectralLimit

section Presentations

/-- The rearrangement turning the conjugated form of `IsCohomologyMap` into a commutative
square. -/
theorem comm_of_conj {C : Type*} [Category C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C} (x : X₁ ≅ Y₁)
    (y : X₂ ≅ Y₂) (e : Y₁ ≅ Z₁) (e' : Y₂ ≅ Z₂) (m : X₁ ⟶ X₂) (d : Z₁ ⟶ Z₂)
    (h : x.inv ≫ m ≫ y.hom = e.hom ≫ d ≫ e'.inv) :
    m ≫ y.hom ≫ e'.hom = x.hom ≫ e.hom ≫ d := by
  simpa using congrArg (fun t => x.hom ≫ t ≫ e'.hom) h

/-- The rearrangement comparing two presentations along their common derived diagram. -/
theorem comm_of_comm {C : Type*} [Category C] {X₁ X₂ W₁ W₂ Z₁ Z₂ : C} (t₁ : X₁ ≅ Z₁)
    (t₂ : X₂ ≅ Z₂) (s₁ : W₁ ≅ Z₁) (s₂ : W₂ ≅ Z₂) (m : X₁ ⟶ X₂) (m' : W₁ ⟶ W₂) (d : Z₁ ⟶ Z₂)
    (h : m ≫ t₂.hom = t₁.hom ≫ d) (h' : m' ≫ s₂.hom = s₁.hom ≫ d) :
    m ≫ (t₂ ≪≫ s₂.symm).hom = (t₁ ≪≫ s₁.symm).hom ≫ m' := by
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h]
  rw [Category.assoc, Category.assoc]
  refine congrArg (t₁.hom ≫ ·) ?_
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h', Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The rearrangement turning the conjugated form of `IsCohomologyMap` for a leg into a
commutative square. -/
theorem comm_of_conj' {C : Type*} [Category C] {X Y Z V P : C} (x : X ≅ Y) (e : Y ≅ Z)
    (v : V ≅ P) (ι : X ⟶ V) (d : Z ⟶ P) (h : x.inv ≫ ι = e.hom ≫ d ≫ v.inv) :
    ι ≫ v.hom = (x ≪≫ e).hom ≫ d := by
  rw [(Iso.inv_comp_eq _).1 h]
  simp

/-- The rearrangement comparing the legs of two presentations. -/
theorem leg_of_comm {C : Type*} [Category C] {X W Z V V' P : C} (t : X ≅ Z) (s : W ≅ Z)
    (v : V ≅ P) (v' : V' ≅ P) (ι : X ⟶ V) (ι' : W ⟶ V') (d : Z ⟶ P)
    (h : ι ≫ v.hom = t.hom ≫ d) (h' : ι' ≫ v'.hom = s.hom ≫ d) :
    (t ≪≫ s.symm).inv ≫ ι ≫ (v ≪≫ v'.symm).hom = ι' := by
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    reassoc_of% h, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← h', Category.assoc, Iso.hom_inv_id, Category.comp_id]

namespace CohomologyCocone

variable {K : Type*} [Category K] {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}}
  {c : Cone E} {O : OpenCone E c} {p : ℕ}

/-- The identification of a stage of a presentation with right-derived sections. -/
def toDerived (P : CohomologyCocone E c O p) (k : K) :
    P.diagram.obj (op k) ≅
      ((sections.{u, u} (E.obj k) (O.obj k)).rightDerived p).obj (E.obj k).sheaf :=
  P.objIso k ≪≫ P.objDerivedIso k

/-- The arrows of a presentation, read on right-derived sections, are the canonical maps. -/
theorem map_comp_toDerived (P : CohomologyCocone E c O p) {j k : K} (a : j ⟶ k) :
    P.diagram.map a.op ≫ (P.toDerived j).hom =
      (P.toDerived k).hom ≫ derivedCohomologyMap (E.map a).hom.base (sheafMap (E.map a))
        (O.obj k) (O.obj j) (O.map_le a) p :=
  comm_of_conj _ _ _ _ _ _ ((isCohomologyMap_iff _ _ _ _ _ _ _ _ _).1 (P.map_eq a))

/-- The legs of a presentation, read on right-derived sections, are the canonical maps. -/
theorem ι_comp_vertexDerivedIso (P : CohomologyCocone E c O p) (k : K) :
    P.ι.app (op k) ≫ P.vertexDerivedIso.hom =
      (P.toDerived k).hom ≫ derivedCohomologyMap (c.π.app k).hom.base (sheafMap (c.π.app k))
        (O.obj k) O.pt (O.leg_le k) p :=
  comm_of_conj' _ _ _ _ _ ((isCohomologyMap_iff _ _ _ _ _ _ _ _ _).1 (P.ι_eq k))

/-- Two presentations of the cohomology cocone have isomorphic diagrams. -/
def diagramIso (P Q : CohomologyCocone E c O p) : P.diagram ≅ Q.diagram :=
  NatIso.ofComponents (fun k => P.toDerived k.unop ≪≫ (Q.toDerived k.unop).symm)
    fun a => comm_of_comm _ _ _ _ _ _ _ (P.map_comp_toDerived a.unop)
      (Q.map_comp_toDerived a.unop)

/-- **The colimit property of a presentation of the cohomology cocone does not depend on the
presentation.** -/
def isColimitOfIsColimit (P Q : CohomologyCocone E c O p) (hP : IsColimit P.cocone) :
    IsColimit Q.cocone :=
  ((IsColimit.precomposeInvEquiv (P.diagramIso Q) _).symm hP).ofIsoColimit
    (Cocone.ext (P.vertexDerivedIso ≪≫ Q.vertexDerivedIso.symm) fun k =>
      leg_of_comm _ _ _ _ _ _ _ (P.ι_comp_vertexDerivedIso k.unop)
        (Q.ι_comp_vertexDerivedIso k.unop))

end CohomologyCocone

end Presentations


namespace SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

section Transfer

variable {c c' : Cone S.E} (φ : c.pt ≅ c'.pt) (hφ : ∀ k, φ.hom ≫ c'.π.app k = c.π.app k)
  (i : J) (U : Opens (S.E.obj i)) (p : ℕ)

include hφ in
/-- `pᵢ⁻¹ U` on the vertex of `c` lies in the inverse image of `pᵢ⁻¹ U` on the vertex of `c'`. -/
theorem pt_le_map_pt :
    (S.stageOpenCone c i U).pt ≤ (Opens.map φ.hom.hom.base).obj (S.stageOpenCone c' i U).pt :=
  (congrArg (fun g : c.pt ⟶ S.E.obj i => (Opens.map g.hom.base).obj U) (hφ i)).ge

include hφ in
/-- `pᵢ⁻¹ U` on the vertex of `c'` lies in the inverse image of `pᵢ⁻¹ U` on the vertex of `c`. -/
theorem pt_le_map_pt' :
    (S.stageOpenCone c' i U).pt ≤ (Opens.map φ.inv.hom.base).obj (S.stageOpenCone c i U).pt := by
  have h : φ.inv ≫ c.π.app i = c'.π.app i := by rw [← hφ i, Iso.inv_hom_id_assoc]
  exact (congrArg (fun g : c'.pt ⟶ S.E.obj i => (Opens.map g.hom.base).obj U) h).ge

/-- The map on cohomology along the isomorphism `φ` of the vertices of two cones. -/
abbrev vertexTransfer
    (e' : Sheaf.H'.{u, u, u} c'.pt.sheaf p (S.stageOpenCone c' i U).pt ≅
      ((sections.{u, u} c'.pt (S.stageOpenCone c' i U).pt).rightDerived p).obj c'.pt.sheaf)
    (e : Sheaf.H'.{u, u, u} c.pt.sheaf p (S.stageOpenCone c i U).pt ≅
      ((sections.{u, u} c.pt (S.stageOpenCone c i U).pt).rightDerived p).obj c.pt.sheaf) :
    Sheaf.H'.{u, u, u} c'.pt.sheaf p (S.stageOpenCone c' i U).pt ⟶
      Sheaf.H'.{u, u, u} c.pt.sheaf p (S.stageOpenCone c i U).pt :=
  spaceCohomologyMap φ.hom _ _ (S.pt_le_map_pt φ hφ i U) p e' e

/-- The canonical maps along mutually inverse morphisms of sheafed spaces compose to the
identity. -/
private theorem spaceCohomologyMap_comp_eq_id {W₁ W₂ : SheafedSpace.{_, _, u} AddCommGrpCat.{u}}
    (g₁ : W₁ ⟶ W₂) (g₂ : W₂ ⟶ W₁) (hg : g₁ ≫ g₂ = 𝟙 W₁) (U₁ : Opens W₁) (U₂ : Opens W₂)
    (h₁ : U₁ ≤ (Opens.map g₁.hom.base).obj U₂) (h₂ : U₂ ≤ (Opens.map g₂.hom.base).obj U₁)
    (p : ℕ)
    (e₁ : Sheaf.H'.{u, u, u} W₁.sheaf p U₁ ≅
      ((sections.{u, u} W₁ U₁).rightDerived p).obj W₁.sheaf)
    (e₂ : Sheaf.H'.{u, u, u} W₂.sheaf p U₂ ≅
      ((sections.{u, u} W₂ U₂).rightDerived p).obj W₂.sheaf) :
    spaceCohomologyMap g₂ U₁ U₂ h₂ p e₁ e₂ ≫ spaceCohomologyMap g₁ U₂ U₁ h₁ p e₂ e₁ = 𝟙 _ := by
  have h₃ : U₁ ≤ (Opens.map (g₁ ≫ g₂).hom.base).obj U₁ := by
    rw [hg]
    exact le_refl _
  exact (spaceCohomologyMap_comp g₁ g₂ U₁ U₂ U₁ h₂ h₁ h₃ p e₁ e₂ e₁).symm.trans
    ((spaceCohomologyMap_congr hg _ _ h₃ (le_refl _) p e₁ e₁).trans
      (spaceCohomologyMap_id _ _ p e₁))

include hφ in
/-- The map on cohomology along an isomorphism of vertices is an isomorphism. -/
theorem isIso_vertexTransfer
    (e' : Sheaf.H'.{u, u, u} c'.pt.sheaf p (S.stageOpenCone c' i U).pt ≅
      ((sections.{u, u} c'.pt (S.stageOpenCone c' i U).pt).rightDerived p).obj c'.pt.sheaf)
    (e : Sheaf.H'.{u, u, u} c.pt.sheaf p (S.stageOpenCone c i U).pt ≅
      ((sections.{u, u} c.pt (S.stageOpenCone c i U).pt).rightDerived p).obj c.pt.sheaf) :
    IsIso (S.vertexTransfer φ hφ i U p e' e) := by
  exact ⟨spaceCohomologyMap φ.inv _ _ (S.pt_le_map_pt' φ hφ i U) p e e',
    spaceCohomologyMap_comp_eq_id φ.inv φ.hom φ.inv_hom_id _ _ _ _ p e' e,
    spaceCohomologyMap_comp_eq_id φ.hom φ.inv φ.hom_inv_id _ _ _ _ p e e'⟩

/-- A presentation over the cone `c'`, carried to the cone `c` along `φ`. -/
def transferCocone
    (P : CohomologyCocone ((Over.forget i) ⋙ S.E) (c'.whisker (Over.forget i))
      (S.stageOpenCone c' i U) p)
    (e : Sheaf.H'.{u, u, u} c.pt.sheaf p (S.stageOpenCone c i U).pt ≅
      ((sections.{u, u} c.pt (S.stageOpenCone c i U).pt).rightDerived p).obj c.pt.sheaf) :
    CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) p where
  diagram := P.diagram
  objIso := P.objIso
  objDerivedIso := P.objDerivedIso
  vertexDerivedIso := e
  map_eq := P.map_eq
  ι := P.ι ≫ (Functor.const _).map (S.vertexTransfer φ hφ i U p P.vertexDerivedIso e)
  ι_eq B := by
    have h₃ : (S.stageOpenCone c i U).pt ≤ (Opens.map (φ.hom ≫ c'.π.app B.left).hom.base).obj
        ((S.stageOpenCone c i U).obj B) := by
      rw [hφ B.left]
      exact (S.stageOpenCone c i U).leg_le B
    have h := (isCohomologyMap_iff _ _ _ _ _ _ _ _ _).1 (P.ι_eq B)
    refine (isCohomologyMap_iff _ _ _ _ _ _ _ _ _).2 ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h)).trans ?_
    exact ((spaceCohomologyMap_comp φ.hom (c'.π.app B.left) _ _ _
      ((S.stageOpenCone c' i U).leg_le B) (S.pt_le_map_pt φ hφ i U) h₃ p _ _ e).symm.trans
      (spaceCohomologyMap_congr (hφ B.left) _ _ h₃ ((S.stageOpenCone c i U).leg_le B) p _ _))

/-- A presentation over `c'` that is a colimit cocone gives one over `c`. -/
theorem isColimit_transferCocone
    (P : CohomologyCocone ((Over.forget i) ⋙ S.E) (c'.whisker (Over.forget i))
      (S.stageOpenCone c' i U) p)
    (e : Sheaf.H'.{u, u, u} c.pt.sheaf p (S.stageOpenCone c i U).pt ≅
      ((sections.{u, u} c.pt (S.stageOpenCone c i U).pt).rightDerived p).obj c.pt.sheaf)
    (hP : IsColimit P.cocone) : Nonempty (IsColimit (S.transferCocone φ hφ i U p P e).cocone) :=
  ⟨hP.ofIsoColimit (Cocone.ext (@asIso _ _ _ _ (S.vertexTransfer φ hφ i U p P.vertexDerivedIso e)
    (S.isIso_vertexTransfer φ hφ i U p P.vertexDerivedIso e)) fun _ => rfl)⟩

end Transfer

/-- **The colimit comparison of Stacks 0A37 over a quasi-compact open of a stage, for every
presentation of the cohomology cocone.**  For a cofiltered system of spectral spaces `Xⱼ` with
spectral transition maps and abelian sheaves `𝓕ⱼ` with compatible `f`-maps, the limit
`X = lim Xⱼ` with the sheaf `𝓕 = colim pⱼ⁻¹𝓕ⱼ` on it (a limiting cone `c` of the diagram of
abelian sheafed spaces), a stage `i` and a quasi-compact open `Uᵢ ⊆ Xᵢ`, the comparison
`colim_{a : j → i} Hᵖ(f_a⁻¹ Uᵢ, 𝓕ⱼ) ⟶ Hᵖ(pᵢ⁻¹ Uᵢ, 𝓕)` of a presentation `D` of the cohomology
cocone is an isomorphism for every `p ≥ 0`. -/
theorem isIso_comparison (c : Cone S.E) (hc : IsLimit c) (i : J) (U : Opens (S.E.obj i))
    (hU : IsCompact (U : Set (S.E.obj i))) (p : ℕ)
    (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) p) :
    IsIso D.comparison := by
  let c₀ : Cone S.typeSystem.diagram.F := (SheafedSpace.forget _).mapCone c
  have hc₀ : IsLimit c₀ := SheafedSpaceLimit.isLimit_mapCone_forget hc
  obtain ⟨h⟩ := (SpectralDiagram.AbelianSystem.isIso_comparisonDelta_iff c₀ U
    S.toAbelianSystem p).1
      (SpectralDiagram.AbelianSystem.isIso_comparisonDelta_app c₀ hc₀ U hU p S.toAbelianSystem)
  have hv : IsLimit (S.toAbelianSystem.vertexCone c₀) := S.toAbelianSystem.isLimitVertexCone c₀ hc₀
  obtain ⟨hT⟩ := S.isColimit_transferCocone (hc.conePointUniqueUpToIso hv)
    (hc.conePointUniqueUpToIso_hom_comp hv) i U p
    (SpectralDiagram.AbelianSystem.canonicalCocone c₀ U S.toAbelianSystem p) D.vertexDerivedIso h
  exact CohomologyCocone.isIso_comparison_of_isColimit D
    (CohomologyCocone.isColimitOfIsColimit _ D hT)

/-- **The global colimit comparison of Stacks 0A37, for every presentation of the cohomology
cocone**: `Hᵖ(X, 𝓕) = colim Hᵖ(Xᵢ, 𝓕ᵢ)` for every `p ≥ 0`. -/
theorem isIso_comparison_global (c : Cone S.E) (hc : IsLimit c) (p : ℕ)
    (D : CohomologyCocone S.E c (S.globalOpenCone c) p) : IsIso D.comparison :=
  S.isIso_comparison_global_of_stage c p
    (fun i U hU D' => S.isIso_comparison c hc i U hU p D') D

/-- **Stacks 0A37, over a quasi-compact open of a stage.**  For a cofiltered system of spectral
spaces `Xⱼ` with spectral transition maps and abelian sheaves `𝓕ⱼ` with compatible `f`-maps, the
limit `X = lim Xⱼ` with the sheaf `𝓕 = colim pⱼ⁻¹𝓕ⱼ` on it (a limiting cone `c` of the diagram
of abelian sheafed spaces), a stage `i`, a quasi-compact open `Uᵢ ⊆ Xᵢ` and `p ≥ 0`, the
cohomology cocone `colim_{a : j → i} Hᵖ(f_a⁻¹ Uᵢ, 𝓕ⱼ) ⟶ Hᵖ(pᵢ⁻¹ Uᵢ, 𝓕)` exists and its
comparison out of the colimit is an isomorphism. -/
@[stacks 0A37 "quasi-compact open: colim_{a : j → i} Hᵖ(f_a⁻¹(Uᵢ), 𝓕ⱼ) = Hᵖ(pᵢ⁻¹(Uᵢ), 𝓕) for every \
p ≥ 0"]
theorem nonempty_and_isIso_comparison (c : Cone S.E) (hc : IsLimit c) (i : J)
    (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) (p : ℕ) :
    Nonempty (CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) p) ∧
    ∀ D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) p, IsIso D.comparison :=
  ⟨S.nonempty_stageCohomologyCocone c hc i U hU p, S.isIso_comparison c hc i U hU p⟩

/-- **Stacks 0A37, the global statement**: for a limiting cone `c` of the system and `p ≥ 0`, the
cohomology cocone `colim Hᵖ(Xᵢ, 𝓕ᵢ) ⟶ Hᵖ(X, 𝓕)` exists and its comparison out of the colimit is
an isomorphism, that is `Hᵖ(X, 𝓕) = colim Hᵖ(Xᵢ, 𝓕ᵢ)`. -/
@[stacks 0A37 "in particular Hᵖ(X, 𝓕) = colim Hᵖ(Xᵢ, 𝓕ᵢ) for every p ≥ 0"]
theorem nonempty_and_isIso_comparison_global (c : Cone S.E) (hc : IsLimit c) (p : ℕ) :
    Nonempty (CohomologyCocone S.E c (S.globalOpenCone c) p) ∧
    ∀ D : CohomologyCocone S.E c (S.globalOpenCone c) p, IsIso D.comparison :=
  ⟨S.nonempty_globalCohomologyCocone c hc p, S.isIso_comparison_global c hc p⟩

/-- The quasi-compact-open colimit comparison of Stacks 0A37 holds for every system. -/
theorem quasiCompactOpenColimitComparison : S.QuasiCompactOpenColimitComparison :=
  S.isIso_comparison

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit
