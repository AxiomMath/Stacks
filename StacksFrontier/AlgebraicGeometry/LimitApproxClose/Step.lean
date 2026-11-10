module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepInputs
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepThreeLimit
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.OverlapBridge
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Reindex
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.SpecCone
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StageCharted
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.CompatibleFamily
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Exists
public import StacksFrontier.AlgebraicGeometry.LimitApproxChain.Transport
public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.OverlapStages

/-!
# The one-affine-open step: the glued approximation from a charting family

This file assembles the approximation of a scheme `S` glued out of a directed inverse system over
a quasi-compact open `V` and one affine open `Y` with `V ⊔ Y = ⊤`, from the data the rest of this
directory produces.

## Main definitions

* `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofWhisker` carries an approximation over a
  reindexed system back to the original system.  Only the index order homomorphism changes; the
  comparison isomorphism and both compatibilities are the input's, the two reindexings composing
  to the composite by reflexivity.

* `Stacks.GluedStep.approximation` is the structure.  Its index is the preorder
  `Stacks.StageSubalgebra` of pairs of a stage and a *charted* subalgebra of the fibre-product
  ring at that stage; the ambient system is `AlgebraicGeometry.gluePairFunctor` of the two legs
  `Stacks.StageSubalgebra.openInclusionLeg` and `Stacks.StageSubalgebra.specLeg`; and the limiting
  property of its cone is `AlgebraicGeometry.isLimitGluePairFunctorCone`, step (iii).

  The hypotheses of step (iii) are discharged as follows: `hα` is
  `Stacks.StageSubalgebra.preimage_opensRange_openInclusionLeg`, `hβ` is
  `Stacks.StageSubalgebra.preimage_opensRange_specLeg`, `hXr` is the given preimage condition on
  the compatible family, `hYr` is the image of the second leg together with
  `AlgebraicGeometry.Scheme.opensRange_homOfLE_inf_right`, `hX` and `hW` are
  `AlgebraicGeometry.isLimitWhiskerOfCofinal` at the projection to the stages, `hY` is
  `Stacks.StageSubalgebra.isLimitSpecDiagramCone` extended along the canonical isomorphism of the
  affine open with the spectrum of its sections, `hXW` is
  `AlgebraicGeometry.overlapCone_app_comp_ι`, and `hYW` is `Stacks.FibreProduct.compat` with
  `AlgebraicGeometry.Scheme.toSpecΓ_naturality` twice.

  The ring layer is built **base-side**: the cocone of sections is that of the limiting cone over
  the overlap *as an open of the base*, so the ring appearing in the fibre products is
  `Γ(V ⊓ Y, ⊤)` and the structure map is the action on sections of the inclusion of `V ⊓ Y` in
  `Y`.  Nothing then has to be transported across the identification of the two guises of the
  overlap.  Tag 01Z0 is applied to that cone directly, which is what makes this possible.

## Implementation notes

One scheme universe; the index preorders live in it, as the structure
`AlgebraicGeometry.Scheme.FiniteTypeApproximation` requires of its index type.  The ring-level
colimits are indexed by the opposite of the dual of the stage preorder, which is where the
ring-level results used here live; `Stacks.preorderToOpDual` reads them back over the preorder
itself.

Transparency gotchas:

* Every intermediate object is an `abbrev`, hence reducible.  That is what lets the charting
  morphisms, stated at `Spec (CommRingCat.of ↥(F.obj k))`, meet the facts about their images,
  stated at `Spec (Stacks.FibreProduct.obj s t)`: the two are one structure-eta step apart, which
  is not taken at instance transparency, so each such fact is introduced with its target spelling
  written out.

* The index of the ring-level colimit is `(Kᵒᵈ)ᵒᵖ` while the index of pairs needs a preorder.
  The colimit is *not* transported along an equivalence: the two facts that
  `Stacks.StageSubalgebra.nonempty_isColimit_ringCocone` asks for are elementwise, and an
  elementwise consequence of a colimit crosses a bijection of index objects by reflexivity.

* Morphisms of the opposite of a preorder are compared with
  `CategoryTheory.Quiver.Hom.unop_inj` applied to `Subsingleton.elim`, there being no
  subsingleton instance for the opposite hom type.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

attribute [local instance] Scheme.FiniteTypeApproximation.indexPreorder
  Scheme.FiniteTypeApproximation.indexNonempty Scheme.FiniteTypeApproximation.indexDirected

/-- **An approximation over a reindexed system is one over the original system.**  The new index
order homomorphism is the composite; nothing else moves, the two reindexings composing to the
composite by reflexivity. -/
noncomputable def Scheme.FiniteTypeApproximation.ofWhisker {I K : Type u} [Preorder I]
    [Preorder K] {D : Iᵒᵈ ⥤ Scheme.{u}} (E : K →o I) {S : Scheme.{u}} {U : S.Opens}
    {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}
    (A : Scheme.FiniteTypeApproximation (E.monotone.dual.functor ⋙ D) S U
      ((Cone.mk (U : Scheme.{u}) p).whisker E.monotone.dual.functor).π) :
    Scheme.FiniteTypeApproximation D S U p where
  indexType := A.indexType
  index := E.comp A.index
  ambient := A.ambient
  openPart := A.openPart
  inclusion := A.inclusion
  comparison := A.comparison
  ambientCone := A.ambientCone
  openCone := A.openCone
  transition_affine := A.transition_affine
  locallyOfFiniteType := A.locallyOfFiniteType
  quasiCompact := A.quasiCompact
  inclusion_isOpenImmersion := A.inclusion_isOpenImmersion
  transition_isPullback := A.transition_isPullback
  ambientCone_isLimit := A.ambientCone_isLimit
  openCone_isLimit := A.openCone_isLimit
  inclusion_compatibility := A.inclusion_compatibility
  comparison_compatibility := A.comparison_compatibility

end AlgebraicGeometry

namespace Stacks.GluedStep

open Stacks.StageSubalgebra

variable {K : Type u} [Preorder K] {Dv : Kᵒᵈ ⥤ Scheme.{u}} {S : Scheme.{u}} {V Y : S.Opens}
  (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
  (W : ∀ a, (Dv.obj a).Opens)
  (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
  (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)

/-- The system of models of the overlap: the subdiagram cut out by the compatible family. -/
@[reducible] noncomputable def mdl : Kᵒᵈ ⥤ Scheme.{u} := compatibleOpensDiagram Dv W hW

/-- The cone over the models of the overlap whose vertex is the overlap read as an open of the
base scheme. -/
@[reducible] noncomputable def cw : Cone (mdl (Dv := Dv) W hW) :=
  Cone.mk ((V ⊓ Y : S.Opens) : Scheme.{u}) (overlapCone V Y pv W hW hT)

/-- The diagram of rings of sections of the models of the overlap. -/
@[reducible] noncomputable def sec : ((Kᵒᵈ)ᵒᵖ) ⥤ CommRingCat.{u} :=
  (mdl (Dv := Dv) W hW).op ⋙ Scheme.Γ

/-- The cocone of sections of the models over the sections of the overlap. -/
@[reducible] noncomputable def tau :
    sec (Dv := Dv) W hW ⟶ (Functor.const ((Kᵒᵈ)ᵒᵖ)).obj Γ(((V ⊓ Y : S.Opens) : Scheme.{u}), ⊤) :=
  (Scheme.Γ.mapCocone (cw pv W hW hT).op).ι

/-- The structure map of the fibre products: the action on sections of the inclusion of the
overlap in the affine open being added. -/
@[reducible] noncomputable def str :
    Γ((Y : Scheme.{u}), ⊤) ⟶ Γ(((V ⊓ Y : S.Opens) : Scheme.{u}), ⊤) :=
  (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).appTop

/-- The diagram of rings of sections, read over the stage preorder itself. -/
@[reducible] noncomputable def secK : K ⥤ CommRingCat.{u} :=
  preorderToOpDual K ⋙ sec (Dv := Dv) W hW

/-- The cocone of sections, read over the stage preorder itself. -/
@[reducible] noncomputable def tauK :
    secK (Dv := Dv) W hW ⟶ (Functor.const K).obj Γ(((V ⊓ Y : S.Opens) : Scheme.{u}), ⊤) :=
  (Cocone.whisker (preorderToOpDual K) (Scheme.Γ.mapCocone (cw pv W hW hT).op)).ι

/-- The diagram of fibre-product rings over the stage preorder. -/
@[reducible] noncomputable def rng : K ⥤ CommRingCat.{u} :=
  preorderToOpDual K ⋙ FibreProduct.diagram (sec (Dv := Dv) W hW) (tau pv W hW hT) (str (V := V))

/-- The cocone of fibre-product rings over the sections of the affine open being added. -/
@[reducible] noncomputable def rngCocone :
    rng pv W hW hT ⟶ (Functor.const K).obj Γ((Y : Scheme.{u}), ⊤) :=
  (Cocone.whisker (preorderToOpDual K)
    (FibreProduct.cocone (sec (Dv := Dv) W hW) (tau pv W hW hT) (str (V := V)))).ι

/-- The charting morphism at a stage: the canonical morphism of the model of the overlap into the
spectrum of its own sections, followed by the spectrum of the second projection of the fibre
product. -/
@[reducible] noncomputable def chart (k : K) :
    (mdl (Dv := Dv) W hW).obj (OrderDual.toDual k) ⟶
      Spec (CommRingCat.of ((rng pv W hW hT).obj k)) :=
  ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k)).toSpecΓ ≫
    Spec.map (FibreProduct.snd (str (V := V) (Y := Y))
      ((tau pv W hW hT).app (op (OrderDual.toDual k))))


variable {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
  (f : ∀ k : K, Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤))
  (hf : ∀ (k : K) (l : Fin n), (tau pv W hW hT).app (op (OrderDual.toDual k)) (f k l) =
    str (V := V) (Y := Y) (g l))

/-- The charting family: the elements of the fibre-product rings built from the chosen sections of
the affine open being added together with their lifts at the stages. -/
@[reducible] noncomputable def fam (k : K) (l : Fin n) : (rng pv W hW hT).obj k :=
  FibreProduct.famMk (secK (Dv := Dv) W hW) (tauK pv W hW hT) (str (V := V) (Y := Y)) g f hf k l

/-- The distinguished predicate on subalgebras: being charted by the charting family. -/
@[reducible] noncomputable def pred :
    ∀ k : K, Subalgebra ℤ ((rng pv W hW hT).obj k) → Prop :=
  ChartedAt (fam pv W hW hT g f hf)

/-- The index of the extended system: pairs of a stage and a charted subalgebra of the
fibre-product ring at that stage. -/
@[reducible] noncomputable def idx : Type u :=
  StageSubalgebra (rng pv W hW hT) (pred pv W hW hT g f hf)

/-- **The charting morphisms are compatible with the transition morphisms.**  This is the
hypothesis `hγ` of `Stacks.StageSubalgebra.specLeg`. -/
lemma chart_naturality {k k' : K} (h : k ≤ k') :
    (mdl (Dv := Dv) W hW).map (homOfLE (OrderDual.toDual_le_toDual.mpr h)) ≫
        chart pv W hW hT k =
      chart pv W hW hT k' ≫ Spec.map ((rng pv W hW hT).map (homOfLE h)) :=
  toSpecΓ_comp_SpecMap_snd_naturality (tau pv W hW hT) (str (V := V) (Y := Y)) h

/-- The first leg of the glueing: the inclusion of the models of the overlap into the stages,
reindexed onto the pairs. -/
@[reducible] noncomputable def legOpen :
    overlapDiagram (mdl (Dv := Dv) W hW) (pred pv W hW hT g f hf) ⟶
      overlapDiagram Dv (pred pv W hW hT g f hf) :=
  openInclusionLeg W hW (pred pv W hW hT g f hf)

/-- The second leg of the glueing: the charting morphism followed by the spectrum of the
inclusion of the subalgebra. -/
@[reducible] noncomputable def legSpec :
    overlapDiagram (mdl (Dv := Dv) W hW) (pred pv W hW hT g f hf) ⟶
      specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf) :=
  specLeg (chart pv W hW hT) fun h ↦ chart_naturality pv W hW hT h


/-- The reindexing of the stage preorder along the projection from the index of pairs. -/
@[reducible] noncomputable def reidx :
    (idx pv W hW hT g f hf)ᵒᵈ ⥤ Kᵒᵈ :=
  (proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf)).monotone.dual.functor

/-- The cone from the open already approximated, over the stages reindexed onto the pairs. -/
@[reducible] noncomputable def coneX : Cone (overlapDiagram Dv (pred pv W hW hT g f hf)) :=
  (Cone.mk (V : Scheme.{u}) pv).whisker (reidx pv W hW hT g f hf)

/-- The cone from the overlap, over the models reindexed onto the pairs. -/
@[reducible] noncomputable def coneWp :
    Cone (overlapDiagram (mdl (Dv := Dv) W hW) (pred pv W hW hT g f hf)) :=
  (cw pv W hW hT).whisker (reidx pv W hW hT g f hf)

/-- The cone from the affine open being added, over the spectra of the distinguished
subalgebras. -/
@[reducible] noncomputable def coneY :
    Cone (specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf)) :=
  Cone.mk ((Y : Scheme.{u})) (coneExtend (Cone.mk (Spec Γ((Y : Scheme.{u}), ⊤))
    (specDiagramCone (rngCocone pv W hW hT) (pred pv W hW hT g f hf)))
    ((Y : Scheme.{u}).toSpecΓ))

/-- **The two legs agree on the overlap, after the spectrum of the fibre product.**  This is the
ring-level content of the hypothesis `hYW` of step (iii): the compatibility of the fibre product,
with `AlgebraicGeometry.Scheme.toSpecΓ_naturality` on each side. -/
lemma keyY (a : Kᵒᵈ) {Z : Scheme.{u}}
    (m : Spec (FibreProduct.obj (str (V := V) (Y := Y)) ((tau pv W hW hT).app (op a))) ⟶ Z) :
    S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫ (Y : Scheme.{u}).toSpecΓ ≫
        Spec.map (FibreProduct.fst (str (V := V) (Y := Y))
          ((tau pv W hW hT).app (op a))) ≫ m =
      (overlapCone V Y pv W hW hT).app a ≫ ((mdl (Dv := Dv) W hW).obj a).toSpecΓ ≫
        Spec.map (FibreProduct.snd (str (V := V) (Y := Y))
          ((tau pv W hW hT).app (op a))) ≫ m := by
  have h1 : S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫ (Y : Scheme.{u}).toSpecΓ =
      ((V ⊓ Y : S.Opens) : Scheme.{u}).toSpecΓ ≫ Spec.map (str (V := V) (Y := Y)) :=
    Scheme.toSpecΓ_naturality _
  have h2 : (overlapCone V Y pv W hW hT).app a ≫ ((mdl (Dv := Dv) W hW).obj a).toSpecΓ =
      ((V ⊓ Y : S.Opens) : Scheme.{u}).toSpecΓ ≫ Spec.map ((tau pv W hW hT).app (op a)) :=
    Scheme.toSpecΓ_naturality _
  have h3 : FibreProduct.fst (str (V := V) (Y := Y)) ((tau pv W hW hT).app (op a)) ≫
        str (V := V) (Y := Y) =
      FibreProduct.snd (str (V := V) (Y := Y)) ((tau pv W hW hT).app (op a)) ≫
        (tau pv W hW hT).app (op a) := (FibreProduct.isPullback _ _).w
  have e1 : Spec.map (str (V := V) (Y := Y)) ≫
        Spec.map (FibreProduct.fst (str (V := V) (Y := Y)) ((tau pv W hW hT).app (op a))) =
      Spec.map ((tau pv W hW hT).app (op a)) ≫
        Spec.map (FibreProduct.snd (str (V := V) (Y := Y)) ((tau pv W hW hT).app (op a))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, h3]
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% e1]
  exact (Category.assoc _ _ _).symm

end Stacks.GluedStep

namespace Stacks.GluedStep

open Stacks.StageSubalgebra

/-- **The glued approximation, from the data of step (iii).**  It fills in the fields of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation` from the hypotheses of step (iii). -/
theorem approximation_of_data {K : Type u} [Preorder K] [Nonempty K] [IsDirected K (· ≤ ·)]
    {Dv : Kᵒᵈ ⥤ Scheme.{u}} [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    [∀ a, LocallyOfFiniteType (terminal.from (Dv.obj a))]
    [∀ a, QuasiCompact (terminal.from (Dv.obj a))] [∀ a, CompactSpace (Dv.obj a)]
    {S : Scheme.{u}} {V Y : S.Opens}
    (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
    (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)
    {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
    (f : ∀ k : K, Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤))
    (hf : ∀ (k : K) (l : Fin n), (tau pv W hW hT).app (op (OrderDual.toDual k)) (f k l) =
      str (V := V) (Y := Y) (g l))
    [Nonempty (idx pv W hW hT g f hf)] [IsDirected (idx pv W hW hT g f hf) (· ≤ ·)]
    [∀ j, IsOpenImmersion ((legSpec pv W hW hT g f hf).app j)]
    [∀ j : (idx pv W hW hT g f hf)ᵒᵈ, LocallyOfFiniteType (terminal.from
      ((specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf)).obj j))]
    [∀ j : (idx pv W hW hT g f hf)ᵒᵈ,
      CompactSpace ((overlapDiagram Dv (pred pv W hW hT g f hf)).obj j)]
    (hS : V ⊔ Y = ⊤)
    (halpha : ∀ ⦃j k : (idx pv W hW hT g f hf)ᵒᵈ⦄ (u : j ⟶ k),
      (overlapDiagram Dv (pred pv W hW hT g f hf)).map u ⁻¹ᵁ
          ((legOpen pv W hW hT g f hf).app k).opensRange =
        ((legOpen pv W hW hT g f hf).app j).opensRange)
    (hbeta : ∀ ⦃j k : (idx pv W hW hT g f hf)ᵒᵈ⦄ (u : j ⟶ k),
      (specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf)).map u ⁻¹ᵁ
          ((legSpec pv W hW hT g f hf).app k).opensRange =
        ((legSpec pv W hW hT g f hf).app j).opensRange)
    (hXr : ∀ j, (coneX pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legOpen pv W hW hT g f hf).app j).opensRange = V.ι ⁻¹ᵁ Y)
    (hYr : ∀ j, (coneY pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legSpec pv W hW hT g f hf).app j).opensRange = Y.ι ⁻¹ᵁ V)
    (hXW : ∀ j, S.homOfLE (inf_le_left : V ⊓ Y ≤ V) ≫ (coneX pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legOpen pv W hW hT g f hf).app j)
    (hYW : ∀ j, S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫ (coneY pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legSpec pv W hW hT g f hf).app j)
    (hX : IsLimit (coneX pv W hW hT g f hf)) (hYlim : IsLimit (coneY pv W hW hT g f hf))
    (hWlim : IsLimit (coneWp pv W hW hT g f hf))
    (hprojcof : ∀ k : K, ∃ j : idx pv W hW hT g f hf,
      k ≤ (proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf)) j) :
    ∃ A : Scheme.FiniteTypeApproximation Dv S V pv,
      ∀ k : K, ∃ j : A.indexType, k ≤ A.index j := by
  refine ⟨{ indexType := idx pv W hW hT g f hf
            index := proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf)
            ambient := gluePairFunctor (legOpen pv W hW hT g f hf) (legSpec pv W hW hT g f hf)
            openPart := overlapDiagram Dv (pred pv W hW hT g f hf)
            inclusion := gluePairFunctorInl _ _
            comparison := Iso.refl _
            ambientCone := gluePairFunctorCone _ _ V Y (coneX pv W hW hT g f hf).π
              (coneY pv W hW hT g f hf).π (coneWp pv W hW hT g f hf).π hXW hYW hS
            openCone := (coneX pv W hW hT g f hf).π
            transition_affine := fun u ↦ isAffineHom_gluePairFunctor_map _ _ halpha hbeta u
            locallyOfFiniteType := fun j ↦
              locallyOfFiniteType_terminal_from_gluePairFunctor_obj _ _ j
            quasiCompact := fun j ↦ quasiCompact_terminal_from_gluePairFunctor_obj _ _ j
            inclusion_isOpenImmersion := fun j ↦
              isOpenImmersion_gluePairFunctorInl_app _ _ j
            transition_isPullback := fun u ↦ isPullback_gluePairFunctorInl_app _ _ hbeta u
            ambientCone_isLimit := isLimitGluePairFunctorCone _ _ V Y _ _ _ hXW hYW hS
              halpha hbeta hXr hYr hX hYlim hWlim
            openCone_isLimit := hX
            inclusion_compatibility := fun j ↦
              ι_gluePairFunctorCone_app_left _ _ V Y _ _ _ hXW hYW hS j
            comparison_compatibility := fun j ↦ Category.comp_id _ }, hprojcof⟩

/-- **The one-affine-open step of Tag 07RN, from a charting family.**  Let `Dv` be a directed
inverse system of finite-type schemes with affine transition morphisms whose limit is a
quasi-compact open `V` of a scheme `S`, let `Y` be an affine open with `V ⊔ Y = ⊤`, let `W` be a
compatible family of quasi-compact opens of the stages cutting the overlap out of `V`, and let a
charting family be given at every stage.  Then `S` is approximated relative to `V` over `Dv`, by
a system whose index projects cofinally to the stages. -/
theorem exists_approximation {K : Type u} [Preorder K] [Nonempty K] [IsDirected K (· ≤ ·)]
    {Dv : Kᵒᵈ ⥤ Scheme.{u}} [∀ {a b : Kᵒᵈ} (v : a ⟶ b), IsAffineHom (Dv.map v)]
    [∀ a, LocallyOfFiniteType (terminal.from (Dv.obj a))]
    [∀ a, QuasiCompact (terminal.from (Dv.obj a))]
    {S : Scheme.{u}} {V Y : S.Opens} [IsAffine (Y : Scheme.{u})]
    (pv : (Functor.const Kᵒᵈ).obj (V : Scheme.{u}) ⟶ Dv)
    (W : ∀ a, (Dv.obj a).Opens)
    (hW : ∀ ⦃a b : Kᵒᵈ⦄ (v : a ⟶ b), Dv.map v ⁻¹ᵁ W b = W a)
    (hT : ∀ a, pv.app a ⁻¹ᵁ W a = V.ι ⁻¹ᵁ Y)
    (hWc : ∀ a : Kᵒᵈ, IsCompact ((W a : (Dv.obj a).Opens) : Set (Dv.obj a)))
    (hS : V ⊔ Y = ⊤)
    (hpv : IsLimit (Cone.mk (V : Scheme.{u}) pv))
    (hwlim : IsLimit (cw pv W hW hT))
    (hcolim : IsColimit (Scheme.Γ.mapCocone (cw pv W hW hT).op))
    {n : ℕ} (g : Fin n → Γ((Y : Scheme.{u}), ⊤))
    (hin : ∀ l, (Y : Scheme.{u}).basicOpen (g l) ≤
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange)
    (hgcov : (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange ≤
      ⨆ l, (Y : Scheme.{u}).basicOpen (g l))
    (f : ∀ k : K, Fin n → Γ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k), ⊤))
    (hf : ∀ (k : K) (l : Fin n), (tau pv W hW hT).app (op (OrderDual.toDual k)) (f k l) =
      str (V := V) (Y := Y) (g l))
    (hfmap : ∀ {k k' : K} (u : k ⟶ k') (l : Fin n), (secK (Dv := Dv) W hW).map u (f k l) = f k' l)
    (haff : ∀ (k : K) (l : Fin n),
      IsAffineOpen (((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k)).basicOpen (f k l)))
    (hcov : ∀ k : K,
      ⨆ l, ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k)).basicOpen (f k l) = ⊤) :
    ∃ A : Scheme.FiniteTypeApproximation Dv S V pv,
      ∀ k : K, ∃ j : A.indexType, k ≤ A.index j := by
  classical
  have hmc : ∀ a : Kᵒᵈ, CompactSpace ((mdl (Dv := Dv) W hW).obj a) :=
    compactSpace_compatibleOpensDiagram_obj W hW hWc
  have hzc : CompactSpace ((V ⊓ Y : S.Opens) : Scheme.{u}) :=
    Scheme.compactSpace_of_isLimit _ _ hwlim
  have hmft : ∀ a : Kᵒᵈ, LocallyOfFiniteType (terminal.from ((mdl (Dv := Dv) W hW).obj a)) :=
    fun a ↦ locallyOfFiniteType_terminal_from_opens (W a)
  have hqa : ∀ k : K, ((mdl (Dv := Dv) W hW).obj (OrderDual.toDual k)).IsQuasiAffine :=
    fun k ↦ Scheme.isQuasiAffine_of_iSup_basicOpen_eq_top _ (f k) (haff k) (hcov k)
  have hvc : ∀ a : Kᵒᵈ, CompactSpace (Dv.obj a) :=
    fun a ↦ (compactSpace_iff_quasiCompact (Dv.obj a)).mpr inferInstance
  have hoi : ∀ k : K, IsOpenImmersion (chart pv W hW hT k) := fun k ↦
    isOpenImmersion_toSpecΓ_comp_SpecMap_snd_of_basicOpen_le
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)) (tau pv W hW hT) (OrderDual.toDual k) g hin
      (f k) (hf k) (haff k) (hcov k)
  have hrange : ∀ k : K, (chart pv W hW hT k).opensRange =
      (⨆ l, PrimeSpectrum.basicOpen (fam pv W hW hT g f hf k l) :
        (Spec (CommRingCat.of ((rng pv W hW hT).obj k))).Opens) := fun k ↦
    opensRange_toSpecΓ_comp_SpecMap_snd (tau pv W hW hT) (str (V := V) (Y := Y))
      (OrderDual.toDual k) g (f k) (hf k)
      (fun l ↦ bijective_awayMap_appTop_of_basicOpen_le_opensRange
        (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)) (g l) (hin l)) (haff k) (hcov k)
  have hrU : ∀ (k : K) (l : Fin n),
      (PrimeSpectrum.basicOpen (fam pv W hW hT g f hf k l) :
          (Spec (CommRingCat.of ((rng pv W hW hT).obj k))).Opens) ≤
        (chart pv W hW hT k).opensRange := fun k l ↦ (le_iSup _ l).trans (hrange k).ge
  have hcovr : ∀ k : K, (chart pv W hW hT k).opensRange ≤
      ⨆ l, (PrimeSpectrum.basicOpen (fam pv W hW hT g f hf k l) :
        (Spec (CommRingCat.of ((rng pv W hW hT).obj k))).Opens) := fun k ↦ (hrange k).le
  have hft : ∀ (k : K) (l : Fin n),
      Algebra.FiniteType ℤ (Localization.Away (fam pv W hW hT g f hf k l)) :=
    finiteType_localization_away_charting (Dw := mdl (Dv := Dv) W hW)
      (fun k ↦ ((rng pv W hW hT).obj k)) (chart pv W hW hT) hoi (fam pv W hW hT g f hf) hrU
  have hne : Nonempty (idx pv W hW hT g f hf) :=
    nonempty_isChartedSubalgebra (rng pv W hW hT) (fam pv W hW hT g f hf) hft
  have hdir : IsDirected (idx pv W hW hT g f hf) (· ≤ ·) :=
    isDirected_isChartedSubalgebra (rng pv W hW hT) (fam pv W hW hT g f hf) hft
  have hprojcof : ∀ k : K, ∃ j : idx pv W hW hT g f hf,
      k ≤ (proj (F := rng pv W hW hT) (P := pred pv W hW hT g f hf)) j := fun k ↦
    exists_le_proj_isChartedSubalgebra (rng pv W hW hT) (fam pv W hW hT g f hf) hft k
  -- the ring-level colimit
  have hfpcol : IsColimit (FibreProduct.cocone (sec (Dv := Dv) W hW) (tau pv W hW hT)
      (str (V := V) (Y := Y))) := FibreProduct.isColimitCocone _ _ _ hcolim
  have hsurj : ∀ x : Γ((Y : Scheme.{u}), ⊤), ∃ (k : K) (y : (rng pv W hW hT).obj k),
      (rngCocone pv W hW hT).app k y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := FibreProduct.exists_app_eq hfpcol x
    exact ⟨OrderDual.ofDual i.unop, y, hy⟩
  have hsep : ∀ (k : K) (y z : (rng pv W hW hT).obj k),
      (rngCocone pv W hW hT).app k y = (rngCocone pv W hW hT).app k z →
        ∃ (k' : K) (v : k ⟶ k'), (rng pv W hW hT).map v y = (rng pv W hW hT).map v z := by
    intro k y z h
    obtain ⟨i, v, hv⟩ := FibreProduct.exists_map_eq hfpcol y z h
    refine ⟨OrderDual.ofDual i.unop, homOfLE (leOfHom v.unop), ?_⟩
    have hvv : (preorderToOpDual K).map (homOfLE (leOfHom v.unop)) = v :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    change (FibreProduct.diagram (sec (Dv := Dv) W hW) (tau pv W hW hT)
      (str (V := V) (Y := Y))).map ((preorderToOpDual K).map
        (homOfLE (leOfHom v.unop))) y = _
    rw [hvv]
    exact hv
  have hringcol : IsColimit (ringCocone (P := pred pv W hW hT g f hf)
      (rngCocone pv W hW hT)) :=
    (nonempty_isColimit_ringCocone (rngCocone pv W hW hT) (fun _ _ h ↦ h.fg)
      (fun k C hC ↦ exists_isChartedSubalgebra_ge (fam pv W hW hT g f hf k) (hft k) C hC)
      hsurj hsep).some
  have hYspec : IsLimit (Cone.mk (Spec Γ((Y : Scheme.{u}), ⊤))
      (specDiagramCone (rngCocone pv W hW hT) (pred pv W hW hT g f hf))) :=
    isLimitSpecDiagramCone _ _ hringcol
  have hYlim : IsLimit (coneY pv W hW hT g f hf) :=
    isLimitConeExtend hYspec (asIso ((Y : Scheme.{u}).toSpecΓ))
  -- the two legs
  have hbetaoi : ∀ j, IsOpenImmersion ((legSpec pv W hW hT g f hf).app j) := fun j ↦
    isOpenImmersion_specLeg_app (fam pv W hW hT g f hf) (chart pv W hW hT)
      (fun h ↦ chart_naturality pv W hW hT h) hrU hcovr j
  have hb : ∀ {k k' : K} (h : k ≤ k') (l : Fin n),
      (rng pv W hW hT).map (homOfLE h) (fam pv W hW hT g f hf k l) =
        fam pv W hW hT g f hf k' l := fun h l ↦
    FibreProduct.diagramMap_famMk (secK (Dv := Dv) W hW) (tauK pv W hW hT)
      (str (V := V) (Y := Y)) g f hf hfmap (homOfLE h) l
  have halpha := preimage_opensRange_openInclusionLeg (F := rng pv W hW hT) W hW
    (pred pv W hW hT g f hf)
  have hbeta := preimage_opensRange_specLeg (fam pv W hW hT g f hf) (chart pv W hW hT)
    (fun h ↦ chart_naturality pv W hW hT h) hrU hcovr hb
  -- the four cone compatibilities
  have hXr : ∀ j, (coneX pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legOpen pv W hW hT g f hf).app j).opensRange = V.ι ⁻¹ᵁ Y := by
    intro j
    have hor : ((legOpen pv W hW hT g f hf).app j).opensRange =
        W (OrderDual.toDual (stage (OrderDual.ofDual j))) := Scheme.Opens.opensRange_ι _
    rw [hor]
    exact hT _
  have hgrange : (⨆ l, (Y : Scheme.{u}).basicOpen (g l)) =
      (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange := le_antisymm (iSup_le hin) hgcov
  have hYr : ∀ j, (coneY pv W hW hT g f hf).π.app j ⁻¹ᵁ
      ((legSpec pv W hW hT g f hf).app j).opensRange = Y.ι ⁻¹ᵁ V := by
    intro j
    have hel : ∀ l : Fin n, (ringCocone (P := pred pv W hW hT g f hf)
        (rngCocone pv W hW hT)).ι.app (OrderDual.ofDual j)
          ⟨fam pv W hW hT g f hf (stage (OrderDual.ofDual j)) l,
            (isChartedSubalgebra_sub (fam pv W hW hT g f hf) (OrderDual.ofDual j)).mem l⟩ =
        g l := fun l ↦ rfl
    have hsup : (⨆ l, PrimeSpectrum.basicOpen
          ((ringCocone (P := pred pv W hW hT g f hf) (rngCocone pv W hW hT)).ι.app
            (OrderDual.ofDual j)
            ⟨fam pv W hW hT g f hf (stage (OrderDual.ofDual j)) l,
              (isChartedSubalgebra_sub (fam pv W hW hT g f hf) (OrderDual.ofDual j)).mem l⟩) :
          (Spec Γ((Y : Scheme.{u}), ⊤)).Opens) =
        ⨆ l, PrimeSpectrum.basicOpen (g l) :=
      iSup_congr fun l ↦ congrArg PrimeSpectrum.basicOpen (hel l)
    have hstep : Spec.map ((ringCocone (P := pred pv W hW hT g f hf)
          (rngCocone pv W hW hT)).ι.app (OrderDual.ofDual j)) ⁻¹ᵁ
        ((legSpec pv W hW hT g f hf).app j).opensRange =
      ⨆ l, PrimeSpectrum.basicOpen (g l) := by
      rw [opensRange_specLeg_app (fam pv W hW hT g f hf) (chart pv W hW hT)
        (fun h ↦ chart_naturality pv W hW hT h) hrU hcovr j]
      exact (SpecMap_preimage_iSup_basicOpen _ _).trans hsup
    refine Eq.trans (congrArg (fun U ↦ (Y : Scheme.{u}).toSpecΓ ⁻¹ᵁ U) hstep) ?_
    refine Eq.trans (Scheme.Hom.preimage_iSup _ _) ?_
    simp only [Scheme.toSpecΓ_preimage_basicOpen]
    rw [hgrange, Scheme.opensRange_homOfLE_inf_right]
  have hXW : ∀ j, S.homOfLE (inf_le_left : V ⊓ Y ≤ V) ≫ (coneX pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legOpen pv W hW hT g f hf).app j := fun j ↦
    (overlapCone_app_comp_ι V Y pv W hW hT _).symm
  have hYW : ∀ j, S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫ (coneY pv W hW hT g f hf).π.app j =
      (coneWp pv W hW hT g f hf).π.app j ≫ (legSpec pv W hW hT g f hf).app j := by
    intro j
    rw [coneExtend_app, specDiagramCone_app, specLeg_app, ringCocone_ι_app]
    refine Eq.trans (congrArg (fun m ↦ S.homOfLE (inf_le_right : V ⊓ Y ≤ Y) ≫
      (Y : Scheme.{u}).toSpecΓ ≫ m) (Spec.map_comp _ _)) ?_
    refine Eq.trans (keyY pv W hW hT (OrderDual.toDual (stage (OrderDual.ofDual j)))
      (Spec.map (CommRingCat.ofHom ((sub (OrderDual.ofDual j)).val :
        sub (OrderDual.ofDual j) →+* (rng pv W hW hT).obj (stage (OrderDual.ofDual j)))))) ?_
    exact congrArg (fun m ↦ (coneWp pv W hW hT g f hf).π.app j ≫ m)
      (Category.assoc _ _ _).symm
  have hxc : ∀ j : (idx pv W hW hT g f hf)ᵒᵈ,
      CompactSpace ((overlapDiagram Dv (pred pv W hW hT g f hf)).obj j) := fun _ ↦ hvc _
  have hspft : ∀ j : (idx pv W hW hT g f hf)ᵒᵈ, LocallyOfFiniteType (terminal.from
      ((specDiagram (rng pv W hW hT) (pred pv W hW hT g f hf)).obj j)) := by
    intro j
    have : Algebra.FiniteType ℤ (sub (OrderDual.ofDual j)) :=
      (Subalgebra.fg_iff_finiteType _).mp
        (isChartedSubalgebra_sub (fam pv W hW hT g f hf) (OrderDual.ofDual j)).fg
    exact locallyOfFiniteType_terminal_from_spec_of_finiteType _
  exact approximation_of_data pv W hW hT g f hf hS halpha hbeta hXr hYr hXW hYW
    (isLimitWhiskerOfCofinal _ hprojcof hpv) hYlim (isLimitWhiskerOfCofinal _ hprojcof hwlim)
    hprojcof

end Stacks.GluedStep
