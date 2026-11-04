module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.GluedRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteApproximation.QuotientSystem
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Slice
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer

/-!
# The system of glued relations of the problem step of Stacks 07SU

In the problem step of the proof of Stacks 07SU one is given a directed system of schemes
`V_i` with compatible open subschemes `W_i ⊆ V_i` (from Stacks 07RN), and an étale morphism
`W_i ⟶ U_i` to the stages `U_i` of an inverse system of algebraic spaces, cartesian over the
transition morphisms of the `U_i` (it is the base change of `W_0 ⟶ U_0`). The proof forms
`R_i = V_i ∪_{W_i} (W_i ×_{U_i} W_i)` and asserts that the `R_i ⇉ V_i` form an inverse system
of étale equivalence relations whose source squares are cartesian. This file constructs that
system on the big fppf site of a scheme `S`, from exactly these inputs, as an
`AlgebraicGeometry.Space.EtaleRelationSystem`.

## Main definitions

* `AlgebraicGeometry.Space.KernelPairSystem.obj`: the inverse system of the kernel pairs
  `W_i ×_{U_i} W_i` of a system of étale morphisms `W_i ⟶ U_i` from objects of the site to
  presheaves, with its two projections `fst`, `snd` and its diagonal `diag`.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData`: the inputs of the construction.
* `AlgebraicGeometry.Space.GluedNeighbourhoodRelationData.etaleRelationSystem`: the system
  `(V_i, R_i)`.
* `AlgebraicGeometry.BigFppfOver.liftFunctor`, `AlgebraicGeometry.BigFppfOver.liftNatTrans`:
  a diagram of schemes over `S` contained in the site (for instance the output of Stacks 07RN),
  as a diagram of the site.

## Main results

* `AlgebraicGeometry.Space.KernelPairSystem.isPullback_snd`: the kernel pairs are cartesian over
  the `W_i` along the second projection, as soon as the `W_i` are cartesian over the `U_i`
  (the displayed computation `(W_{i'} ×_{U_{i'}} W_{i'}) ×_{U_{i'}} U_i = W_i ×_{U_i} W_i` of the
  proof).
* `AlgebraicGeometry.Space.isEquivalenceRelation_toScheme_map`: an internal equivalence
  relation of the site is one of schemes.
* `AlgebraicGeometry.BigFppfSite.contains_gluePair`: the site is closed under glueing two
  of its objects along a common open.

## References

* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The big fppf site is closed under glueing two of its objects along a common open.** -/
theorem BigFppfSite.contains_gluePair (B : BigFppfSite.{u}) {W X Y : Scheme.{u}} (f : W ⟶ X)
    (g : W ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g] (hX : B.Contains X) (hY : B.Contains Y) :
    B.Contains (Scheme.gluePair f g) := by
  let U : ULift.{u} Bool → (Scheme.gluePair f g).Opens := fun i ↦
    cond i.down (Scheme.gluePairInl f g).opensRange (Scheme.gluePairInr f g).opensRange
  have hcov : ⨆ i, U i = ⊤ := by
    refine top_unique ?_
    rw [← Scheme.gluePair_opensRange_sup f g]
    exact sup_le (le_iSup U ⟨true⟩) (le_iSup U ⟨false⟩)
  refine (Scheme.size_le_of_iSup_eq_top U hcov).trans_lt (max_lt ?_ ?_)
  · exact (Cardinal.mk_lt_aleph0 (α := ULift.{u} Bool)).trans B.aleph0_lt_cutoff
  · refine (ciSup_le' fun i ↦ ?_).trans_lt (max_lt hX hY)
    rcases i with ⟨_ | _⟩
    · exact (Scheme.size_congr (Scheme.Hom.isoOpensRange (Scheme.gluePairInr f g)).symm).le.trans
        (le_max_right _ _)
    · exact (Scheme.size_congr (Scheme.Hom.isoOpensRange (Scheme.gluePairInl f g)).symm).le.trans
        (le_max_left _ _)

namespace BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {J : Type*} [Category* J]

variable (B S hS) in
/-- **A diagram of schemes over `S` contained in the site, as a diagram of the site.** Its
composite with `AlgebraicGeometry.BigFppfOver.toScheme` is the given diagram, by definition. -/
noncomputable def liftFunctor (D : J ⥤ Scheme.{u}) (hD : ∀ j, B.Contains (D.obj j))
    (p : D ⟶ (Functor.const J).obj S) : J ⥤ BigFppfOver B S hS :=
  Functor.toOver (ObjectProperty.lift _ D hD) (B.obj hS) (fun j ↦ ObjectProperty.homMk (p.app j))
    (fun {j k} u ↦ ObjectProperty.hom_ext _ (by
      change D.map u ≫ p.app k = p.app j
      simp))

/-- The composite of `liftFunctor B S hS D hD p` with `AlgebraicGeometry.BigFppfOver.toScheme`
is `D`. -/
lemma liftFunctor_comp_toScheme (D : J ⥤ Scheme.{u}) (hD : ∀ j, B.Contains (D.obj j))
    (p : D ⟶ (Functor.const J).obj S) : liftFunctor B S hS D hD p ⋙ toScheme B S hS = D := rfl

variable (B S hS) in
/-- **A natural transformation of diagrams of schemes over `S`, as one of diagrams of the
site.** -/
noncomputable def liftNatTrans {D D' : J ⥤ Scheme.{u}} (hD : ∀ j, B.Contains (D.obj j))
    (hD' : ∀ j, B.Contains (D'.obj j)) (p : D ⟶ (Functor.const J).obj S)
    (p' : D' ⟶ (Functor.const J).obj S) (α : D ⟶ D') (hα : α ≫ p' = p) :
    liftFunctor B S hS D hD p ⟶ liftFunctor B S hS D' hD' p' where
  app j := Over.homMk (ObjectProperty.homMk (α.app j)) (ObjectProperty.hom_ext _ (by
    change α.app j ≫ p'.app j = p.app j
    rw [← NatTrans.comp_app, hα]))
  naturality {j k} u := (toScheme B S hS).map_injective (α.naturality u)

/-- The component of `liftNatTrans B S hS hD hD' p p' α hα` at `j`, as a morphism of schemes, is
`α.app j`. -/
lemma toScheme_map_liftNatTrans_app {D D' : J ⥤ Scheme.{u}} (hD : ∀ j, B.Contains (D.obj j))
    (hD' : ∀ j, B.Contains (D'.obj j)) (p : D ⟶ (Functor.const J).obj S)
    (p' : D' ⟶ (Functor.const J).obj S) (α : D ⟶ D') (hα : α ≫ p' = p) (j : J) :
    (toScheme B S hS).map ((liftNatTrans B S hS hD hD' p p' α hα).app j) = α.app j := rfl

end BigFppfOver

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An internal equivalence relation of the big fppf site is one of schemes.** The functor to
schemes forgets the structure morphism, which preserves equivalence relations, and then includes
the site into schemes, which preserves finite limits. -/
theorem isEquivalenceRelation_toScheme_map {R U : BigFppfOver B S hS} (p₁ p₂ : R ⟶ U)
    (h : IsEquivalenceRelation p₁ p₂) :
    IsEquivalenceRelation ((BigFppfOver.toScheme B S hS).map p₁)
      ((BigFppfOver.toScheme B S hS).map p₂) := by
  have _ : HasFiniteLimits B.Schemes := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have _ : PreservesFiniteLimits B.inclusion :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks B.inclusion
  exact isEquivalenceRelation_map B.inclusion p₁.left p₂.left (isEquivalenceRelation_left p₁ p₂ h)

/-- **An internal equivalence relation of schemes between objects of the big fppf site is one of
the site.** -/
theorem isEquivalenceRelation_of_toScheme_map {R U : BigFppfOver B S hS} (p₁ p₂ : R ⟶ U)
    (h : IsEquivalenceRelation ((BigFppfOver.toScheme B S hS).map p₁)
      ((BigFppfOver.toScheme B S hS).map p₂)) :
    IsEquivalenceRelation p₁ p₂ := by
  have _ : IsEquivalenceRelation p₁.left p₂.left := isEquivalenceRelation_of_map B.inclusion _ _ h
  exact CategoryTheory.isEquivalenceRelation_of_left p₁ p₂

/-! ### The system of kernel pairs -/

namespace KernelPairSystem

variable {J : Type u} [Category.{u} J] {Q : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (W : J ⥤ BigFppfOver B S hS) (b : W ⋙ yoneda ⟶ Q)
  (hb : ∀ j, yoneda.relativelyRepresentable (b.app j))

/-- The kernel pair `W_j ×_{U_j} W_j` at a stage, as an object of the site. -/
noncomputable def objObj (j : J) : BigFppfOver B S hS := (hb j).pullback (b.app j)

/-- The first projection of the kernel pair at a stage. -/
noncomputable def fstApp (j : J) : objObj W b hb j ⟶ W.obj j :=
  yoneda.preimage ((hb j).fst (b.app j))

/-- The second projection of the kernel pair at a stage. -/
noncomputable def sndApp (j : J) : objObj W b hb j ⟶ W.obj j := (hb j).snd (b.app j)

/-- The kernel pair at a stage is a kernel pair in presheaves. -/
theorem isPullback_app (j : J) :
    IsPullback (yoneda.map (fstApp W b hb j)) (yoneda.map (sndApp W b hb j)) (b.app j)
      (b.app j) := by
  have h : yoneda.map (fstApp W b hb j) = (hb j).fst (b.app j) := Functor.map_preimage yoneda _
  rw [h]
  exact (hb j).isPullback (b.app j)

/-- The naturality square of `b` at a morphism `u : i ⟶ j`. -/
lemma map_comp_app {i j : J} (u : i ⟶ j) :
    yoneda.map (W.map u) ≫ b.app j = b.app i ≫ Q.map u := b.naturality u

/-- The transition morphism of the kernel pairs. -/
noncomputable def objMap {i j : J} (u : i ⟶ j) : objObj W b hb i ⟶ objObj W b hb j :=
  yoneda.preimage ((isPullback_app W b hb j).lift (yoneda.map (fstApp W b hb i ≫ W.map u))
    (yoneda.map (sndApp W b hb i ≫ W.map u)) (by
      simp only [Functor.map_comp, Category.assoc, map_comp_app]
      rw [(isPullback_app W b hb i).w_assoc]))

/-- The transition morphism of the kernel pairs commutes with the first projections. -/
@[reassoc (attr := simp)]
lemma objMap_fstApp {i j : J} (u : i ⟶ j) :
    objMap W b hb u ≫ fstApp W b hb j = fstApp W b hb i ≫ W.map u := by
  apply yoneda.map_injective
  rw [Functor.map_comp, objMap, Functor.map_preimage, IsPullback.lift_fst]

/-- The transition morphism of the kernel pairs commutes with the second projections. -/
@[reassoc (attr := simp)]
lemma objMap_sndApp {i j : J} (u : i ⟶ j) :
    objMap W b hb u ≫ sndApp W b hb j = sndApp W b hb i ≫ W.map u := by
  apply yoneda.map_injective
  rw [Functor.map_comp, objMap, Functor.map_preimage, IsPullback.lift_snd]

/-- Two morphisms to the kernel pair at a stage are equal if their composites with both
projections are. -/
lemma hom_ext_app {j : J} {T : BigFppfOver B S hS} {x y : T ⟶ objObj W b hb j}
    (h₁ : x ≫ fstApp W b hb j = y ≫ fstApp W b hb j)
    (h₂ : x ≫ sndApp W b hb j = y ≫ sndApp W b hb j) : x = y := by
  apply yoneda.map_injective
  refine (isPullback_app W b hb j).hom_ext ?_ ?_
  · rw [← Functor.map_comp, ← Functor.map_comp, h₁]
  · rw [← Functor.map_comp, ← Functor.map_comp, h₂]

/-- **The inverse system of kernel pairs** `W_j ×_{U_j} W_j`. -/
noncomputable def obj : J ⥤ BigFppfOver B S hS where
  obj := objObj W b hb
  map := objMap W b hb
  map_id j := hom_ext_app W b hb (by simp) (by simp)
  map_comp u v := hom_ext_app W b hb (by simp) (by simp)

/-- The first projection of the system of kernel pairs. -/
noncomputable def fst : obj W b hb ⟶ W where
  app := fstApp W b hb
  naturality _ _ u := objMap_fstApp W b hb u

/-- The second projection of the system of kernel pairs. -/
noncomputable def snd : obj W b hb ⟶ W where
  app := sndApp W b hb
  naturality _ _ u := objMap_sndApp W b hb u

/-- The diagonal at a stage. -/
noncomputable def diagApp (j : J) : W.obj j ⟶ objObj W b hb j :=
  yoneda.preimage ((isPullback_app W b hb j).lift (𝟙 _) (𝟙 _) rfl)

/-- The diagonal at a stage is a section of the first projection. -/
@[reassoc (attr := simp)]
lemma diagApp_fstApp (j : J) : diagApp W b hb j ≫ fstApp W b hb j = 𝟙 _ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, diagApp, Functor.map_preimage, IsPullback.lift_fst]
  exact (yoneda.map_id _).symm

/-- The diagonal at a stage is a section of the second projection. -/
@[reassoc (attr := simp)]
lemma diagApp_sndApp (j : J) : diagApp W b hb j ≫ sndApp W b hb j = 𝟙 _ := by
  apply yoneda.map_injective
  rw [Functor.map_comp, diagApp, Functor.map_preimage, IsPullback.lift_snd]
  exact (yoneda.map_id _).symm

/-- The diagonal of the system of kernel pairs. -/
noncomputable def diag : W ⟶ obj W b hb where
  app := diagApp W b hb
  naturality _ _ u := hom_ext_app W b hb (by simp [obj]) (by simp [obj])

/-- The diagonal of the system of kernel pairs is a section of the first projection. -/
@[simp]
lemma diag_fst : diag W b hb ≫ fst W b hb = 𝟙 W :=
  NatTrans.ext <| funext fun j ↦ diagApp_fstApp W b hb j

/-- The diagonal of the system of kernel pairs is a section of the second projection. -/
@[simp]
lemma diag_snd : diag W b hb ≫ snd W b hb = 𝟙 W :=
  NatTrans.ext <| funext fun j ↦ diagApp_sndApp W b hb j

/-- The projections of a kernel pair form an internal equivalence relation of schemes. -/
theorem isEquivalenceRelation (j : J) :
    IsEquivalenceRelation ((BigFppfOver.toScheme B S hS).map ((fst W b hb).app j))
      ((BigFppfOver.toScheme B S hS).map ((snd W b hb).app j)) := by
  refine isEquivalenceRelation_toScheme_map _ _ ?_
  have _ : HasPullbacks (BigFppfOver B S hS) := inferInstance
  exact isEquivalenceRelation_of_map yoneda _ _
    (IsKernelPair.equivalenceRelation (b.app j) _ _ (pullback.isLimit _ _)
      (isPullback_app W b hb j)).isEquivalenceRelation

variable (hW : ∀ ⦃i j : J⦄ (u : i ⟶ j),
  IsPullback (yoneda.map (W.map u)) (b.app i) (b.app j) (Q.map u))

include hW in
/-- **The kernel pairs are cartesian over the `W_i` along the second projection**, as soon as the
`W_i` are cartesian over the `U_i`: `(W_j ×_{U_j} W_j) ×_{W_j} W_i = W_i ×_{U_i} W_i`. -/
theorem isPullback_snd_yoneda ⦃i j : J⦄ (u : i ⟶ j) :
    IsPullback (yoneda.map (objMap W b hb u)) (yoneda.map (sndApp W b hb i))
      (yoneda.map (sndApp W b hb j)) (yoneda.map (W.map u)) := by
  have e₁ : yoneda.map (objMap W b hb u) ≫ yoneda.map (fstApp W b hb j) =
      yoneda.map (fstApp W b hb i) ≫ yoneda.map (W.map u) := by
    simpa only [Functor.map_comp] using congrArg yoneda.map (objMap_fstApp W b hb u)
  have e₂ : yoneda.map (objMap W b hb u) ≫ yoneda.map (sndApp W b hb j) =
      yoneda.map (sndApp W b hb i) ≫ yoneda.map (W.map u) := by
    simpa only [Functor.map_comp] using congrArg yoneda.map (objMap_sndApp W b hb u)
  refine IsPullback.of_right ?_ e₂ (isPullback_app W b hb j)
  rw [e₁, map_comp_app]
  exact (isPullback_app W b hb i).paste_horiz (hW u)

include hW in
/-- The kernel pairs are cartesian over the `W_i`, in schemes. -/
theorem isPullback_snd ⦃i j : J⦄ (u : i ⟶ j) :
    IsPullback ((BigFppfOver.toScheme B S hS).map ((obj W b hb).map u))
      ((BigFppfOver.toScheme B S hS).map ((snd W b hb).app i))
      ((BigFppfOver.toScheme B S hS).map ((snd W b hb).app j))
      ((BigFppfOver.toScheme B S hS).map (W.map u)) := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget B S hS) := inferInstance
  have _ : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  exact (BigFppfOver.toScheme B S hS).map_isPullback
    ((isPullback_snd_yoneda W b hb hW u).of_map yoneda ((snd W b hb).naturality u))

end KernelPairSystem

/-! ### The glued relations -/

variable (B S hS) in
/-- **The inputs of the glueing step of the proof of Stacks 07SU.** An inverse system `base` of
presheaves (the algebraic spaces `U_i`), an inverse system `nbhd` of objects of the site (the
schemes `W_i`) with étale morphisms `toBase` to the `U_i` whose naturality squares are cartesian
(so `W_i = W_0 ×_{U_0} U_i`), and an inverse system `ambient` of objects of the site (the schemes
`V_i`) containing the `W_i` as compatible open subschemes, cut out by the transition
morphisms. -/
structure GluedNeighbourhoodRelationData (J : Type u) [Category.{u} J] where
  /-- The inverse system of presheaves `U_i`. -/
  base : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The inverse system of the étale neighbourhoods `W_i`. -/
  nbhd : J ⥤ BigFppfOver B S hS
  /-- The inverse system of the ambient schemes `V_i`. -/
  ambient : J ⥤ BigFppfOver B S hS
  /-- The étale morphisms `W_i ⟶ U_i`. -/
  toBase : nbhd ⋙ yoneda ⟶ base
  /-- The morphisms `W_i ⟶ U_i` are étale. -/
  etale_toBase : ∀ j, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf (toBase.app j)
  /-- The `W_i` are cartesian over the `U_i`. -/
  isPullback_toBase : ∀ ⦃i j : J⦄ (u : i ⟶ j),
    IsPullback (yoneda.map (nbhd.map u)) (toBase.app i) (toBase.app j) (base.map u)
  /-- The inclusions `W_i ⟶ V_i`. -/
  incl : nbhd ⟶ ambient
  /-- The inclusions are open immersions. -/
  isOpenImmersion_incl : ∀ j,
    _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (incl.app j))
  /-- The open subschemes `W_i ⊆ V_i` are cut out by the transition morphisms. -/
  isPullback_incl : ∀ ⦃i j : J⦄ (u : i ⟶ j),
    IsPullback ((BigFppfOver.toScheme B S hS).map (nbhd.map u))
      ((BigFppfOver.toScheme B S hS).map (incl.app i))
      ((BigFppfOver.toScheme B S hS).map (incl.app j))
      ((BigFppfOver.toScheme B S hS).map (ambient.map u))

namespace GluedNeighbourhoodRelationData

variable {J : Type u} [Category.{u} J] (G : GluedNeighbourhoodRelationData B S hS J)

attribute [instance] isOpenImmersion_incl

/-- The system of kernel pairs `W_i ×_{U_i} W_i`. -/
noncomputable abbrev kernelPair : J ⥤ BigFppfOver B S hS :=
  KernelPairSystem.obj G.nbhd G.toBase fun j ↦ (G.etale_toBase j).rep

/-- The first projection `W_i ×_{U_i} W_i ⟶ W_i`. -/
noncomputable abbrev fst : G.kernelPair ⟶ G.nbhd :=
  KernelPairSystem.fst G.nbhd G.toBase fun j ↦ (G.etale_toBase j).rep

/-- The second projection `W_i ×_{U_i} W_i ⟶ W_i`. -/
noncomputable abbrev snd : G.kernelPair ⟶ G.nbhd :=
  KernelPairSystem.snd G.nbhd G.toBase fun j ↦ (G.etale_toBase j).rep

/-- The diagonal `W_i ⟶ W_i ×_{U_i} W_i`. -/
noncomputable abbrev diag : G.nbhd ⟶ G.kernelPair :=
  KernelPairSystem.diag G.nbhd G.toBase fun j ↦ (G.etale_toBase j).rep


/-- The schemes `W_i`. -/
noncomputable abbrev nbhdScheme : J ⥤ Scheme.{u} := G.nbhd ⋙ BigFppfOver.toScheme B S hS

/-- The schemes `V_i`. -/
noncomputable abbrev ambientScheme : J ⥤ Scheme.{u} := G.ambient ⋙ BigFppfOver.toScheme B S hS

/-- The schemes `W_i ×_{U_i} W_i`. -/
noncomputable abbrev kernelPairScheme : J ⥤ Scheme.{u} :=
  G.kernelPair ⋙ BigFppfOver.toScheme B S hS

/-- The inclusions `W_i ⟶ V_i` of schemes. -/
noncomputable abbrev inclScheme : G.nbhdScheme ⟶ G.ambientScheme :=
  Functor.whiskerRight G.incl (BigFppfOver.toScheme B S hS)

/-- The diagonals `W_i ⟶ W_i ×_{U_i} W_i` of schemes. -/
noncomputable abbrev diagScheme : G.nbhdScheme ⟶ G.kernelPairScheme :=
  Functor.whiskerRight G.diag (BigFppfOver.toScheme B S hS)

/-- The first projections of schemes. -/
noncomputable abbrev fstScheme : G.kernelPairScheme ⟶ G.nbhdScheme :=
  Functor.whiskerRight G.fst (BigFppfOver.toScheme B S hS)

/-- The second projections of schemes. -/
noncomputable abbrev sndScheme : G.kernelPairScheme ⟶ G.nbhdScheme :=
  Functor.whiskerRight G.snd (BigFppfOver.toScheme B S hS)

/-- The inclusion `W_j ⟶ V_j` of schemes is an open immersion. -/
instance (j : J) : _root_.AlgebraicGeometry.IsOpenImmersion (G.inclScheme.app j) :=
  G.isOpenImmersion_incl j

/-- The first projection `W_j ×_{U_j} W_j ⟶ W_j` of schemes is étale. -/
instance etale_fstScheme (j : J) : Etale (G.fstScheme.app j) :=
  (G.etale_toBase j).property (G.toBase.app j) _ _
    (KernelPairSystem.isPullback_app G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep) j).flip

/-- The second projection `W_j ×_{U_j} W_j ⟶ W_j` of schemes is étale. -/
instance etale_sndScheme (j : J) : Etale (G.sndScheme.app j) :=
  (G.etale_toBase j).property (G.toBase.app j) _ _
    (KernelPairSystem.isPullback_app G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep) j)

/-- The two projections `W_j ×_{U_j} W_j ⟶ W_j` of schemes form an equivalence relation. -/
instance isEquivalenceRelation_fstScheme_sndScheme (j : J) :
    IsEquivalenceRelation (G.fstScheme.app j) (G.sndScheme.app j) :=
  KernelPairSystem.isEquivalenceRelation G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep) j

/-- The diagonals of schemes are sections of the first projections. -/
lemma diagScheme_fstScheme : G.diagScheme ≫ G.fstScheme = 𝟙 _ := by
  rw [← Functor.whiskerRight_comp, KernelPairSystem.diag_fst, Functor.whiskerRight_id']

/-- The diagonals of schemes are sections of the second projections. -/
lemma diagScheme_sndScheme : G.diagScheme ≫ G.sndScheme = 𝟙 _ := by
  rw [← Functor.whiskerRight_comp, KernelPairSystem.diag_snd, Functor.whiskerRight_id']

/-- The diagonal of schemes at a stage is a section of the first projection. -/
lemma diagScheme_app_fstScheme_app (j : J) : G.diagScheme.app j ≫ G.fstScheme.app j = 𝟙 _ := by
  rw [← NatTrans.comp_app, diagScheme_fstScheme, NatTrans.id_app]

/-- The diagonal of schemes at a stage is a section of the second projection. -/
lemma diagScheme_app_sndScheme_app (j : J) : G.diagScheme.app j ≫ G.sndScheme.app j = 𝟙 _ := by
  rw [← NatTrans.comp_app, diagScheme_sndScheme, NatTrans.id_app]

/-- The diagonal `W_j ⟶ W_j ×_{U_j} W_j` of schemes is an open immersion. -/
instance isOpenImmersion_diagScheme (j : J) :
    _root_.AlgebraicGeometry.IsOpenImmersion (G.diagScheme.app j) :=
  isOpenImmersion_of_section_of_etale (G.fstScheme.app j) _ (G.diagScheme_app_fstScheme_app j)

/-- The glued relations `R_i = V_i ∪_{W_i} (W_i ×_{U_i} W_i)`, as schemes. -/
noncomputable abbrev relScheme : J ⥤ Scheme.{u} := gluePairFunctor G.inclScheme G.diagScheme

/-- The source maps `R_i ⟶ V_i` of schemes, extending the second projections. -/
noncomputable abbrev sourceScheme : G.relScheme ⟶ G.ambientScheme :=
  gluedRelationProjNatTrans G.inclScheme G.diagScheme G.sndScheme G.diagScheme_sndScheme

/-- The target maps `R_i ⟶ V_i` of schemes, extending the first projections. -/
noncomputable abbrev targetScheme : G.relScheme ⟶ G.ambientScheme :=
  gluedRelationProjNatTrans G.inclScheme G.diagScheme G.fstScheme G.diagScheme_fstScheme

/-- The glued relation `R_j` is contained in the site. -/
lemma contains_relScheme (j : J) : B.Contains (G.relScheme.obj j) :=
  B.contains_gluePair _ _ (G.ambient.obj j).left.property (G.kernelPair.obj j).left.property

/-- The glued relations, as objects of the site, over `S` through the source maps. -/
noncomputable def rel : J ⥤ BigFppfOver B S hS :=
  Functor.toOver (ObjectProperty.lift _ G.relScheme G.contains_relScheme) (B.obj hS)
    (fun j ↦ ObjectProperty.homMk
      (G.sourceScheme.app j ≫ B.inclusion.map (G.ambient.obj j).hom))
    (fun {j k} u ↦ by
      apply ObjectProperty.hom_ext
      change G.relScheme.map u ≫ G.sourceScheme.app k ≫ B.inclusion.map (G.ambient.obj k).hom =
        G.sourceScheme.app j ≫ B.inclusion.map (G.ambient.obj j).hom
      rw [G.sourceScheme.naturality_assoc]
      change G.sourceScheme.app j ≫ B.inclusion.map ((G.ambient.map u).left) ≫
        B.inclusion.map (G.ambient.obj k).hom = _
      rw [← B.inclusion.map_comp, Over.w])

/-- The underlying scheme of `G.rel.obj j` is `G.relScheme.obj j`. -/
lemma toScheme_obj_rel (j : J) :
    (BigFppfOver.toScheme B S hS).obj (G.rel.obj j) = G.relScheme.obj j := rfl

/-- The underlying morphism of schemes of `G.rel.map u` is `G.relScheme.map u`. -/
lemma toScheme_map_rel {j k : J} (u : j ⟶ k) :
    (BigFppfOver.toScheme B S hS).map (G.rel.map u) = G.relScheme.map u := rfl

/-- The target and source maps lie over `S`. -/
lemma targetScheme_comp_hom (j : J) :
    G.targetScheme.app j ≫ B.inclusion.map (G.ambient.obj j).hom =
      G.sourceScheme.app j ≫ B.inclusion.map (G.ambient.obj j).hom := by
  have key : ∀ {X Y : BigFppfOver B S hS} (f : X ⟶ Y),
      B.inclusion.map f.left ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom := fun f ↦ by
    rw [← B.inclusion.map_comp, Over.w]
  have hι : G.inclScheme.app j ≫ B.inclusion.map (G.ambient.obj j).hom =
      B.inclusion.map (G.nbhd.obj j).hom := key (G.incl.app j)
  have h₁ : G.fstScheme.app j ≫ B.inclusion.map (G.nbhd.obj j).hom =
      B.inclusion.map (G.kernelPair.obj j).hom := key (G.fst.app j)
  have h₂ : G.sndScheme.app j ≫ B.inclusion.map (G.nbhd.obj j).hom =
      B.inclusion.map (G.kernelPair.obj j).hom := key (G.snd.app j)
  exact gluedRelationProj_comp_eq (G.inclScheme.app j) (G.diagScheme.app j) (G.fstScheme.app j)
    (G.sndScheme.app j) (G.diagScheme_app_fstScheme_app j) (G.diagScheme_app_sndScheme_app j) _
    (by rw [hι, h₁, h₂])

/-- The source maps `R_i ⟶ V_i`. -/
noncomputable def source : G.rel ⟶ G.ambient where
  app j := Over.homMk (ObjectProperty.homMk (G.sourceScheme.app j)) rfl
  naturality _ _ u := (BigFppfOver.toScheme B S hS).map_injective
    (G.sourceScheme.naturality u)

/-- The target maps `R_i ⟶ V_i`. -/
noncomputable def target : G.rel ⟶ G.ambient where
  app j := Over.homMk (ObjectProperty.homMk (G.targetScheme.app j))
    (ObjectProperty.hom_ext _ (G.targetScheme_comp_hom j))
  naturality _ _ u := (BigFppfOver.toScheme B S hS).map_injective
    (G.targetScheme.naturality u)

/-- The underlying morphism of schemes of `G.source.app j` is `G.sourceScheme.app j`. -/
lemma toScheme_map_source_app (j : J) :
    (BigFppfOver.toScheme B S hS).map (G.source.app j) = G.sourceScheme.app j := rfl

/-- The underlying morphism of schemes of `G.target.app j` is `G.targetScheme.app j`. -/
lemma toScheme_map_target_app (j : J) :
    (BigFppfOver.toScheme B S hS).map (G.target.app j) = G.targetScheme.app j := rfl

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The glued relations form an inverse system of étale equivalence relations with cartesian
source squares** (the claims of the proof of Stacks 07SU that `j_i = (t_i, s_i)` is an étale
equivalence relation and that the squares (70.8.1.1) are cartesian). -/
noncomputable def etaleRelationSystem : EtaleRelationSystem B S hS J where
  obj := G.ambient
  rel := G.rel
  s := G.source
  t := G.target
  isEtaleEquivalenceRelation j := by
    have hsch : IsEquivalenceRelation ((BigFppfOver.toScheme B S hS).map (G.target.app j))
        ((BigFppfOver.toScheme B S hS).map (G.source.app j)) :=
      isEquivalenceRelation_gluedRelationProj (G.inclScheme.app j) (G.diagScheme.app j)
        (G.fstScheme.app j) (G.sndScheme.app j) (G.diagScheme_app_fstScheme_app j)
        (G.diagScheme_app_sndScheme_app j)
    have hsite := isEquivalenceRelation_of_toScheme_map _ _ hsch
    have _ : HasFiniteLimits (BigFppfOver B S hS) := hasFiniteLimits_of_hasTerminal_and_pullbacks
    have hy := isEquivalenceRelation_map yoneda _ _ hsite
    refine isEtaleEquivalenceRelation_of_yoneda B S hS (G.source.app j) (G.target.app j)
      (Iso.refl _) (by simpa using hy) ?_ ?_
    · exact etale_gluedRelationProj _ _ _ (G.diagScheme_app_fstScheme_app j)
    · exact etale_gluedRelationProj _ _ _ (G.diagScheme_app_sndScheme_app j)
  isPullback_s {i j} u :=
    isPullback_gluedRelationProjNatTrans G.inclScheme G.diagScheme G.sndScheme
      G.diagScheme_sndScheme G.isPullback_incl
      (KernelPairSystem.isPullback_snd G.nbhd G.toBase (fun j ↦ (G.etale_toBase j).rep)
        G.isPullback_toBase) u

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The objects of `G.etaleRelationSystem` are the schemes `V_i`. -/
lemma etaleRelationSystem_obj : G.etaleRelationSystem.obj = G.ambient := rfl

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The relations of `G.etaleRelationSystem` are the glued relations `R_i`. -/
lemma etaleRelationSystem_rel : G.etaleRelationSystem.rel = G.rel := rfl

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The glued relations are quasi-compact as soon as the `V_i` and the `W_i ×_{U_i} W_i` are. -/
lemma compactSpace_rel (j : J)
    [CompactSpace (G.ambientScheme.obj j)] [CompactSpace (G.kernelPairScheme.obj j)] :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (G.etaleRelationSystem.rel.obj j)) :=
  Scheme.compactSpace_gluePair _ _

end GluedNeighbourhoodRelationData

end Space

end AlgebraicGeometry
