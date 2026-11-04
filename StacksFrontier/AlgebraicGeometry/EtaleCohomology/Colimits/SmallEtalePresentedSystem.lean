module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitPresentationComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionComposition

/-!
# The cohomology cocone of a presented system of abelian étale sheaves

`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.PresentedSystem` is the datum of
[Stacks, Tag 09YQ] on the small étale sites: a system `(F_i, φ_a)` of abelian sheaves on the
levels of an inverse system of schemes, a sheaf `𝒢` on the small étale site of the limit, legs
`ι_i : f_i^{-1}F_i ⟶ 𝒢`, the hypothesis that these present `𝒢` as `colim f_i^{-1}F_i`, **and two
laws** making the induced maps on cohomology a cocone over a filtered diagram:

* `transition_comp`, the cocycle law `H^p(X_k, F_k) → H^p(X_j, F_j) → H^p(X_i, F_i)` composing to
  the map of the composite transition; and
* `leg_transition`, the cocone law: the leg at a level factors every earlier leg.

Without them the statement of the tag — that the cocone is a colimit cocone — does not mean
anything, so the dimension shift
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_degreeZero_of_vanishing`
quantifies over `PresentedSystem`s and is only as strong as the supply of them. Until now the only
one exhibited was the zero system
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.trivialPresentedSystem`).

This file proves the two laws for an **arbitrary** system with a colimit presentation, so that
`presentedSystemOfIsColimitPresentation` turns the data the source gives into a `PresentedSystem`
and the dimension shift applies to every system.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyMapTo_comp` — **the composition law for
  `Stacks.EtaleCohomology.etaleCohomologyMapTo`.** Both laws are instances of it: it says that
  the cohomology map of `k₁` and `w₁` after that of `k₂` and `w₂` is the cohomology map of the
  composite `k = k₁ ≫ k₂` and of `w = (k^{-1} ≅ k₁^{-1}k₂^{-1}) ≫ k₁^{-1}w₂ ≫ w₁`.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemPullbackComp_inv_comp` — the two
  comparisons of inverse images along a composite transition agree, once the two inverse images
  this library carries are compared at each of the three morphisms.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemTransitionMap_comp` — the cocycle
  condition of the system, read in the constructed inverse image.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.etaleCohomologyTransition_comp` and
  `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.etaleCohomologyMapTo_transition` — **the two
  laws.**
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.presentedSystemOfIsColimitPresentation` —
  **every system with a colimit presentation is a presented system.**

## Implementation notes

**The composition law for restriction is in the tree.** The module docstring of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleCohomologyColimit.lean` says
that deducing the two laws "needs the composition law for restriction, `k₁^{-1}k₂^{-1} ≅
(k₂ ∘ k₁)^{-1}` transported to `Ext` and matched against the constant-sheaf comparison, which
this library does not have". That is no longer so: it is
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp`, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/RestrictionComposition.lean`,
whose proof matches the composition of the actions on `Ext` against
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso_comp` — exactly the step described as
missing. Together with naturality in the sheaf,
`Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_mk₀`, it gives
`etaleCohomologyMapTo_comp`, and nothing else about `Ext` is needed.

**The cocone law is the presentation hypothesis itself.** `IsCompatibleFamily`, the first clause
of `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.IsColimitPresentation`, is stated at
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.coneInverseImageComp`, which *is*
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'` at the factorisation
`f_j = f_i ≫ f_{ji}`; so it is literally the hypothesis `hw` of `etaleCohomologyMapTo_comp` at
that factorisation, and `leg_transition` costs nothing beyond it.

**The cocycle law needs one crossing.** The system carries its transitions along
`Stacks.EtaleCohomology.systemPullback`, the abstract left adjoint, and its cocycle condition is
stated at `Stacks.EtaleCohomology.systemPullbackComp`; the hypothesis of
`etaleCohomologyMapTo_comp` is stated at `etaleAbelianInverseImageCompIso'`, the comparison for
the constructed inverse image. `systemPullbackComp_inv_comp` identifies the two. It is the
transition-side twin of
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.conePullbackComp_inv_comp` and has the same
proof: both comparisons are induced by one and the same comparison of *direct* images —
`Stacks.EtaleCohomology.smallEtalePushforwardAbComp'`, which
`Stacks.EtaleCohomology.etaleAbelianDirectImageCompIso'` is by definition — so
`CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker` applies, with
`Stacks.EtaleCohomology.systemPullbackComp_eq` and
`Stacks.EtaleCohomology.smallEtalePullbackAbComp'_eq_leftAdjointCompIso` identifying the abstract
side. `systemTransitionMap_comp` then reads the cocycle condition across it, the chase being two
uses of the naturality of that comparison.

**What this does not do.** It supplies the two laws and nothing else. The dimension shift's three
substantive hypotheses — the degree-zero statement, the vanishing for a pointwise injective
system, and the dévissage of [Stacks, Tag 0EXZ] for systems on the small étale sites — are
untouched, and [Stacks, Tag 09YQ] is not closed here.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 09ZI](https://stacks.math.columbia.edu/tag/09ZI)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

section MapToComp

variable {X Y Z : Scheme.{u}}
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The composition law for the cohomology map of a morphism together with a map of sheaves.**
-/
theorem etaleCohomologyMapTo_comp (k₁ : Z ⟶ Y) (k₂ : Y ⟶ X) (k : Z ⟶ X) (hk : k = k₁ ≫ k₂)
    {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {C : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w₂ : (etaleAbelianInverseImage.{u, u + 1} k₂).obj A ⟶ B)
    (w₁ : (etaleAbelianInverseImage.{u, u + 1} k₁).obj B ⟶ C)
    (w : (etaleAbelianInverseImage.{u, u + 1} k).obj A ⟶ C)
    (hw : (etaleAbelianInverseImageCompIso'.{u, u + 1} k₁ k₂ k hk).hom.app A ≫
        (etaleAbelianInverseImage.{u, u + 1} k₁).map w₂ ≫ w₁ = w)
    (p : ℕ) (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k₁ w₁ p (etaleCohomologyMapTo k₂ w₂ p x) =
      etaleCohomologyMapTo k w p x := by
  subst hw
  have hres := etaleCohomologyRestrictionMap_comp.{u, u + 1, u + 1} k₂ k₁ k hk A p x
  have hnat := etaleCohomologyRestrictionMap_comp_mk₀.{u, u + 1, u + 1} k₁ w₂ p
    (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₂ A p x)
  show Sheaf.H.map w₁ p (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₁ B p
      (Sheaf.H.map w₂ p (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₂ A p x))) = _
  rw [show (Sheaf.H.map w₂ p (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₂ A p x)) =
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₂ A p x).comp
        (Ext.mk₀ w₂) (add_zero p) from rfl, hnat]
  show Sheaf.H.map w₁ p (Sheaf.H.map ((etaleAbelianInverseImage.{u, u + 1} k₁).map w₂) p
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₁ _ p
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₂ A p x))) = _
  rw [← Sheaf.H.map_comp_apply]
  show _ = Sheaf.H.map ((etaleAbelianInverseImageCompIso'.{u, u + 1} k₁ k₂ k hk).hom.app A ≫
      (etaleAbelianInverseImage.{u, u + 1} k₁).map w₂ ≫ w₁) p
      (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A p x)
  rw [← hres, ← Sheaf.H.map_comp_apply, ← Category.assoc, Iso.inv_hom_id_app,
    Category.id_comp]

end MapToComp

/-! ### The cocycle condition of a system in the constructed inverse image -/

namespace SmallEtaleLimitCohomology

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]

/-- The inverse of the canonical isomorphism between two left adjoints is the one the other way. -/
private theorem leftAdjointUniq_inv_eq_hom {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G) :
    (adj₁.leftAdjointUniq adj₂).inv = (adj₂.leftAdjointUniq adj₁).hom :=
  NatTrans.ext (funext fun x => Adjunction.leftAdjointUniq_inv_app _ _ x)

/-- **The two comparisons of inverse images along a composite transition agree.** -/
theorem systemPullbackComp_inv_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (systemPullbackComp D AddCommGrpCat.{u + 1} a b).inv ≫
        Functor.whiskerRight (inverseImageIsoPullbackAb (D.map b)).hom
            (systemPullback D AddCommGrpCat.{u + 1} a) ≫
          Functor.whiskerLeft (etaleAbelianInverseImage.{u, u + 1} (D.map b))
            (inverseImageIsoPullbackAb (D.map a)).hom =
      (inverseImageIsoPullbackAb (D.map (a ≫ b))).hom ≫
        (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
          (D.map_comp a b)).hom := by
  have hhex := Adjunction.leftAdjointUniq_hom_comp_whisker
    (smallEtaleAdjunctionAb (D.map b))
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map b))
    (smallEtaleAdjunctionAb (D.map a))
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a))
    (smallEtaleAdjunctionAb (D.map (a ≫ b)))
    (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map b)).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a))).ofNatIsoRight
      (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)))
    (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)) rfl
  have h₁ : Adjunction.leftAdjointUniq
      (((smallEtaleAdjunctionAb (D.map b)).comp
          (smallEtaleAdjunctionAb (D.map a))).ofNatIsoRight
        (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)))
      (smallEtaleAdjunctionAb (D.map (a ≫ b))) =
      systemPullbackComp D AddCommGrpCat.{u + 1} a b := by
    rw [Adjunction.leftAdjointUniq_ofNatIsoRight_comp,
      ← smallEtalePullbackAbComp'_eq_leftAdjointCompIso]
    exact (systemPullbackComp_eq D a b).symm
  have h₂ : Adjunction.leftAdjointUniq
      (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map b)).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a))).ofNatIsoRight
        (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)))
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map (a ≫ b))) =
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
        (D.map_comp a b)).symm := by
    refine (Adjunction.leftAdjointUniq_ofNatIsoRight_comp
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map b))
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a))
      (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map (a ≫ b)))
      (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b))
        (D.map_comp a b))).trans ?_
    rfl
  have h₃ := Adjunction.leftAdjointUniq_trans
    (smallEtaleAdjunctionAb (D.map (a ≫ b)))
    (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map (a ≫ b)))
    (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map b)).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a))).ofNatIsoRight
      (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)))
  have hA : (systemPullbackComp D AddCommGrpCat.{u + 1} a b).inv =
      (Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb (D.map (a ≫ b)))
        (((smallEtaleAdjunctionAb (D.map b)).comp
            (smallEtaleAdjunctionAb (D.map a))).ofNatIsoRight
          (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b))
            (D.map_comp a b)))).hom := by
    rw [← h₁, leftAdjointUniq_inv_eq_hom]
  have hR : (inverseImageIsoPullbackAb (D.map (a ≫ b))).hom ≫
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
        (D.map_comp a b)).hom =
      (Adjunction.leftAdjointUniq (smallEtaleAdjunctionAb (D.map (a ≫ b)))
        (((etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map b)).comp
            (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} (D.map a))).ofNatIsoRight
          (smallEtalePushforwardAbComp' (D.map a) (D.map b) (D.map (a ≫ b))
            (D.map_comp a b)))).hom := by
    rw [← h₃]
    refine congrArg (fun t => (inverseImageIsoPullbackAb (D.map (a ≫ b))).hom ≫ t) ?_
    exact (congrArg Iso.inv h₂).symm.trans (leftAdjointUniq_inv_eq_hom _ _)
  rw [hA, hR]
  exact hhex

/-- **The cocycle condition of a system, in the constructed inverse image.** -/
theorem systemTransitionMap_comp (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j k : Iᵒᵖ}
    (a : i ⟶ j) (b : j ⟶ k) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
          (D.map_comp a b)).hom.app (F.obj k) ≫
        (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (systemTransitionMap F b) ≫
          systemTransitionMap F a =
      systemTransitionMap F (a ≫ b) := by
  have hco := NatTrans.congr_app (systemPullbackComp_inv_comp (D := D) a b) (F.obj k)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hco
  have hT : (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
        (D.map_comp a b)).hom.app (F.obj k) =
      (inverseImageIsoPullbackAb (D.map (a ≫ b))).inv.app (F.obj k) ≫
        (systemPullbackComp D AddCommGrpCat.{u + 1} a b).inv.app (F.obj k) ≫
          (systemPullback D AddCommGrpCat.{u + 1} a).map
              ((inverseImageIsoPullbackAb (D.map b)).hom.app (F.obj k)) ≫
            (inverseImageIsoPullbackAb (D.map a)).hom.app
              ((etaleAbelianInverseImage.{u, u + 1} (D.map b)).obj (F.obj k)) := by
    rw [hco]
    simp
  rw [systemTransitionMap_eq F a, systemTransitionMap_eq F b, systemTransitionMap_eq F (a ≫ b),
    ← F.map_comp a b, hT, (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map_comp]
  simp only [Category.assoc]
  rw [← (inverseImageIsoPullbackAb (D.map a)).hom.naturality_assoc
      ((inverseImageIsoPullbackAb (D.map b)).inv.app (F.obj k)),
    ← (systemPullback D AddCommGrpCat.{u + 1} a).map_comp_assoc, Iso.hom_inv_id_app,
    (systemPullback D AddCommGrpCat.{u + 1} a).map_id, Category.id_comp,
    ← (inverseImageIsoPullbackAb (D.map a)).hom.naturality_assoc (F.map b),
    Iso.hom_inv_id_app_assoc]

/-! ### The two cocone laws, and the presented system -/

variable [∀ i : Iᵒᵖ, HasExt.{u + 1} (Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})]

/-- **The cocycle law on cohomology**: the maps of the cohomology diagram of a system compose.
-/
theorem etaleCohomologyTransition_comp (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j k : Iᵒᵖ} (b : i ⟶ j) (a : j ⟶ k) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (F.obj k) p) :
    etaleCohomologyTransition F b p (etaleCohomologyTransition F a p x) =
      etaleCohomologyTransition F (b ≫ a) p x :=
  etaleCohomologyMapTo_comp (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a)
    (systemTransitionMap F a) (systemTransitionMap F b) (systemTransitionMap F (b ≫ a))
    (systemTransitionMap_comp F b a) p x

/-- **The cocone law**: the leg at a level factors every earlier leg through the diagram map. -/
theorem etaleCohomologyMapTo_transition {F : EtaleSheafSystem D AddCommGrpCat.{u + 1}}
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢}
    (h : IsColimitPresentation F 𝒢 ι) {i j : Iᵒᵖ} (a : i ⟶ j) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} (F.obj j) p) :
    etaleCohomologyMapTo (conePi c i) (ι i) p (etaleCohomologyTransition F a p x) =
      etaleCohomologyMapTo (conePi c j) (ι j) p x :=
  etaleCohomologyMapTo_comp (conePi c i) (D.map a) (conePi c j) (conePi_comp c a).symm
    (systemTransitionMap F a) (ι i) (ι j) (h.compatible a) p x

/-- **Every system with a colimit presentation is a presented system.** -/
def presentedSystemOfIsColimitPresentation (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢)
    (h : IsColimitPresentation F 𝒢 ι) :
    PresentedSystem (c := c) IsColimitPresentation where
  sys := F
  sheaf := 𝒢
  ι := ι
  pres := h
  transition_comp b a p x := etaleCohomologyTransition_comp F b a p x
  leg_transition a p x := etaleCohomologyMapTo_transition h a p x

end SmallEtaleLimitCohomology

end Stacks.EtaleCohomology

end
