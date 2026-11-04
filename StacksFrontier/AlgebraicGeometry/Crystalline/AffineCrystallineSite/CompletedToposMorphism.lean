module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksCore.CategoryTheory.Sites.Pretopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineCrystallineSite.FiniteLevelCofinality
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite.ProObject
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim

/-!
# The morphism of topoi from the affine crystalline site to its completion

The canonical functor from the little affine crystalline category `Cris(C/A)` to its completed
counterpart `Cris^∧(C/A)` sends a divided power thickening to itself, read as a complete one.
Both categories carry the chaotic topology, so their sheaves are presheaves; the functor is
both continuous and cocontinuous and therefore represents a morphism of topoi, whose direct
image is precomposition.

On abelian sheaves the same direct image is the right Kan extension along the functor, which is
the form in which its derived functors are computed; and on underlying sets it is the direct
image of the morphism of topoi. A completed thickening is approximated by the system of its
finite-level quotients, and the sections of an abelian presheaf on that system form an inverse
system of abelian groups.

## Main definitions

* `Crystalline.completedCrystallineToposMorphism` — the resulting morphism of topoi.
* `Crystalline.abelianSheafPushforward`, `Crystalline.setSheafPushforward` — the
  site-theoretic direct images on abelian and on set-valued sheaves.
* `Crystalline.abelianDirectImage` — the right Kan extension along
  `crystallineToCompleted`.
* `Crystalline.finiteLevelSections` — the inverse system of sections on the finite-level
  quotients of a completed thickening.
* `Crystalline.abelianSheafPushforwardIsoDirectImage` — the natural isomorphism of the
  abelian direct image with the right Kan extension.
* `Crystalline.abelianSheafPushforwardForgetIsoPushforward` — the natural isomorphism
  exhibiting the abelian direct image, on underlying sets, as the direct image of the
  morphism of topoi.
* `Crystalline.completedCrystallineToposMorphismPushforwardIso` — the
  direct image of the morphism of topoi read as the site-theoretic direct image, which it
  is by construction.

## Implementation notes

Sheaves for the chaotic topology are presheaves, and the comparisons are stated on the actual
sheaf topoi. The abelian direct image is naturally the right Kan extension along the canonical
inclusion after passing through the chaotic-sheaf equivalences, and its underlying set-valued
functor is naturally the direct image of the geometric morphism. The finite-level system may
begin at any sufficiently large power of the fixed prime; its kernel specification identifies
each term with the corresponding quotient.

The canonical functor `Crystalline.crystallineToCompleted` is defined, written out, in
`AffineCrystallineSite.FiniteLevelCofinality`, together with the cofinality of the finite-level
approximation of a completed thickening — the initiality of
`Crystalline.finiteLevelStructuredArrow`, which is what makes the finite-level diagram compute
the right Kan extension.

## References

* [Stacks Project, Tag 07JL](https://stacks.math.columbia.edu/tag/07JL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Crystalline


/-- On chaotic sites every functor is cocontinuous. -/
public instance crystallineToCompleted_op_isCocontinuous
    (S : AffineCrystallineSituation.{u, v}) :
    (crystallineToCompleted S).op.IsCocontinuous
      (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ)
      (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ) where
  cover_lift := by
    intro U R hR
    rw [GrothendieckTopology.bot_covering] at hR ⊢
    subst R
    exact Sieve.functorPullback_top _ _

/-- Precomposition preserves sheaves for the chaotic topology. -/
public instance crystallineToCompleted_op_isContinuous
    (S : AffineCrystallineSituation.{u, v}) :
    (crystallineToCompleted S).op.IsContinuous
      (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ)
      (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ) where
  op_comp_isSheaf_of_types _ := Presieve.isSheaf_bot

/-- The site-theoretic pushforward of abelian sheaves for the functor defining
the completed crystalline morphism of topoi. -/
public def abelianSheafPushforward
    (S : AffineCrystallineSituation.{u, v}) :
    Sheaf (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ)
        Ab.{max u v (w + 1)} ⥤
      Sheaf (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ)
        Ab.{max u v (w + 1)} :=
  (crystallineToCompleted S).op.sheafPushforwardCocontinuous
    Ab.{max u v (w + 1)} ⊥ ⊥

/-- The site-theoretic pushforward of abelian sheaves is additive, being a right adjoint. -/
public instance abelianSheafPushforward_additive
    (S : AffineCrystallineSituation.{u, v}) :
    (abelianSheafPushforward.{u, v, w} S).Additive := by
  have : (abelianSheafPushforward.{u, v, w} S).IsRightAdjoint :=
    ⟨⟨_, ⟨(crystallineToCompleted S).op.sheafAdjunctionCocontinuous
      Ab.{max u v (w + 1)} ⊥ ⊥⟩⟩⟩
  apply Functor.additive_of_preserves_binary_products

/-- The site-theoretic pushforward of set-valued sheaves. -/
public def setSheafPushforward
    (S : AffineCrystallineSituation.{u, v}) :
    Sheaf (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ)
        (Type (max u v (w + 1))) ⥤
      Sheaf (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ)
        (Type (max u v (w + 1))) :=
  (crystallineToCompleted S).op.sheafPushforwardCocontinuous
    (Type (max u v (w + 1))) ⊥ ⊥

/-- Chaotic abelian sheaves, expressed as functors on thickenings. -/
public def abelianSheafEquivalence
    (S : AffineCrystallineSituation.{u, v}) :
    Sheaf (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ)
        Ab.{max u v (w + 1)} ≌
      (CrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)}) :=
  (sheafBotEquivalence (C := (CrystallineThickening.{u, v, w} S)ᵒᵖ)
    (A := Ab.{max u v (w + 1)})).trans
      (Equivalence.congrLeft (opOpEquivalence (CrystallineThickening.{u, v, w} S)))

/-- Chaotic abelian sheaves on completed thickenings, expressed as functors. -/
public def completedAbelianSheafEquivalence
    (S : AffineCrystallineSituation.{u, v}) :
    Sheaf (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ)
        Ab.{max u v (w + 1)} ≌
      (CompletedCrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)}) :=
  (sheafBotEquivalence (C := (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ)
    (A := Ab.{max u v (w + 1)})).trans
      (Equivalence.congrLeft (opOpEquivalence (CompletedCrystallineThickening.{u, v, w} S)))

/-- The inverse system of sections of an abelian presheaf on the ordinary
crystalline category, evaluated on the finite-level quotients of `X`. -/
public def finiteLevelSections {S : AffineCrystallineSituation.{u, v}}
    {X : CompletedCrystallineThickening.{u, v, w} S}
    (T : FiniteLevelSystem X)
    (F : CrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)}) :
    Rlim.InvSystemAb.{max u v (w + 1)} where
  obj e := F.obj (T.term e.unop)
  map {e e'} f := F.map (T.transition (leOfHom f.unop))
  map_id e := by
    change F.map (T.transition (le_refl e.unop)) = 𝟙 (F.obj (T.term e.unop))
    rw [T.transition_id, F.map_id]
  map_comp f g := by
    simp only [← F.map_comp]
    congr 1
    exact (T.transition_comp _ _).symm

/-- The morphism of topoi induced by the canonical functor from crystalline
thickenings to completed crystalline thickenings. -/
@[stacks 07JL "the morphism of topoi"]
public def completedCrystallineToposMorphism
    (S : AffineCrystallineSituation.{u, v}) :
    MorphismOfTopoi
      (Sheaf (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ)
        (Type (max u v (w + 1))))
      (Sheaf (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ)
        (Type (max u v (w + 1)))) where
  pushforward := (crystallineToCompleted S).op.sheafPushforwardCocontinuous _ _ _
  inverseImage := (crystallineToCompleted S).op.sheafPushforwardContinuous _ _ _
  adj := (crystallineToCompleted S).op.sheafAdjunctionCocontinuous _ _ _
  preservesFiniteLimits := by infer_instance

/-- The set-valued direct image of the geometric morphism is the site-theoretic
pushforward along the crystalline inclusion.

The identification is `Iso.refl`: `completedCrystallineToposMorphism` is built from the
adjunction `Functor.sheafAdjunctionCocontinuous`, whose right adjoint is by definition
`setSheafPushforward`, so the two functors are the same functor and this isomorphism
states nothing beyond that definitional choice. It is recorded for consumers that need
to rewrite between the two spellings. The mathematical content of the identification is
carried by the construction of `completedCrystallineToposMorphism` itself, which exhibits
the canonical functor as a morphism of topoi. -/
public def completedCrystallineToposMorphismPushforwardIso
    (S : AffineCrystallineSituation.{u, v}) :
    (completedCrystallineToposMorphism S).pushforward ≅ setSheafPushforward S :=
  Iso.refl _

/-- The direct image on abelian sheaves, identified with abelian presheaves
for the chaotic topology. -/
public def abelianDirectImage (S : AffineCrystallineSituation.{u, v}) :
    (CrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)}) ⥤
      (CompletedCrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)}) :=
  (crystallineToCompleted S).ran

/-- The natural isomorphism identifying the abelian-sheaf pushforward induced by the
crystalline site functor with the right Kan extension used to compute its derived
functors. It comes from the uniqueness of right adjoints, and is an isomorphism of
functors, not merely an objectwise comparison. -/
@[stacks 07JL "identification of the abelian direct image"]
public noncomputable def abelianSheafPushforwardIsoDirectImage
    (S : AffineCrystallineSituation.{u, v}) :
    abelianSheafPushforward S ⋙
        (completedAbelianSheafEquivalence.{u, v, w} S).functor ≅
      (abelianSheafEquivalence.{u, v, w} S).functor ⋙ abelianDirectImage S := by
  let i := crystallineToCompleted S
  let eC := abelianSheafEquivalence.{u, v, w} S
  let eD := completedAbelianSheafEquivalence.{u, v, w} S
  let q := (eD.inverse ⋙
    (i.op.sheafPushforwardContinuous Ab.{max u v (w + 1)} ⊥ ⊥)) ⋙ eC.functor
  let p := (Functor.whiskeringLeft
    (CrystallineThickening.{u, v, w} S) (CompletedCrystallineThickening.{u, v, w} S)
    Ab.{max u v (w + 1)}).obj i
  have hq : q ≅ p := by
    refine NatIso.ofComponents (fun F => ?_) ?_
    · dsimp [q, p, eC, eD, abelianSheafEquivalence,
        completedAbelianSheafEquivalence, Equivalence.congrLeft,
        Functor.sheafPushforwardContinuous, sheafBotEquivalence]
      exact Iso.refl _
    · intro F₁ F₂ η
      ext X
      simp [q, p, eC, eD, abelianSheafEquivalence,
        completedAbelianSheafEquivalence, Equivalence.congrLeft,
        Functor.sheafPushforwardContinuous, sheafBotEquivalence,
        Functor.comp_obj, Functor.comp_map, opOp, unopUnop]
      rfl
  let adj₁ := (eD.symm.toAdjunction.comp
    (i.op.sheafAdjunctionCocontinuous Ab.{max u v (w + 1)} ⊥ ⊥)).comp eC.toAdjunction
  exact (eC.funInvIdAssoc (abelianSheafPushforward S ⋙ eD.functor)).symm ≪≫
    Functor.isoWhiskerLeft eC.functor
      (adj₁.rightAdjointUniq ((i.ranAdjunction (H := Ab.{max u v (w + 1)})).ofNatIsoLeft hq.symm))

/-- The natural isomorphism exhibiting the abelian-sheaf direct image, on underlying
sets, as the direct image of the same morphism of topoi. It comes from the uniqueness
of right adjoints, and is natural in the sheaf. -/
@[stacks 07JL "compatibility with the geometric morphism"]
public noncomputable def abelianSheafPushforwardForgetIsoPushforward
    (S : AffineCrystallineSituation.{u, v}) :
    abelianSheafPushforward S ⋙
        sheafForget
          (⊥ : GrothendieckTopology (CompletedCrystallineThickening.{u, v, w} S)ᵒᵖ) ≅
      sheafForget
          (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ) ⋙
        (completedCrystallineToposMorphism S).pushforward := by
  let C := CrystallineThickening.{u, v, w} S
  let D := CompletedCrystallineThickening.{u, v, w} S
  let i := crystallineToCompleted S
  let A := Ab.{max u v (w + 1)}
  let qC := sheafBotEquivalence (C := Cᵒᵖ) (A := Type (max u v (w + 1)))
  let qD := sheafBotEquivalence (C := Dᵒᵖ) (A := Type (max u v (w + 1)))
  let aC := sheafBotEquivalence (C := Cᵒᵖ) (A := A)
  let aD := sheafBotEquivalence (C := Dᵒᵖ) (A := A)
  let freeC := (Functor.whiskeringRight Cᵒᵖᵒᵖ (Type (max u v (w + 1))) A).obj
    AddCommGrpCat.free
  let freeD := (Functor.whiskeringRight Dᵒᵖᵒᵖ (Type (max u v (w + 1))) A).obj
    AddCommGrpCat.free
  let forgetC := (Functor.whiskeringRight Cᵒᵖᵒᵖ A
    (Type (max u v (w + 1)))).obj (forget A)
  let forgetD := (Functor.whiskeringRight Dᵒᵖᵒᵖ A
    (Type (max u v (w + 1)))).obj (forget A)
  let FC := qC.functor ⋙ freeC ⋙ aC.inverse
  let FD := qD.functor ⋙ freeD ⋙ aD.inverse
  let UC := aC.functor ⋙ forgetC ⋙ qC.inverse
  let UD := aD.functor ⋙ forgetD ⋙ qD.inverse
  let qSet := i.op.sheafPushforwardContinuous
    (Type (max u v (w + 1))) ⊥ ⊥
  let qAb := i.op.sheafPushforwardContinuous A ⊥ ⊥
  have hUC : UC ≅ sheafForget (⊥ : GrothendieckTopology Cᵒᵖ) := by
    refine NatIso.ofComponents (fun F => ?_) ?_
    · dsimp [UC, aC, qC, forgetC, sheafBotEquivalence]
      rfl
    · intro F G η
      ext X x
      rfl
  have hUD : UD ≅ sheafForget (⊥ : GrothendieckTopology Dᵒᵖ) := by
    refine NatIso.ofComponents (fun F => ?_) ?_
    · dsimp [UD, aD, qD, forgetD, sheafBotEquivalence]
      rfl
    · intro F G η
      ext X x
      rfl
  have hfree : qSet ⋙ FC ≅ FD ⋙ qAb := by
    refine NatIso.ofComponents (fun F => ?_) ?_
    · dsimp [FC, FD, qSet, qAb, qC, qD, aC, aD,
        freeC, freeD, sheafBotEquivalence, Functor.sheafPushforwardContinuous]
      exact aC.inverse.mapIso (Functor.associator i.op.op F.obj AddCommGrpCat.free)
    · intro F G η
      ext X x
      simp [FC, FD, qSet, qAb, qC, qD, aC, aD,
        freeC, freeD, sheafBotEquivalence, Functor.sheafPushforwardContinuous]
      rfl
  let adjFreeC := (qC.toAdjunction.comp
      (AddCommGrpCat.adj.whiskerRight Cᵒᵖᵒᵖ)).comp aC.symm.toAdjunction
  let adjFreeD := (qD.toAdjunction.comp
      (AddCommGrpCat.adj.whiskerRight Dᵒᵖᵒᵖ)).comp aD.symm.toAdjunction
  let adjSiteAb := i.op.sheafAdjunctionCocontinuous A ⊥ ⊥
  let adjSiteSet := i.op.sheafAdjunctionCocontinuous
    (Type (max u v (w + 1))) ⊥ ⊥
  let adj₁ := (adjFreeD.ofNatIsoRight hUD).comp adjSiteAb
  let adj₂ := adjSiteSet.comp (adjFreeC.ofNatIsoRight hUC)
  exact (adj₂.rightAdjointUniq (adj₁.ofNatIsoLeft hfree.symm)).symm

/-- **The direct image of [Stacks, Tag 07JL], computed.** For an abelian presheaf `F` on the
ordinary affine crystalline category and a finite-level system `T` for a completed thickening
`X`, the value at `X` of the direct image of `F` is the inverse limit of the sections of `F` on
the finite-level quotients of `X`:
`g_*(F)(X) ≅ lim_e F(X/(p)^(N + e))`.

The direct image is the right Kan extension along `crystallineToCompleted`, whose value at `X`
is the limit over the structured-arrow category, and the finite-level diagram is initial there
by `Crystalline.finiteLevel_initial`. -/
@[stacks 07JL "the direct image computed as the limit over the finite levels"]
public noncomputable def abelianDirectImageObjObjIsoLimitFiniteLevelSections
    {S : AffineCrystallineSituation.{u, v}}
    (F : CrystallineThickening.{u, v, w} S ⥤ Ab.{max u v (w + 1)})
    {X : CompletedCrystallineThickening.{u, v, w} S} (T : FiniteLevelSystem X) :
    ((abelianDirectImage S).obj F).obj X ≅ limit (finiteLevelSections T F) := by
  let L := crystallineToCompleted.{u, v, w} S
  have : (finiteLevelStructuredArrow T).Initial := finiteLevel_initial T
  exact Functor.ranObjObjIsoLimit L F X ≪≫
    (Functor.Initial.limitIso (finiteLevelStructuredArrow T) (StructuredArrow.proj X L ⋙ F)).symm ≪≫
      HasLimit.isoOfNatIso (NatIso.ofComponents (fun _ => Iso.refl _)
        fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The sections of the direct image of [Stacks, Tag 07JL].** The value at a completed
thickening `X` of the direct image of an abelian sheaf `F` on the ordinary affine crystalline
site is the inverse limit of the sections of `F` on the finite-level quotients of `X`.

This is `Crystalline.abelianDirectImageObjObjIsoLimitFiniteLevelSections` transported along
`Crystalline.abelianSheafPushforwardIsoDirectImage`, so that it speaks about the
site-theoretic pushforward rather than the right Kan extension. -/
@[stacks 07JL "the sections of the direct image as the limit over the finite levels"]
public noncomputable def abelianSheafPushforwardObjObjIsoLimitFiniteLevelSections
    (S : AffineCrystallineSituation.{u, v})
    (F : Sheaf (⊥ : GrothendieckTopology (CrystallineThickening.{u, v, w} S)ᵒᵖ)
      Ab.{max u v (w + 1)})
    {X : CompletedCrystallineThickening.{u, v, w} S} (T : FiniteLevelSystem X) :
    ((completedAbelianSheafEquivalence.{u, v, w} S).functor.obj
        ((abelianSheafPushforward S).obj F)).obj X ≅
      limit (finiteLevelSections T
        ((abelianSheafEquivalence.{u, v, w} S).functor.obj F)) :=
  ((abelianSheafPushforwardIsoDirectImage.{u, v, w} S).app F).app X ≪≫
    abelianDirectImageObjObjIsoLimitFiniteLevelSections _ T


end Crystalline

end
