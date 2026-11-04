module
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pullback of sheaves commutes with postcomposition by a functor preserving sheafification

Let `u : C ⥤ D` be a continuous functor of sites, giving a morphism of sites `f : D → C` whose
pushforward is `f_* = u^s` and whose inverse image is `f^{-1} = u_s`; on presheaves the
corresponding pair is `u_p ⊣ u^p`, with `u^p` restriction along `u.op` and `u_p` the left Kan
extension along `u.op`. Let `s : A ⥤ B` be a functor which commutes with filtered colimits, along
which an `A`-valued presheaf is a sheaf as soon as its image is, and which commutes with
sheafification.

The pushforward is restriction along `u.op` at both levels, so it commutes with `s` on the nose.
The pullback does not, in general: `u_p F(V)` is a colimit over the comma category `I^u_V` of
pairs `(U, V ⟶ u U)`, and `s` is assumed to commute only with *filtered* colimits. What makes the
pullback of `A`-valued sheaves exist and be compatible with `s` is that every `I^u_V` is
cofiltered — which is exactly `CategoryTheory.RepresentablyFlat u`, and which holds under the
hypotheses of Stacks 00X6 (`C` has a final object and fibre products, both preserved by `u`).
Then `A` and `B` have the colimits defining `u_p`, `s` preserves them, and sheafification is
compatible with `s` as well, so `f^{-1} = (u_p -)^#` commutes with `s`.

Stacks 00YT is the case `B = Type u` with `s` the underlying-set functor of a type of algebraic
structure (Stacks 007L): a functor `s : A ⥤ Type u` which is faithful, reflects isomorphisms, and
commutes with limits and with filtered colimits. In that case the statement below reads: the
pullback of sheaves of algebraic structures commutes with taking the underlying sheaf of sets.

## Main results

* `CategoryTheory.Functor.isIso_mateEquiv_sheafAdjunctionContinuous`: the canonical comparison
  map `f^{-1}(s ∘ F) ⟶ s ∘ (f^{-1} F)` — the mate, under the adjunction `f^{-1} ⊣ f_*`, of the
  identity square on the pushforwards — is an isomorphism.

## Implementation notes

* The statement is for an arbitrary `s : A ⥤ B`, not for the underlying-set functor of the
  source's type of algebraic structure, because nothing in it or in the source's proof mentions
  the target of `s`: that proof factors through the presheaf level (a left Kan extension along
  `u.op`, computed by filtered colimits, which `s` preserves) and the compatibility of `s` with
  sheafification, and neither knows what `s` lands in. Taking `B := Type u` recovers Stacks 00YT
  verbatim, the two hypotheses on `B` being then found by instance search
  (`HasWeakSheafify K (Type u)`, and `HasFilteredColimitsOfSize.{u, u} (Type u)` from
  `hasFilteredColimitsOfSize_of_hasColimitsOfSize`). This is the shape of Mathlib's
  `CategoryTheory.constantCommuteCompose`, the commutation of the *other* left adjoint built as
  `(- ⋙ sheafify)` with `sheafCompose`, which Mathlib states for an arbitrary `U : D ⥤ B` under
  precisely `HasWeakSheafify`, `PreservesSheafification` and `HasSheafCompose`; the presheaf-level
  companion `Functor.lanCompIsoOfPreserves` is target-agnostic as well.
* The source asserts the compatibility at both levels in one sentence, and the two levels are
  separate statements, because the presheaf level mentions neither topology: it is the assertion
  that for a functor `L : C ⥤ D` and a functor `s : A ⥤ B` preserving left Kan extensions along
  `L`, the functor `L.lan` commutes with postcomposition by `s`. In that generality it is
  `Functor.lanCompIsoOfPreserves`, so the presheaf level of the source's lemma is already
  available, with `L = u.op`: the hypotheses `RepresentablyFlat u`, `HasFilteredColimitsOfSize A`
  and `PreservesFilteredColimitsOfSize s` supply `[∀ F, u.op.HasLeftKanExtension F]` and
  `[s.PreservesLeftKanExtensions u.op]` by instance search, through
  `preservesPointwiseLeftKanExtensionAtOfPreservesColimit` and
  `preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise`. Restating it here with the sites in
  the binders would be the same theorem with a strictly stronger and less usable hypothesis set,
  and conjoining it with the sheaf level would make a topology-free fact reachable only after
  choosing topologies on `C` and `D`, proving `u` continuous and sheafifying `A`-valued presheaves
  compatibly with `s`. So the declaration below is the sheaf level, which is the level with
  nothing upstream: no result relates `sheafCompose` to `sheafPullback`.
* The hypothesis is `RepresentablyFlat u` rather than the literal hypotheses of Stacks 00X6.
  Those hypotheses enter the source's proof only through "all the colimits used to define `u_p`
  are filtered", and `RepresentablyFlat u` *is* that statement (`RepresentablyFlat.cofiltered`
  says each `StructuredArrow V u = I^u_V` is cofiltered, whence each
  `CostructuredArrow u.op V ≌ (I^u_V)ᵒᵖ` is filtered). Stacks 00X6's hypotheses give it by
  `Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks`,
  `Limits.preservesFiniteLimits_of_preservesTerminal_and_pullbacks` and
  `flat_of_preservesFiniteLimits`; they are strictly stronger, so the statement here is the
  general one. Continuity of `u` is kept, being what `f_*` and `f^{-1}` are defined from.
* Of the four axioms for a type of algebraic structure, only "`A` has filtered colimits and `s`
  commutes with them" is assumed, as `HasFilteredColimitsOfSize.{u, u} A` and
  `PreservesFilteredColimitsOfSize.{u, u} s`. Faithfulness of `s` and reflection of isomorphisms
  are not used and are therefore dropped. The role of the other axiom, "`A` has limits and `s`
  commutes with them", is played by the three hypotheses it is used for in the unnumbered
  discussion preceding the source's statement: `HasWeakSheafify K A` (sheafification of
  `A`-valued presheaves exists, the source's `(β)`, `(ε)`), `J.HasSheafCompose s` and
  `K.HasSheafCompose s` (an `A`-valued presheaf is a sheaf as soon as its image under `s` is, the
  source's `(α)`), and `K.PreservesSheafification s` (sheafification commutes with `s`, the
  source's `(β)`, `(γ)`). Assuming those directly keeps the statement about Stacks 00YT rather
  than about the discussion it builds on.
* "Commutes with taking the underlying sheaf of sets" is stated by pinning the canonical
  comparison map and asserting it invertible, not by asserting that some isomorphism exists.
  The pushforward square commutes strictly — both `f_* ⋙ (s ∘ -)` and `(s ∘ -) ⋙ f_*` send `P`
  to `u.op ⋙ P ⋙ s` — so the identity is a `TwoSquare` for it, and its mate under `mateEquiv`
  is the canonical map from the pullback of the image to the image of the pullback. Invertibility
  of that mate is the whole content, and it simultaneously records the pushforward compatibility,
  which is the square being mated.

## References

* [Stacks 00YT](https://stacks.math.columbia.edu/tag/00YT), in the section "Sheaves of algebraic
  structures", together with the unnumbered discussion `(α)`–`(ζ)` preceding it, Stacks 00YS (the
  pushforward `u^p F(U) = F(u U)`), Stacks 00X6 (the criterion making `u` a morphism of sites) and
  Stacks 00VE (the presheaf adjunction `u_p ⊣ u^p`). Types of algebraic structure are Stacks 007L.
-/


namespace CategoryTheory.Functor

section

universe w w' v v' u w'' v'' u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory Limits
open CategoryTheory Limits _root_.CategoryTheory.Functor

namespace Stacks.AlgebraicStructure.SheafPullback

@[expose] public section

section Mates

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [Category.{v₁} C₁]
  [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄] {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
  {L₁ L₁' : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ L₂' : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}

/-- A 2-cell `α : G ⋙ L₂ ⟶ L₁ ⋙ H` which satisfies the compatibility with the units of `L₁ ⊣ R₁`
and `L₂ ⊣ R₂` that `CategoryTheory.unit_mateEquiv_symm` records for the mate of
`β : R₁ ⋙ G ⟶ H ⋙ R₂` *is* that mate: the compatibility determines `α` through the bijection
`CategoryTheory.Adjunction.homEquiv`. -/
private lemma mateEquiv_symm_eq_of_unit (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (β : TwoSquare R₁ H G R₂)
    (α : TwoSquare G L₁ L₂ H)
    (h :
      ∀ X : C₁,
        G.map (adj₁.unit.app X) ≫ β.natTrans.app (L₁.obj X) =
          adj₂.unit.app (G.obj X) ≫ R₂.map (α.natTrans.app X)) :
    (mateEquiv adj₁ adj₂).symm β = α := by
  ext X
  exact (adj₂.homEquiv _ _).injective ((unit_mateEquiv_symm adj₁ adj₂ β X).symm.trans (h X))

/-- The mate of `β : R₁ ⋙ G ⟶ H ⋙ R₂` does not depend on the chosen left adjoints, except through
the isomorphisms `CategoryTheory.Adjunction.leftAdjointUniq` comparing them: the mate for `adj₁`
and `adj₂` is the mate for `adj₁'` and `adj₂'`, whiskered by those isomorphisms. -/
private lemma mateEquiv_symm_eq_whisker (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₂' : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂) :
    (mateEquiv adj₁ adj₂).symm β =
      TwoSquare.whiskerRight
        (TwoSquare.whiskerLeft ((mateEquiv adj₁' adj₂').symm β)
          (Adjunction.leftAdjointUniq adj₁' adj₁).hom)
        (Adjunction.leftAdjointUniq adj₂ adj₂').hom := by
  refine mateEquiv_symm_eq_of_unit adj₁ adj₂ β _ fun X => ?_
  have hβ :
    G.map (R₁.map ((Adjunction.leftAdjointUniq adj₁' adj₁).hom.app X)) ≫
        β.natTrans.app (L₁.obj X) =
      β.natTrans.app (L₁'.obj X) ≫
        R₂.map (H.map ((Adjunction.leftAdjointUniq adj₁' adj₁).hom.app X)) :=
    β.natTrans.naturality _
  calc
    G.map (adj₁.unit.app X) ≫ β.natTrans.app (L₁.obj X) =
        G.map (adj₁'.unit.app X ≫ R₁.map ((Adjunction.leftAdjointUniq adj₁' adj₁).hom.app X)) ≫
          β.natTrans.app (L₁.obj X) :=
      by rw [Adjunction.unit_leftAdjointUniq_hom_app]
    _ =
        G.map (adj₁'.unit.app X) ≫
          G.map (R₁.map ((Adjunction.leftAdjointUniq adj₁' adj₁).hom.app X)) ≫
          β.natTrans.app (L₁.obj X) :=
      by rw [G.map_comp, Category.assoc]
    _ =
        G.map (adj₁'.unit.app X) ≫
          β.natTrans.app (L₁'.obj X) ≫
          R₂.map (H.map ((Adjunction.leftAdjointUniq adj₁' adj₁).hom.app X)) :=
      by rw [hβ]
    _ =
        (adj₂'.unit.app (G.obj X) ≫ R₂.map (((mateEquiv adj₁' adj₂').symm β).natTrans.app X)) ≫
          R₂.map (H.map ((Adjunction.leftAdjointUniq adj₁' adj₁).hom.app X)) :=
      by rw [Category.assoc, reassoc_of% (unit_mateEquiv_symm adj₁' adj₂' β X)]
    _ =
        adj₂.unit.app (G.obj X) ≫
          R₂.map
            ((Adjunction.leftAdjointUniq adj₂ adj₂').hom.app (G.obj X) ≫
              ((mateEquiv adj₁' adj₂').symm β).natTrans.app X ≫
              H.map ((Adjunction.leftAdjointUniq adj₁' adj₁).hom.app X)) :=
      by
      rw [R₂.map_comp, R₂.map_comp, ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app, ←
        Category.assoc]

/-- Invertibility of a mate does not depend on the choice of the two left adjoints. -/
private lemma isIso_mateEquiv_symm_natTrans (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₂' : L₂' ⊣ R₂) (β : TwoSquare R₁ H G R₂)
    (h : IsIso ((mateEquiv adj₁' adj₂').symm β).natTrans) :
    IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  rw [mateEquiv_symm_eq_whisker adj₁ adj₁' adj₂ adj₂' β]
  change
    IsIso
      (whiskerLeft G (Adjunction.leftAdjointUniq adj₂ adj₂').hom ≫
        ((mateEquiv adj₁' adj₂').symm β).natTrans ≫
        whiskerRight (Adjunction.leftAdjointUniq adj₁' adj₁).hom H)
  infer_instance

end Mates

section ConstructedUnit

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (u : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K] {E : Type w''}
  [Category.{v''} E] [∀ P : Cᵒᵖ ⥤ E, u.op.HasLeftKanExtension P] [HasWeakSheafify K E]

/-- The unit of the constructed pullback-pushforward adjunction, read on underlying presheaves and
evaluated at an object: it is the left Kan extension unit followed by the sheafification unit. -/
private lemma constructedUnit_val_app (F : Sheaf J E) (X : Cᵒᵖ) :
    ((sheafToPresheaf J E).map
            ((sheafPullbackConstruction.sheafAdjunctionContinuous u E J K).unit.app F)).app
        X =
      (u.op.lanUnit.app F.obj).app X ≫
        ((sheafificationAdjunction K E).unit.app (u.op.lan.obj F.obj)).app (u.op.obj X) := by
  have h :=
    Adjunction.map_restrictFullyFaithful_unit_app (L :=
      sheafPullbackConstruction.sheafPullback u E J K) (R := u.sheafPushforwardContinuous E J K)
      ((u.op.lanAdjunction E).comp (sheafificationAdjunction K E))
      (fullyFaithfulSheafToPresheaf J E) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  have h' :
    (sheafToPresheaf J E).map
        ((sheafPullbackConstruction.sheafAdjunctionContinuous u E J K).unit.app F) =
      _ :=
    h
  rw [h', Adjunction.comp_unit_app, Functor.lanAdjunction_unit]
  -- Both `Iso.refl` correction factors are identities and
  -- `((whiskeringLeft _ _ E).obj u.op).map α` evaluated at `X` is `α.app (u.op.obj X)`, all
  -- definitionally; only the two identities have to be cancelled.
  have hcomp : ∀ {P Q : E} (f : P ⟶ Q), f ≫ 𝟙 Q ≫ 𝟙 Q = f := fun f => by simp
  exact hcomp _

end ConstructedUnit

section Sites

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] (u : C ⥤ D)
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) [u.IsContinuous J K]
  [RepresentablyFlat u] {A : Type w} [Category.{v} A] {B : Type w'} [Category.{v'} B] (s : A ⥤ B)
  [HasFilteredColimitsOfSize.{u, u} A] [HasFilteredColimitsOfSize.{u, u} B]
  [PreservesFilteredColimitsOfSize.{u, u} s] [HasWeakSheafify K A] [HasWeakSheafify K B]
  [J.HasSheafCompose s] [K.HasSheafCompose s] [K.PreservesSheafification s]

/-- Postcomposition with `s` commutes with the *constructed* pullback of sheaves: on presheaves
this is `CategoryTheory.Functor.lanCompIsoOfPreserves`, and the sheafification step is
`CategoryTheory.sheafComposeNatIso`. -/
private noncomputable def middleIso :
    sheafCompose J s ⋙ sheafPullbackConstruction.sheafPullback u B J K ≅
      sheafPullbackConstruction.sheafPullback u A J K ⋙ sheafCompose K s :=
  isoWhiskerLeft (sheafToPresheaf J A)
    (isoWhiskerRight (s.lanCompIsoOfPreserves u.op).symm (presheafToSheaf K B) ≪≫
      isoWhiskerLeft u.op.lan
        (sheafComposeNatIso K s (sheafificationAdjunction K A) (sheafificationAdjunction K B)))

omit [u.IsContinuous J K] in
private lemma middleIso_hom_app_hom_app (F : Sheaf J A) (Y : Dᵒᵖ) :
    (((middleIso u J K s).hom.app F).hom).app Y =
      (((presheafToSheaf K B).map ((s.lanCompIsoOfPreserves u.op).inv.app F.obj)).hom).app Y ≫
        (((sheafComposeNatTrans K s (sheafificationAdjunction K A)
                    (sheafificationAdjunction K B)).app
                (u.op.lan.obj F.obj)).hom).app
          Y :=
  rfl

omit [K.PreservesSheafification s] in
/-- At the level of presheaves, the left Kan extension unit followed by the sheafification unit
is compatible with postcomposition by `s`. -/
private lemma key (P : Cᵒᵖ ⥤ A) (X : Cᵒᵖ) :
    (u.op.lanUnit.app (P ⋙ s)).app X ≫
        (((sheafificationAdjunction K B).unit.app (u.op.lan.obj (P ⋙ s))).app (u.op.obj X) ≫
          ((((presheafToSheaf K B).map ((s.lanCompIsoOfPreserves u.op).inv.app P)).hom).app
              (u.op.obj X) ≫
            (((sheafComposeNatTrans K s (sheafificationAdjunction K A)
                        (sheafificationAdjunction K B)).app
                    (u.op.lan.obj P)).hom).app
              (u.op.obj X))) =
      s.map
        ((u.op.lanUnit.app P).app X ≫
          ((sheafificationAdjunction K A).unit.app (u.op.lan.obj P)).app (u.op.obj X)) := by
  have h1 :
    (u.op.lanUnit.app (P ⋙ s)).app X ≫
        ((s.lanCompIsoOfPreserves u.op).inv.app P).app (u.op.obj X) =
      s.map ((u.op.lanUnit.app P).app X) :=
    leftKanExtensionCompIsoOfPreserves_inv_fac_app s P u.op X
  have h2 :
    ((sheafificationAdjunction K B).unit.app (u.op.lan.obj (P ⋙ s))).app (u.op.obj X) ≫
        (((presheafToSheaf K B).map ((s.lanCompIsoOfPreserves u.op).inv.app P)).hom).app
          (u.op.obj X) =
      ((s.lanCompIsoOfPreserves u.op).inv.app P).app (u.op.obj X) ≫
        ((sheafificationAdjunction K B).unit.app (u.op.lan.obj P ⋙ s)).app (u.op.obj X) :=
    NatTrans.congr_app
      (((sheafificationAdjunction K B).unit.naturality
          ((s.lanCompIsoOfPreserves u.op).inv.app P)).symm)
      (u.op.obj X)
  have h3 :
    ((sheafificationAdjunction K B).unit.app (u.op.lan.obj P ⋙ s)).app (u.op.obj X) ≫
        (((sheafComposeNatTrans K s (sheafificationAdjunction K A)
                    (sheafificationAdjunction K B)).app
                (u.op.lan.obj P)).hom).app
          (u.op.obj X) =
      s.map (((sheafificationAdjunction K A).unit.app (u.op.lan.obj P)).app (u.op.obj X)) :=
    NatTrans.congr_app
      (sheafComposeNatTrans_fac K s (sheafificationAdjunction K A) (sheafificationAdjunction K B)
        (u.op.lan.obj P))
      (u.op.obj X)
  rw [s.map_comp, ← h1, ← h3, reassoc_of% h2]
  exact (Category.assoc _ _ _).symm

/-- The unit compatibility of `middleIso`, at the level of the constructed pullback. -/
private lemma sheafCompose_map_unit_eq (F : Sheaf J A) :
    (sheafCompose J s).map
        ((sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app F) =
      (sheafPullbackConstruction.sheafAdjunctionContinuous u B J K).unit.app
          ((sheafCompose J s).obj F) ≫
        (u.sheafPushforwardContinuous B J K).map ((middleIso u J K s).hom.app F) := by
  apply Sheaf.hom_ext
  ext X
  change
    s.map
        (((sheafToPresheaf J A).map
              ((sheafPullbackConstruction.sheafAdjunctionContinuous u A J K).unit.app F)).app
          X) =
      ((sheafToPresheaf J B).map
              ((sheafPullbackConstruction.sheafAdjunctionContinuous u B J K).unit.app
                ((sheafCompose J s).obj F))).app
          X ≫
        (((middleIso u J K s).hom.app F).hom).app (u.op.obj X)
  rw [constructedUnit_val_app u J K F X,
    constructedUnit_val_app u J K ((sheafCompose J s).obj F) X, middleIso_hom_app_hom_app]
  exact (key u K s F.obj X).symm.trans (Category.assoc _ _ _).symm

/-- For the constructed pullback, the mate of the identity square on the pushforwards is
`middleIso`. -/
private lemma mateEquiv_symm_eq :
    (mateEquiv (sheafPullbackConstruction.sheafAdjunctionContinuous u A J K)
            (sheafPullbackConstruction.sheafAdjunctionContinuous u B J K)).symm
        (TwoSquare.mk (u.sheafPushforwardContinuous A J K) (sheafCompose K s) (sheafCompose J s)
          (u.sheafPushforwardContinuous B J K) (𝟙 _)) =
      TwoSquare.mk _ _ _ _ (middleIso u J K s).hom :=
  mateEquiv_symm_eq_of_unit _ _ _ _ fun F =>
    (Category.comp_id _).trans (sheafCompose_map_unit_eq u J K s F)

end Sites

end

end Stacks.AlgebraicStructure.SheafPullback

@[expose] public section

open Stacks.AlgebraicStructure.SheafPullback in
/-- Let `(C, J)` and `(D, K)` be sites, let `u : C ⥤ D` be continuous and representably flat —
the latter holds under the hypotheses of Stacks 00X6 — and let `s : A ⥤ B` be a functor such that
`A` and `B` have filtered colimits, `s` preserves them, `A`- and `B`-valued presheaves on `D` can
be sheafified, sheafification commutes with `s`, and an `A`-valued presheaf is a sheaf as soon as
its image under `s` is.

Then the pullback functor `f^{-1}` on `A`-valued sheaves commutes with postcomposition by `s`:
the mate, under the adjunction `f^{-1} ⊣ f_*`, of the identity square expressing that the
pushforward `f_* = u^s` is restriction along `u.op` on both sides, namely the canonical map
`f^{-1}(s ∘ F) ⟶ s ∘ (f^{-1} F)`, is an isomorphism.

For `B = Type u` and `s` the underlying-set functor of a type of algebraic structure, this says
that the pullback of sheaves of algebraic structures commutes with taking the underlying sheaf of
sets.

At the level of presheaves the corresponding assertion, that `u_p` commutes with postcomposition
by `s`, is `Functor.lanCompIsoOfPreserves` for `L = u.op`, which needs neither topology. -/
@[stacks 00YT "The sheaf level, for an arbitrary `s : A ⥤ B`: for a continuous, representably flat
  `u : C ⥤ D` and a functor `s` preserving filtered colimits and sheafification, the pullback
  `f^{-1}` of `A`-valued sheaves commutes with postcomposition by `s`, in that the canonical mate
  `f^{-1}(s ∘ F) ⟶ s ∘ (f^{-1} F)` of the pushforward square is an isomorphism. The tag is the
  case `B = Type u`, `s` the underlying-set functor of a type of algebraic structure. The presheaf
  level, `u_p (F ⋙ s) ≅ (u_p F) ⋙ s`, is `lanCompIsoOfPreserves` at `L = u.op`, which mentions no
  topology.",
  sga "4 III 1.7" "4) diagram commutes",
  sga "4 III 2.4" "underlying sheaf of sets",
  sga "4 IV 3.1.2" "u^* preserves structures"]
public theorem isIso_mateEquiv_sheafAdjunctionContinuous {C : Type u} [SmallCategory C]
    {D : Type u} [SmallCategory D] (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K] [RepresentablyFlat u] {A : Type w}
    [Category.{v} A] {B : Type w'} [Category.{v'} B] (s : A ⥤ B)
    [HasFilteredColimitsOfSize.{u, u} A] [HasFilteredColimitsOfSize.{u, u} B]
    [PreservesFilteredColimitsOfSize.{u, u} s] [HasWeakSheafify K A] [HasWeakSheafify K B]
    [J.HasSheafCompose s] [K.HasSheafCompose s] [K.PreservesSheafification s] :
    IsIso
      ((mateEquiv (u.sheafAdjunctionContinuous A J K) (u.sheafAdjunctionContinuous B J K)).symm
          (TwoSquare.mk (u.sheafPushforwardContinuous A J K) (sheafCompose K s) (sheafCompose J s)
            (u.sheafPushforwardContinuous B J K) (𝟙 _))).natTrans := by
  refine
    isIso_mateEquiv_symm_natTrans _ (sheafPullbackConstruction.sheafAdjunctionContinuous u A J K) _
      (sheafPullbackConstruction.sheafAdjunctionContinuous u B J K) _ ?_
  rw [mateEquiv_symm_eq u J K s]
  exact inferInstanceAs (IsIso (middleIso u J K s).hom)

end

end

end CategoryTheory.Functor

/-!
# Morphisms of topoi preserve algebraic structure

A *type of algebraic structure defined by finite projective limits* — SGA4's *espèce de structure
algébrique définie par limites projectives finies* — is given by a category `T`, the theory, and a
structure of that type in a category `E` is a functor `T ⥤ E` preserving finite limits, that is,
an object of `T ⥤ₗ E`; the underlying object of a structure is its value at the sort, a
distinguished object of `T`. Pointed sets, abelian groups, groups, monoids, rings, modules over a
fixed ring `R` and Lie algebras over a fixed field `k` are all of this form: each of those
categories `A` is locally finitely presentable, so by Gabriel–Ulmer duality one may take for `T`
the opposite of (a skeleton of) its full subcategory of finitely presented objects, for the sort
the free object on one generator, and then `T ⥤ₗ Set ≌ A`, while `T ⥤ₗ E` is the category of
`A`-structures internal to `E` — for `E = Sh(C)` the category of sheaves on a site `C` with values
in `A`. The fixed `R`, resp. `k`, enters through `T` and nowhere else.

Let `f = (f⁻¹, f_*)` be a morphism of topoi `Sh(D) → Sh(C)`, that is, an adjoint pair
`f⁻¹ ⊣ f_*` with `f⁻¹ : Sh(C) ⥤ Sh(D)` left exact. Postcomposing a structure with `f⁻¹`, resp.
with `f_*`, is again a structure — a composite of finite-limit-preserving functors preserves finite
limits, and `f_*`, being a right adjoint, is left exact for free — and the two functors so obtained
on structures are again an adjoint pair. This is the statement below, for an arbitrary theory `T`
and an arbitrary adjunction between left exact functors: neither sheaves nor finite limits in `T`,
`E`, `E'` play any role in it.

Compatibility with taking the underlying sheaf of sets is not a separate assertion here: the two
functors are pinned as postcomposition, so a structure `M` is sent to `M ⋙ f⁻¹`, resp. `M ⋙ f_*`
(`CategoryTheory.LeftExactFunctor.whiskeringRight_obj_obj_obj`), and evaluating at the sort
`t : T` gives `f⁻¹(M t)`, resp. `f_*(M t)`, on the nose.

## Main results

* `CategoryTheory.Adjunction.leftExactWhiskerRight`: Stacks 00YV — an adjunction between left exact
  functors `E ⥤ₗ E'`, `E' ⥤ₗ E` induces, by postcomposition, an adjunction between the categories
  `T ⥤ₗ E` and `T ⥤ₗ E'` of structures of an arbitrary theory `T`.

## Implementation notes

* The source states the conclusion for the seven types of algebraic structure listed in Stacks 00YV
  rather than for a general espèce, saying that formalizing the construction is avoided by listing
  the cases; the statement here is the construction, so it is the seven cases at once, each
  obtained by instantiating `T` at the theory of that structure as above. The bridges
  `T ⥤ₗ E ≌ Grp E` and the like — Gabriel–Ulmer duality for the seven listed categories — are not
  part of this statement; for monoid, group and commutative group objects in a cartesian monoidal
  category the conclusion in the internal-object presentation is already Mathlib's
  `CategoryTheory.Adjunction.mapMon`, `.mapGrp` and `.mapCommGrp`, for a finite-product-preserving
  (there: braided) `f⁻¹`, and those are the same statement read through the bridge.
* A morphism of topoi is taken to be its adjoint pair with the left adjoint left exact, as
  elsewhere in this development (Stacks 00XO, 00XS): no `Topos` structure is used, and no site data
  is available to a bare morphism of topoi, which is exactly why the structures have to be
  described internally rather than as `A`-valued sheaves. Contrast Stacks 00YT, where a functor of
  sites is given and the algebraic structure is a concrete category `(A, s)`.
* Both functors are bundled as objects of `E ⥤ₗ E'` and `E' ⥤ₗ E`. Left exactness of `f⁻¹` is the
  hypothesis of the proposition; left exactness of `f_*` is automatic
  (`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`), so bundling it restricts nothing and
  the statement applies to every morphism of topoi. It is bundled anyway because
  `CategoryTheory.LeftExactFunctor.whiskeringRight` postcomposes with a bundled functor.
* The adjunction is `@[no_expose]`, as `Adjunction.whiskerRight` is upstream: what carries
  mathematical content here is the *pair of functors*, and those are pinned in the type rather than
  in the construction, so the compatibilities with taking the underlying object hold definitionally
  whatever adjunction datum realizes them. What a user of an adjunction wants — `homEquiv`, `unit`,
  `counit` and the equations between them — comes from `Adjunction` itself, so nothing needs to
  unfold the construction, and nothing in this development does.

## References

* [Stacks 00YV](https://stacks.math.columbia.edu/tag/00YV), Proposition in the section "Sheaves of
  algebraic structures", together with the unnumbered discussion (α)–(ζ) and the quadruple
  `(F, +, 0, i)` description preceding it; types of algebraic structure are Stacks 007L and
  Stacks 007N, the pushforward for presheaves of algebraic structures is Stacks 00YS, and the case
  of a morphism of sites is Stacks 00YT.
* [SGA4], Exposé IV, for *espèces de structure algébrique définies par limites projectives finies*.
-/


namespace CategoryTheory.Adjunction

section

universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory Limits
open CategoryTheory

namespace Stacks.AlgebraicStructure.ToposAdjoint

@[expose] public section

/-- Postcomposition with a left exact functor `F : E ⥤ₗ E'` on structures of type `T` is plain
postcomposition with `F.obj` after forgetting left exactness, on the nose:
`CategoryTheory.LeftExactFunctor.whiskeringRight` is a lift of the plain whiskering functor
through `CategoryTheory.ObjectProperty.ι`, so this is `CategoryTheory.ObjectProperty.liftCompιIso`
read backwards. -/
private def forgetCompWhiskeringRightIso (T : Type u₁) [Category.{v₁} T] {E : Type u₂}
    [Category.{v₂} E] {E' : Type u₃} [Category.{v₃} E'] (F : E ⥤ₗ E') :
    LeftExactFunctor.forget T E ⋙ (Functor.whiskeringRight T E E').obj F.obj ≅
      (LeftExactFunctor.whiskeringRight T E E').obj F ⋙ LeftExactFunctor.forget T E' :=
  ((leftExactFunctor T E').liftCompιIso _ _).symm

end

end Stacks.AlgebraicStructure.ToposAdjoint

@[expose] public section

open Stacks.AlgebraicStructure.ToposAdjoint in
/-- Let `T` be a theory of algebraic structures defined by finite projective limits, so that a
structure of that type in a category `E` is a left exact functor `T ⥤ E`, its underlying object
being its value at the sort. Let `f = (f⁻¹, f_*)` be a morphism of topoi, that is, an adjunction
`f⁻¹ ⊣ f_*` whose left adjoint `f⁻¹` is left exact (the right adjoint `f_*` then being left exact
for free).

Then postcomposition with `f⁻¹` and with `f_*` are functors on structures of type `T`, and they
form an adjoint pair. Since they are postcomposition, they commute with taking the underlying
object — for `E`, `E'` categories of sheaves of sets, the underlying sheaf of sets — on the nose.
-/
@[no_expose,
  stacks 00YV "Stated for an arbitrary theory `T` of algebraic structures defined by
  finite projective limits — structures of type `T` in `E` being the left exact functors `T ⥤ E` —
  rather than for the seven listed types of algebraic structure separately, and for an arbitrary
  adjunction between left exact functors rather than for a morphism of topoi: postcomposition with
  `f⁻¹` and with `f_*` is an adjoint pair on structures, compatible with taking the underlying
  sheaf of sets by construction.",
  sga "4 IV 3.1.2" "finite proj lim structs",
  sga "4 III 1.7" "special case"]
public noncomputable def leftExactWhiskerRight (T : Type u₁) [Category.{v₁} T] {E : Type u₂}
    [Category.{v₂} E] {E' : Type u₃} [Category.{v₃} E'] {f : E ⥤ₗ E'} {g : E' ⥤ₗ E}
    (adj : f.obj ⊣ g.obj) :
    (LeftExactFunctor.whiskeringRight T E E').obj f ⊣
      (LeftExactFunctor.whiskeringRight T E' E).obj g :=
  (Adjunction.whiskerRight T adj).restrictFullyFaithful (LeftExactFunctor.fullyFaithful T E)
    (LeftExactFunctor.fullyFaithful T E') (forgetCompWhiskeringRightIso T f)
    (forgetCompWhiskeringRightIso T g)

end

end

end CategoryTheory.Adjunction
