module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic

/-!
# Finite étale covers of an inverse limit of schemes

Let `D : I ⥤ Scheme` be a cofiltered inverse system of quasi-compact and quasi-separated schemes
with affine transition morphisms, and let `c` be a limit cone on it, so that `c.pt` is the scheme
`X = lim Xᵢ`. Base change along the projections `c.π.app i : c.pt ⟶ D.obj i` gives functors
`FÉt_{Xᵢ} ⥤ FÉt_X`, and this file proves that they exhibit `FÉt_X` as the filtered colimit of the
categories `FÉt_{Xᵢ}`: every finite étale cover of `X` is the base change of one at a stage, every
morphism between base-changed covers is the base change of one at a later stage, and two morphisms
at a stage which agree over `X` already agree at a later stage.

## Main definitions

* `AlgebraicGeometry.finiteEtaleLimitCompIso` — the canonical isomorphism between base change along
  a projection of the cone and the two-step base change through a later stage.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_model` — essential surjectivity: a finite étale cover of
  the limit is the base change of a finite étale cover of one of the stages.
* `AlgebraicGeometry.exists_finiteEtale_model_of_isLimit` — the same statement for the plain
  over-category `Over c.pt`, with finiteness and étaleness of the structure morphism as instance
  hypotheses rather than bundled into the object.
* `AlgebraicGeometry.exists_finiteEtale_model_over_open_of_isLimit` — the same statement over a
  quasi-compact open of the limit, which comes from a quasi-compact open of a stage.
* `AlgebraicGeometry.exists_finiteEtale_hom_model` — fullness: a morphism between the base changes
  to the limit of two finite étale covers of a stage is, up to the canonical comparison
  isomorphism, the base change of a morphism at a later stage.
* `AlgebraicGeometry.eventually_eq_of_finiteEtaleBaseChange_eq` — faithfulness: two morphisms of
  finite étale covers of a stage whose base changes to the limit agree are equal after passing to
  a later stage.

## Implementation notes

The limit of the system is modelled, as everywhere in the surrounding development, by a cone `c`
together with `IsLimit c`; the three results are therefore about the same object as the descent
theorems they rest on, rather than about a separately built limit.

The three clauses together are the content of the equivalence of categories
`colim FÉt_{Xᵢ} = FÉt_X`; they are stated separately because the diagram `i ↦ FÉt_{Xᵢ}` is a
pseudofunctor rather than a functor, base change along a composite being isomorphic and not equal
to the composite of the base changes. The comparison isomorphism witnessing this,
`AlgebraicGeometry.finiteEtaleLimitCompIso`, is what the fullness clause is stated against. The
second conclusion of the source lemma, the description of the étale fundamental group of the limit
as the inverse limit of the fundamental groups of the stages, is not part of this file.

Each clause reduces to its counterpart for schemes merely of finite presentation over the base:
a finite étale morphism is of finite presentation, and `FÉt_X` is a *full* subcategory of the
category of schemes over `X`, cut out by a property of objects only, so morphisms need no
descending beyond what tag 01ZM already provides. What essential surjectivity needs in addition is
that the property of being finite étale descends: the structure morphism of an object of
`Over (D.obj i)` is read as a morphism to the terminal object `𝟙 (D.obj i)`, whose base changes
differ from the base changes of the structure morphism by the isomorphism `pullback.snd (𝟙 _) g`,
and tags 01ZO and 07RP then descend finiteness and étaleness separately, after which the two
stages are merged by cofilteredness.

The index category is taken in the same universe as the schemes, `I : Type u` with
`Category.{u} I`, because tag 07RP is stated at that universe; essential smallness, which tags
01ZM and 01ZO ask for, is then automatic.

The two unbundled restatements obtain their isomorphism by applying
`MorphismProperty.Over.forget` to the bundled one: that functor sends a base change of finite
étale covers to the corresponding base change in `Over`, by definition and not merely up to
isomorphism, so no transport along an equality of functors is involved. The version over an open
calls the bundled statement rather than the unbundled one because its base is the cone point of
`AlgebraicGeometry.opensCone`, and `Over.mk`-style data crosses that definition where a search
for an instance of `IsFinite` would not.

## References

* [Stacks Project, Tag 0BTV](https://stacks.math.columbia.edu/tag/0BTV)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZO](https://stacks.math.columbia.edu/tag/01ZO)
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A finite étale morphism is of finite presentation. -/
private lemma finitePresentation_of_finiteEtaleOver {X : Scheme.{u}} (A : FiniteEtaleOver X) :
    FinitePresentation A.hom := by
  have := A.prop.1
  have := A.prop.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The underlying morphism of schemes over the base of a morphism of finite étale covers. -/
private def overHomOfFiniteEtaleHom {X : Scheme.{u}} {A B : FiniteEtaleOver X} (φ : A ⟶ B) :
    Over.mk A.hom ⟶ Over.mk B.hom :=
  Over.homMk φ.left (MorphismProperty.Over.w φ)

/-- Base change of finite étale covers and base change in the over category agree on the
underlying morphisms of schemes. -/
private lemma finiteEtaleBaseChange_map_left_eq {X Y : Scheme.{u}} (u : X ⟶ Y)
    {A B : FiniteEtaleOver Y} (φ : A ⟶ B) :
    ((finiteEtaleBaseChange u).map φ).left
      = ((Over.pullback u).map (overHomOfFiniteEtaleHom φ)).left := rfl

/-- The structure morphism of an object of `Over T`, read as a morphism to the terminal object
`𝟙 T` of `Over T`. -/
private def overToTerminal {T : Scheme.{u}} (A : Over T) : A ⟶ Over.mk (𝟙 T) :=
  Over.homMk A.hom (by simp)

/-- A base change of the morphism to the terminal object differs from the corresponding base
change of the structure morphism by the projection out of a pullback along an identity. -/
private lemma overToTerminal_pullback_comp {T S : Scheme.{u}} (g : S ⟶ T) (A : Over T) :
    ((Over.pullback g).map (overToTerminal A)).left ≫ pullback.snd (𝟙 T) g
      = pullback.snd A.hom g :=
  pullback.lift_snd _ _ _

/-- A property stable under isomorphism holds of a base change of the morphism to the terminal
object exactly when it holds of the corresponding base change of the structure morphism. -/
private lemma prop_overToTerminal_pullback_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {T S : Scheme.{u}} (g : S ⟶ T) (A : Over T) :
    P ((Over.pullback g).map (overToTerminal A)).left ↔ P (pullback.snd A.hom g) := by
  rw [← overToTerminal_pullback_comp g A]
  exact (P.cancel_right_of_respectsIso _ _).symm

/-- A property stable under base change, holding of the base change of a structure morphism along
one morphism, holds of its base change along any precomposition of that morphism. -/
private lemma prop_pullback_snd_comp (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {T S S' : Scheme.{u}} (A : Over T) (w : S ⟶ T) (v : S' ⟶ S)
    (h : P (pullback.snd A.hom w)) : P (pullback.snd A.hom (v ≫ w)) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← MorphismProperty.cancel_left_of_respectsIso P
        (pullbackLeftPullbackSndIso A.hom w v).hom, pullbackLeftPullbackSndIso_hom_snd]
  exact MorphismProperty.pullback_snd _ _ h

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- **The comparison isomorphism of the system of finite étale categories.** Base change of finite
étale covers along the projection of the cone at a stage `i` is isomorphic to base change along a
transition morphism `e : j ⟶ i` followed by base change along the projection at `j`. -/
abbrev finiteEtaleLimitCompIso {i j : I} (e : j ⟶ i) :
    finiteEtaleBaseChange (c.π.app i)
      ≅ finiteEtaleBaseChange (D.map e) ⋙ finiteEtaleBaseChange (c.π.app j) :=
  finiteEtaleBaseChangeComp (c.π.app j) (D.map e) (c.π.app i) (c.w e).symm

/-- The inverse comparison isomorphism is a section of the forward one on underlying schemes. -/
private lemma finiteEtaleLimitCompIso_inv_hom_app_left {i j : I} (e : j ⟶ i)
    (A : FiniteEtaleOver (D.obj i)) :
    ((finiteEtaleLimitCompIso D c e).inv.app A).left
      ≫ ((finiteEtaleLimitCompIso D c e).hom.app A).left = 𝟙 _ := by
  rw [← MorphismProperty.Comma.comp_left, ← NatTrans.comp_app, Iso.inv_hom_id]
  rfl

/-- A morphism over the limit from a two-step base change of a finite étale cover to the one-step
base change is the inverse comparison isomorphism as soon as it is compatible with the projections
to the original cover. -/
private lemma eq_finiteEtaleLimitCompIso_inv_app_left {i j : I} (e : j ⟶ i)
    (A : FiniteEtaleOver (D.obj i))
    (k : pullback (pullback.snd A.hom (D.map e)) (c.π.app j) ⟶ pullback A.hom (c.π.app i))
    (hfst : k ≫ pullback.fst A.hom (c.π.app i)
      = pullback.fst (pullback.snd A.hom (D.map e)) (c.π.app j) ≫ pullback.fst A.hom (D.map e))
    (hsnd : k ≫ pullback.snd A.hom (c.π.app i)
      = pullback.snd (pullback.snd A.hom (D.map e)) (c.π.app j)) :
    k = ((finiteEtaleLimitCompIso D c e).inv.app A).left := by
  have hproj := finiteEtaleBaseChangeComp_hom_app_left_proj (c.π.app j) (D.map e) (c.π.app i)
    (c.w e).symm A
  have key : ((finiteEtaleLimitCompIso D c e).inv.app A).left ≫ pullback.fst A.hom (c.π.app i)
      = pullback.fst (pullback.snd A.hom (D.map e)) (c.π.app j)
        ≫ pullback.fst A.hom (D.map e) := by
    rw [show pullback.fst A.hom (c.π.app i) = finiteEtaleBaseChangeProj (c.π.app i) A from rfl,
      ← hproj, ← Category.assoc, ← Category.assoc,
      finiteEtaleLimitCompIso_inv_hom_app_left, Category.id_comp]
    rfl
  apply pullback.hom_ext
  · exact hfst.trans key.symm
  · exact hsnd.trans (MorphismProperty.Over.w ((finiteEtaleLimitCompIso D c e).inv.app A)).symm

variable [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- If the base change to the limit of the structure morphism of an object of finite presentation
over a stage is finite étale, then its base change to some later stage is finite étale. -/
private theorem exists_finiteEtale_pullback_stage (hc : IsLimit c) (i : I) (A : Over (D.obj i))
    (hA : FinitePresentation A.hom)
    (hlim : finiteEtale (pullback.snd A.hom (c.π.app i))) :
    ∃ (j : I) (e : j ⟶ i), finiteEtale (pullback.snd A.hom (D.map e)) := by
  have hRF : MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hRE : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hlfp : LocallyOfFinitePresentation A.hom := hA.1
  have : QuasiCompact A.hom := hA.2.1
  have : QuasiSeparated A.hom := hA.2.2
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have : CompactSpace (Over.mk (𝟙 (D.obj i))).left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have hlfp' : LocallyOfFinitePresentation (overToTerminal A).left := hlfp
  have hlft : LocallyOfFiniteType (overToTerminal A).left := inferInstance
  have hfin : IsFinite ((Over.pullback (c.π.app i)).map (overToTerminal A)).left :=
    (prop_overToTerminal_pullback_iff (@IsFinite) _ A).mpr hlim.1
  have het : Etale ((Over.pullback (c.π.app i)).map (overToTerminal A)).left :=
    (prop_overToTerminal_pullback_iff (@Etale) _ A).mpr hlim.2
  obtain ⟨j₁, e₁, h₁⟩ := exists_isFinite_baseChange_of_isLimit D c hc i A
    (Over.mk (𝟙 (D.obj i))) (overToTerminal A)
  obtain ⟨ii, h₂⟩ := exists_etale_pullback_of_isLimit D c hc i A
    (Over.mk (𝟙 (D.obj i))) (overToTerminal A)
  obtain ⟨k, k₁, k₂, hfac⟩ := IsCofiltered.cospan e₁ ii.hom
  refine ⟨k, k₁ ≫ e₁, ?_⟩
  have hF : IsFinite (pullback.snd A.hom (D.map e₁)) :=
    (prop_overToTerminal_pullback_iff (@IsFinite) _ A).mp h₁
  have hE : Etale (pullback.snd A.hom (D.map ii.hom)) :=
    (prop_overToTerminal_pullback_iff (@Etale) _ A).mp h₂
  constructor
  · rw [D.map_comp]
    exact prop_pullback_snd_comp (@IsFinite) A (D.map e₁) (D.map k₁) hF
  · rw [hfac, D.map_comp]
    exact prop_pullback_snd_comp (@Etale) A (D.map ii.hom) (D.map k₂) hE

/-- **Every finite étale cover of the limit comes from a stage.** A scheme finite étale over the
limit of a cofiltered inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms is isomorphic, as a cover of the limit, to the base change of a scheme finite
étale over one of the stages. -/
@[stacks 0BTV "equivalence of categories: every finite étale cover of the limit comes from a stage"]
theorem exists_finiteEtale_model (hc : IsLimit c) (Y : FiniteEtaleOver c.pt) :
    ∃ (j : I) (B : FiniteEtaleOver (D.obj j)),
      Nonempty (Y ≅ (finiteEtaleBaseChange (c.π.app j)).obj B) := by
  have hfin : IsFinite Y.hom := Y.prop.1
  have het : Etale Y.hom := Y.prop.2
  have hfp : FinitePresentation Y.hom := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨i, A, hA, ⟨ε⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk Y.hom) hfp
  have hw : ε.hom.left ≫ pullback.snd A.hom (c.π.app i) = Y.hom := Over.w ε.hom
  have hisoleft : IsIso ε.hom.left := inferInstanceAs (IsIso ((Over.forget _).map ε.hom))
  have hlim : finiteEtale (pullback.snd A.hom (c.π.app i)) := by
    have hR : MorphismProperty.RespectsIso (finiteEtale : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (finiteEtale : MorphismProperty Scheme.{u}) ε.hom.left, hw]
    exact ⟨hfin, het⟩
  obtain ⟨j, e, hj⟩ := exists_finiteEtale_pullback_stage D c hc i A hA hlim
  refine ⟨j, MorphismProperty.Over.mk ⊤ (pullback.snd A.hom (D.map e)) hj, ⟨?_⟩⟩
  let φ : Y.left ≅ pullback (pullback.snd A.hom (D.map e)) (c.π.app j) :=
    (Over.forget _).mapIso ε ≪≫ (pullback.congrHom rfl (c.w e)).symm ≪≫
      (pullbackLeftPullbackSndIso A.hom (D.map e) (c.π.app j)).symm
  have hcompat : φ.hom ≫ pullback.snd (pullback.snd A.hom (D.map e)) (c.π.app j) = Y.hom := by
    simp only [φ, Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Iso.symm_hom,
      Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]
    exact hw
  exact MorphismProperty.Over.isoMk φ hcompat

/-- **Every finite étale scheme over the limit comes from a stage.** The form of
`AlgebraicGeometry.exists_finiteEtale_model` for the plain over-category: a scheme over the limit
of a cofiltered inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms whose structure morphism is finite and étale is isomorphic, as a scheme over the limit,
to the pullback along one of the projections of a scheme over a stage whose structure morphism is
again finite and étale. -/
theorem exists_finiteEtale_model_of_isLimit (hc : IsLimit c) (X : Over c.pt)
    [IsFinite X.hom] [Etale X.hom] :
    ∃ (j : I) (Xj : Over (D.obj j)), IsFinite Xj.hom ∧ Etale Xj.hom ∧
      Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xj) := by
  obtain ⟨j, B, ⟨ε⟩⟩ := exists_finiteEtale_model D c hc
    (MorphismProperty.Over.mk ⊤ X.hom ⟨inferInstance, inferInstance⟩)
  exact ⟨j, Over.mk B.hom, B.prop.1, B.prop.2,
    ⟨(MorphismProperty.Over.forget finiteEtale ⊤ c.pt).mapIso ε⟩⟩

omit [∀ i : I, CompactSpace (D.obj i)] in
/-- **Every finite étale scheme over a quasi-compact open of the limit comes from a stage.** A
scheme whose structure morphism to a quasi-compact open `V` of the limit is finite and étale comes
from a quasi-compact open `Vᵢ` of some stage: the open `V` is the preimage of `Vᵢ` under the
projection, as a pullback square, and the scheme is the pullback along the induced
`V ⟶ Vᵢ` of a scheme over `Vᵢ` whose structure morphism is again finite and étale.

The stages are not assumed quasi-compact here; compactness of `V` is what makes the restricted
system `AlgebraicGeometry.opensDiagram` a system of quasi-compact schemes, which is all the
descent needs. -/
theorem exists_finiteEtale_model_over_open_of_isLimit (hc : IsLimit c) (V : c.pt.Opens)
    (hV : IsCompact (V : Set c.pt)) (X : Over V.toScheme) [IsFinite X.hom] [Etale X.hom] :
    ∃ (i : I) (Vi : (D.obj i).Opens) (g : V.toScheme ⟶ Vi.toScheme),
      IsCompact (Vi : Set (D.obj i)) ∧ IsPullback V.ι g (c.π.app i) Vi.ι ∧
      ∃ Xi : Over Vi.toScheme, IsFinite Xi.hom ∧ Etale Xi.hom ∧
        Nonempty (X ≅ (Over.pullback g).obj Xi) := by
  obtain ⟨i, Vi, hVi, rfl⟩ := exists_preimage_eq D c hc V hV
  have (j : Over i) : CompactSpace ((opensDiagram D i Vi).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ Vi.2 hVi)
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i Vi).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ Vi).2).mp
      (.of_quasiSeparatedSpace _)
  obtain ⟨j, B, ⟨ε⟩⟩ := exists_finiteEtale_model (opensDiagram D i Vi) (opensCone D c i Vi)
    (isLimitOpensCone D c hc i Vi)
    (MorphismProperty.Over.mk ⊤ X.hom ⟨‹IsFinite X.hom›, ‹Etale X.hom›⟩)
  refine ⟨j.left, D.map j.hom ⁻¹ᵁ Vi, (opensCone D c i Vi).π.app j,
    QuasiCompact.isCompact_preimage _ Vi.2 hVi, IsPullback.flip ?_,
    Over.mk B.hom, B.prop.1, B.prop.2,
    ⟨(MorphismProperty.Over.forget finiteEtale ⊤ (opensCone D c i Vi).pt).mapIso ε⟩⟩
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · simp [opensCone]
  · simp [← Scheme.Hom.comp_preimage, c.w]

/-- **Every morphism of finite étale covers over the limit comes from a stage.** A morphism between
the base changes to the limit of two finite étale covers of a stage is, after transport along the
comparison isomorphism `AlgebraicGeometry.finiteEtaleLimitCompIso`, the base change of a morphism
of the base changes of those covers to some later stage. -/
@[stacks 0BTV "equivalence of categories: every morphism over the limit comes from a stage"]
theorem exists_finiteEtale_hom_model (hc : IsLimit c) (i : I) (A B : FiniteEtaleOver (D.obj i))
    (ψ : (finiteEtaleBaseChange (c.π.app i)).obj A ⟶
      (finiteEtaleBaseChange (c.π.app i)).obj B) :
    ∃ (j : I) (e : j ⟶ i)
      (χ : (finiteEtaleBaseChange (D.map e)).obj A ⟶ (finiteEtaleBaseChange (D.map e)).obj B),
      ψ = (finiteEtaleLimitCompIso D c e).hom.app A
        ≫ (finiteEtaleBaseChange (c.π.app j)).map χ
        ≫ (finiteEtaleLimitCompIso D c e).inv.app B := by
  let ψ' : (Over.pullback (c.π.app i)).obj (Over.mk A.hom) ⟶
      (Over.pullback (c.π.app i)).obj (Over.mk B.hom) :=
    Over.homMk ψ.left (MorphismProperty.Over.w ψ)
  obtain ⟨j, e, g, α, β, hα, hβ, hcomm⟩ :=
    exists_morphism_after_baseChange D c hc i (Over.mk A.hom) (Over.mk B.hom)
      (finitePresentation_of_finiteEtaleOver A) (finitePresentation_of_finiteEtaleOver B) ψ'
  let χ : (finiteEtaleBaseChange (D.map e)).obj A ⟶ (finiteEtaleBaseChange (D.map e)).obj B :=
    MorphismProperty.Over.homMk g.left (Over.w g) trivial
  refine ⟨j, e, χ, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  have hαl : α.hom.left = ((finiteEtaleLimitCompIso D c e).inv.app A).left :=
    eq_finiteEtaleLimitCompIso_inv_app_left D c e A α.hom.left hα (Over.w α.hom)
  have hβl : β.hom.left = ((finiteEtaleLimitCompIso D c e).inv.app B).left :=
    eq_finiteEtaleLimitCompIso_inv_app_left D c e B β.hom.left hβ (Over.w β.hom)
  have hmapχ : ((finiteEtaleBaseChange (c.π.app j)).map χ).left
      = ((Over.pullback (c.π.app j)).map g).left := rfl
  have hepi : IsIso α.hom.left := inferInstanceAs (IsIso ((Over.forget _).map α.hom))
  have hvu2 : ∀ {Z : Scheme.{u}}
      (X : ((finiteEtaleBaseChange (D.map e) ⋙ finiteEtaleBaseChange (c.π.app j)).obj A).left
        ⟶ Z),
      ((finiteEtaleLimitCompIso D c e).inv.app A).left
        ≫ ((finiteEtaleLimitCompIso D c e).hom.app A).left ≫ X = X := by
    intro Z X
    rw [← Category.assoc, finiteEtaleLimitCompIso_inv_hom_app_left, Category.id_comp]
  have hL : α.hom.left ≫ ψ.left
      = ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left := by
    have h : α.hom.left ≫ ψ'.left
        = ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left := by
      rw [← Over.comp_left, ← Over.comp_left, hcomm]
    exact h
  have hR : α.hom.left ≫ ((finiteEtaleLimitCompIso D c e).hom.app A).left
        ≫ ((finiteEtaleBaseChange (c.π.app j)).map χ).left
        ≫ ((finiteEtaleLimitCompIso D c e).inv.app B).left
      = ((Over.pullback (c.π.app j)).map g).left ≫ β.hom.left := by
    rw [hβl, hmapχ, hαl]
    exact hvu2 _
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  exact (cancel_epi α.hom.left).mp (hL.trans hR.symm)

/-- **Morphisms of finite étale covers agreeing over the limit agree at a later stage.** Two
morphisms of finite étale covers of a stage whose base changes along the projection of the cone
agree are already equal after base change to some later stage. -/
@[stacks 0BTV "equivalence of categories: morphisms agreeing over the limit agree at a later stage"]
theorem eventually_eq_of_finiteEtaleBaseChange_eq (hc : IsLimit c) (i : I)
    (A B : FiniteEtaleOver (D.obj i)) (f g : A ⟶ B)
    (h : (finiteEtaleBaseChange (c.π.app i)).map f
      = (finiteEtaleBaseChange (c.π.app i)).map g) :
    ∃ (j : I) (e : j ⟶ i),
      (finiteEtaleBaseChange (D.map e)).map f = (finiteEtaleBaseChange (D.map e)).map g := by
  have hover : (Over.pullback (c.π.app i)).map (overHomOfFiniteEtaleHom f)
      = (Over.pullback (c.π.app i)).map (overHomOfFiniteEtaleHom g) := by
    apply Over.OverMorphism.ext
    rw [← finiteEtaleBaseChange_map_left_eq, ← finiteEtaleBaseChange_map_left_eq, h]
  obtain ⟨j, e, hje⟩ := eventually_eq_of_baseChange_eq D c hc i (Over.mk A.hom) (Over.mk B.hom)
    (finitePresentation_of_finiteEtaleOver A) (finitePresentation_of_finiteEtaleOver B)
    (overHomOfFiniteEtaleHom f) (overHomOfFiniteEtaleHom g) hover
  refine ⟨j, e, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  rw [finiteEtaleBaseChange_map_left_eq, finiteEtaleBaseChange_map_left_eq, hje]

end AlgebraicGeometry

end
