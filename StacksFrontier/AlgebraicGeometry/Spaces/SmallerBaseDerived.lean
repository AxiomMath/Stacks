module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseCohomology
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.SiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeSiteComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartBaseChangeCompIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparisonComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackCompositionCanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom

/-!
# Derived categories of an algebraic space over a smaller base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site, `Z` an algebraic space over `W` and `Y` an
algebraic space over `S` together with an identification `ε : Λ_h Z ≅ Y` of the lower-shriek
extension of `Z` with `Y` (Stacks 04SG). The two are the same space seen over two bases. This
file shows that their derived categories of modules are the same.

## Main definitions

* `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso`: the small étale sites of `Z`
  and `Y` are equivalent, by an equivalence that does not change the underlying scheme of a
  chart.
* `AlgebraicGeometry.Space.smallerBaseModulesEquivalenceOfIso`: the module categories of `Y` and
  `Z` are equivalent.
* `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence`: the derived categories
  `D(𝒪_Y) ≌ D(𝒪_Z)`, for arbitrary models of the two derived categories.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_smallerBaseDerivedEquivalence_iff`:
  pseudo-coherence (Stacks 08FT) is preserved and reflected by the equivalence.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) {Z : AlgebraicSpaces B W hW} {Y : AlgebraicSpaces B S hS}
  (ε : (OverShriek.relocalizePresheafFunctor h).obj Z.1 ≅ Y.1)

/-! ### The small étale sites and the modules -/

/-- **The small étale sites of `Z` and of `Y` are equivalent** when `Λ_h Z ≅ Y`: the
equivalence of the small étale sites of `Z` and of its lower-shriek extension, followed by the
one induced by `ε`. It does not change the underlying scheme of a chart. -/
def smallerBaseSmallEtaleEquivalenceOfIso :
    SmallEtale B W hW Z.1 ≌ SmallEtale B S hS Y.1 :=
  (SmallEtale.relocalizeEquivalence B W S hW hS h Z.1).trans (SmallEtale.congr B S hS ε)

/-- The functor of `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso` is
continuous for the étale topologies. -/
instance smallerBaseSmallEtaleEquivalenceOfIso_functor_isContinuous :
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.IsContinuous
      (SmallEtale.topology B W hW Z.1) (SmallEtale.topology B S hS Y.1) :=
  have := SmallEtale.congr_functor_isContinuous B S hS ε
  Functor.isContinuous_comp _ _ _
    (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj Z.1)) _

/-- The inverse of `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso` is
continuous for the étale topologies. -/
instance smallerBaseSmallEtaleEquivalenceOfIso_inverse_isContinuous :
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε).inverse.IsContinuous
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B W hW Z.1) :=
  have : (SmallEtale.congr B S hS ε).inverse.IsContinuous (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj Z.1)) :=
    Functor.isContinuous_iff_coverPreserving.2 (SmallEtale.congr_inverse_coverPreserving B S hS _)
  Functor.isContinuous_comp _ _ _
    (SmallEtale.topology B S hS ((OverShriek.relocalizePresheafFunctor h).obj Z.1)) _

/-- The continuity of `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso`, at the
spelling of the topologies as projections of the small étale ringed sites. -/
instance smallerBaseSmallEtaleEquivalenceOfIso_functor_isContinuous_ringedSite :
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.IsContinuous
      (smallEtaleRingedSite B W hW Z.1 Z.2).J (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  smallerBaseSmallEtaleEquivalenceOfIso_functor_isContinuous B h ε

/-- The continuity of the inverse of
`AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso`, at the spelling of the
topologies as projections of the small étale ringed sites. -/
instance smallerBaseSmallEtaleEquivalenceOfIso_inverse_isContinuous_ringedSite :
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε).inverse.IsContinuous
      (smallEtaleRingedSite B S hS Y.1 Y.2).J (smallEtaleRingedSite B W hW Z.1 Z.2).J :=
  smallerBaseSmallEtaleEquivalenceOfIso_inverse_isContinuous B h ε

/-- `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso_functor_isContinuous` with the
categories spelled through the small étale ringed sites. -/
instance smallerBaseSmallEtaleEquivalenceOfIso_functor_isContinuous_ringedSite' :
    @Functor.IsContinuous (smallEtaleRingedSite B W hW Z.1 Z.2).C
      (smallEtaleRingedSite B W hW Z.1 Z.2).category
      (smallEtaleRingedSite B S hS Y.1 Y.2).C (smallEtaleRingedSite B S hS Y.1 Y.2).category
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor
      (smallEtaleRingedSite B W hW Z.1 Z.2).J (smallEtaleRingedSite B S hS Y.1 Y.2).J :=
  smallerBaseSmallEtaleEquivalenceOfIso_functor_isContinuous B h ε

/-- `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso_inverse_isContinuous` with the
categories spelled through the small étale ringed sites. -/
instance smallerBaseSmallEtaleEquivalenceOfIso_inverse_isContinuous_ringedSite' :
    @Functor.IsContinuous (smallEtaleRingedSite B S hS Y.1 Y.2).C
      (smallEtaleRingedSite B S hS Y.1 Y.2).category
      (smallEtaleRingedSite B W hW Z.1 Z.2).C (smallEtaleRingedSite B W hW Z.1 Z.2).category
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε).inverse
      (smallEtaleRingedSite B S hS Y.1 Y.2).J (smallEtaleRingedSite B W hW Z.1 Z.2).J :=
  smallerBaseSmallEtaleEquivalenceOfIso_inverse_isContinuous B h ε

/-- **The modules on `Y` and on `Z` are the same**: transport along the equivalence of small
étale sites `AlgebraicGeometry.Space.smallerBaseSmallEtaleEquivalenceOfIso`, which carries the
structure sheaf of `Y` to that of `Z` on the nose. -/
def smallerBaseModulesEquivalenceOfIso :
    Modules.{u, u} B S hS Y.1 Y.2 ≌ Modules.{u, u} B W hW Z.1 Z.2 :=
  @Stacks.SheafOfModules.reindexEquivalence.{u, u} _ _ _ _
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B W hW Z.1)
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε)
    (smallerBaseSmallEtaleEquivalenceOfIso_functor_isContinuous B h ε)
    (smallerBaseSmallEtaleEquivalenceOfIso_inverse_isContinuous B h ε)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)

/-- The functor of `AlgebraicGeometry.Space.smallerBaseModulesEquivalenceOfIso` is additive. -/
instance smallerBaseModulesEquivalenceOfIso_functor_additive :
    (smallerBaseModulesEquivalenceOfIso B h ε).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of `AlgebraicGeometry.Space.smallerBaseModulesEquivalenceOfIso` is additive. -/
instance smallerBaseModulesEquivalenceOfIso_inverse_additive :
    (smallerBaseModulesEquivalenceOfIso B h ε).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The extension of a morphism of charts along `h` is `Over.map h` of it. -/
theorem smallerBaseSmallEtaleEquivalenceOfIso_functor_map_hom_left {V V' : SmallEtale B W hW Z.1}
    (k : V ⟶ V') :
    ((smallerBaseSmallEtaleEquivalenceOfIso B h ε).functor.map k).hom.left =
      (Over.map h).map k.hom.left :=
  rfl

/-- The base change of a morphism of charts is compatible with the projections to the source
space. -/
theorem yoneda_map_smallBaseChange_map_hom_left_fst {T : Scheme.{u}} {hT : B.Contains T}
    {X X' : AlgebraicSpaces B T hT} (q : X ⟶ X') (hq : yoneda.relativelyRepresentable q.hom)
    {V V' : SmallEtale B T hT X'.1} (k : V ⟶ V') :
    yoneda.map ((smallBaseChange B T hT q hq).map k).hom.left ≫ hq.fst V'.1.hom =
      hq.fst V.1.hom :=
  hq.lift_fst _ _ _

/-- Two morphisms into a base-changed chart are equal when their projections to the chart agree. -/
theorem smallBaseChange_hom_ext {T : Scheme.{u}} {hT : B.Contains T}
    {X X' : AlgebraicSpaces B T hT} {q : X ⟶ X'} (hq : yoneda.relativelyRepresentable q.hom)
    {A : SmallEtale B T hT X.1} {V : SmallEtale B T hT X'.1}
    (a b : A ⟶ (smallBaseChange B T hT q hq).obj V)
    (e : a.hom.left ≫ hq.snd V.1.hom = b.hom.left ≫ hq.snd V.1.hom) : a = b :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hq.hom_ext
    ((CostructuredArrow.w a.hom).trans (CostructuredArrow.w b.hom).symm) e))

/-! ### Mates along equivalences -/

section Mates

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  {G : C₁ ≌ C₃} {H : C₂ ≌ C₄} {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}

/-- **The mate of an isomorphism along two equivalences is an isomorphism.** For adjunctions
`L₁ ⊣ R₁` and `L₂ ⊣ R₂` and equivalences `G`, `H`, the mate `G ⋙ L₂ ⟶ L₁ ⋙ H` of an
isomorphism `R₁ ⋙ G ≅ H ⋙ R₂` is an isomorphism: its mate along the adjunctions of the two
equivalences is built from their units and counits, and it is the conjugate of the original
transformation (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`). -/
theorem isIso_mateEquiv_symm_of_equivalence (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (β : TwoSquare R₁ H.functor G.functor R₂) (hβ : IsIso β) :
    IsIso ((mateEquiv adj₁ adj₂).symm β) := by
  have key := iterated_mateEquiv_conjugateEquiv adj₁ adj₂ G.toAdjunction H.toAdjunction
    ((mateEquiv adj₁ adj₂).symm β)
  have e : (mateEquiv adj₁ adj₂) ((mateEquiv adj₁ adj₂).symm β) = β :=
    Equiv.apply_symm_apply _ _
  rw [e] at key
  have : IsIso (mateEquiv H.toAdjunction G.toAdjunction β) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    rw [mateEquiv_apply]
    have hβ : ∀ Y, IsIso (β.app Y) := fun Y => NatIso.isIso_app_of_isIso _ Y
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Equivalence.toAdjunction_unit, Equivalence.toAdjunction_counit]
    have := hβ (H.inverse.obj X)
    have : IsIso ((Functor.whiskerRight β G.inverse).app (H.inverse.obj X)) :=
      inferInstanceAs (IsIso (G.inverse.map (β.app (H.inverse.obj X))))
    infer_instance
  rw [key] at this
  exact conjugateEquiv_of_iso (adj₁.comp H.toAdjunction) (G.toAdjunction.comp adj₂) _

end Mates

/-! ### Transporting a left derived functor along an equivalence -/

section DerivedTransfer

open CategoryTheory.LeftDerivedByResolutions

variable {C D H C' D' H' : Type*} [Category* C] [Category* D] [Category* H] [Category* C']
  [Category* D'] [Category* H']
  {W : MorphismProperty C} [W.HasRightCalculusOfFractions] [W.RespectsIso]
  {W' : MorphismProperty C'} [W'.HasRightCalculusOfFractions] [W'.RespectsIso]
  {Q : C ⥤ D} [Q.IsLocalization W] {Q' : C' ⥤ D'} [Q'.IsLocalization W']
  {P : C ⥤ H} {P' : C' ⥤ H'} (LP' : D' ⥤ H') (α' : Q' ⋙ LP' ⟶ P')
  {R' : ObjectProperty C'} (hR' : ∀ X, ∃ (Y : C') (_ : R' Y) (s : Y ⟶ X), W' s)
  (hP' : ∀ {X Y : C'} (s : X ⟶ Y), W' s → R' X → R' Y → IsIso (P'.map s))
  (hα' : ∀ X, R' X → IsIso (α'.app X))
  (Φ : C ≌ C') (hΦ : ∀ {X Y : C} (s : X ⟶ Y), W s → W' (Φ.functor.map s))
  (hΨ : ∀ {X Y : C'} (s : X ⟶ Y), W' s → W (Φ.inverse.map s))
  (F₂ : D ⥤ D') (e₂ : Q ⋙ F₂ ≅ Φ.functor ⋙ Q') (F₁ : H ⥤ H') (τ : P ⋙ F₁ ≅ Φ.functor ⋙ P')

/-- The comparison exhibiting `F₂ ⋙ LP'` as a left derived functor of `P ⋙ F₁`: the
comparison `e₂` of the localizations, then `α'`, then the underived comparison `τ`. -/
def transferCounit : Q ⋙ F₂ ⋙ LP' ⟶ P ⋙ F₁ :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e₂.hom LP' ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Φ.functor α' ≫ τ.inv

/-- The component of `AlgebraicGeometry.Space.transferCounit` at `X` is
`LP'.map (e₂.hom.app X) ≫ α'.app (Φ.functor.obj X) ≫ τ.inv.app X`. -/
theorem transferCounit_app (X : C) :
    (transferCounit LP' α' Φ F₂ e₂ F₁ τ).app X =
      LP'.map (e₂.hom.app X) ≫ α'.app (Φ.functor.obj X) ≫ τ.inv.app X := by
  simp [transferCounit]

omit [W'.HasRightCalculusOfFractions] [Q'.IsLocalization W'] in
include hR' hP' hα' hΦ hΨ in
/-- **A left derived functor transported along an equivalence of the sources is a left derived
functor.** If `LP'` is left derived from `P'` by resolutions in `R'`, and `Φ : C ≌ C'` matches
the weak equivalences and `P ⋙ F₁` with `Φ ⋙ P'`, then `F₂ ⋙ LP'` is a left derived functor of
`P ⋙ F₁`, computed on the objects whose image is isomorphic to one of `R'`. -/
theorem isLeftDerivedFunctor_transfer :
    (F₂ ⋙ LP').IsLeftDerivedFunctor (transferCounit LP' α' Φ F₂ e₂ F₁ τ) W := by
  let R : ObjectProperty C := fun X => R'.isoClosure (Φ.functor.obj X)
  refine isLeftDerivedFunctor_of_isIso_on_resolutions W R (fun X => ?_) (P ⋙ F₁) ?_ Q
    (F₂ ⋙ LP') _ ?_
  · obtain ⟨Y', hY', s', hs'⟩ := hR' (Φ.functor.obj X)
    refine ⟨Φ.inverse.obj Y', ⟨Y', hY', ⟨Φ.counitIso.app Y'⟩⟩,
      Φ.inverse.map s' ≫ (Φ.unitIso.app X).inv, ?_⟩
    exact (MorphismProperty.RespectsIso.postcomp W _ _ (hΨ s' hs'))
  · intro X Y s hs hX hY
    obtain ⟨X', hX', ⟨eX⟩⟩ := hX
    obtain ⟨Y', hY', ⟨eY⟩⟩ := hY
    have hs' : W' (eX.inv ≫ Φ.functor.map s ≫ eY.hom) :=
      MorphismProperty.RespectsIso.precomp W' _ _
        (MorphismProperty.RespectsIso.postcomp W' _ _ (hΦ s hs))
    have := hP' _ hs' hX' hY'
    have : IsIso (P'.map (Φ.functor.map s)) := by
      have e : P'.map (Φ.functor.map s) =
          P'.map eX.hom ≫ P'.map (eX.inv ≫ Φ.functor.map s ≫ eY.hom) ≫ P'.map eY.inv := by
        simp [← Functor.map_comp]
      rw [e]
      infer_instance
    rw [← NatIso.naturality_2 τ s]
    dsimp only [Functor.comp_map]
    infer_instance
  · intro X hX
    obtain ⟨X', hX', ⟨eX⟩⟩ := hX
    have := hα' X' hX'
    have : IsIso (α'.app (Φ.functor.obj X)) := by
      rw [NatTrans.isIso_app_iff_of_iso α' eX]
      exact this
    rw [transferCounit_app]
    infer_instance

end DerivedTransfer

/-! ### Coherence of a pasting of squares with composition -/

section CompSquare

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁'] [Category* C₂'] [Category* C₃']
  {pg : C₂ ⥤ C₁} {pg' : C₃ ⥤ C₂} {pgg : C₃ ⥤ C₁} {pf : C₂' ⥤ C₁'} {pf' : C₃' ⥤ C₂'}
  {pff : C₃' ⥤ C₁'} {Φ₁ : C₁ ⥤ C₁'} {Φ₂ : C₂ ⥤ C₂'} {Φ₃ : C₃ ⥤ C₃'}

/-- **Squares compatible with composition.** Given composition isomorphisms
`c : pg' ⋙ pg ≅ pgg` and `c' : pf' ⋙ pf ≅ pff` on two sides and squares `κ` relating them along
`Φ₁, Φ₂, Φ₃`, the square `κgg` of the composites is the pasting of `κg` and `κg'`, read through
`c` and `c'`.

It is stated as a proposition on the isomorphisms, so that a hypothesis of this form is matched
against a goal by comparing the isomorphisms, and not their components at an object. -/
def IsCompSquareCoherent (c : pg' ⋙ pg ≅ pgg) (c' : pf' ⋙ pf ≅ pff)
    (κg : pg ⋙ Φ₁ ≅ Φ₂ ⋙ pf) (κg' : pg' ⋙ Φ₂ ≅ Φ₃ ⋙ pf') (κgg : pgg ⋙ Φ₁ ≅ Φ₃ ⋙ pff) : Prop :=
  ∀ M, κg.hom.app (pg'.obj M) ≫ pf.map (κg'.hom.app M) ≫ c'.hom.app (Φ₃.obj M) =
    Φ₁.map (c.hom.app M) ≫ κgg.hom.app M

end CompSquare

/-! ### Coherence of transported derived functors with composition -/

section DerivedCoherence

variable {C₁ C₂ C₃ D₁ D₂ D₃ C₁' C₂' C₃' D₁' D₂' D₃' : Type*} [Category* C₁] [Category* C₂]
  [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃] [Category* C₁'] [Category* C₂']
  [Category* C₃'] [Category* D₁'] [Category* D₂'] [Category* D₃']
  {W₃ : MorphismProperty C₃} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₃ : C₃ ⥤ D₃} [Q₃.IsLocalization W₃]
  {Q₁' : C₁' ⥤ D₁'} {Q₂' : C₂' ⥤ D₂'} {Q₃' : C₃' ⥤ D₃'}
  {pg : C₂ ⥤ C₁} {pg' : C₃ ⥤ C₂} {pgg : C₃ ⥤ C₁} {pf : C₂' ⥤ C₁'} {pf' : C₃' ⥤ C₂'}
  {pff : C₃' ⥤ C₁'}
  {Lg : D₂ ⥤ D₁} {Lg' : D₃ ⥤ D₂} {Lgg : D₃ ⥤ D₁} {Lf : D₂' ⥤ D₁'} {Lf' : D₃' ⥤ D₂'}
  {Lff : D₃' ⥤ D₁'}
  (αg : Q₂ ⋙ Lg ⟶ pg ⋙ Q₁) (αg' : Q₃ ⋙ Lg' ⟶ pg' ⋙ Q₂) (αgg : Q₃ ⋙ Lgg ⟶ pgg ⋙ Q₁)
  (αf : Q₂' ⋙ Lf ⟶ pf ⋙ Q₁') (αf' : Q₃' ⋙ Lf' ⟶ pf' ⋙ Q₂') (αff : Q₃' ⋙ Lff ⟶ pff ⋙ Q₁')
  (c : pg' ⋙ pg ≅ pgg) (c' : pf' ⋙ pf ≅ pff)
  (CC : Lg' ⋙ Lg ≅ Lgg)
  (hC : ∀ M, CC.hom.app (Q₃.obj M) ≫ αgg.app M =
    Lg.map (αg'.app M) ≫ αg.app (pg'.obj M) ≫ Q₁.map (c.hom.app M))
  (CC' : Lf' ⋙ Lf ≅ Lff)
  (hC' : ∀ M, CC'.hom.app (Q₃'.obj M) ≫ αff.app M =
    Lf.map (αf'.app M) ≫ αf.app (pf'.obj M) ≫ Q₁'.map (c'.hom.app M))
  {Φ₁ : C₁ ⥤ C₁'} {Φ₂ : C₂ ⥤ C₂'} {Φ₃ : C₃ ⥤ C₃'} {F₁ : D₁ ⥤ D₁'} {F₂ : D₂ ⥤ D₂'}
  {F₃ : D₃ ⥤ D₃'}
  (e₁ : Q₁ ⋙ F₁ ≅ Φ₁ ⋙ Q₁') (e₂ : Q₂ ⋙ F₂ ≅ Φ₂ ⋙ Q₂') (e₃ : Q₃ ⋙ F₃ ≅ Φ₃ ⋙ Q₃')
  (κg : pg ⋙ Φ₁ ≅ Φ₂ ⋙ pf) (κg' : pg' ⋙ Φ₂ ≅ Φ₃ ⋙ pf') (κgg : pgg ⋙ Φ₁ ≅ Φ₃ ⋙ pff)
  (hκ : ∀ M, κg.hom.app (pg'.obj M) ≫ pf.map (κg'.hom.app M) ≫ c'.hom.app (Φ₃.obj M) =
    Φ₁.map (c.hom.app M) ≫ κgg.hom.app M)
  (Tg : Lg ⋙ F₁ ≅ F₂ ⋙ Lf)
  (hTg : ∀ N, Tg.hom.app (Q₂.obj N) ≫ Lf.map (e₂.hom.app N) ≫ αf.app (Φ₂.obj N) =
    F₁.map (αg.app N) ≫ e₁.hom.app (pg.obj N) ≫ Q₁'.map (κg.hom.app N))
  (Tg' : Lg' ⋙ F₂ ≅ F₃ ⋙ Lf')
  (hTg' : ∀ M, Tg'.hom.app (Q₃.obj M) ≫ Lf'.map (e₃.hom.app M) ≫ αf'.app (Φ₃.obj M) =
    F₂.map (αg'.app M) ≫ e₂.hom.app (pg'.obj M) ≫ Q₂'.map (κg'.hom.app M))
  (Tgg : Lgg ⋙ F₁ ≅ F₃ ⋙ Lff)
  (hTgg : ∀ M, Tgg.hom.app (Q₃.obj M) ≫ Lff.map (e₃.hom.app M) ≫ αff.app (Φ₃.obj M) =
    F₁.map (αgg.app M) ≫ e₁.hom.app (pgg.obj M) ≫ Q₁'.map (κgg.hom.app M))
  {G : C₃ ⥤ D₁'} (β : Q₃ ⋙ F₃ ⋙ Lff ⟶ G) [(F₃ ⋙ Lff).IsLeftDerivedFunctor β W₃]
  (ρ : ∀ M, (Φ₃ ⋙ pff ⋙ Q₁').obj M ⟶ G.obj M)
  (hβ : ∀ M, β.app M = Lff.map (e₃.hom.app M) ≫ αff.app (Φ₃.obj M) ≫ ρ M)

include W₃ hC hC' hκ hTg hTg' hTgg hβ in
/-- **Transported derived functors are compatible with composition.** Given left derived
functors on two sides, their composition isomorphisms characterized by the underived ones, and
isomorphisms `T` transporting them along functors `F` and `Φ` which are characterized by
underived isomorphisms `κ` compatible with the underived composition, the transported
isomorphisms are compatible with the derived composition isomorphisms. -/
theorem transfer_comp_app (X : D₃) :
    F₁.map (CC.hom.app X) ≫ Tgg.hom.app X =
      Tg.hom.app (Lg'.obj X) ≫ Lf.map (Tg'.hom.app X) ≫ CC'.hom.app (F₃.obj X) := by
  let γ₁ : Lg' ⋙ Lg ⋙ F₁ ⟶ F₃ ⋙ Lff :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight CC.hom F₁ ≫ Tgg.hom
  let γ₂ : Lg' ⋙ Lg ⋙ F₁ ⟶ F₃ ⋙ Lff :=
    Functor.whiskerLeft Lg' Tg.hom ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight Tg'.hom Lf ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F₃ CC'.hom
  have key : γ₁ = γ₂ := by
    refine Functor.leftDerived_ext (F₃ ⋙ Lff) β W₃ _ γ₁ γ₂ ?_
    ext M
    simp only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp, hβ]
    have l1 : F₁.map (CC.hom.app (Q₃.obj M)) ≫ Tgg.hom.app (Q₃.obj M) ≫
        Lff.map (e₃.hom.app M) ≫ αff.app (Φ₃.obj M) =
        F₁.map (Lg.map (αg'.app M) ≫ αg.app (pg'.obj M) ≫ Q₁.map (c.hom.app M)) ≫
          e₁.hom.app (pgg.obj M) ≫ Q₁'.map (κgg.hom.app M) := by
      rw [hTgg, ← Functor.map_comp_assoc, hC]
    have n1 := CC'.hom.naturality (e₃.hom.app M)
    have n2 := Tg.hom.naturality (αg'.app M)
    have n3 := αf.naturality (κg'.hom.app M)
    have n4 := e₁.hom.naturality (c.hom.app M)
    simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3 n4
    have r1 : Tg.hom.app (Lg'.obj (Q₃.obj M)) ≫ Lf.map (Tg'.hom.app (Q₃.obj M)) ≫
        CC'.hom.app (F₃.obj (Q₃.obj M)) ≫ Lff.map (e₃.hom.app M) ≫ αff.app (Φ₃.obj M) =
        F₁.map (Lg.map (αg'.app M) ≫ αg.app (pg'.obj M) ≫ Q₁.map (c.hom.app M)) ≫
          e₁.hom.app (pgg.obj M) ≫ Q₁'.map (κgg.hom.app M) := by
      rw [← reassoc_of% n1, hC']
      have k1 : Lf.map (Tg'.hom.app (Q₃.obj M)) ≫ Lf.map (Lf'.map (e₃.hom.app M)) ≫
          Lf.map (αf'.app (Φ₃.obj M)) = Lf.map (F₂.map (αg'.app M)) ≫
            Lf.map (e₂.hom.app (pg'.obj M)) ≫ Lf.map (Q₂'.map (κg'.hom.app M)) := by
        simp only [← Functor.map_comp]
        rw [hTg']
      have k2 : Q₁'.map (κg.hom.app (pg'.obj M)) ≫ Q₁'.map (pf.map (κg'.hom.app M)) ≫
          Q₁'.map (c'.hom.app (Φ₃.obj M)) =
            Q₁'.map (Φ₁.map (c.hom.app M)) ≫ Q₁'.map (κgg.hom.app M) := by
        simp only [← Functor.map_comp]
        rw [hκ]
      rw [reassoc_of% k1, ← reassoc_of% n2, reassoc_of% n3, reassoc_of% (hTg (pg'.obj M)), k2,
        ← reassoc_of% n4]
      simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc] at l1
    simp only [Category.assoc] at l1 r1 ⊢
    rw [reassoc_of% l1, reassoc_of% r1]
  have := NatTrans.congr_app key X
  simpa [γ₁, γ₂] using this

include W₃ hC hC' hTg hTg' hTgg hβ in
/-- `AlgebraicGeometry.Space.transfer_comp_app` with its underived coherence `hκ` in the form
`AlgebraicGeometry.Space.IsCompSquareCoherent`. -/
theorem transfer_comp_app_of_isCompSquareCoherent
    (hκ' : IsCompSquareCoherent c c' κg κg' κgg) (X : D₃) :
    F₁.map (CC.hom.app X) ≫ Tgg.hom.app X =
      Tg.hom.app (Lg'.obj X) ≫ Lf.map (Tg'.hom.app X) ≫ CC'.hom.app (F₃.obj X) :=
  transfer_comp_app (W₃ := W₃) αg αg' αgg αf αf' αff c c' CC hC CC' hC' e₁ e₂ e₃ κg κg' κgg hκ'
    Tg hTg Tg' hTg' Tgg hTgg β ρ hβ X

end DerivedCoherence

/-! ### Coherence of degreewise comparisons on homotopy categories -/

section HomotopyCoherence

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category* A₁] [Category* A₂] [Category* A₃]
  [Category* B₁] [Category* B₂] [Category* B₃] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
  [Preadditive B₁] [Preadditive B₂] [Preadditive B₃]
  {ℓg : A₂ ⥤ A₁} {ℓg' : A₃ ⥤ A₂} {ℓgg : A₃ ⥤ A₁} {kf : B₂ ⥤ B₁} {kf' : B₃ ⥤ B₂} {kff : B₃ ⥤ B₁}
  {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂} {E₃ : A₃ ⥤ B₃}
  [ℓg.Additive] [ℓg'.Additive] [ℓgg.Additive] [kf.Additive] [kf'.Additive] [kff.Additive]
  [E₁.Additive] [E₂.Additive] [E₃.Additive]

/-- The comparison induced on homotopy categories by `τ : ℓ ⋙ E ≅ E' ⋙ k`. -/
abbrev homotopySquareIso {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B]
    [Category* B'] [Preadditive A] [Preadditive A'] [Preadditive B] [Preadditive B']
    {ℓ : A ⥤ A'} {E : A' ⥤ B'} {E' : A ⥤ B} {k : B ⥤ B'} [ℓ.Additive] [E.Additive] [E'.Additive]
    [k.Additive] (τ : ℓ ⋙ E ≅ E' ⋙ k) :
    ℓ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ E.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      E'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ k.mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso τ _ ≪≫ (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm

/-- At the image of a complex `K`, the comparison `AlgebraicGeometry.Space.homotopySquareIso τ`
is the image in the homotopy category of the degreewise comparison induced by `τ`. -/
theorem homotopySquareIso_hom_app {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B]
    [Category* B'] [Preadditive A] [Preadditive A'] [Preadditive B] [Preadditive B']
    {ℓ : A ⥤ A'} {E : A' ⥤ B'} {E' : A ⥤ B} {k : B ⥤ B'} [ℓ.Additive] [E.Additive] [E'.Additive]
    [k.Additive] (τ : ℓ ⋙ E ≅ E' ⋙ k) (K : CochainComplex A ℤ) :
    (homotopySquareIso τ).hom.app ((HomotopyCategory.quotient A _).obj K) =
      (HomotopyCategory.quotient B' _).map
        ((Functor.mapHomologicalComplexCompIso τ (ComplexShape.up ℤ)).hom.app K) := by
  have e : (Functor.mapHomotopyCategoryCompIso (Iso.refl (E' ⋙ k)) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient A _).obj K) = 𝟙 _ := by
    change (HomotopyCategory.quotient B' _).map
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (E' ⋙ k)) _).inv.app K) = _
    refine Eq.trans (congrArg (HomotopyCategory.quotient B' _).map (?_ : _ = 𝟙 _))
      ((HomotopyCategory.quotient B' _).map_id _)
    ext n
    simp
  simp only [homotopySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, e]
  exact (Category.comp_id _).trans (Functor.mapHomotopyCategoryCompIso_hom_app_quotient τ K)

/-- **Degreewise comparisons are coherent on homotopy categories when they are on modules.** -/
theorem homotopySquareIso_comp_app (μ : ℓg' ⋙ ℓg ≅ ℓgg) (μ' : kf' ⋙ kf ≅ kff)
    (τg : ℓg ⋙ E₁ ≅ E₂ ⋙ kf) (τg' : ℓg' ⋙ E₂ ≅ E₃ ⋙ kf') (τgg : ℓgg ⋙ E₁ ≅ E₃ ⋙ kff)
    (hU : ∀ X, τg.hom.app (ℓg'.obj X) ≫ kf.map (τg'.hom.app X) ≫ μ'.hom.app (E₃.obj X) =
      E₁.map (μ.hom.app X) ≫ τgg.hom.app X)
    (M : HomotopyCategory A₃ (ComplexShape.up ℤ)) :
    (homotopySquareIso τg).hom.app ((ℓg'.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (kf.mapHomotopyCategory (ComplexShape.up ℤ)).map ((homotopySquareIso τg').hom.app M) ≫
        (Functor.mapHomotopyCategoryCompIso μ' (ComplexShape.up ℤ)).hom.app
          ((E₃.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      (E₁.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso μ (ComplexShape.up ℤ)).hom.app M) ≫
        (homotopySquareIso τgg).hom.app M := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  have h1 := homotopySquareIso_hom_app τg ((ℓg'.mapHomologicalComplex _).obj K)
  have h2 := homotopySquareIso_hom_app τg' K
  have h3 := Functor.mapHomotopyCategoryCompIso_hom_app_quotient μ'
    ((E₃.mapHomologicalComplex _).obj K)
  have h4 := Functor.mapHomotopyCategoryCompIso_hom_app_quotient μ K
  have h5 := homotopySquareIso_hom_app τgg K
  refine Eq.trans ?_ ((congrArg₂ (· ≫ ·) (congrArg _ h4) h5).symm)
  refine Eq.trans (congrArg₂ (· ≫ ·) h1 (congrArg₂ (· ≫ ·) (congrArg _ h2) h3)) ?_
  refine (congrArg (_ ≫ ·) ((HomotopyCategory.quotient B₁ _).map_comp _ _).symm).trans ?_
  refine ((HomotopyCategory.quotient B₁ _).map_comp _ _).symm.trans ?_
  refine Eq.trans ?_ ((HomotopyCategory.quotient B₁ _).map_comp _ _)
  congr 1
  ext n
  exact hU (K.X n)

/-- `AlgebraicGeometry.Space.homotopySquareIso_comp_app` with the composition isomorphisms on
homotopy categories given as a composition isomorphism followed by an induced isomorphism, the
form of `Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso`
followed by a 2-isomorphism. -/
theorem homotopySquareIso_comp_app_of_trans {H : A₃ ⥤ A₁} {H' : B₃ ⥤ B₁} [H.Additive]
    [H'.Additive] (μ₀ : ℓg' ⋙ ℓg ≅ H) (ν : H ≅ ℓgg) (μ₀' : kf' ⋙ kf ≅ H') (ν' : H' ≅ kff)
    (τg : ℓg ⋙ E₁ ≅ E₂ ⋙ kf) (τg' : ℓg' ⋙ E₂ ≅ E₃ ⋙ kf') (τgg : ℓgg ⋙ E₁ ≅ E₃ ⋙ kff)
    (hU : ∀ X, τg.hom.app (ℓg'.obj X) ≫ kf.map (τg'.hom.app X) ≫ (μ₀' ≪≫ ν').hom.app (E₃.obj X) =
      E₁.map ((μ₀ ≪≫ ν).hom.app X) ≫ τgg.hom.app X)
    (M : HomotopyCategory A₃ (ComplexShape.up ℤ)) :
    (homotopySquareIso τg).hom.app ((ℓg'.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (kf.mapHomotopyCategory (ComplexShape.up ℤ)).map ((homotopySquareIso τg').hom.app M) ≫
        (Functor.mapHomotopyCategoryCompIso μ₀' (ComplexShape.up ℤ) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso ν' (ComplexShape.up ℤ)).hom.app
          ((E₃.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      (E₁.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso μ₀ (ComplexShape.up ℤ) ≪≫
            Stacks.Homology.mapHomotopyCategoryIso ν (ComplexShape.up ℤ)).hom.app M) ≫
        (homotopySquareIso τgg).hom.app M := by
  rw [Stacks.Homology.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso,
    Stacks.Homology.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso]
  exact homotopySquareIso_comp_app _ _ τg τg' τgg hU M

/-- **Coherence on homotopy categories from coherence on modules**, in the form
`AlgebraicGeometry.Space.IsCompSquareCoherent`: degreewise comparisons compatible with the
composition isomorphisms on modules are compatible with the induced ones on homotopy
categories. -/
theorem isCompSquareCoherent_homotopySquareIso {H : A₃ ⥤ A₁} {H' : B₃ ⥤ B₁} [H.Additive]
    [H'.Additive] (μ₀ : ℓg' ⋙ ℓg ≅ H) (ν : H ≅ ℓgg) (μ₀' : kf' ⋙ kf ≅ H') (ν' : H' ≅ kff)
    (τg : ℓg ⋙ E₁ ≅ E₂ ⋙ kf) (τg' : ℓg' ⋙ E₂ ≅ E₃ ⋙ kf') (τgg : ℓgg ⋙ E₁ ≅ E₃ ⋙ kff)
    (hU : IsCompSquareCoherent (μ₀ ≪≫ ν) (μ₀' ≪≫ ν') τg τg' τgg) :
    IsCompSquareCoherent
      (Functor.mapHomotopyCategoryCompIso μ₀ (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso ν (ComplexShape.up ℤ))
      (Functor.mapHomotopyCategoryCompIso μ₀' (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso ν' (ComplexShape.up ℤ))
      (homotopySquareIso τg) (homotopySquareIso τg') (homotopySquareIso τgg) :=
  fun M => homotopySquareIso_comp_app_of_trans μ₀ ν μ₀' ν' τg τg' τgg hU M

end HomotopyCoherence

/-! ### Base change of charts over the two bases -/

section BaseChange

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
  (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)

include hfg in
/-- **The extension of a base-changed chart is a base change.** For a chart `a : h_U ⟶ Z₂` of
`Z₂`, the extension along `h` of the base change of `a` along `f` is a fibre product of `g` and
of the extension of `a`, read through `ε₁` and `ε₂`: the lower-shriek extension preserves fibre
products. -/
theorem isPullback_relocalizeChart_fst {U : BigFppfOver B W hW} (a : yoneda.obj U ⟶ Z₂.1) :
    IsPullback (relocalizeChart B W S hW hS h (hf.fst a) ≫ ε₁.hom)
      (yoneda.map ((Over.map h).map (hf.snd a))) g.hom
      (relocalizeChart B W S hW hS h a ≫ ε₂.hom) := by
  have := relocalizePresheaf_preservesConnectedLimits (K := WalkingCospan) h
  have h₁ := (OverShriek.relocalizePresheafFunctor h).map_isPullback (hf.isPullback a)
  refine h₁.of_iso (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h (hf.pullback a)) ε₁
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U) ε₂ ?_ ?_ hfg.symm ?_
  · simp [relocalizeChart]
  · exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h (hf.snd a)
  · simp [relocalizeChart]

/-- The scheme of the extension of the base change along `f` of a chart of `Z₂` is the scheme of
the base change along `g` of its extension. -/
def relocalizeChartPullbackIso (V : SmallEtale B W hW Z₂.1) :
    (Over.map h).obj (hf.pullback V.1.hom) ≅
      hg.pullback ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V).1.hom :=
  Yoneda.fullyFaithful.preimageIso
    ((isPullback_relocalizeChart_fst B h ε₁ ε₂ hfg hf V.1.hom).isoIsPullback _ _
      (hg.isPullback ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V).1.hom))

/-- `AlgebraicGeometry.Space.relocalizeChartPullbackIso` is compatible with the first
projections of the two fibre products. -/
theorem relocalizeChartPullbackIso_hom_fst (V : SmallEtale B W hW Z₂.1) :
    yoneda.map (relocalizeChartPullbackIso B h ε₁ ε₂ hfg hf hg V).hom ≫
        hg.fst ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V).1.hom =
      relocalizeChart B W S hW hS h (hf.fst V.1.hom) ≫ ε₁.hom := by
  simp only [relocalizeChartPullbackIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  apply IsPullback.isoIsPullback_hom_fst

/-- `AlgebraicGeometry.Space.relocalizeChartPullbackIso` followed by the second projection to
the extended chart is the extension of the second projection of the base change along `f`. -/
theorem relocalizeChartPullbackIso_hom_snd (V : SmallEtale B W hW Z₂.1) :
    (relocalizeChartPullbackIso B h ε₁ ε₂ hfg hf hg V).hom ≫
        hg.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V).1.hom =
      (Over.map h).map (hf.snd V.1.hom) := by
  apply yoneda.map_injective
  simp only [relocalizeChartPullbackIso, Functor.FullyFaithful.preimageIso_hom, Functor.map_comp,
    Functor.FullyFaithful.map_preimage]
  apply IsPullback.isoIsPullback_hom_snd

/-- The chart of `Y₁` extending the base change along `f` of a chart `V` of `Z₂` is the base
change along `g` of the chart of `Y₂` extending `V`. -/
def relocalizeBaseChangeChartIso (V : SmallEtale B W hW Z₂.1) :
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.obj
        ((smallBaseChange B W hW f hf).obj V) ≅
      (smallBaseChange B S hS g hg).obj
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V) :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk (relocalizeChartPullbackIso B h ε₁ ε₂ hfg hf hg V)
    (relocalizeChartPullbackIso_hom_fst B h ε₁ ε₂ hfg hf hg V))

/-- The underlying morphism of schemes of `AlgebraicGeometry.Space.relocalizeBaseChangeChartIso`
is `AlgebraicGeometry.Space.relocalizeChartPullbackIso`. -/
theorem relocalizeBaseChangeChartIso_hom_left (V : SmallEtale B W hW Z₂.1) :
    (relocalizeBaseChangeChartIso B h ε₁ ε₂ hfg hf hg V).hom.hom.left =
      (relocalizeChartPullbackIso B h ε₁ ε₂ hfg hf hg V).hom :=
  rfl

/-- `AlgebraicGeometry.Space.relocalizeBaseChangeChartIso` followed by the second projection to
the extended chart is the extension of the second projection of the base change along `f`. -/
@[reassoc]
theorem relocalizeBaseChangeChartIso_hom_snd (V : SmallEtale B W hW Z₂.1) :
    (relocalizeBaseChangeChartIso B h ε₁ ε₂ hfg hf hg V).hom.hom.left ≫
        hg.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj V).1.hom =
      (Over.map h).map (hf.snd V.1.hom) :=
  relocalizeChartPullbackIso_hom_snd B h ε₁ ε₂ hfg hf hg V

/-- **Base change of charts commutes with the change of base**: extending charts along `h` and
then base changing along `g` is base changing along `f` and then extending. -/
def relocalizeBaseChangeNatIso :
    smallBaseChange B W hW f hf ⋙ (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor ≅
      (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor ⋙ smallBaseChange B S hS g hg :=
  NatIso.ofComponents (relocalizeBaseChangeChartIso B h ε₁ ε₂ hfg hf hg) fun {V V'} k => by
    refine smallBaseChange_hom_ext B hg _ _ ?_
    have e₁ := relocalizeBaseChangeChartIso_hom_snd B h ε₁ ε₂ hfg hf hg V
    have e₂ := relocalizeBaseChangeChartIso_hom_snd B h ε₁ ε₂ hfg hf hg V'
    dsimp only [smallBaseChange, Functor.comp_obj, Functor.comp_map,
      ObjectProperty.FullSubcategory.comp_hom, CostructuredArrow.comp_left,
      ObjectProperty.homMk_hom, CostructuredArrow.homMk_left] at e₁ e₂ ⊢
    rw [Category.assoc, Category.assoc, e₂, hg.lift_snd, ← Category.assoc, e₁,
      smallerBaseSmallEtaleEquivalenceOfIso_functor_map_hom_left]
    exact ((Over.map h).map_comp _ _).symm.trans
      ((congrArg (fun t => (Over.map h).map t) (hf.lift_snd _ _ _)).trans
        ((Over.map h).map_comp _ _))

/-- The extended base change along `f` followed by extension, as a continuous functor. -/
instance isContinuous_smallBaseChange_comp_smallerBase :
    (smallBaseChange B W hW f hf ⋙
        (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor).IsContinuous
      (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₁.1) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B W hW Z₁.1) _

/-- Extension followed by base change along `g`, as a continuous functor. -/
instance isContinuous_smallerBase_comp_smallBaseChange :
    ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor ⋙
        smallBaseChange B S hS g hg).IsContinuous
      (SmallEtale.topology B W hW Z₂.1) (SmallEtale.topology B S hS Y₁.1) :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS Y₂.1) _

/-- **The base-change direct images commute with the change of base**: pushing forward along
base change of charts of `g` and then transporting to `Z₂` is transporting to `Z₁` and then
pushing forward along base change of charts of `f`. The two composites are pushforwards along the
two composites of site functors compared by `AlgebraicGeometry.Space.relocalizeBaseChangeNatIso`,
whose structure maps agree since the two cartesian projections do. -/
def smallerBaseChartPushforwardIso :
    smallBaseChangeModulePushforward.{u, u} B S hS g hg ⋙
        (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ⋙
        smallBaseChangeModulePushforward.{u, u} B W hW f hf :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardCongr₂ _ (relocalizeBaseChangeNatIso B h ε₁ ε₂ hfg hf hg) (by
      apply ObjectProperty.hom_ext
      refine NatTrans.ext (funext fun V => ?_)
      change (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map
            ((BigFppfOver.toScheme B S hS).map
              (hg.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj
                V.unop).1.hom)).op) ≫
          (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((relocalizeBaseChangeNatIso B h ε₁ ε₂ hfg hf hg).hom.app V.unop).hom.left).op) =
        (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B W hW).map
            (hf.snd V.unop.1.hom)).op)
      refine ((forget₂ CommRingCat.{u} RingCat.{u}).map_comp _ _).symm.trans ?_
      refine congrArg (fun q => (forget₂ CommRingCat.{u} RingCat.{u}).map q) ?_
      refine (Scheme.Γ.map_comp _ _).symm.trans ?_
      refine congrArg (fun q => Scheme.Γ.map q) ?_
      refine op_comp.symm.trans ?_
      refine congrArg Quiver.Hom.op ?_
      refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ?_
      exact congrArg (fun q => (BigFppfOver.toScheme B S hS).map q)
        (relocalizeBaseChangeChartIso_hom_snd B h ε₁ ε₂ hfg hf hg V.unop)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- **The direct images of modules commute with the change of base**, for representable
morphisms: `g_* ⋙ (−)' ≅ (−)' ⋙ f_*` for the direct images of modules of the morphisms of small
étale ringed topoi of `g` and of `f`. Both are compared with the base-change direct images
(`AlgebraicGeometry.Space.modulePushforwardChartIso`), which commute with the change of base by
`AlgebraicGeometry.Space.smallerBaseChartPushforwardIso`. -/
def smallerBasePushforwardIso :
    (smallEtaleRingedToposHom B S hS g).pushforwardModules ⋙
        (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ⋙
        (smallEtaleRingedToposHom B W hW f).pushforwardModules :=
  Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS g ≪≫
      modulePushforwardChartIso B S hS g hg) _ ≪≫
    smallerBaseChartPushforwardIso B h ε₁ ε₂ hfg hf hg ≪≫
    Functor.isoWhiskerLeft _ (pushforwardModulesIsoModulePushforward B W hW f ≪≫
      modulePushforwardChartIso B W hW f hf).symm

/-- `AlgebraicGeometry.Space.smallerBasePushforwardIso` as a square of functors. -/
abbrev smallerBasePushforwardSquare :
    TwoSquare (smallEtaleRingedToposHom B S hS g).pushforwardModules
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor
      (smallerBaseModulesEquivalenceOfIso B h ε₂).functor
      (smallEtaleRingedToposHom B W hW f).pushforwardModules :=
  (smallerBasePushforwardIso B h ε₁ ε₂ hfg hf hg).hom

/-- The square `AlgebraicGeometry.Space.smallerBasePushforwardSquare` is an isomorphism. -/
instance isIso_smallerBasePushforwardSquare :
    IsIso (smallerBasePushforwardSquare B h ε₁ ε₂ hfg hf hg) :=
  inferInstanceAs (IsIso (smallerBasePushforwardIso B h ε₁ ε₂ hfg hf hg).hom)

/-- The mate of `AlgebraicGeometry.Space.smallerBasePushforwardSquare` under the adjunctions
`g^* ⊣ g_*` and `f^* ⊣ f_*`. -/
abbrev smallerBasePullbackSquare :
    TwoSquare (smallerBaseModulesEquivalenceOfIso B h ε₂).functor
      (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
      (smallEtaleRingedToposHom B W hW f).toModulesHom.pullbackModules
      (smallerBaseModulesEquivalenceOfIso B h ε₁).functor :=
  (mateEquiv (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B W hW f))).symm
      (smallerBasePushforwardSquare B h ε₁ ε₂ hfg hf hg)

/-- The square `AlgebraicGeometry.Space.smallerBasePullbackSquare` is an isomorphism. -/
instance isIso_smallerBasePullbackSquare :
    IsIso (smallerBasePullbackSquare B h ε₁ ε₂ hfg hf hg) :=
  isIso_mateEquiv_symm_of_equivalence (G := smallerBaseModulesEquivalenceOfIso B h ε₂)
    (H := smallerBaseModulesEquivalenceOfIso B h ε₁)
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B W hW f))
    (smallerBasePushforwardSquare B h ε₁ ε₂ hfg hf hg)
    (isIso_smallerBasePushforwardSquare B h ε₁ ε₂ hfg hf hg)

/-- **The inverse images of modules commute with the change of base**, for representable
morphisms: `g^* ⋙ (−)' ≅ (−)' ⋙ f^*`, the mate of
`AlgebraicGeometry.Space.smallerBasePushforwardIso` under the adjunctions `g^* ⊣ g_*` and
`f^* ⊣ f_*` of the morphisms of small étale ringed topoi. -/
def smallerBasePullbackIso :
    (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules ⋙
        (smallerBaseModulesEquivalenceOfIso B h ε₁).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε₂).functor ⋙
        (smallEtaleRingedToposHom B W hW f).toModulesHom.pullbackModules :=
  (asIso (smallerBasePullbackSquare B h ε₁ ε₂ hfg hf hg)).symm

end BaseChange

/-! ### The derived categories, Stacks 04SG -/

section Derived

variable [HasDerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)]
  [HasDerivedCategory (Modules.{u, u} B W hW Z.1 Z.2)]

/-- **The derived categories of `Y` and of `Z` are equivalent**, `D(𝒪_Y) ≌ D(𝒪_Z)`: the
equivalence induced on derived categories by the exact equivalence
`AlgebraicGeometry.Space.smallerBaseModulesEquivalenceOfIso` of module categories. Its functor
is `CategoryTheory.Functor.mapDerivedCategory` of the module equivalence. -/
def smallerBaseDerivedEquivalence :
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ≌
      DerivedCategory (Modules.{u, u} B W hW Z.1 Z.2) :=
  letI := Stacks.DerivedCategory.mapDerivedCategory_isEquivalence
    (smallerBaseModulesEquivalenceOfIso B h ε)
  (smallerBaseModulesEquivalenceOfIso B h ε).functor.mapDerivedCategory.asEquivalence

/-- The functor of `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` is the functor
induced on derived categories by `AlgebraicGeometry.Space.smallerBaseModulesEquivalenceOfIso`. -/
theorem smallerBaseDerivedEquivalence_functor :
    (smallerBaseDerivedEquivalence B h ε).functor =
      (smallerBaseModulesEquivalenceOfIso B h ε).functor.mapDerivedCategory :=
  rfl

/-- The functor of `AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` on the image of a
complex is the image of the degreewise transported complex. -/
def smallerBaseDerivedEquivalenceFactors :
    DerivedCategory.Q ⋙ (smallerBaseDerivedEquivalence B h ε).functor ≅
      (smallerBaseModulesEquivalenceOfIso B h ε).functor.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (smallerBaseModulesEquivalenceOfIso B h ε).functor.mapDerivedCategoryFactors

/-! ### Pseudo-coherence -/

/-- Restriction to a chart is right exact on the small étale ringed site of an algebraic
space. -/
local instance overFunctorPreservesFiniteColimits_smallerBase {T : Scheme.{u}}
    {hT : B.Contains T} (X : AlgebraicSpaces B T hT) (U : (smallEtaleRingedSite B T hT X.1 X.2).C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT X.1 X.2).O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- Restriction to a chart is left exact on the small étale ringed site of an algebraic
space. -/
local instance overFunctorPreservesFiniteLimits_smallerBase {T : Scheme.{u}}
    {hT : B.Contains T} (X : AlgebraicSpaces B T hT) (U : (smallEtaleRingedSite B T hT X.1 X.2).C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B T hT X.1 X.2).O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- An object of `D(𝒪_X)` is pseudo-coherent exactly when a complex representing it is. -/
theorem isPseudoCoherent_iff_isPseudoCoherentComplex_of_iso {T : Scheme.{u}}
    {hT : B.Contains T} {X : AlgebraicSpaces B T hT}
    [HasDerivedCategory (Modules.{u, u} B T hT X.1 X.2)]
    {L : CochainComplex (Modules.{u, u} B T hT X.1 X.2) ℤ}
    {E : DerivedCategory (Modules.{u, u} B T hT X.1 X.2)} (e : DerivedCategory.Q.obj L ≅ E) :
    (smallEtaleRingedSite B T hT X.1 X.2).IsPseudoCoherent E ↔
      (smallEtaleRingedSite B T hT X.1 X.2).IsPseudoCoherentComplex L := by
  refine ⟨fun ⟨K, hK, ⟨eK⟩⟩ m => ?_, fun hL => ⟨L, hL, ⟨e⟩⟩⟩
  exact (RingedSite.isPseudoCoherentFrom_iff_isPseudoCoherentComplexFrom _ e m).1
    ⟨K, hK m, ⟨eK⟩⟩

/-- **Pseudo-coherence over the smaller base** (Stacks 08FT): an object of `D(𝒪_Y)` is
pseudo-coherent exactly when the corresponding object of `D(𝒪_Z)` is. Reindexing along an
equivalence of ringed sites preserves and reflects pseudo-coherence of complexes
(`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_reindex_iff`). -/
theorem isPseudoCoherent_smallerBaseDerivedEquivalence_iff
    (K : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    (smallEtaleRingedSite B W hW Z.1 Z.2).IsPseudoCoherent
        ((smallerBaseDerivedEquivalence B h ε).functor.obj K) ↔
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent K := by
  let eL := DerivedCategory.Q.objObjPreimageIso K
  let L := DerivedCategory.Q.objPreimage K
  let eL' : DerivedCategory.Q.obj
      (((smallerBaseModulesEquivalenceOfIso B h ε).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) ≅ (smallerBaseDerivedEquivalence B h ε).functor.obj K :=
    ((smallerBaseDerivedEquivalenceFactors B h ε).app L).symm ≪≫
      (smallerBaseDerivedEquivalence B h ε).functor.mapIso eL
  rw [isPseudoCoherent_iff_isPseudoCoherentComplex_of_iso B eL',
    isPseudoCoherent_iff_isPseudoCoherentComplex_of_iso B eL]
  have := Stacks.SheafOfModules.isDenseSubsite_inverse_of_isContinuous
    (J := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
    (J' := (smallEtaleRingedSite B W hW Z.1 Z.2).J) (smallerBaseSmallEtaleEquivalenceOfIso B h ε)
  exact forall_congr' fun m =>
    RingedSite.isPseudoCoherentComplexFrom_reindex_iff (smallEtaleRingedSite B S hS Y.1 Y.2)
      (smallEtaleRingedSite B W hW Z.1 Z.2).J (smallerBaseSmallEtaleEquivalenceOfIso B h ε) L m

end Derived


/-! ### The derived pullbacks, Stacks 04SG and 06YY -/

section DerivedPullback

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

attribute [local instance] HasDerivedCategory.standard

/-- An additive functor which preserves homology and reflects isomorphisms preserves and
reflects quasi-isomorphisms on homotopy categories. -/
theorem mem_quasiIso_mapHomotopyCategory_map_iff {A A' : Type*} [Category* A] [Abelian A]
    [Category* A'] [Abelian A'] (F : A ⥤ A') [F.Additive] [F.PreservesHomology]
    [F.ReflectsIsomorphisms] {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (t : X ⟶ Y) :
    HomotopyCategory.quasiIso A' (ComplexShape.up ℤ)
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map t) ↔
      HomotopyCategory.quasiIso A (ComplexShape.up ℤ) t := by
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective t
  change HomotopyCategory.quasiIso A' (ComplexShape.up ℤ) ((HomotopyCategory.quotient A' _).map
    ((F.mapHomologicalComplex _).map φ)) ↔ _
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology φ F).trans
    (HomotopyCategory.quotient_map_mem_quasiIso_iff φ).symm

/-- `AlgebraicGeometry.Space.smallerBaseModulesEquivalenceOfIso` with the module categories
spelled as those of the small étale ringed topoi, the spelling of the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
def smallerBaseToposModulesEquivalence :
    SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y) ≌
      SheafOfModules.{u} (ringedToposStructureRingSheaf B W hW Z) :=
  smallerBaseModulesEquivalenceOfIso B h ε

/-- The functor of `AlgebraicGeometry.Space.smallerBaseToposModulesEquivalence` is additive. -/
instance smallerBaseToposModulesEquivalence_functor_additive :
    (smallerBaseToposModulesEquivalence B h ε).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of `AlgebraicGeometry.Space.smallerBaseToposModulesEquivalence` is additive. -/
instance smallerBaseToposModulesEquivalence_inverse_additive :
    (smallerBaseToposModulesEquivalence B h ε).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor of `AlgebraicGeometry.Space.smallerBaseToposModulesEquivalence` preserves
homology. -/
instance smallerBaseToposModulesEquivalence_functor_preservesHomology :
    (smallerBaseToposModulesEquivalence B h ε).functor.PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The functor induced on homotopy categories by
`AlgebraicGeometry.Space.smallerBaseToposModulesEquivalence` is an equivalence. -/
instance smallerBaseToposModulesEquivalence_functor_mapHomotopyCategory_isEquivalence :
    ((smallerBaseToposModulesEquivalence B h ε).functor.mapHomotopyCategory
      (ComplexShape.up ℤ)).IsEquivalence :=
  Stacks.DerivedFunctor.isEquivalence_mapHomotopyCategory _

/-- The equivalence of homotopy categories of complexes of modules on `Y` and on `Z`. -/
abbrev smallerBaseHomotopyEquivalence :
    HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) ≌
      HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B W hW Z))
        (ComplexShape.up ℤ) :=
  ((smallerBaseToposModulesEquivalence B h ε).functor.mapHomotopyCategory
    (ComplexShape.up ℤ)).asEquivalence

/-- The functor of `AlgebraicGeometry.Space.smallerBaseHomotopyEquivalence` preserves and
reflects quasi-isomorphisms. -/
theorem mem_quasiIso_smallerBaseHomotopyEquivalence_functor_map_iff
    {X X' : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ)} (t : X ⟶ X') :
    HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
        ((smallerBaseHomotopyEquivalence B h ε).functor.map t) ↔
      HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) t :=
  mem_quasiIso_mapHomotopyCategory_map_iff _ t

/-- The inverse of `AlgebraicGeometry.Space.smallerBaseHomotopyEquivalence` preserves
quasi-isomorphisms. -/
theorem mem_quasiIso_smallerBaseHomotopyEquivalence_inverse_map
    {X X' : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B W hW Z))
      (ComplexShape.up ℤ)} (t : X ⟶ X')
    (ht : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ) t) :
    HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
      ((smallerBaseHomotopyEquivalence B h ε).inverse.map t) := by
  rw [← mem_quasiIso_smallerBaseHomotopyEquivalence_functor_map_iff, Equivalence.fun_inv_map]
  exact MorphismProperty.RespectsIso.precomp _ _ _ (MorphismProperty.RespectsIso.postcomp _ _ _ ht)

/-- The inverse image of modules along the morphism of small étale ringed topoi of `a` is
additive. -/
instance smallEtaleRingedToposHom_pullbackModules_additive {T : Scheme.{u}} {hT : B.Contains T}
    {X X' : AlgebraicSpaces B T hT} (a : X ⟶ X') :
    (smallEtaleRingedToposHom B T hT a).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B T hT a)

/-- The inverse image of modules along the composite
`AlgebraicGeometry.Space.smallEtaleRingedToposHomComp` of morphisms of small étale ringed topoi
is additive. -/
instance smallEtaleRingedToposHomComp_pullbackModules_additive {T : Scheme.{u}}
    {hT : B.Contains T} {X X' X'' : AlgebraicSpaces B T hT} (a : X ⟶ X') (b : X' ⟶ X'') :
    (smallEtaleRingedToposHomComp B T hT a b).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHomComp B T hT a b)

/-- **The composition isomorphism of Stacks 0D6D for algebraic spaces, at the image of a
complex**: followed by the comparison of the derived pullback along the composite, it is the
comparison for `g`, then the one for `f`, then the underived compositor followed by the
2-isomorphism `AlgebraicGeometry.Space.pullbackModulesCompTransport`. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_app_comparison_compTransport {T : Scheme.{u}}
    {hT : B.Contains T} {X X' X'' : AlgebraicSpaces B T hT} (a : X ⟶ X') (b : X' ⟶ X'')
    (K : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B T hT X''))
      (ComplexShape.up ℤ)) :
    (smallEtaleDerivedModulePullbackCompIso B T hT a b).hom.app (DerivedCategory.Qh.obj K) ≫
        (smallEtaleDerivedModulePullbackComparison B T hT (a ≫ b)).app K =
      (smallEtaleDerivedModulePullback B T hT a).map
          ((smallEtaleDerivedModulePullbackComparison B T hT b).app K) ≫
        (smallEtaleDerivedModulePullbackComparison B T hT a).app
          ((Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy
            (smallEtaleRingedToposHom B T hT b)).obj K) ≫
        DerivedCategory.Qh.map ((pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B T hT a)
            (smallEtaleRingedToposHom B T hT b) ≪≫
          Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B T hT a b)
            (ComplexShape.up ℤ)).hom.app K) := by
  have := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
    (smallEtaleRingedToposHom B T hT a) (smallEtaleRingedToposHom B T hT b)
    (pullbackModulesCompTransport B T hT a b) K
  exact (Category.assoc _ _ _).trans this

section Pullback

variable {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
  (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)

/-- `AlgebraicGeometry.Space.smallerBasePullbackIso` in the ringed-topos spelling. -/
def smallerBaseToposPullbackIso :
    (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules ⋙
        (smallerBaseToposModulesEquivalence B h ε₁).functor ≅
      (smallerBaseToposModulesEquivalence B h ε₂).functor ⋙
        (smallEtaleRingedToposHom B W hW f).toModulesHom.pullbackModules :=
  smallerBasePullbackIso B h ε₁ ε₂ hfg hf hg

/-- Degreewise pullback commutes with the change of base on homotopy categories:
`AlgebraicGeometry.Space.smallerBasePullbackIso` applied degreewise. -/
def smallerBaseHomotopyPullbackIso :
    (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (smallerBaseHomotopyEquivalence B h ε₁).functor ≅
      (smallerBaseHomotopyEquivalence B h ε₂).functor ⋙
        (smallEtaleRingedToposHom B W hW f).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (smallerBaseToposPullbackIso B h ε₁ ε₂ hfg hf hg) _ ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm

/-- Degreewise pullback followed by localization commutes with the change of base, on homotopy
categories. -/
def smallerBasePullbackOnHomotopyIso :
    smallEtaleModulePullbackOnHomotopy B S hS g ⋙
        (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory ≅
      (smallerBaseHomotopyEquivalence B h ε₂).functor ⋙
        smallEtaleModulePullbackOnHomotopy B W hW f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (smallerBaseHomotopyPullbackIso B h ε₁ ε₂ hfg hf hg)
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- The component of `AlgebraicGeometry.Space.smallerBasePullbackOnHomotopyIso` at `N` is the
factorization isomorphism of the change of base on derived categories followed by the
localization of `AlgebraicGeometry.Space.smallerBaseHomotopyPullbackIso`. -/
theorem smallerBasePullbackOnHomotopyIso_hom_app
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₂))
      (ComplexShape.up ℤ)) :
    (smallerBasePullbackOnHomotopyIso B h ε₁ ε₂ hfg hf hg).hom.app N =
      (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategoryFactorsh.hom.app
          (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategory
            (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((smallerBaseHomotopyPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app N) := by
  simp only [smallerBasePullbackOnHomotopyIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- The derived pullback along `g` followed by the change of base is a left derived functor of
degreewise pullback along `g` followed by the change of base. -/
theorem isLeftDerivedFunctor_smallEtaleDerivedModulePullback_comp_smallerBase :
    (smallEtaleDerivedModulePullback B S hS g ⋙
        (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (smallEtaleDerivedModulePullbackComparison B S hS g)
          (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory)
      (smallEtaleModuleQuasiIso B S hS Y₂) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions _
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Y₂))
    (hasResolutions_isKFlat' (Y := smallEtaleRingedTopos B S hS Y₂)) _
    (pullbackInvertsQuasiIso_isKFlat (smallEtaleRingedToposHom B S hS g)) DerivedCategory.Qh _ _ _

/-- The comparison exhibiting the change of base followed by the derived pullback along `f` as
a left derived functor of degreewise pullback along `g` followed by the change of base. -/
abbrev smallerBaseDerivedPullbackCounit :=
  transferCounit (smallEtaleDerivedModulePullback B W hW f)
    (smallEtaleDerivedModulePullbackComparison B W hW f) (smallerBaseHomotopyEquivalence B h ε₂)
    (smallerBaseToposModulesEquivalence B h ε₂).functor.mapDerivedCategory
    (smallerBaseToposModulesEquivalence B h ε₂).functor.mapDerivedCategoryFactorsh
    (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory
    (smallerBasePullbackOnHomotopyIso B h ε₁ ε₂ hfg hf hg)

/-- The change of base followed by the derived pullback along `f` is a left derived functor of
degreewise pullback along `g` followed by the change of base. -/
theorem isLeftDerivedFunctor_smallerBase_comp_smallEtaleDerivedModulePullback :
    ((smallerBaseToposModulesEquivalence B h ε₂).functor.mapDerivedCategory ⋙
        smallEtaleDerivedModulePullback B W hW f).IsLeftDerivedFunctor
      (smallerBaseDerivedPullbackCounit B h ε₁ ε₂ hfg hf hg)
      (smallEtaleModuleQuasiIso B S hS Y₂) :=
  isLeftDerivedFunctor_transfer _ _
    (hasResolutions_isKFlat' (Y := smallEtaleRingedTopos B W hW Z₂))
    (pullbackInvertsQuasiIso_isKFlat (smallEtaleRingedToposHom B W hW f))
    (fun X hX =>
      isIso_derivedPullbackComparison_app_isKFlat (smallEtaleRingedToposHom B W hW f) X hX)
    (smallerBaseHomotopyEquivalence B h ε₂)
    (fun s hs => (mem_quasiIso_smallerBaseHomotopyEquivalence_functor_map_iff B h ε₂ s).2 hs)
    (fun s hs => mem_quasiIso_smallerBaseHomotopyEquivalence_inverse_map B h ε₂ s hs) _ _ _ _

/-- **Stacks 04SG for derived pullbacks, in the ringed-topos spelling.** -/
def smallerBaseToposDerivedPullbackIso :
    smallEtaleDerivedModulePullback B S hS g ⋙
        (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory ≅
      (smallerBaseToposModulesEquivalence B h ε₂).functor.mapDerivedCategory ⋙
        smallEtaleDerivedModulePullback B W hW f :=
  haveI := isLeftDerivedFunctor_smallEtaleDerivedModulePullback_comp_smallerBase B h ε₁ (g := g)
  haveI := isLeftDerivedFunctor_smallerBase_comp_smallEtaleDerivedModulePullback B h ε₁ ε₂ hfg hf hg
  Functor.leftDerivedNatIso _ _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (smallEtaleDerivedModulePullbackComparison B S hS g)
        (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory)
    (smallerBaseDerivedPullbackCounit B h ε₁ ε₂ hfg hf hg)
    (smallEtaleModuleQuasiIso B S hS Y₂) (Iso.refl _)

/-- **The defining property of `AlgebraicGeometry.Space.smallerBaseToposDerivedPullbackIso`.** At
the image of a complex, followed by the change of base of the localization and by the comparison
of `Lf^*`, it is the change of base of the comparison of `Lg^*` followed by the underived
comparison. -/
theorem smallerBaseToposDerivedPullbackIso_hom_app_fac
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₂))
      (ComplexShape.up ℤ)) :
    (smallerBaseToposDerivedPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app (DerivedCategory.Qh.obj N) ≫
        (smallEtaleDerivedModulePullback B W hW f).map
          ((smallerBaseToposModulesEquivalence B h ε₂).functor.mapDerivedCategoryFactorsh.hom.app
            N) ≫
        (smallEtaleDerivedModulePullbackComparison B W hW f).app
          ((smallerBaseHomotopyEquivalence B h ε₂).functor.obj N) =
      (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory.map
          ((smallEtaleDerivedModulePullbackComparison B S hS g).app N) ≫
        (smallerBasePullbackOnHomotopyIso B h ε₁ ε₂ hfg hf hg).hom.app N := by
  have := isLeftDerivedFunctor_smallEtaleDerivedModulePullback_comp_smallerBase B h ε₁ (g := g)
  have := isLeftDerivedFunctor_smallerBase_comp_smallEtaleDerivedModulePullback B h ε₁ ε₂ hfg hf hg
  have key := Functor.leftDerivedNatTrans_app _ _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (smallEtaleDerivedModulePullbackComparison B S hS g)
        (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory)
    (smallerBaseDerivedPullbackCounit B h ε₁ ε₂ hfg hf hg)
    (smallEtaleModuleQuasiIso B S hS Y₂) (Iso.refl _).hom N
  simp only [smallerBaseDerivedPullbackCounit, transferCounit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerRight_app,
    Category.id_comp, Iso.refl_hom, NatTrans.id_app, Category.comp_id] at key
  rw [← key]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rfl

/-- **Stacks 04SG for derived pullbacks**: for representable morphisms `f : Z₁ ⟶ Z₂` over `W`
and `g : Y₁ ⟶ Y₂` over `S` matched by `Λ_h Zᵢ ≅ Yᵢ`, the change of base
`AlgebraicGeometry.Space.smallerBaseDerivedEquivalence` intertwines the derived pullbacks
`Lg^*` and `Lf^*` of Stacks 06YY: `Lg^* ⋙ (−)' ≅ (−)' ⋙ Lf^*`.

Both sides are left derived functors of degreewise pullback along `g` followed by the change
of base: the left one because a derived functor computed by resolutions stays one after
composition, the right one because degreewise pullback commutes with the change of base
(`AlgebraicGeometry.Space.smallerBasePullbackIso`, the mate of the comparison of direct images
of `AlgebraicGeometry.Space.smallerBasePushforwardIso`). -/
def smallerBaseDerivedPullbackIso :
    smallEtaleDerivedModulePullback B S hS g ⋙ (smallerBaseDerivedEquivalence B h ε₁).functor ≅
      (smallerBaseDerivedEquivalence B h ε₂).functor ⋙ smallEtaleDerivedModulePullback B W hW f :=
  smallerBaseToposDerivedPullbackIso B h ε₁ ε₂ hfg hf hg

end Pullback

section Comp

variable {Z₁ Z₂ Z₃ : AlgebraicSpaces B W hW} {Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  (ε₃ : (OverShriek.relocalizePresheafFunctor h).obj Z₃.1 ≅ Y₃.1)
  {f : Z₁ ⟶ Z₂} {f' : Z₂ ⟶ Z₃} {g : Y₁ ⟶ Y₂} {g' : Y₂ ⟶ Y₃}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
  (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
  (hfg' : ε₂.hom ≫ g'.hom = (OverShriek.relocalizePresheafFunctor h).map f'.hom ≫ ε₃.hom)
  (hf' : yoneda.relativelyRepresentable f'.hom) (hg' : yoneda.relativelyRepresentable g'.hom)
  (hfg'' : ε₁.hom ≫ (g ≫ g').hom =
    (OverShriek.relocalizePresheafFunctor h).map (f ≫ f').hom ≫ ε₃.hom)
  (hf'' : yoneda.relativelyRepresentable (f ≫ f').hom)
  (hg'' : yoneda.relativelyRepresentable (g ≫ g').hom)

/-- **The degreewise comparisons are compatible with Stacks 03D6, on modules**: the comparison
`AlgebraicGeometry.Space.smallerBaseToposPullbackIso` of the composite is the pasting of the
comparisons of `g, g'` (over `S`) and `f, f'` (over `W`), read through the compositor of Stacks
03D6 followed by the 2-isomorphism `AlgebraicGeometry.Space.pullbackModulesCompTransport` on both
sides. -/
def SmallerBasePullbackIsoCoherent : Prop :=
  IsCompSquareCoherent
    ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS g)
        (smallEtaleRingedToposHom B S hS g')).symm ≪≫ pullbackModulesCompTransport B S hS g g')
    ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B W hW f)
        (smallEtaleRingedToposHom B W hW f')).symm ≪≫ pullbackModulesCompTransport B W hW f f')
    (smallerBaseToposPullbackIso B h ε₁ ε₂ hfg hf hg)
    (smallerBaseToposPullbackIso B h ε₂ ε₃ hfg' hf' hg')
    (smallerBaseToposPullbackIso B h ε₁ ε₃ hfg'' hf'' hg'')

/-- `AlgebraicGeometry.Space.SmallerBasePullbackIsoCoherent` on homotopy categories: the
comparison `AlgebraicGeometry.Space.smallerBaseHomotopyPullbackIso` of the composite is the
pasting of the comparisons, read through the underived composition isomorphisms of Stacks 0D6D on
both sides. -/
def SmallerBaseHomotopyPullbackIsoCoherent : Prop :=
  IsCompSquareCoherent
    (pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B S hS g)
        (smallEtaleRingedToposHom B S hS g') ≪≫
      Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS g g')
        (ComplexShape.up ℤ))
    (pullbackMapHomotopyCompIso (smallEtaleRingedToposHom B W hW f)
        (smallEtaleRingedToposHom B W hW f') ≪≫
      Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B W hW f f')
        (ComplexShape.up ℤ))
    (smallerBaseHomotopyPullbackIso B h ε₁ ε₂ hfg hf hg)
    (smallerBaseHomotopyPullbackIso B h ε₂ ε₃ hfg' hf' hg')
    (smallerBaseHomotopyPullbackIso B h ε₁ ε₃ hfg'' hf'' hg'')

/-- The coherence on modules gives the coherence on homotopy categories, degreewise
(`AlgebraicGeometry.Space.isCompSquareCoherent_homotopySquareIso`). -/
theorem smallerBaseHomotopyPullbackIsoCoherent_of
    (hU : SmallerBasePullbackIsoCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg'') :
    SmallerBaseHomotopyPullbackIsoCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg'' :=
  isCompSquareCoherent_homotopySquareIso _ _ _ _ _ _ _ hU

/-- The defining property of `AlgebraicGeometry.Space.smallerBaseToposDerivedPullbackIso`, with
the comparison `smallerBasePullbackOnHomotopyIso` unfolded to the underived square. -/
private theorem smallerBaseToposDerivedPullbackIso_hom_app_fac_homotopy
    (N : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₂))
      (ComplexShape.up ℤ)) :
    (smallerBaseToposDerivedPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app (DerivedCategory.Qh.obj N) ≫
        (smallEtaleDerivedModulePullback B W hW f).map
          ((smallerBaseToposModulesEquivalence B h ε₂).functor.mapDerivedCategoryFactorsh.hom.app
            N) ≫
        (smallEtaleDerivedModulePullbackComparison B W hW f).app
          ((smallerBaseHomotopyEquivalence B h ε₂).functor.obj N) =
      (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory.map
          ((smallEtaleDerivedModulePullbackComparison B S hS g).app N) ≫
        ((smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategoryFactorsh.hom.app
          (((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules.mapHomotopyCategory
            (ComplexShape.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map
          ((smallerBaseHomotopyPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app N)) := by
  rw [smallerBaseToposDerivedPullbackIso_hom_app_fac,
    smallerBasePullbackOnHomotopyIso_hom_app]

include hfg hf hg hfg' hf' hg' hfg'' hf'' hg'' in
/-- **The derived comparison is compatible with Stacks 0D6D, in the ringed-topos spelling**,
given the coherence on homotopy categories
`AlgebraicGeometry.Space.SmallerBaseHomotopyPullbackIsoCoherent`: for composable representable
`f, f'` over `W` and `g, g'` over `S`, the comparison
`AlgebraicGeometry.Space.smallerBaseToposDerivedPullbackIso` of the composite is the composite of
the comparisons, read through the composition isomorphisms
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` on both sides.

All the isomorphisms involved are characterized on the images of complexes, and the claim follows
from `AlgebraicGeometry.Space.transfer_comp_app`. -/
theorem smallerBaseToposDerivedPullbackIso_comp_of_isCoherent
    (hU : SmallerBaseHomotopyPullbackIsoCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf''
      hg'')
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₃))) :
    (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory.map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g g').hom.app K) ≫
      (smallerBaseToposDerivedPullbackIso B h ε₁ ε₃ hfg'' hf'' hg'').hom.app K =
    (smallerBaseToposDerivedPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app
        ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
      (smallEtaleDerivedModulePullback B W hW f).map
        ((smallerBaseToposDerivedPullbackIso B h ε₂ ε₃ hfg' hf' hg').hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompIso B W hW f f').hom.app
        ((smallerBaseToposModulesEquivalence B h ε₃).functor.mapDerivedCategory.obj K) := by
  have := isLeftDerivedFunctor_smallerBase_comp_smallEtaleDerivedModulePullback B h ε₁ ε₃
    hfg'' hf'' hg''
  refine transfer_comp_app_of_isCompSquareCoherent (W₃ := smallEtaleModuleQuasiIso B S hS Y₃)
    _ _ _ _ _ _ _ _ _
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison_compTransport B g g') _
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison_compTransport B f f') _ _ _ _ _ _ _
    (smallerBaseToposDerivedPullbackIso_hom_app_fac_homotopy B h ε₁ ε₂ hfg hf hg) _
    (smallerBaseToposDerivedPullbackIso_hom_app_fac_homotopy B h ε₂ ε₃ hfg' hf' hg') _
    (smallerBaseToposDerivedPullbackIso_hom_app_fac_homotopy B h ε₁ ε₃ hfg'' hf'' hg'')
    (smallerBaseDerivedPullbackCounit B h ε₁ ε₃ hfg'' hf'' hg'') _
    (fun M => transferCounit_app _ _ _ _ _ _ _ M) hU K

include hfg hf hg hfg' hf' hg' hfg'' hf'' hg'' in
/-- **The derived comparison is compatible with Stacks 0D6D**, given its module-level
counterpart `AlgebraicGeometry.Space.SmallerBasePullbackIsoCoherent`: for composable
representable `f, f'` over `W` and `g, g'` over `S`, the comparison
`AlgebraicGeometry.Space.smallerBaseDerivedPullbackIso` of the composite is the composite of the
comparisons, read through the composition isomorphisms
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` on both sides. -/
theorem smallerBaseDerivedPullbackIso_comp_of_isCoherent
    (hU : SmallerBasePullbackIsoCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg'')
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₃))) :
    (smallerBaseDerivedEquivalence B h ε₁).functor.map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g g').hom.app K) ≫
      (smallerBaseDerivedPullbackIso B h ε₁ ε₃ hfg'' hf'' hg'').hom.app K =
    (smallerBaseDerivedPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app
        ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
      (smallEtaleDerivedModulePullback B W hW f).map
        ((smallerBaseDerivedPullbackIso B h ε₂ ε₃ hfg' hf' hg').hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompIso B W hW f f').hom.app
        ((smallerBaseDerivedEquivalence B h ε₃).functor.obj K) :=
  smallerBaseToposDerivedPullbackIso_comp_of_isCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg'
    hfg'' hf'' hg''
    (smallerBaseHomotopyPullbackIsoCoherent_of B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg''
      hU) K

end Comp

end DerivedPullback

end AlgebraicGeometry.Space

end
