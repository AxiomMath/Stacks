module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.Separated
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChowDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ProjectiveSpaceContracted
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Chow's lemma with an immersion into projective space over the target

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over a scheme `S`,
with `Y` separated and quasi-compact. [Stacks, Tag 089M] asserts that there are a proper
surjective `X' ⟶ X` and an immersion `X' ⟶ ℙⁿ_Y` over `Y`. This file proves it.

## Main results

* `AlgebraicGeometry.Space.exists_isProper_isSurjective_isImmersion_projectiveSpace`:
  **[Stacks, Tag 089M].**

## Implementation notes

Relative projective space `ℙⁿ_Y` is the fibre product `Y ×_S ℙⁿ_S`, taken in presheaves on the big
fppf site of `S` over the presheaf represented by `S`, which is terminal
(`AlgebraicGeometry.Space.isTerminal_yoneda_obj_base`); `ℙⁿ_S` is the object
`AlgebraicGeometry.Space.projectiveSpaceSiteObj` of the site, the base change of the integral model
`AlgebraicGeometry.projectiveSpaceOver`, which is the realisation of `ℙⁿ_Y` used by
`AlgebraicGeometry.Space.ProjectiveSpaceImmersion`. That `ℙⁿ_S` is an object of the site is part of
the conclusion, as is the integer `n`. "Separated" for `Y` is the absolute notion of
[Stacks, Tag 03BS], `AlgebraicGeometry.Space.IsAbsolutelySeparated`, which is the source's.

## References

* [Stacks Project, Tag 089M](https://stacks.math.columbia.edu/tag/089M)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 0873](https://stacks.math.columbia.edu/tag/0873)
* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 086Q](https://stacks.math.columbia.edu/tag/086Q)
* [Stacks Project, Tag 0828](https://stacks.math.columbia.edu/tag/0828)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

include hS in
/-- The fibre product `S ×_ℤ V` of the base with a scheme `V` contained in the site is
contained in the site. -/
private theorem contains_pullback_terminal {V : Scheme.{u}} (hV : B.Contains V) :
    B.Contains (pullback (terminal.from S) (terminal.from V)) :=
  B.contains_of_mono
    (Over.prodLeftIsoPullback (Over.mk (terminal.from S)) (Over.mk (terminal.from V))).inv
    (B.contains_prod_left _ _ hS hV)

/-- The base change `S ×_ℤ V` of a scheme `V` contained in the site, as an object of the big
fppf site of `S`. -/
private def intBaseChangeObj (V : Scheme.{u}) (hV : B.Contains V) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_pullback_terminal B S hS hV) (pullback.fst _ _)

/-- The base change `S ×_ℤ V ⟶ S ×_ℤ W` of a morphism of schemes. -/
private abbrev intBaseChangeMap {V W : Scheme.{u}} (g : V ⟶ W) :
    pullback (terminal.from S) (terminal.from V) ⟶ pullback (terminal.from S) (terminal.from W) :=
  pullback.map (terminal.from S) (terminal.from V) (terminal.from S) (terminal.from W)
    (𝟙 S) g (𝟙 _) (by simp) (terminal.hom_ext _ _)

/-- A multiplicative, base-change-stable property of morphisms of schemes is preserved by the base
change `S ×_ℤ V ⟶ S ×_ℤ W` of a morphism with this property. -/
private theorem intBaseChangeMap_mem (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] {V W : Scheme.{u}} {g : V ⟶ W} (hg : P g) :
    P (intBaseChangeMap S g) :=
  have := MorphismProperty.IsMultiplicative.toIsStableUnderComposition (W := P)
  MorphismProperty.pullbackMap (P.id_mem S) hg (by simp) (terminal.hom_ext _ _)

/-- The base change of a morphism of schemes lies over `S`. -/
private theorem intBaseChangeMap_fst {V W : Scheme.{u}} (g : V ⟶ W) :
    intBaseChangeMap S g ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp

/-- The second coordinate of the base change of `g` is `g`. -/
private theorem intBaseChangeMap_snd {V W : Scheme.{u}} (g : V ⟶ W) :
    intBaseChangeMap S g ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g := by
  simp

/-- Base change preserves identities. -/
private theorem intBaseChangeMap_id (V : Scheme.{u}) : intBaseChangeMap S (𝟙 V) = 𝟙 _ :=
  pullback.hom_ext (by simp) (by simp)

/-- Base change preserves composition. -/
private theorem intBaseChangeMap_comp {V W Z : Scheme.{u}} (g : V ⟶ W) (h : W ⟶ Z) :
    intBaseChangeMap S (g ≫ h) = intBaseChangeMap S g ≫ intBaseChangeMap S h :=
  pullback.hom_ext (by simp) (by simp)

/-- The base change `S ×_ℤ V ⟶ S ×_ℤ W` of a morphism of schemes, as a morphism of the big fppf
site of `S`. -/
private def intBaseChangeHom {V W : Scheme.{u}} (hV : B.Contains V) (hW : B.Contains W)
    (g : V ⟶ W) : intBaseChangeObj B S hS V hV ⟶ intBaseChangeObj B S hS W hW :=
  BigFppfOver.homMk B S hS _ _ (intBaseChangeMap S g) (intBaseChangeMap_fst S g)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.intBaseChangeHom`. -/
private theorem toScheme_map_intBaseChangeHom {V W : Scheme.{u}} (hV : B.Contains V)
    (hW : B.Contains W) (g : V ⟶ W) :
    (BigFppfOver.toScheme B S hS).map (intBaseChangeHom B S hS hV hW g) = intBaseChangeMap S g :=
  rfl

/-- The base change of an identity is an identity of the site. -/
private theorem intBaseChangeHom_id {V : Scheme.{u}} (hV : B.Contains V) :
    intBaseChangeHom B S hS hV hV (𝟙 V) = 𝟙 _ := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  dsimp only
  rw [CategoryTheory.Functor.map_id]
  exact intBaseChangeMap_id S V

/-- The base change of a composite is the composite in the site. -/
private theorem intBaseChangeHom_comp {V W Z : Scheme.{u}} (hV : B.Contains V) (hW : B.Contains W)
    (hZ : B.Contains Z) (g : V ⟶ W) (h : W ⟶ Z) :
    intBaseChangeHom B S hS hV hZ (g ≫ h) =
      intBaseChangeHom B S hS hV hW g ≫ intBaseChangeHom B S hS hW hZ h := by
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  dsimp only
  rw [CategoryTheory.Functor.map_comp]
  exact intBaseChangeMap_comp S g h

/-- The base change `S ×_ℤ -` of a diagram of schemes contained in the site, as a diagram in the
big fppf site of `S`. -/
private def intBaseChangeDiagram {J : Type u} [Category.{u} J] (D : J ⥤ Scheme.{u})
    (hD : ∀ j, B.Contains (D.obj j)) : J ⥤ BigFppfOver B S hS where
  obj j := intBaseChangeObj B S hS (D.obj j) (hD j)
  map g := intBaseChangeHom B S hS (hD _) (hD _) (D.map g)
  map_id j := by
    rw [D.map_id]
    exact intBaseChangeHom_id B S hS (hD j)
  map_comp g h := by
    rw [D.map_comp]
    exact intBaseChangeHom_comp B S hS _ _ _ _ _

/-- The base change `S ×_ℤ -` of a cone of schemes contained in the site. -/
private def intBaseChangeCone {J : Type u} [Category.{u} J] {D : J ⥤ Scheme.{u}}
    (hD : ∀ j, B.Contains (D.obj j)) (c : Cone D) (hc : B.Contains c.pt) :
    Cone (intBaseChangeDiagram B S hS D hD) where
  pt := intBaseChangeObj B S hS c.pt hc
  π :=
    { app j := intBaseChangeHom B S hS hc (hD j) (c.π.app j)
      naturality j k g := by
        change 𝟙 _ ≫ intBaseChangeHom B S hS hc (hD k) (c.π.app k) =
          intBaseChangeHom B S hS hc (hD j) (c.π.app j) ≫ intBaseChangeHom B S hS _ _ (D.map g)
        rw [Category.id_comp, ← intBaseChangeHom_comp, c.w] }

/-- The base change along `S ⟶ Spec ℤ` of a limit cone of schemes over a connected index
category is a limit cone of schemes. -/
private def isLimitToSchemeMapIntBaseChangeCone {J : Type u} [Category.{u} J] [IsConnected J]
    {D : J ⥤ Scheme.{u}} (hD : ∀ j, B.Contains (D.obj j)) (c : Cone D) (hc : IsLimit c)
    (hcpt : B.Contains c.pt) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone (intBaseChangeCone B S hS hD c hcpt)) := by
  classical
  let j₀ : J := Classical.arbitrary J
  let K := intBaseChangeDiagram B S hS D hD ⋙ BigFppfOver.toScheme B S hS
  let fstK (j : J) : K.obj j ⟶ S := pullback.fst (terminal.from S) (terminal.from (D.obj j))
  let sndK (j : J) : K.obj j ⟶ D.obj j := pullback.snd (terminal.from S) (terminal.from (D.obj j))
  have hfstK {j k : J} (g : j ⟶ k) : K.map g ≫ fstK k = fstK j :=
    intBaseChangeMap_fst S (D.map g)
  have hsndK {j k : J} (g : j ⟶ k) : K.map g ≫ sndK k = sndK j ≫ D.map g :=
    intBaseChangeMap_snd S (D.map g)
  have hconst : ∀ (s : Cone K) (j : J), s.π.app j ≫ fstK j = s.π.app j₀ ≫ fstK j₀ := by
    intro s j
    refine constant_of_preserves_morphisms (fun j : J => s.π.app j ≫ fstK j) ?_ j j₀
    intro j k g
    change s.π.app j ≫ fstK j = s.π.app k ≫ fstK k
    rw [← s.w g, Category.assoc, hfstK]
  let coneD (s : Cone K) : Cone D :=
    { pt := s.pt
      π :=
        { app j := s.π.app j ≫ sndK j
          naturality j k g := by
            change 𝟙 _ ≫ s.π.app k ≫ sndK k = (s.π.app j ≫ sndK j) ≫ D.map g
            rw [Category.id_comp, ← s.w g, Category.assoc, hsndK, Category.assoc] } }
  let fstc : (BigFppfOver.toScheme B S hS).obj (intBaseChangeObj B S hS c.pt hcpt) ⟶ S :=
    pullback.fst (terminal.from S) (terminal.from c.pt)
  let sndc : (BigFppfOver.toScheme B S hS).obj (intBaseChangeObj B S hS c.pt hcpt) ⟶ c.pt :=
    pullback.snd (terminal.from S) (terminal.from c.pt)
  have hπfst (j : J) : ((BigFppfOver.toScheme B S hS).mapCone
      (intBaseChangeCone B S hS hD c hcpt)).π.app j ≫ fstK j = fstc :=
    intBaseChangeMap_fst S (c.π.app j)
  have hπsnd (j : J) : ((BigFppfOver.toScheme B S hS).mapCone
      (intBaseChangeCone B S hS hD c hcpt)).π.app j ≫ sndK j = sndc ≫ c.π.app j :=
    intBaseChangeMap_snd S (c.π.app j)
  refine
    { lift s := pullback.lift (s.π.app j₀ ≫ fstK j₀) (hc.lift (coneD s))
        (terminal.hom_ext _ _)
      fac s j := ?_
      uniq s m hm := ?_ }
  · refine pullback.hom_ext ?_ ?_
    · change _ ≫ fstK j = _ ≫ fstK j
      exact (Category.assoc _ _ _).trans <| (congrArg (pullback.lift _ _ _ ≫ ·) (hπfst j)).trans <|
        (pullback.lift_fst _ _ _).trans (hconst s j).symm
    · change _ ≫ sndK j = _ ≫ sndK j
      exact (Category.assoc _ _ _).trans <| (congrArg (pullback.lift _ _ _ ≫ ·) (hπsnd j)).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ c.π.app j) (pullback.lift_snd _ _ _)).trans (hc.fac (coneD s) j)
  · refine pullback.hom_ext ?_ ?_
    · change m ≫ fstc = pullback.lift _ _ _ ≫ fstc
      exact (congrArg (m ≫ ·) (hπfst j₀)).symm.trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ fstK j₀) (hm j₀)).trans (pullback.lift_fst _ _ _).symm
    · change m ≫ sndc = pullback.lift _ _ _ ≫ sndc
      refine (hc.uniq (coneD s) _ fun j => ?_).trans (pullback.lift_snd _ _ _).symm
      change (m ≫ sndc) ≫ c.π.app j = s.π.app j ≫ sndK j
      exact (Category.assoc _ _ _).trans <| (congrArg (m ≫ ·) (hπsnd j)).symm.trans <|
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ sndK j) (hm j))

/-- The functor from the big fppf site of `S` to schemes reflects connected limits. -/
private theorem reflectsLimitsOfShape_toScheme (J : Type u) [Category.{u} J] [IsConnected J] :
    ReflectsLimitsOfShape J (BigFppfOver.toScheme B S hS) := by
  have : ReflectsLimitsOfShape J (Over.forget (B.obj hS)) :=
    inferInstanceAs (ReflectsLimitsOfShape J (CostructuredArrow.proj (𝟭 _) _))
  exact inferInstanceAs (ReflectsLimitsOfShape J (Over.forget (B.obj hS) ⋙ B.inclusion))

/-- The base change along `S ⟶ Spec ℤ` of a limit cone of schemes over a connected index
category is a limit cone in the big fppf site of `S`. -/
private def isLimitIntBaseChangeCone {J : Type u} [Category.{u} J] [IsConnected J]
    {D : J ⥤ Scheme.{u}} (hD : ∀ j, B.Contains (D.obj j)) (c : Cone D) (hc : IsLimit c)
    (hcpt : B.Contains c.pt) : IsLimit (intBaseChangeCone B S hS hD c hcpt) :=
  have := reflectsLimitsOfShape_toScheme B S hS J
  isLimitOfReflects (BigFppfOver.toScheme B S hS)
    (isLimitToSchemeMapIntBaseChangeCone B S hS hD c hc hcpt)

/-- The product `X ⨯ -` with a fixed object carries a limit cone over a connected diagram to a
limit cone. This is `CategoryTheory.Limits.prod_preservesConnectedLimits` without its smallness
condition on the index. -/
private def isLimitProdFunctorMapCone {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C]
    {J : Type u₂} [Category.{v₂} J] [IsConnected J] (X : C) {K : J ⥤ C} {c : Cone K}
    (hc : IsLimit c) :
    IsLimit ((prod.functor.obj X).mapCone c) := by
  classical
  let j₀ : J := Classical.arbitrary J
  let fstK (j : J) : (K ⋙ prod.functor.obj X).obj j ⟶ X := (prod.fst : X ⨯ K.obj j ⟶ X)
  let sndK (j : J) : (K ⋙ prod.functor.obj X).obj j ⟶ K.obj j := (prod.snd : X ⨯ K.obj j ⟶ _)
  have hfstK {j k : J} (g : j ⟶ k) : (K ⋙ prod.functor.obj X).map g ≫ fstK k = fstK j :=
    (prod.map_fst _ _).trans (Category.comp_id _)
  have hsndK {j k : J} (g : j ⟶ k) :
      (K ⋙ prod.functor.obj X).map g ≫ sndK k = sndK j ≫ K.map g :=
    prod.map_snd _ _
  have hconst : ∀ (s : Cone (K ⋙ prod.functor.obj X)) (j : J),
      s.π.app j ≫ fstK j = s.π.app j₀ ≫ fstK j₀ := by
    intro s j
    refine constant_of_preserves_morphisms (fun j : J => s.π.app j ≫ fstK j) ?_ j j₀
    intro j k g
    change s.π.app j ≫ fstK j = s.π.app k ≫ fstK k
    rw [← s.w g, Category.assoc, hfstK]
  let coneK (s : Cone (K ⋙ prod.functor.obj X)) : Cone K :=
    { pt := s.pt
      π :=
        { app j := s.π.app j ≫ sndK j
          naturality j k g := by
            change 𝟙 _ ≫ s.π.app k ≫ sndK k = (s.π.app j ≫ sndK j) ≫ K.map g
            rw [Category.id_comp, ← s.w g, Category.assoc, hsndK, Category.assoc] } }
  have hπfst (j : J) : ((prod.functor.obj X).mapCone c).π.app j ≫ fstK j = prod.fst :=
    (prod.map_fst _ _).trans (Category.comp_id _)
  have hπsnd (j : J) : ((prod.functor.obj X).mapCone c).π.app j ≫ sndK j = prod.snd ≫ c.π.app j :=
    prod.map_snd _ _
  refine
    { lift s := prod.lift (s.π.app j₀ ≫ fstK j₀) (hc.lift (coneK s))
      fac s j := ?_
      uniq s m hm := ?_ }
  · refine prod.hom_ext ?_ ?_
    · change _ ≫ fstK j = _ ≫ fstK j
      exact (Category.assoc _ _ _).trans <| (congrArg (prod.lift _ _ ≫ ·) (hπfst j)).trans <|
        (prod.lift_fst _ _).trans (hconst s j).symm
    · change _ ≫ sndK j = _ ≫ sndK j
      exact (Category.assoc _ _ _).trans <| (congrArg (prod.lift _ _ ≫ ·) (hπsnd j)).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ c.π.app j) (prod.lift_snd _ _)).trans (hc.fac (coneK s) j)
  · refine prod.hom_ext ?_ ?_
    · exact (congrArg (m ≫ ·) (hπfst j₀)).symm.trans <| (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ fstK j₀) (hm j₀)).trans (prod.lift_fst _ _).symm
    · refine (hc.uniq (coneK s) _ fun j => ?_).trans (prod.lift_snd _ _).symm
      change (m ≫ prod.snd) ≫ c.π.app j = s.π.app j ≫ sndK j
      exact (Category.assoc _ _ _).trans <| (congrArg (m ≫ ·) (hπsnd j)).symm.trans <|
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ sndK j) (hm j))

/-- The product of `Y` with the yoneda image of a morphism of the site that is an immersion of
schemes is an immersion. -/
private theorem isImmersion_prod_map_yoneda_map (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {T T' : BigFppfOver B S hS} (g : T ⟶ T')
    (hg : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    IsImmersion B S hS (prod.map (𝟙 Y) (yoneda.map g)) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (Stacks.CategoryTheory.Hypercovering.isPullback_prod_snd (B := Y) (yoneda.map g))
    ((presheaf_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.IsImmersion.isStableUnderBaseChange) g).2 hg)

/-! ### Assembling the diagram from a projectively immersed proper cover of a stage -/

/-- Suppose `X₂ ⟶ X` is a proper surjective morphism from an object of the site and
`F : X₂ ⟶ Y ⨯ W` an immersion over `Y` into the product with an object `W` of the site, and suppose
`ρ : T ⟶ W` is proper and surjective with `T` immersed into `ℙⁿ_S`. Then the fibre product
`X' = X₂ ×_{Y ⨯ W} (Y ⨯ T)` maps properly and surjectively to `X` and immerses into
`Y ⨯ ℙⁿ_S = ℙⁿ_Y`, over `Y`. -/
private theorem exists_of_isImmersion_prod
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (X₂ : BigFppfOver B S hS) (c : yoneda.obj X₂ ⟶ X) (hcp : IsProper B S hS c)
    (hcs : IsSurjective B S hS c) (W : BigFppfOver B S hS) (F : yoneda.obj X₂ ⟶ Y ⨯ yoneda.obj W)
    (hF : IsImmersion B S hS F) (hFfst : F ≫ prod.fst = c ≫ f)
    (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S)) (T : BigFppfOver B S hS) (ρ : T ⟶ W)
    (ι : T ⟶ projectiveSpaceSiteObj B S hS n hP)
    (hρ : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map ρ))
    (hρs : Surjective ((BigFppfOver.toScheme B S hS).map ρ))
    (hι : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map ι)) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X') (q : X' ⟶ X)
      (i : X' ⟶ Y ⨯ yoneda.obj (projectiveSpaceSiteObj B S hS n hP)),
      IsProper B S hS q ∧ IsSurjective B S hS q ∧ IsImmersion B S hS i ∧ q ≫ f = i ≫ prod.fst := by
  have hX₂ := isAlgebraicSpace_yoneda B S hS X₂
  have hW := isAlgebraicSpace_yoneda B S hS W
  have hT := isAlgebraicSpace_yoneda B S hS T
  have hYW : IsAlgebraicSpace B S hS (Y ⨯ yoneda.obj W) := isAlgebraicSpace_prod B S hS hY hW
  have hYT : IsAlgebraicSpace B S hS (Y ⨯ yoneda.obj T) := isAlgebraicSpace_prod B S hS hY hT
  let a : Y ⨯ yoneda.obj T ⟶ Y ⨯ yoneda.obj W := prod.map (𝟙 Y) (yoneda.map ρ)
  have ha : IsProper B S hS a :=
    isProper_of_isPullback' hYT hT hYW hW
      (Stacks.CategoryTheory.Hypercovering.isPullback_prod_snd (B := Y) (yoneda.map ρ))
      (isProper_yoneda_map B S hS ρ hρ)
  have has : IsSurjective B S hS a :=
    isSurjective_of_isPullback_presheaf hYT hT hYW hW
      (Stacks.CategoryTheory.Hypercovering.isPullback_prod_snd (B := Y) (yoneda.map ρ))
      (isSurjective_yoneda_map B S hS ρ hρs)
  let b : Y ⨯ yoneda.obj T ⟶ Y ⨯ yoneda.obj (projectiveSpaceSiteObj B S hS n hP) :=
    prod.map (𝟙 Y) (yoneda.map ι)
  have hb : IsImmersion B S hS b :=
    isImmersion_prod_map_yoneda_map B S hS Y ι hι
  have hsq := IsPullback.of_hasPullback F a
  have hXp := isAlgebraicSpace_pullback B S hS F a hX₂ hYT hYW
  refine ⟨pullback F a, hXp, pullback.fst F a ≫ c, pullback.snd F a ≫ b, ?_, ?_, ?_, ?_⟩
  · exact isProper_comp B S hS hXp hX₂ hX _ _
      (isProper_of_isPullback' hXp hYT hX₂ hYW hsq.flip ha) hcp
  · exact isSurjective_comp B S hS
      (isSurjective_of_isPullback_presheaf hXp hYT hX₂ hYW hsq.flip has) hcs
  · exact isImmersion_comp B S hS _ _
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq hF) hb
  · rw [Category.assoc, ← hFfst, ← Category.assoc, hsq.w, Category.assoc, Category.assoc]
    simp [a, b]

/-! ### Chow's lemma for a separated scheme of finite type over `Spec ℤ`, base changed to `S` -/

/-- **Chow's lemma over `Spec ℤ`, base changed to `S`.** For a separated scheme `V` of finite type
over `Spec ℤ` there are a proper surjective morphism `T ⟶ S ×_ℤ V` of the site and an immersion
`T ⟶ ℙⁿ_S`: the base changes along `S ⟶ Spec ℤ` of the proper surjective `T₀ ⟶ V` and the
immersion `T₀ ⟶ ℙⁿ_ℤ` of Chow's lemma for schemes, [Stacks, Tag 0202]. -/
private theorem exists_chow_intBaseChange (V : Scheme.{u}) (hV : B.Contains V) [V.IsSeparated]
    [LocallyOfFiniteType (terminal.from V)] [QuasiCompact (terminal.from V)] :
    ∃ (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S)) (T : BigFppfOver B S hS)
      (ρ : T ⟶ intBaseChangeObj B S hS V hV) (ι : T ⟶ projectiveSpaceSiteObj B S hS n hP),
      _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map ρ) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map ρ) ∧
        _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map ι) := by
  have : _root_.AlgebraicGeometry.IsSeparated (terminal.from V) := (Scheme.isSeparated_iff V).1 ‹_›
  obtain ⟨n, T₀, ρ₀, i₀, hρ₀, hρ₀s, hi₀, -⟩ :=
    hasChowModification_of_compactSpace_quasiSeparatedSpace (terminal.from V)
  have := hρ₀
  have := hi₀
  have hT₀ : B.Contains T₀ := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact ρ₀ hV
  let ι₀ : T₀ ⟶ projectiveSpaceAtUniverse.{u} n :=
    i₀ ≫ pullback.snd (terminal.from (⊤_ Scheme.{u})) (terminal.from (ProjectiveSpaceZ.{u} n))
  have hsnd : _root_.AlgebraicGeometry.IsImmersion
      (pullback.snd (terminal.from (⊤_ Scheme.{u})) (terminal.from (ProjectiveSpaceZ.{u} n))) := by
    have : IsIso (terminal.from (⊤_ Scheme.{u})) :=
      ⟨⟨𝟙 _, terminal.hom_ext _ _, terminal.hom_ext _ _⟩⟩
    infer_instance
  have hι₀ : _root_.AlgebraicGeometry.IsImmersion ι₀ :=
    have := MorphismProperty.IsMultiplicative.toIsStableUnderComposition
      (W := @_root_.AlgebraicGeometry.IsImmersion.{u})
    MorphismProperty.comp_mem (@_root_.AlgebraicGeometry.IsImmersion.{u}) _ _ hi₀ hsnd
  have hP := contains_projectiveSpaceOver B S hS n
  let m : pullback (terminal.from S) (terminal.from T₀) ⟶ projectiveSpaceOver n S :=
    pullback.map (terminal.from S) (terminal.from T₀) (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) (𝟙 S) ι₀ (𝟙 _) (by simp)
      (terminal.hom_ext _ _)
  have hm : _root_.AlgebraicGeometry.IsImmersion m :=
    intBaseChangeMap_mem S (@_root_.AlgebraicGeometry.IsImmersion.{u}) hι₀
  refine ⟨n, hP, intBaseChangeObj B S hS T₀ hT₀, intBaseChangeHom B S hS hT₀ hV ρ₀,
    Over.homMk (ObjectProperty.homMk m) (by
      apply ObjectProperty.hom_ext
      change m ≫ pullback.fst _ _ = pullback.fst _ _
      simp [m]), ?_, ?_, hm⟩
  · exact intBaseChangeMap_mem S (@_root_.AlgebraicGeometry.IsProper.{u}) hρ₀
  · exact intBaseChangeMap_mem S (@Surjective.{u}) hρ₀s

/-! ### Immersing a scheme cover over `Y` into the product with a stage of an approximation -/

/-- Let `X₂` be an object of the site whose scheme is quasi-compact and separated, with a morphism
`k : X₂ ⟶ Y` locally of finite type to a separated algebraic space. Then there is a separated
scheme `V` of finite type over `Spec ℤ` such that `k` factors through an immersion
`X₂ ⟶ Y ⨯ (S ×_ℤ V)` followed by the first projection. -/
private theorem exists_isImmersion_prod_intBaseChange (hZ : B.Contains (⊤_ Scheme.{u}))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYsep : IsAbsolutelySeparated B S hS hZ Y)
    (X₂ : BigFppfOver B S hS) (k : yoneda.obj X₂ ⟶ Y) (hk : IsLocallyOfFiniteType B S hS k)
    (hX₂qc : IsQuasiCompactSpace B S hS (yoneda.obj X₂))
    (hX₂c : CompactSpace ((BigFppfOver.toScheme B S hS).obj X₂))
    (hX₂s : ((BigFppfOver.toScheme B S hS).obj X₂).IsSeparated) :
    ∃ (V : Scheme.{u}) (hV : B.Contains V) (_ : V.IsSeparated)
      (_ : LocallyOfFiniteType (terminal.from V)) (_ : QuasiCompact (terminal.from V))
      (F : yoneda.obj X₂ ⟶ Y ⨯ yoneda.obj (intBaseChangeObj B S hS V hV)),
      IsImmersion B S hS F ∧ F ≫ prod.fst = k := by
  classical
  let X₂s := (BigFppfOver.toScheme B S hS).obj X₂
  have hX₂ : B.Contains X₂s := X₂.left.property
  obtain ⟨I, _, _, _, D, c₀, haff, hft, hqc, -, hcomp, hqsD, ⟨hlim⟩, hpt⟩ :=
    exists_isLimit_finiteType_isNoetherian X₂s
  have hD : ∀ j, B.Contains (D.obj j) := fun j =>
    have := hft j
    have := hqc j
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (terminal.from (D.obj j)) hZ
  have hcpt : B.Contains c₀.pt := hpt ▸ hX₂
  have : IsConnected Iᵒᵖ := IsCofiltered.isConnected _
  let E := intBaseChangeDiagram B S hS D hD
  let cE := intBaseChangeCone B S hS hD c₀ hcpt
  let cP := (prod.functor.obj Y).mapCone (yoneda.mapCone cE)
  have hP : IsLimit cP := isLimitProdFunctorMapCone Y
    (isLimitOfPreserves yoneda (isLimitIntBaseChangeCone B S hS hD c₀ hlim hcpt))
  let D' : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := (E ⋙ yoneda) ⋙ prod.functor.obj Y
  have hD'alg : ∀ i : I, IsAlgebraicSpace B S hS (D'.obj (op i)) := fun i =>
    isAlgebraicSpace_prod B S hS hY (isAlgebraicSpace_yoneda B S hS _)
  let t : D' ⟶ (Functor.const Iᵒᵖ).obj Y :=
    { app _ := prod.fst
      naturality _ _ g := (prod.map_fst _ _).trans (Category.comp_id _).symm }
  have hcomm : cP.π ≫ t = (Functor.const Iᵒᵖ).map prod.fst :=
    NatTrans.ext (funext fun _ => (prod.map_fst _ _).trans (Category.comp_id _))
  let hT := isTerminal_yoneda_obj_base B S hS
  have hYsepS : IsSeparated B S hS (hT.from Y) :=
    isSeparated_of_isSeparatedOver B S hS
      (isSeparatedOver_of_isAbsolutelySeparated B S hS hZ hY hYsep) _
  let γs : X₂s ⟶ pullback (terminal.from S) (terminal.from c₀.pt) :=
    pullback.lift (B.inclusion.map X₂.hom) (eqToHom hpt.symm) (terminal.hom_ext _ _)
  let γ : X₂ ⟶ intBaseChangeObj B S hS c₀.pt hcpt :=
    BigFppfOver.homMk B S hS _ _ γs (pullback.lift_fst _ _ _)
  have hγ : _root_.AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map γ) := by
    have : _root_.AlgebraicGeometry.IsImmersion (γs ≫ pullback.snd _ _) := by
      rw [pullback.lift_snd]
      infer_instance
    exact _root_.AlgebraicGeometry.IsImmersion.of_comp γs (pullback.snd _ _)
  let F₀ : yoneda.obj X₂ ⟶ cP.pt := prod.lift k (yoneda.map γ)
  have hfk : F₀ ≫ (prod.fst : cP.pt ⟶ Y) = k := prod.lift_fst _ _
  have hF₀ : IsImmersion B S hS F₀ := by
    have hgraph : IsClosedImmersion B S hS (prod.lift k (𝟙 (yoneda.obj X₂))) :=
      isClosedImmersion_of_isSeparated_of_section B S hS prod.snd
        (isSeparated_of_isPullback B S hS
          (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd Y (yoneda.obj X₂)) hT)
          hYsepS) _ (prod.lift_snd _ _)
    have hmap : IsImmersion B S hS (prod.map (𝟙 Y) (yoneda.map γ)) :=
      isImmersion_prod_map_yoneda_map B S hS Y γ hγ
    have hF₀eq : prod.lift k (𝟙 _) ≫ prod.map (𝟙 Y) (yoneda.map γ) = F₀ := by
      rw [prod.lift_map, Category.comp_id, Category.id_comp]
      rfl
    rw [← hF₀eq]
    exact isImmersion_comp B S hS _ _ (isImmersion_of_isClosedImmersion B S hS hgraph) hmap
  have haffD' : ∀ ⦃i j : I⦄ (h : i ≤ j), IsAffineHom B S hS (D'.map (homOfLE h).op) := by
    intro i j h
    let g := (homOfLE h).op
    have hs : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (E.map g)) :=
      intBaseChangeMap_mem S (@_root_.AlgebraicGeometry.IsAffineHom.{u}) (haff g)
    exact isAffineHom_of_isPullback
      (Stacks.CategoryTheory.Hypercovering.isPullback_prod_snd (B := Y) (yoneda.map (E.map g)))
      (isAffineHom_of_presheaf ((presheaf_yoneda_map_iff B S hS
        (@_root_.AlgebraicGeometry.isAffineHom_isStableUnderBaseChange) (E.map g)).2 hs))
  have hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y :=
    isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ Y hYsep
  have hqsD' : ∀ i : I, IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (D'.obj (op i)) := by
    intro i
    let φ : E.obj (op i) ⟶ Over.mk (𝟙 (B.obj hS)) := Over.homMk (E.obj (op i)).hom (by simp)
    have hφs : QuasiSeparated ((BigFppfOver.toScheme B S hS).map φ) := by
      have : QuasiSeparated (terminal.from (D.obj (op i))) :=
        (quasiSeparatedSpace_iff_quasiSeparated _).1 (hqsD _)
      change QuasiSeparated (pullback.fst (terminal.from S) (terminal.from (D.obj (op i))))
      infer_instance
    have hφ : IsQuasiSeparated B S hS (hT.from (yoneda.obj (E.obj (op i)))) := by
      rw [hT.hom_ext (hT.from _) (yoneda.map φ)]
      exact (isQuasiSeparated_yoneda_map_iff B S hS φ).2 hφs
    exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (hD'alg i) hYqs
      (isQuasiSeparated_of_isPullback B S hS
        (IsPullback.of_isLimit_binaryFan_of_isTerminal
          (prodIsProd Y (yoneda.obj (E.obj (op i)))) hT).flip hφ)
  have hev := eventually_isImmersion_comp_limitπ B S hS Y hY D' hD'alg t cP hP prod.fst hcomm
    (yoneda.obj X₂) (isAlgebraicSpace_yoneda B S hS X₂) hX₂qc F₀ haffD' hqsD'
    (hfk ▸ hk) hF₀
  have : ∀ {i j : Iᵒᵖ} (v : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (D.map v) := haff
  have : ∀ i, CompactSpace (D.obj i) := hcomp
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := hqsD
  have : c₀.pt.IsSeparated := hpt ▸ hX₂s
  obtain ⟨j₁, hj₁⟩ := exists_isSeparated_stage D c₀ hlim
  obtain ⟨i, hi, hij⟩ := (hev.and (Filter.eventually_ge_atTop j₁.unop)).exists
  have hsep : (D.obj (op i)).IsSeparated := by
    let g : op i ⟶ j₁ := (homOfLE hij).op
    refine (Scheme.isSeparated_iff _).2 ?_
    have : _root_.AlgebraicGeometry.IsSeparated (terminal.from (D.obj j₁)) :=
      (Scheme.isSeparated_iff _).1 hj₁
    have : _root_.AlgebraicGeometry.IsSeparated (D.map g ≫ terminal.from (D.obj j₁)) :=
      inferInstance
    rwa [terminal.comp_from] at this
  refine ⟨D.obj (op i), hD _, hsep, hft _, hqc _, F₀ ≫ cP.π.app (op i), hi, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (F₀ ≫ ·) ((prod.map_fst _ _).trans (Category.comp_id _))).trans hfk)

/-! ### Chow's lemma with an immersion into projective space over the base -/

/-- **Chow's lemma over a quasi-compact separated base, [Stacks, Tag 089M].** Let `S` be a
scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S`, separated and of finite type,
with `Y` separated and quasi-compact. Then there are an algebraic space `X'`, a proper surjective
morphism `q : X' ⟶ X` and an immersion `i : X' ⟶ ℙⁿ_Y` with `q ≫ f = i ≫ (ℙⁿ_Y ⟶ Y)`.

Relative projective space `ℙⁿ_Y` is the fibre product `Y ×_S ℙⁿ_S` over the presheaf represented
by `S`, which is terminal, with `ℙⁿ_S` the object `AlgebraicGeometry.Space.projectiveSpaceSiteObj`
of the site; `ℙⁿ_Y ⟶ Y` is the first projection. "Separated" for `Y` is the absolute notion of
[Stacks, Tag 03BS]. -/
@[stacks 089M]
theorem exists_isProper_isSurjective_isImmersion_projectiveSpace
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hfsep : IsSeparated B S hS f) (hfft : IsFiniteType B S hS f)
    (hYsep : IsAbsolutelySeparated B S hS hZ Y) (hYqc : IsQuasiCompactSpace B S hS Y) :
    ∃ (n : ℕ) (hP : B.Contains (projectiveSpaceOver n S))
      (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X') (q : X' ⟶ X)
      (i : X' ⟶ pullback ((isTerminal_yoneda_obj_base B S hS).from Y)
        ((isTerminal_yoneda_obj_base B S hS).from
          (yoneda.obj (projectiveSpaceSiteObj B S hS n hP)))),
      IsProper B S hS q ∧ IsSurjective B S hS q ∧ IsImmersion B S hS i ∧
        q ≫ f = i ≫ pullback.fst _ _ := by
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hY hYqc f hfft.2
  have hXsep : IsAbsolutelySeparated B S hS hZ X :=
    isAbsolutelySeparated_of_isSeparated B S hS hZ hYsep hfsep
  have hXqs := isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B S hS hZ X hXsep
  obtain ⟨X₂, c, hcs, hcf⟩ :=
    existsFiniteSurjectiveSchemeCover_of_isQuasiCompactSpace B S hS hZ X hX hXqc hXqs
  have hX₂ := isAlgebraicSpace_yoneda B S hS X₂
  have hcp : IsProper B S hS c := ((isFinite_iff_isAffineHom_and_isProper B S hS hX₂ hX c).mp hcf).2
  have hX₂qc : IsQuasiCompactSpace B S hS (yoneda.obj X₂) :=
    isQuasiCompactSpace_of_isQuasiCompact B S hS hX hXqc c hcp.2.1.2
  have hX₂c := compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hX₂qc
  have hX₂sepA : IsAbsolutelySeparated B S hS hZ (yoneda.obj X₂) :=
    isAbsolutelySeparated_of_isSeparated B S hS hZ hXsep hcp.1
  have hX₂s : ((BigFppfOver.toScheme B S hS).obj X₂).IsSeparated := by
    let γ : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
    let V : BigFppfOver B (⊤_ Scheme.{u}) hZ := (Over.map γ).obj X₂
    have hterm : IsTerminal (Over.mk (𝟙 (B.obj hZ)) : BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
      Over.mkIdTerminal
    have hterm' := hterm.isTerminalObj yoneda _
    let e := (OverShriek.relocalizeYonedaIso γ).app X₂
    have h1 : IsSeparated B (⊤_ Scheme.{u}) hZ (e.hom ≫ yoneda.map (hterm.from V)) :=
      (isSeparatedOver_iff_isSeparated_of_isTerminal B (⊤_ Scheme.{u}) hZ hterm' _).1 hX₂sepA
    have h2 : IsSeparated B (⊤_ Scheme.{u}) hZ (yoneda.map (hterm.from V)) := by
      have h := isSeparated_comp B (⊤_ Scheme.{u}) hZ e.inv _
        (isSeparated_of_isIso B (⊤_ Scheme.{u}) hZ e.inv) h1
      rwa [Iso.inv_hom_id_assoc] at h
    have h3 := (isSeparated_yoneda_map_iff B (⊤_ Scheme.{u}) hZ (hterm.from V)).1 h2
    have hm : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (hterm.from V) =
        terminal.from _ := terminal.hom_ext _ _
    exact ⟨hm ▸ h3⟩
  have hk : IsLocallyOfFiniteType B S hS (c ≫ f) :=
    (isFiniteType_comp B S hS hX₂ hX hY c f hcp.2.1 hfft).1
  obtain ⟨V, hV, _, _, _, F, hF, hFfst⟩ :=
    exists_isImmersion_prod_intBaseChange B S hS hZ hY hYsep X₂ (c ≫ f) hk hX₂qc hX₂c hX₂s
  obtain ⟨n, hP, T, ρ, ι, hρ, hρs, hι⟩ := exists_chow_intBaseChange B S hS V hV
  obtain ⟨X', hX', q, i, hqp, hqs, hi, hcomm⟩ :=
    exists_of_isImmersion_prod B S hS hX hY f X₂ c hcp hcs _ F hF hFfst n hP T ρ ι hρ hρs hι
  have hpb := IsPullback.of_isLimit_binaryFan_of_isTerminal
    (prodIsProd Y (yoneda.obj (projectiveSpaceSiteObj B S hS n hP)))
    (isTerminal_yoneda_obj_base B S hS)
  have := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨n, hP, X', hX', q, i ≫ hpb.isoPullback.hom, hqp, hqs,
    MorphismProperty.RespectsIso.postcomp _ _ i hi,
    (hcomm.trans (congrArg (i ≫ ·) hpb.isoPullback_hom_fst.symm)).trans
      (Category.assoc _ _ _).symm⟩

end AlgebraicGeometry.Space

end
