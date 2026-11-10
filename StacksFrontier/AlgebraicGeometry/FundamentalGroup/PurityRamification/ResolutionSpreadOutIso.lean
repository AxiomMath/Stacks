module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOut
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism

/-!
# Spreading out a scheme over the local ring at a point: the locus where it is an isomorphism

Continuing `PurityRamification/ResolutionSpreadOut.lean`: in the proof of [Stacks, Tag 0EA3] the
resolution `W ⟶ Spec(𝒪_{X, x})` is an isomorphism over the punctured spectrum, and its proper
model `b : X' ⟶ U` over an affine open neighbourhood `U` of `x` can be chosen to be an
isomorphism over `U \ \overline{\{x\}}`. More generally, for an open `V ⊆ X`, if the base change
of `W` to the preimage of `V` in `Spec(𝒪_{X, x})` is an isomorphism, then so is the base change
of the model to `U ∩ V` for `U` small enough: the preimage of `V` in `Spec(𝒪_{X, x})` is the limit
of the opens `U ∩ V` (`AlgebraicGeometry.isLimitOpensSpecStalkCone`), and [Stacks, Tag 081E]
applies.

## Main results

* `AlgebraicGeometry.exists_isProper_model_specStalk_isIso`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Base change along a composite, read as an iterated base change, as far as being an
isomorphism is concerned. -/
theorem isIso_pullback_snd_snd_iff {X Y Z T : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : T ⟶ Y) :
    IsIso (pullback.snd (pullback.snd f g) h) ↔ IsIso (pullback.snd f (h ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_hom_snd f g h]
  exact isIso_comp_left_iff _ _

/-- Precomposing with an isomorphism does not change whether a base change is an isomorphism. -/
theorem isIso_pullback_snd_comp_left_iff {X X' Y S : Scheme.{u}} (a : X' ⟶ X) [IsIso a]
    (b : X ⟶ S) (h : Y ⟶ S) :
    IsIso (pullback.snd (a ≫ b) h) ↔ IsIso (pullback.snd b h) := by
  have : pullback.snd (a ≫ b) h = pullback.map (a ≫ b) h b h a (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]) ≫
        pullback.snd b h := by
    rw [pullback.lift_snd, Category.comp_id]
  rw [this]
  exact isIso_comp_left_iff _ _

/-- The base change of the structure morphism of `X₀`, seen as a morphism of `Over S` to the
terminal object, is an isomorphism exactly when the base change of `X₀` is. -/
theorem isIso_overPullback_map_homMk_iff {S T : Scheme.{u}} (q : T ⟶ S) (X₀ : Over S) :
    IsIso ((Over.pullback q).map (Over.homMk X₀.hom : X₀ ⟶ Over.mk (𝟙 S))).left ↔
      IsIso (pullback.snd X₀.hom q) := by
  have : pullback.snd X₀.hom q = ((Over.pullback q).map
      (Over.homMk X₀.hom : X₀ ⟶ Over.mk (𝟙 S))).left ≫ pullback.snd (𝟙 S) q := by
    simp only [Over.pullback_map_left]
    exact (pullback.lift_snd _ _ _).symm.trans (Category.comp_id _).symm
  rw [this]
  exact (isIso_comp_right_iff _ _).symm

/-- Being an isomorphism, for a base change, depends only on the morphism base changed along. -/
theorem isIso_pullback_snd_congr {X Y S : Scheme.{u}} (f : X ⟶ S) {g g' : Y ⟶ S} (h : g = g') :
    IsIso (pullback.snd f g) ↔ IsIso (pullback.snd f g') := by
  subst h
  rfl

/-- Being an isomorphism, for a base change to an open, depends only on the open. -/
theorem isIso_pullback_snd_opens_congr {X S : Scheme.{u}} (f : X ⟶ S) {U U' : S.Opens}
    (h : U = U') : IsIso (pullback.snd f U.ι) ↔ IsIso (pullback.snd f U'.ι) := by
  subst h
  rfl

/-- Being an isomorphism, for a base change, depends only on the morphism base changed. -/
theorem isIso_pullback_snd_left_congr {X Y S : Scheme.{u}} {f f' : X ⟶ S} (h : f = f')
    (g : Y ⟶ S) : IsIso (pullback.snd f g) ↔ IsIso (pullback.snd f' g) := by
  subst h
  rfl

/-- The iterated version of `AlgebraicGeometry.isIso_pullback_snd_left_congr`. -/
theorem isIso_pullback_snd_snd_congr {X Y S T : Scheme.{u}} (f : X ⟶ S) {g g' : Y ⟶ S}
    (h : g = g') (k : T ⟶ Y) :
    IsIso (pullback.snd (pullback.snd f g) k) ↔ IsIso (pullback.snd (pullback.snd f g') k) := by
  subst h
  rfl

/-- Iterated base changes along commuting squares of the base changed morphisms agree as far as
being an isomorphism is concerned. -/
private theorem isIso_pullback_snd_snd_iff_of_comp_eq {X Y Z T U : Scheme.{u}} (f : X ⟶ Z)
    {a : T ⟶ Y} {b : Y ⟶ Z} {c : T ⟶ U} {d : U ⟶ Z} (h : a ≫ b = c ≫ d) :
    IsIso (pullback.snd (pullback.snd f b) a) ↔ IsIso (pullback.snd (pullback.snd f d) c) := by
  rw [isIso_pullback_snd_snd_iff, isIso_pullback_snd_snd_iff, isIso_pullback_snd_congr f h]

/-- **A model becomes an isomorphism where the given morphism is, over a smaller neighbourhood
([Stacks, Tag 081E]).** Let `X` be locally Noetherian, `x ∈ X`, `V ⊆ X` open, and let
`g : W ⟶ Spec(𝒪_{X, x})` have base change to the preimage of `V` an isomorphism. If `g` is the
base change of a morphism of finite presentation `Z ⟶ U` over an affine open neighbourhood `U`
of `x`, then the base change of `Z` to a smaller affine open neighbourhood `U'` is an
isomorphism over `U' ∩ V`: the preimage of `V` is the limit of the opens `U' ∩ V`. -/
theorem exists_hom_isIso_pullback_snd_model (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {W : Scheme.{u}} (g : W ⟶ Spec (X.presheaf.stalk x)) (V : X.Opens)
    (hV : IsIso (pullback.snd g ((X.fromSpecStalk x) ⁻¹ᵁ V).ι)) {j : AffineOpenNhds X x}
    (Z : Over ((affineOpenNhdsDiagram X x).obj j)) (hfp : FinitePresentation Z.hom)
    (e : Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) :
    ∃ (k : AffineOpenNhds X x) (h : k ⟶ j),
      IsIso (pullback.snd (pullback.snd Z.hom ((affineOpenNhdsDiagram X x).map h))
        (Scheme.Opens.ι (X := X) k.obj.1 ⁻¹ᵁ V).ι) := by
  let D := affineOpenNhdsDiagram X x
  let c := specStalkCone X x
  let V' : (D.obj j).Opens := Scheme.Opens.ι (X := X) j.obj.1 ⁻¹ᵁ V
  let i₀ : Over j := Over.mk (𝟙 j)
  let O : (D.obj j).Opens := D.map i₀.hom ⁻¹ᵁ V'
  let X₀ : Over ((opensDiagram D j V').obj i₀) := Over.mk (pullback.snd Z.hom O.ι)
  let f₀ : X₀ ⟶ Over.mk (𝟙 _) := Over.homMk X₀.hom
  have := hfp.1
  have := hfp.2.1
  have := hfp.2.2
  have : IsLocallyNoetherian (D.obj j) :=
    inferInstanceAs (IsLocallyNoetherian (Scheme.Opens.toScheme (X := X) j.obj.1))
  have : IsNoetherian (D.obj j) := {}
  have : CompactSpace ((opensDiagram D j V').obj i₀) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (O : Set (D.obj j)))
  have : QuasiSeparatedSpace ((opensDiagram D j V').obj i₀) :=
    inferInstanceAs (QuasiSeparatedSpace O.toScheme)
  have : QuasiCompact X₀.hom := inferInstanceAs (QuasiCompact (pullback.snd Z.hom O.ι))
  have : QuasiSeparated X₀.hom := inferInstanceAs (QuasiSeparated (pullback.snd Z.hom O.ι))
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  have : LocallyOfFinitePresentation f₀.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Z.hom O.ι))
  have hlim : IsIso ((Over.pullback ((opensCone D c j V').π.app i₀)).map f₀).left := by
    have hτ : (opensCone D c j V').π.app i₀ ≫ O.ι = (c.π.app j ⁻¹ᵁ V').ι ≫ c.π.app j :=
      Scheme.Hom.resLE_comp_ι _ _
    refine (isIso_overPullback_map_homMk_iff _ X₀).mpr
      ((isIso_pullback_snd_snd_iff_of_comp_eq Z.hom hτ).mpr ?_)
    have hw : e.hom.left ≫ ((Over.pullback (c.π.app j)).obj Z).hom = g := Over.w e.hom
    change IsIso (pullback.snd ((Over.pullback (c.π.app j)).obj Z).hom _)
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e).hom)
    refine (isIso_pullback_snd_comp_left_iff e.hom.left _ _).mp ?_
    refine (isIso_pullback_snd_left_congr hw _).mpr ?_
    exact (isIso_pullback_snd_opens_congr g (specStalkCone_π_preimage X x j V)).mpr hV
  have : CompactSpace (Over.mk (𝟙 ((opensDiagram D j V').obj i₀))).left :=
    inferInstanceAs (CompactSpace ((opensDiagram D j V').obj i₀))
  have : QuasiSeparatedSpace (Over.mk (𝟙 ((opensDiagram D j V').obj i₀))).left :=
    inferInstanceAs (QuasiSeparatedSpace ((opensDiagram D j V').obj i₀))
  obtain ⟨k, h, hk⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange (opensDiagram D j V')
    (opensCone D c j V') (isLimitOpensSpecStalkCone X x j V) i₀ X₀ (Over.mk (𝟙 _)) f₀
  have hh : h.left = k.hom := by simpa [i₀] using Over.w h
  refine ⟨k.left, k.hom, ?_⟩
  have hσ : (opensDiagram D j V').map h ≫ O.ι = (D.map k.hom ⁻¹ᵁ V').ι ≫ D.map h.left :=
    Scheme.Hom.resLE_comp_ι _ _
  replace hk := (isIso_pullback_snd_snd_iff_of_comp_eq Z.hom hσ).mp
    ((isIso_overPullback_map_homMk_iff _ X₀).mp hk)
  replace hk := (isIso_pullback_snd_snd_congr Z.hom (congrArg D.map hh) _).mp hk
  have hQ : D.map k.hom ⁻¹ᵁ V' = Scheme.Opens.ι (X := X) k.left.obj.1 ⁻¹ᵁ V := by
    have e' : (k.left.obj.1 : X.Opens) ≤ j.obj.1 := leOfHom ((affineOpenNhds X x).ι.map k.hom)
    have h1 := Scheme.Hom.comp_preimage (X.homOfLE e') (Scheme.Opens.ι (X := X) j.obj.1) V
    rw [Scheme.homOfLE_ι] at h1
    exact h1.symm
  exact (isIso_pullback_snd_opens_congr _ hQ).mp hk

/-- **A proper model which is an isomorphism where the given morphism is ([Stacks, Tags 01ZM,
081F and 081E]).** Let `X` be locally Noetherian, `x ∈ X`, `V ⊆ X` open, and let
`g : W ⟶ Spec(𝒪_{X, x})` be proper and of finite presentation, with base change to the preimage
of `V` an isomorphism. Then `g` is the base change of a proper morphism of finite presentation
`Z ⟶ U` over an affine open neighbourhood `U` of `x` whose base change to `U ∩ V` is an
isomorphism. -/
theorem exists_isProper_model_specStalk_isIso (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {W : Scheme.{u}} (g : W ⟶ Spec (X.presheaf.stalk x)) [IsProper g]
    (hg : FinitePresentation g) (V : X.Opens)
    (hV : IsIso (pullback.snd g ((X.fromSpecStalk x) ⁻¹ᵁ V).ι)) :
    ∃ (j : AffineOpenNhds X x) (Z : Over ((affineOpenNhdsDiagram X x).obj j)),
      FinitePresentation Z.hom ∧ IsProper Z.hom ∧
        IsIso (pullback.snd Z.hom (Scheme.Opens.ι (X := X) j.obj.1 ⁻¹ᵁ V).ι) ∧
        Nonempty (Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) := by
  obtain ⟨j, Z, hfp, hprop, ⟨e⟩⟩ := exists_isProper_model_specStalk X x g hg
  obtain ⟨k, h, hk⟩ := exists_hom_isIso_pullback_snd_model X x g V hV Z hfp e
  have := hprop
  exact ⟨k, (Over.pullback ((affineOpenNhdsDiagram X x).map h)).obj Z,
    finitePresentation_overPullback_obj _ Z hfp,
    inferInstanceAs (IsProper (pullback.snd Z.hom ((affineOpenNhdsDiagram X x).map h))), hk,
    ⟨specStalkModelShrinkIso X x h e⟩⟩

end AlgebraicGeometry

end
