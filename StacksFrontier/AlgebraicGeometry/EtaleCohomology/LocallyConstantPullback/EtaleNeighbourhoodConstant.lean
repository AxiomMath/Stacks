module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Locally constant sheaves are constant on étale neighbourhoods, through inverse images

For an object `U ⟶ X` of the small étale site of `X`, the slice of `X_étale` over `U` is `U_étale`
(`Stacks.EtaleCohomology.etaleOverEquivalence`), so sheaves on the slice are sheaves on `U_étale`
(`Stacks.EtaleCohomology.etaleOverSheafEquivalence`). Restriction to the slice followed by this
equivalence is restriction along `U_étale ⥤ X_étale`, which is left adjoint to the direct image
along `U ⟶ X` (`Stacks.EtaleCohomology.etaleOverRestrictionAdj`, from the adjunction between
composition with and base change along `U ⟶ X`); it is therefore the inverse image along
`U ⟶ X` (`Stacks.EtaleCohomology.etaleModuleInverseImageIsoOverRestriction`).

Hence a locally constant sheaf of finite type of `Λ`-modules on `X_étale` (Stacks 03RW, whose
trivializations are stated on slices of the site) is, around every point of `X`, constant on an
étale neighbourhood in the sense of inverse images
(`Stacks.EtaleCohomology.exists_etale_inverseImage_constant_of_isFiniteTypeLocallyConstant`).

The comparison of the slice with `U_étale` is the public form of the one used privately in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward`.

## Main results

* `Stacks.EtaleCohomology.etaleOverSheafEquivalence`.
* `Stacks.EtaleCohomology.etaleModuleInverseImageIsoOverRestriction`.
* `Stacks.EtaleCohomology.exists_etale_inverseImage_constant_of_isFiniteTypeLocallyConstant`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology


/-- **The slice of `X_étale` over `U` is `U_étale`.** -/
def etaleOverEquivalence {X : Scheme.{u}} (U : X.Etale) :
    Over U ≌ U.left.Etale where
  functor :=
  { obj V := MorphismProperty.Over.mk ⊤ V.hom.left inferInstance
    map g := MorphismProperty.Over.homMk g.left.left (by
      have := congrArg (fun morphism ↦ morphism.left) g.w
      exact this)
    map_id _ := rfl
    map_comp _ _ := rfl }
  inverse :=
  { obj V := Over.mk (MorphismProperty.Over.homMk
      (A := MorphismProperty.Over.mk (P := (@Etale : MorphismProperty Scheme.{u}))
        ⊤ (V.hom ≫ U.hom) inferInstance)
      (B := U) V.hom)
    map {V W} g := Over.homMk (MorphismProperty.Over.homMk g.left (by
      change g.left ≫ (W.hom ≫ U.hom) = V.hom ≫ U.hom
      have h : g.left ≫ W.hom = V.hom := by simp
      rw [← Category.assoc, h])) (by
        apply MorphismProperty.Comma.Hom.ext
        · exact g.w
        · apply Subsingleton.elim)
    map_id _ := rfl
    map_comp _ _ := rfl }
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk
    (MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (V.hom.left ≫ U.hom) = V.left.hom
      simp)) (by
        apply MorphismProperty.Comma.Hom.ext
        · change 𝟙 _ ≫ V.hom.left = V.hom.left
          simp
        · apply Subsingleton.elim)) (by
          intro V W g
          apply Over.OverMorphism.ext
          apply MorphismProperty.Comma.Hom.ext
          · change g.left.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left.left
            simp
          · apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _)) (by
      intro V W g
      apply MorphismProperty.Comma.Hom.ext
      · change g.left ≫ 𝟙 _ = 𝟙 _ ≫ g.left
        simp
      · apply Subsingleton.elim)

/-- The slice-to-site functor preserves covers. -/
theorem etaleOverFunctor_coverPreserving {X : Scheme.{u}} (U : X.Etale) :
    CoverPreserving ((smallEtaleTopology X).over U) (smallEtaleTopology U.left)
      ((etaleOverEquivalence U).functor) := by
  constructor
  intro V S hS
  obtain ⟨members, W, g, rfl⟩ := S.exists_eq_ofArrows
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hS
  rw [Sieve.functorPushforward_ofArrows, ofArrows_mem_smallEtaleTopology_iff]
  exact (ofArrows_mem_smallEtaleTopology_iff (fun member ↦ (g member).left)).mp hS

/-- The site-to-slice functor preserves covers. -/
theorem etaleOverInverse_coverPreserving {X : Scheme.{u}} (U : X.Etale) :
    CoverPreserving (smallEtaleTopology U.left) ((smallEtaleTopology X).over U)
      ((etaleOverEquivalence U).inverse) := by
  constructor
  intro V S hS
  obtain ⟨members, W, g, rfl⟩ := S.exists_eq_ofArrows
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows, ofArrows_mem_smallEtaleTopology_iff]
  exact (ofArrows_mem_smallEtaleTopology_iff g).mp hS

/-- `U_étale` is a dense subsite of the slice of `X_étale` over `U`. -/
theorem etaleOverInverse_isDenseSubsite {X : Scheme.{u}} (U : X.Etale) :
    (etaleOverEquivalence U).inverse.IsDenseSubsite
      (smallEtaleTopology U.left) ((smallEtaleTopology X).over U) := by
  have : (etaleOverEquivalence U).functor.IsCocontinuous
      ((smallEtaleTopology X).over U) (smallEtaleTopology U.left) :=
    ((etaleOverEquivalence U).toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (etaleOverInverse_coverPreserving U)
  have : (etaleOverEquivalence U).inverse.IsCocontinuous
      (smallEtaleTopology U.left) ((smallEtaleTopology X).over U) :=
    ((etaleOverEquivalence U).symm.toAdjunction.isCocontinuous_iff_coverPreserving
      _ _).mpr (etaleOverFunctor_coverPreserving U)
  exact Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- **Sheaves on the slice of `X_étale` over `U` are sheaves on `U_étale`.** -/
def etaleOverSheafEquivalence {X : Scheme.{u}} (U : X.Etale)
    (A : Type*) [Category* A] :
    Sheaf ((smallEtaleTopology X).over U) A ≌ Sheaf (smallEtaleTopology U.left) A := by
  let := etaleOverInverse_isDenseSubsite U
  exact (etaleOverEquivalence U).sheafCongr _ _ A

/-- Restriction of a sheaf on `X_étale` to `U_étale`, through the slice over `U`. -/
def etaleOverRestriction {X : Scheme.{u}} (U : X.Etale)
    (A : Type*) [Category* A] :
    Sheaf (smallEtaleTopology X) A ⥤ Sheaf (smallEtaleTopology U.left) A :=
  (smallEtaleTopology X).overPullback A U ⋙
    (etaleOverSheafEquivalence U A).functor

/-- An étale `U`-scheme as an étale `X`-scheme, through the structure morphism of `U`. -/
def etaleOverComposition {X : Scheme.{u}} (U : X.Etale) :
    U.left.Etale ⥤ X.Etale :=
  (etaleOverEquivalence U).inverse ⋙ Over.forget U

/-- The functor `U_étale ⥤ X_étale` is continuous. -/
theorem etaleOverComposition_isContinuous {X : Scheme.{u}} (U : X.Etale) :
    (etaleOverComposition U).IsContinuous
      (smallEtaleTopology U.left) (smallEtaleTopology X) := by
  let := etaleOverInverse_isDenseSubsite U
  exact Functor.isContinuous_comp _ _ (smallEtaleTopology U.left)
    ((smallEtaleTopology X).over U) (smallEtaleTopology X)

/-- The equivalence of the slice over `U` with `U_étale` carries constant sheaves to constant
sheaves. -/
def etaleOverSheafEquivalenceConstantIso
    {X : Scheme.{u}} (U : X.Etale) (A : Type*) [Category* A]
    [HasWeakSheafify ((smallEtaleTopology X).over U) A]
    [HasWeakSheafify (smallEtaleTopology U.left) A] :
    constantSheaf ((smallEtaleTopology X).over U) A ⋙
      (etaleOverSheafEquivalence U A).functor ≅
        constantSheaf (smallEtaleTopology U.left) A := by
  let := etaleOverInverse_isDenseSubsite U
  let adj := (etaleOverEquivalence U).symm.toAdjunction
  have : (etaleOverEquivalence U).symm.functor.IsContinuous (smallEtaleTopology U.left)
      ((smallEtaleTopology X).over U) :=
    inferInstanceAs ((etaleOverEquivalence U).inverse.IsContinuous _ _)
  have : (etaleOverEquivalence U).symm.inverse.IsContinuous ((smallEtaleTopology X).over U)
      (smallEtaleTopology U.left) :=
    inferInstanceAs ((etaleOverEquivalence U).functor.IsContinuous _ _)
  let hterminal := Over.mkIdTerminal (X := U)
  exact ((constantSheafAdj ((smallEtaleTopology X).over U) A hterminal).comp
    (adj.sheafPushforwardContinuous (smallEtaleTopology U.left)
      ((smallEtaleTopology X).over U))).leftAdjointUniq
        (constantSheafAdj (smallEtaleTopology U.left) A
          (hterminal.isTerminalObj (etaleOverEquivalence U).functor (Over.mk (𝟙 U))))

/-- **Composition with `U ⟶ X` is left adjoint to base change along it**, on small étale
sites. -/
def etaleOverCompositionAdj {X : Scheme.{u}} (U : X.Etale) :
    etaleOverComposition U ⊣ smallEtaleBaseChange (X := U.left) (Y := X) U.hom :=
  letI : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) U.hom := ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) U.hom :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let P : MorphismProperty Scheme.{u} := @Etale
  let : P.IsMultiplicative := inferInstance
  let : P.IsStableUnderBaseChange := inferInstance
  (MorphismProperty.Over.mapPullbackAdj (P := P)
    (Q := (⊤ : MorphismProperty Scheme.{u})) U.hom U.prop trivial).ofNatIsoLeft
    (Iso.refl _)

/-- **Restriction to `U_étale` is left adjoint to direct image along `U ⟶ X`.** -/
def etaleOverRestrictionAdj {X : Scheme.{u}} (U : X.Etale) (A : Type*) [Category* A] :
    letI := etaleOverComposition_isContinuous U
    (etaleOverComposition U).sheafPushforwardContinuous A (smallEtaleTopology U.left)
        (smallEtaleTopology X) ⊣
      (smallEtaleBaseChange (X := U.left) (Y := X) U.hom).sheafPushforwardContinuous A
        (smallEtaleTopology X) (smallEtaleTopology U.left) :=
  letI := etaleOverComposition_isContinuous U
  (etaleOverCompositionAdj U).sheafPushforwardContinuous _ _

/-- **The inverse image along `U ⟶ X` of sheaves of modules is restriction to `U_étale`.** -/
def etaleModuleInverseImageIsoOverRestriction (Λ : Type r) [Ring Λ] {X : Scheme.{u}}
    (U : X.Etale) :
    letI := etaleOverComposition_isContinuous U
    etaleModuleInverseImage.{u, r} Λ (X := U.left) (Y := X) U.hom ≅
      (etaleOverComposition U).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
        (smallEtaleTopology U.left) (smallEtaleTopology X) :=
  (etaleModuleInverseImageAdj.{u, r} Λ (X := U.left) (Y := X) U.hom).leftAdjointUniq
    (etaleOverRestrictionAdj U (ModuleCat.{max (u + 1) r} Λ))

/-- Restriction through the slice is restriction along `U_étale ⥤ X_étale`. -/
def etaleOverRestrictionIso {X : Scheme.{u}} (U : X.Etale) (A : Type*) [Category* A] :
    letI := etaleOverComposition_isContinuous U
    etaleOverRestriction U A ≅
      (etaleOverComposition U).sheafPushforwardContinuous A (smallEtaleTopology U.left)
        (smallEtaleTopology X) :=
  Iso.refl _

/-- **A locally constant sheaf of finite type is constant on étale neighbourhoods**, in the sense
of inverse images: for a sheaf `H` of `Λ`-modules on `X_étale` satisfying Stacks 03RW's
condition and a point `x` of `X`, there are an étale `e : V ⟶ X` with `x` in its image and a
finitely generated `Λ`-module `E` with `e⁻¹ H` the constant sheaf on `E`. -/
theorem exists_etale_inverseImage_constant_of_isFiniteTypeLocallyConstant (Λ : Type r) [Ring Λ]
    {X : Scheme.{u}} (H : EtaleModules.{u, r} Λ X)
    (hH : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology H) (x : X) :
    ∃ (V : Scheme.{u}) (e : V ⟶ X) (_ : Etale e) (E : ModuleCat.{max (u + 1) r} Λ),
      x ∈ Set.range e.base ∧ ModuleCat.isFG Λ E ∧
        Nonempty ((etaleModuleInverseImage.{u, r} Λ e).obj H ≅
          (constantSheaf (smallEtaleTopology V) (ModuleCat.{max (u + 1) r} Λ)).obj E) := by
  obtain ⟨I, V, f, hcov, htriv⟩ := hH (Scheme.Etale.mk (𝟙 X))
  have hsurj := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).1 hcov
  obtain ⟨i, y, hy⟩ : ∃ i, ∃ y, (f i).left.base y = x := by
    have hx : x ∈ ⋃ i, Set.range (f i).left.base := by rw [hsurj]; trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.1 hx
    exact ⟨i, y, hy⟩
  obtain ⟨E, hE, ⟨c⟩⟩ := htriv i
  have hw : (V i).hom = (f i).left :=
    (MorphismProperty.Over.w (f i)).symm.trans (Category.comp_id _)
  refine ⟨(V i).left, (V i).hom, inferInstance, E, ⟨y, ?_⟩, hE, ⟨?_⟩⟩
  · rwa [hw]
  · exact (etaleModuleInverseImageIsoOverRestriction Λ (V i)).app H ≪≫
      (etaleOverRestrictionIso (V i) _).symm.app H ≪≫
      (etaleOverSheafEquivalence (V i) _).functor.mapIso c.symm ≪≫
      (etaleOverSheafEquivalenceConstantIso (V i) _).app E

end Stacks.EtaleCohomology

end
