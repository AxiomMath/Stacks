module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsRingEquivSquare
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutModules
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# The gluing functor of Tag 08KU

Let `i : X ⟶ X'` be a thickening, `f : X ⟶ Y` affine, `Y' = Y ⨿_X X'` the pushout of
[Stacks Project, Tag 07RT] and `g : V' ⟶ Y'` a morphism, with the three base changes
`V = Y ×_{Y'} V'`, `U' = X' ×_{Y'} V'` and `U = X ×_{Y'} V'`.  The gluing functor sends a triple
`(𝒢, ℱ', φ)` to the fibre product of sheaves
`(V ⟶ V')_* 𝒢 ×_{(U ⟶ V')_* (U ⟶ U')^* ℱ'} (U' ⟶ V')_* ℱ'` on `V'`; it is right adjoint to the
comparison functor `Stacks.Pushout.baseChangeTripleFunctor` of [Stacks Project, Tag 08KU].  Over
an affine chart of `V'` the sections of the glued module are the compatible pairs of a relative
Milnor patching situation, and the glued module of a triple of relatively flat quasi-coherent
modules is quasi-coherent and flat over `Y'`.

## Main definitions

* `Stacks.Pushout.commonRestriction`: the restriction `U ⟶ V'`.
* `Stacks.Pushout.glueTargetNat` and `Stacks.Pushout.glueAmbientNat`: the two maps into
  `(U ⟶ V')_* (U ⟶ U')^* ℱ'` whose fibre product is the glued module.
* `Stacks.Pushout.tripleGluingFunctor`: the gluing functor `GluingTriple i f g ⥤ V'.Modules`.
* `Stacks.Pushout.gluingUnitApp`: the map from a module on `V'` to the glued module of its
  comparison triple.
* `Stacks.Pushout.targetOverlap` and `Stacks.Pushout.ambientOverlap`: the canonical comparisons of
  `(U ⟶ V')^* M` with the restriction of `M` to `U` through `V` and through `U'`.
* `Stacks.Pushout.tripleHomEquiv`: a morphism of triples out of the comparison triple of `M` is
  the same thing as a morphism from `M` into the glued module.
* `Stacks.Pushout.baseChangeTripleAdjunction`: the adjunction
  `baseChangeTripleFunctor i f hi g ⊣ tripleGluingFunctor i f g`.
* `Stacks.Pushout.chartToBase` and `Stacks.Pushout.chartSurjection`: the two restrictions
  `Γ(Y, (Y ⟶ Y') ⁻¹ᵁ W) ⟶ Γ(X, (X ⟶ Y') ⁻¹ᵁ W)` and
  `Γ(X', (X' ⟶ Y') ⁻¹ᵁ W) ⟶ Γ(X, (X ⟶ Y') ⁻¹ᵁ W)`.
* `Stacks.Pushout.compatibleSections`: the pairs of sections of two modules with the same image in
  a third.

## Main results

* `Stacks.Pushout.isQuasicoherent_tripleGluingFunctor_obj`: the glued module of a triple of
  quasi-coherent modules is quasi-coherent.
* `Stacks.Pushout.isAffineHom_targetRestriction`,
  `Stacks.Pushout.isAffineHom_ambientRestriction` and
  `Stacks.Pushout.isAffineHom_commonRestriction`: the three restrictions to `V'` are affine.
* `Stacks.Pushout.homEquiv_glue_condition`: a pair of morphisms out of the two restrictions of `M`
  is compatible on `U` through a triple's isomorphism if and only if the two transposes agree
  after mapping into the pushforward of the common restriction.
* `Stacks.Pushout.baseChangeTripleAdjunction_unit_app`,
  `Stacks.Pushout.baseChangeTripleAdjunction_counit_app_target` and
  `Stacks.Pushout.baseChangeTripleAdjunction_counit_app_ambient`: the unit of the adjunction is
  `Stacks.Pushout.gluingUnitApp`, and the two components of its counit are the transposes of the
  two projections of the glued module.
* `Stacks.Pushout.affineChart_isPushout`: for an affine morphism `u : B ⟶ S`, an affine open `W`
  of `S` and an affine open `T` of `A` lying over `W`, the sections of `B ×_S A` over the chart
  `(B ×_S A ⟶ A) ⁻¹ᵁ T` are the base change of `Γ(A, T)` along `Γ(S, W) ⟶ Γ(B, u ⁻¹ᵁ W)`; and
  `Stacks.Pushout.targetChart_isPushout`, `Stacks.Pushout.ambientChart_isPushout`,
  `Stacks.Pushout.commonChart_isPushout` are its three instances for `V`, `U'` and `U`.
* `Stacks.Pushout.exists_tensorEquiv_of_isPushout`: a cocartesian square of rings is a tensor
  product.
* `Stacks.Pushout.chartSections_isPullback`: `Γ(Y', W)` is the fibre product of
  `Stacks.Pushout.chartToBase` and `Stacks.Pushout.chartSurjection`;
  `Stacks.Pushout.exists_chartSituation`: for an affine open `W` of `Y'` and an open `U` of `V'`
  above it, this gives a relative Milnor patching situation
  `MilnorPatching.RelativeModuleFibreProductSituation` with `D' = Γ(V', U)`.
* `Stacks.Pushout.exists_targetChartRingEquiv`, `Stacks.Pushout.exists_ambientChartRingEquiv` and
  `Stacks.Pushout.exists_commonChartRingEquiv`: the three base-change rings `D`, `C'`, `C` of that
  situation are the chart section rings `Γ(V, (V ⟶ V') ⁻¹ᵁ U)`, `Γ(U', (U' ⟶ V') ⁻¹ᵁ U)` and
  `Γ(U, (U ⟶ V') ⁻¹ᵁ U)`; `Stacks.Pushout.chartRingEquiv_DtoC` and
  `Stacks.Pushout.chartRingEquiv_C'toC`: these isomorphisms carry `D ⟶ C` and `C' ⟶ C` to
  restriction along `U ⟶ V` and along `U ⟶ U'`.
* `Stacks.Pushout.sectionsPullbackIso`: the sections over an open of a fibre product of modules
  are the compatible pairs of sections.
* `Stacks.Pushout.exists_chartCompatibleModules`: over an affine chart, a triple gives an object of
  the categorical pullback of the two base changes of the chart's Milnor patching situation.
* `Stacks.Pushout.exists_chartGluingSectionsCompatiblePairsLinearEquiv`: over an affine chart the
  sections of the glued module are, `Γ(V', U)`-linearly, the compatible pairs of that object.
* `Stacks.Pushout.isFlatOver_tripleGluingFunctor_obj` and
  `Stacks.Pushout.flatQuasicoherent_tripleGluingFunctor_obj`: the glued module of a triple of
  relatively flat quasi-coherent modules is quasi-coherent and flat over `Y'`.

## References

* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RW](https://stacks.math.columbia.edu/tag/07RW)
* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.Pushout

variable {X X' Y V' : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f]
  (g : V' ⟶ pushout i f)

/-- The restriction `U = X ×_{Y'} V' ⟶ V'`. -/
noncomputable abbrev commonRestriction : pullback (i ≫ pushout.inl i f) g ⟶ V' :=
  pullback.snd _ _

/-- The composite `U ⟶ V ⟶ V'` is the restriction `U ⟶ V'`. -/
theorem commonToTarget_comp_restriction :
    commonToTarget i f g ≫ targetRestriction i f g = commonRestriction i f g :=
  pullback.lift_snd _ _ _

/-- The composite `U ⟶ U' ⟶ V'` is the restriction `U ⟶ V'`. -/
theorem commonToAmbient_comp_restriction :
    commonToAmbient i f g ≫ ambientRestriction i f g = commonRestriction i f g :=
  pullback.lift_snd _ _ _

/-! ### Ingredients for the affine charts -/

/-- Two equal morphisms have the same `AlgebraicGeometry.Scheme.Hom.appLE` over a fixed pair of
opens, whatever proofs of containment are supplied for either. -/
theorem appLE_congr_morphism {A B : Scheme.{u}} {p q : A ⟶ B} (h : p = q) (U : B.Opens)
    (V : A.Opens) (e₁ : V ≤ p ⁻¹ᵁ U) (e₂ : V ≤ q ⁻¹ᵁ U) :
    p.appLE U V e₁ = q.appLE U V e₂ := by
  subst h
  rfl

/-- Let `φ`, `ψ`, `α`, `β` be a cocartesian square of rings with base `R`, let `e : R ≃+* R'`
rename the base and let `φ'`, `ψ'` be the two legs out of `R'`.  Then the fourth corner `Q` is
`S ⊗_{R'} T`, by a ring isomorphism carrying `x ⊗ 1` to `α x` and `1 ⊗ y` to `β y`. -/
theorem exists_tensorEquiv_of_isPushout
    {R R' S T Q : Type u} [CommRing R] [CommRing R'] [CommRing S] [CommRing T] [CommRing Q]
    (φ : R →+* S) (ψ : R →+* T) (α : S →+* Q) (β : T →+* Q)
    (h : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)
      (CommRingCat.ofHom α) (CommRingCat.ofHom β))
    (e : R ≃+* R') (φ' : R' →+* S) (ψ' : R' →+* T)
    (hφ : φ'.comp e.toRingHom = φ) (hψ : ψ'.comp e.toRingHom = ψ) :
    letI : Algebra R' S := φ'.toAlgebra
    letI : Algebra R' T := ψ'.toAlgebra
    ∃ k : (S ⊗[R'] T) ≃+* Q,
      (∀ x : S, k (x ⊗ₜ[R'] (1 : T)) = α x) ∧ (∀ y : T, k ((1 : S) ⊗ₜ[R'] y) = β y) := by
  let : Algebra R' S := φ'.toAlgebra
  let : Algebra R' T := ψ'.toAlgebra
  let : Algebra S Q := α.toAlgebra
  let : Algebra T Q := β.toAlgebra
  let : Algebra R' Q := (β.comp ψ').toAlgebra
  have h' : IsPushout (CommRingCat.ofHom φ') (CommRingCat.ofHom ψ')
      (CommRingCat.ofHom α) (CommRingCat.ofHom β) := by
    apply h.of_iso e.toCommRingCatIso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · exact CommRingCat.hom_ext hφ.symm
    · exact CommRingCat.hom_ext hψ.symm
    · simp
    · simp
  let : IsScalarTower R' T Q := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R' S Q := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom h'.w).symm
  let : Algebra.IsPushout R' S T Q := CommRingCat.isPushout_iff_isPushout.mp h'
  refine ⟨(Algebra.IsPushout.equiv R' S T Q).toRingEquiv, fun x ↦ ?_, fun y ↦ ?_⟩
  · show Algebra.IsPushout.equiv R' S T Q (x ⊗ₜ[R'] (1 : T)) = α x
    rw [Algebra.IsPushout.equiv_tmul, map_one, mul_one]
    rfl
  · show Algebra.IsPushout.equiv R' S T Q ((1 : S) ⊗ₜ[R'] y) = β y
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    rfl

/-- Base changing the second tensor factor fixes the image of the first: `d ⊗ 1` goes to
`d ⊗ 1`. -/
theorem tensorMap_includeLeft {R D B A : Type u} [CommRing R] [CommRing D] [CommRing B]
    [CommRing A] [Algebra R D] [Algebra R B] [Algebra R A] (h : B →ₐ[R] A) (d : D) :
    Algebra.TensorProduct.map (AlgHom.id R D) h
        (Algebra.TensorProduct.includeLeftRingHom d) =
      (d ⊗ₜ[R] (1 : A)) := by
  have h1 : (Algebra.TensorProduct.includeLeftRingHom d : D ⊗[R] B) =
      d ⊗ₜ[R] (1 : B) := rfl
  rw [h1, Algebra.TensorProduct.map_tmul]
  simp

/-- The preimage of `W` in `X` along `X ⟶ X' ⟶ Y'` is its preimage along `X ⟶ Y ⟶ Y'`. -/
theorem commonBase_eq_targetBase (W : (pushout i f).Opens) :
    (i ≫ pushout.inl i f) ⁻¹ᵁ W = f ⁻¹ᵁ (pushout.inr i f ⁻¹ᵁ W) :=
  congrArg (fun k : X ⟶ pushout i f ↦ k ⁻¹ᵁ W) (pushout.condition (f := i) (g := f))

/-- The preimage of `W` in `X` along `X ⟶ X' ⟶ Y'` is contained in the preimage of the chart
`(Y ⟶ Y') ⁻¹ᵁ W` along `f`. -/
theorem commonBase_le_targetBase (W : (pushout i f).Opens) :
    (i ≫ pushout.inl i f) ⁻¹ᵁ W ≤ f ⁻¹ᵁ (pushout.inr i f ⁻¹ᵁ W) :=
  le_of_eq (commonBase_eq_targetBase i f W)

/-- The restriction `Γ(Y, (Y ⟶ Y') ⁻¹ᵁ W) ⟶ Γ(X, (X ⟶ Y') ⁻¹ᵁ W)` along `f`. -/
noncomputable abbrev chartToBase (W : (pushout i f).Opens) :
    Γ(Y, pushout.inr i f ⁻¹ᵁ W) →+* Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W) :=
  (f.appLE (pushout.inr i f ⁻¹ᵁ W) ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
    (commonBase_le_targetBase i f W)).hom

/-- The restriction `Γ(X', (X' ⟶ Y') ⁻¹ᵁ W) ⟶ Γ(X, (X ⟶ Y') ⁻¹ᵁ W)` along `i`. -/
noncomputable abbrev chartSurjection (W : (pushout i f).Opens) :
    Γ(X', pushout.inl i f ⁻¹ᵁ W) →+* Γ(X, (i ≫ pushout.inl i f) ⁻¹ᵁ W) :=
  (i.appLE (pushout.inl i f ⁻¹ᵁ W) ((i ≫ pushout.inl i f) ⁻¹ᵁ W) le_rfl).hom

/-- The restriction `Γ(Y', W) ⟶ Γ(Y, (Y ⟶ Y') ⁻¹ᵁ W)` followed by `Stacks.Pushout.chartToBase`
is the restriction `Γ(Y', W) ⟶ Γ(X, (X ⟶ Y') ⁻¹ᵁ W)` along `X ⟶ Y'`. -/
theorem app_comp_chartToBase (W : (pushout i f).Opens) :
    (pushout.inr i f).app W ≫
        f.appLE (pushout.inr i f ⁻¹ᵁ W) ((i ≫ pushout.inl i f) ⁻¹ᵁ W)
          (commonBase_le_targetBase i f W) =
      (i ≫ pushout.inl i f).app W := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact (appLE_congr_morphism (pushout.condition (f := i) (g := f)).symm W
    ((i ≫ pushout.inl i f) ⁻¹ᵁ W) _ le_rfl).trans (Scheme.Hom.appLE_eq_app _)

/-- The chart of `U` in `U` lies over the chart of `U` in `V`. -/
theorem commonChart_le_targetChart (U : V'.Opens) :
    commonRestriction i f g ⁻¹ᵁ U ≤
      commonToTarget i f g ⁻¹ᵁ (targetRestriction i f g ⁻¹ᵁ U) :=
  by rw [← commonToTarget_comp_restriction]; exact (Scheme.Hom.comp_preimage _ _ _).le

/-- The chart of `U` in `U` lies over the chart of `U` in `U'`. -/
theorem commonChart_le_ambientChart (U : V'.Opens) :
    commonRestriction i f g ⁻¹ᵁ U ≤
      commonToAmbient i f g ⁻¹ᵁ (ambientRestriction i f g ⁻¹ᵁ U) :=
  by rw [← commonToAmbient_comp_restriction]; exact (Scheme.Hom.comp_preimage _ _ _).le

/-- The projection `U ⟶ V ⟶ Y` is `U ⟶ X ⟶ Y`. -/
theorem commonToTarget_comp_base :
    commonToTarget i f g ≫ targetBase i f g = pullback.fst (i ≫ pushout.inl i f) g ≫ f :=
  pullback.lift_fst _ _ _

/-- The projection `U ⟶ U' ⟶ X'` is `U ⟶ X ⟶ X'`. -/
theorem commonToAmbient_comp_base :
    commonToAmbient i f g ≫ ambientBase i f g = pullback.fst (i ≫ pushout.inl i f) g ≫ i :=
  pullback.lift_fst _ _ _

variable {i f g}

/-- The first component of a triple, as a functor. -/
noncomputable abbrev tripleTarget :
    GluingTriple i f g ⥤ (pullback (pushout.inr i f) g).Modules where
  obj T := T.target
  map φ := φ.target

/-- The second component of a triple, as a functor. -/
noncomputable abbrev tripleAmbient :
    GluingTriple i f g ⥤ (pullback (pushout.inl i f) g).Modules where
  obj T := T.ambient
  map φ := φ.ambient

variable (i f g)

/-- `T ↦ (V ⟶ V')_* T.target`. -/
noncomputable abbrev glueTargetFunctor : GluingTriple i f g ⥤ V'.Modules :=
  tripleTarget ⋙ Scheme.Modules.pushforward (targetRestriction i f g)

/-- `T ↦ (U' ⟶ V')_* T.ambient`. -/
noncomputable abbrev glueAmbientFunctor : GluingTriple i f g ⥤ V'.Modules :=
  tripleAmbient ⋙ Scheme.Modules.pushforward (ambientRestriction i f g)

/-- `T ↦ (U ⟶ V')_* (U ⟶ U')^* T.ambient`. -/
noncomputable abbrev glueCommonFunctor : GluingTriple i f g ⥤ V'.Modules :=
  tripleAmbient ⋙ Scheme.Modules.pullback (commonToAmbient i f g) ⋙
    Scheme.Modules.pushforward (commonRestriction i f g)

/-- The unit of `(U ⟶ V)^* ⊣ (U ⟶ V)_*`, pushed forward to `V'`: a module on `V` maps to the
pushforward to `V'` of its restriction to `U`. -/
noncomputable def targetUnitNat :
    Scheme.Modules.pushforward (targetRestriction i f g) ⟶
      Scheme.Modules.pullback (commonToTarget i f g) ⋙
        Scheme.Modules.pushforward (commonRestriction i f g) :=
  Functor.whiskerRight
      (Scheme.Modules.pullbackPushforwardAdjunction (commonToTarget i f g)).unit
      (Scheme.Modules.pushforward (targetRestriction i f g)) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback (commonToTarget i f g))
      ((Scheme.Modules.pushforwardComp (commonToTarget i f g)
          (targetRestriction i f g)).hom ≫
        (Scheme.Modules.pushforwardCongr (commonToTarget_comp_restriction i f g)).hom)

/-- The unit of `(U ⟶ U')^* ⊣ (U ⟶ U')_*`, pushed forward to `V'`: a module on `U'` maps to the
pushforward to `V'` of its restriction to `U`. -/
noncomputable def ambientUnitNat :
    Scheme.Modules.pushforward (ambientRestriction i f g) ⟶
      Scheme.Modules.pullback (commonToAmbient i f g) ⋙
        Scheme.Modules.pushforward (commonRestriction i f g) :=
  Functor.whiskerRight
      (Scheme.Modules.pullbackPushforwardAdjunction (commonToAmbient i f g)).unit
      (Scheme.Modules.pushforward (ambientRestriction i f g)) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback (commonToAmbient i f g))
      ((Scheme.Modules.pushforwardComp (commonToAmbient i f g)
          (ambientRestriction i f g)).hom ≫
        (Scheme.Modules.pushforwardCongr (commonToAmbient_comp_restriction i f g)).hom)

/-- The comparison from the pushforward of the first component of a triple into the pushforward
of the common restriction, using the triple's isomorphism. -/
noncomputable def glueTargetNat :
    glueTargetFunctor i f g ⟶ glueCommonFunctor i f g where
  app T := (targetUnitNat i f g).app T.target ≫
    (Scheme.Modules.pushforward (commonRestriction i f g)).map T.comparison.hom
  naturality T T' φ := by
    have hθ := (targetUnitNat i f g).naturality (GluingTripleHom.target φ)
    dsimp only [glueTargetFunctor, glueAmbientFunctor, glueCommonFunctor, Functor.comp_map,
      tripleTarget, tripleAmbient]
    rw [← Category.assoc, hθ, Category.assoc, Category.assoc,
      ← (Scheme.Modules.pushforward (commonRestriction i f g)).map_comp]
    simp only [Functor.comp_map]
    rw [← (Scheme.Modules.pushforward (commonRestriction i f g)).map_comp, φ.comm]

/-- The comparison from the pushforward of the second component of a triple into the pushforward
of the common restriction. -/
noncomputable def glueAmbientNat :
    glueAmbientFunctor i f g ⟶ glueCommonFunctor i f g :=
  Functor.whiskerLeft tripleAmbient (ambientUnitNat i f g)

/-- The gluing functor of [Stacks Project, Tag 08KU]: a triple `(𝒢, ℱ', φ)` is sent to the
fibre product
`(V ⟶ V')_* 𝒢 ×_{(U ⟶ V')_* (U ⟶ U')^* ℱ'} (U' ⟶ V')_* ℱ'` on `V'`. -/
noncomputable def tripleGluingFunctor : GluingTriple i f g ⥤ V'.Modules where
  obj T := pullback ((glueTargetNat i f g).app T) ((glueAmbientNat i f g).app T)
  map φ := pullback.map _ _ _ _ ((glueTargetFunctor i f g).map φ)
    ((glueAmbientFunctor i f g).map φ) ((glueCommonFunctor i f g).map φ)
    ((glueTargetNat i f g).naturality φ).symm ((glueAmbientNat i f g).naturality φ).symm
  map_id T := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    · rw [pullback.lift_snd, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  map_comp φ ψ := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        CategoryTheory.Functor.map_comp, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        CategoryTheory.Functor.map_comp, Category.assoc]

/-! ### Affineness of the three restrictions -/

/-- The base change of an affine morphism along any morphism is affine. -/
private theorem isAffineHom_pullback_snd {A B C : Scheme.{u}} (p : A ⟶ C) (q : B ⟶ C)
    [IsAffineHom p] : IsAffineHom (pullback.snd p q) :=
  AlgebraicGeometry.isAffineHom_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback p q) inferInstance

open Stacks.Thickenings in
/-- The restriction `V ⟶ V'` is affine. -/
theorem isAffineHom_targetRestriction (hi : IsThickening i) [IsAffineHom f] :
    IsAffineHom (targetRestriction i f g) := by
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  exact isAffineHom_pullback_snd _ _

open Stacks.Thickenings in
/-- The restriction `U' ⟶ V'` is affine. -/
theorem isAffineHom_ambientRestriction (hi : IsThickening i) [IsAffineHom f] :
    IsAffineHom (ambientRestriction i f g) := by
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  exact isAffineHom_pullback_snd _ _

open Stacks.Thickenings in
/-- The restriction `U ⟶ V'` is affine. -/
theorem isAffineHom_commonRestriction (hi : IsThickening i) [IsAffineHom f] :
    IsAffineHom (commonRestriction i f g) := by
  have : IsClosedImmersion i := hi.1
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  exact isAffineHom_pullback_snd (i ≫ pushout.inl i f) g

/-! ### Quasi-coherence of the glued module -/

/-- A fibre product of quasi-coherent modules is quasi-coherent. -/
private theorem isQuasicoherent_pullback_modules {Z : Scheme.{u}} {P Q R : Z.Modules}
    (u : P ⟶ R) (v : Q ⟶ R) (hP : P.IsQuasicoherent) (hQ : Q.IsQuasicoherent)
    (hR : R.IsQuasicoherent) : (pullback u v).IsQuasicoherent := by
  have := hR
  have hbi : (P ⊞ Q).IsQuasicoherent := directSum_isQuasicoherent _ _ _
  have : (kernel (biprod.desc u (-v))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel _
  have e : kernel (biprod.desc u (-v)) ≅ pullback u v :=
    IsLimit.conePointUniqueUpToIso (kernelIsKernel (biprod.desc u (-v)))
      (CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct u v)
  exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e inferInstance

open Stacks.Thickenings in
/-- The glued module of a triple of quasi-coherent modules is quasi-coherent. -/
theorem isQuasicoherent_tripleGluingFunctor_obj (hi : IsThickening i) [IsAffineHom f]
    (T : GluingTriple i f g) (hG : T.target.IsQuasicoherent)
    (hF : T.ambient.IsQuasicoherent) :
    ((tripleGluingFunctor i f g).obj T).IsQuasicoherent := by
  have := hG
  have := hF
  have : IsAffineHom (targetRestriction i f g) := isAffineHom_targetRestriction i f g hi
  have : IsAffineHom (ambientRestriction i f g) := isAffineHom_ambientRestriction i f g hi
  have : IsAffineHom (commonRestriction i f g) := isAffineHom_commonRestriction i f g hi
  have : ((Scheme.Modules.pullback (commonToAmbient i f g)).obj T.ambient).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (commonToAmbient i f g).toLRSHom.toShHom T.ambient hF
  exact isQuasicoherent_pullback_modules _ _
    (inferInstanceAs
      (((Scheme.Modules.pushforward (targetRestriction i f g)).obj T.target).IsQuasicoherent))
    (inferInstanceAs
      (((Scheme.Modules.pushforward (ambientRestriction i f g)).obj T.ambient).IsQuasicoherent))
    (inferInstanceAs (((Scheme.Modules.pushforward (commonRestriction i f g)).obj
      ((Scheme.Modules.pullback (commonToAmbient i f g)).obj T.ambient)).IsQuasicoherent))

end Stacks.Pushout

end
