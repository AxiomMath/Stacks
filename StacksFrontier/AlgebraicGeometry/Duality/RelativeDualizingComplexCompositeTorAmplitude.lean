module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeDiagonal
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChangeFull
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeOpenImmersion
public import StacksFrontier.Homology.TorAmplitude.CompositionCanonical
public import StacksFrontier.Homology.TorAmplitude.Module

/-!
# Tor amplitude of `L pr₁^*M` over the diagonal open of the base

Let `g : X ⟶ S` and `f : Y ⟶ X` be morphisms of schemes with `f` flat and locally of finite
presentation, let `W ⊆ X ×_S X` and `W' ⊆ Y ×_S Y` be the diagonal opens of the proof of
Stacks 0E30 (`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.comp`), and let `M ∈ D(𝒪_Y)` be
`X`-perfect. Then `L pr₁^*M|_{W'}` has, locally on `W'`, bounded Tor amplitude over `𝒪_W` along
`f × f : W' ⟶ W`.

Over rings this is the statement that for `R → A → B` with `B` flat over `A` and a `B`-complex
`M` of finite Tor amplitude over `A`, the complex `M ⊗_B (B ⊗_R B) = M ⊗_R B` has finite Tor
amplitude over `A ⊗_R A`. Geometrically, `f × f` factors as

`Y ×_S Y ──f × 1──> X ×_S Y ──1 × f──> X ×_S X`,

the square formed by `pr₁ : Y ×_S Y ⟶ Y`, `f × 1`, `f` and `pr₁ : X ×_S Y ⟶ X` is cartesian, so
Tor-independent base change (Stacks 0C0V) carries the Tor amplitude of `M` over `X` to that of
`L pr₁^*M` over `X ×_S Y`, and `1 × f` is flat, so restriction of scalars along its local rings
keeps the amplitude (Stacks 066K with `d = 0`).

## Main results

* `AlgebraicGeometry.hasTorAmplitudeOver_comp_of_flat`: Tor amplitude over the base is kept by
  composing the base morphism with a flat morphism.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isPullback_prodLeftMap`: the cartesian square above.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_hasTorAmplitudeOver_compProd`: the statement
  above.

## References

* [Stacks Project, Lemma 48.28.11 (Tag 0E30)](https://stacks.math.columbia.edu/tag/0E30)
* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Tag 066K](https://stacks.math.columbia.edu/tag/066K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open StacksDraft.TorAmplitude
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **Restriction of scalars along a flat ring map keeps Tor amplitude**, in the form of a
factorisation `τ = σ ∘ ρ` with `ρ` flat: if a complex of `A`-modules read over `S` along `σ` has
Tor amplitude in `[a, b]`, then read over `R` along `τ` it has Tor amplitude in `[a, b]`. This is
Stacks 066K with `d = 0`, the flat `R`-algebra `S` having Tor amplitude in `[0, 0]`. -/
theorem hasTorAmplitudeCanonicalLift_restrictScalars_comp_of_flat
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (σ : S →+* A) (ρ : R →+* S) (τ : R →+* A) (hρ : ρ.Flat) (hτ : τ = σ.comp ρ)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (h : HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars τ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) a b := by
  have hB : HasTorAmplitudeCanonicalLift.{u, u, u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of S S))) (-0) 0 := by
    refine BaseChangeTorAmplitude.hasTorAmplitudeCanonical_moduleLift _ _ _ ?_
    refine (hasTorAmplitudeCanonical_iff_hasFlatRepresentative _ _ _ _).2 ?_
    exact (hasFlatRepresentative_single_zero_iff _).2 hρ
  have h1 := hasTorAmplitudeCanonicalLift_restrictScalars_of_torDimensionLE ρ
    (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) a b 0 hB h
  rw [sub_zero] at h1
  exact hasTorAmplitudeCanonicalLift_of_iso (DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso
      (ModuleCat.restrictScalarsComp'.{u} ρ σ τ hτ).symm (ComplexShape.up ℤ)).app M)) a b h1

/-- **Tor amplitude over the base is kept by composing the base morphism with a flat
morphism.** At every point the stalk complex is read over the local ring of `Z` instead of that
of `Y`, along a flat local homomorphism, and restriction of scalars along a flat ring map keeps
Tor amplitude. -/
theorem hasTorAmplitudeOver_comp_of_flat {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) [Flat b]
    (E : DerivedCategory X.Modules) (c d : ℤ) (h : HasTorAmplitudeOver a E c d) :
    HasTorAmplitudeOver (a ≫ b) E c d := by
  obtain ⟨K, hK, hx⟩ := h
  exact ⟨K, hK, fun x => hasTorAmplitudeCanonicalLift_restrictScalars_comp_of_flat
    (a.stalkMap x).hom (b.stalkMap (a.base x)).hom ((a ≫ b).stalkMap x).hom
    (Flat.stalkMap b (a.base x)) (Stacks.ModuleSkyscraper.stalkMap_hom_comp a b x) _ c d (hx x)⟩

/-- Tor amplitude over the base along equal morphisms. -/
theorem hasTorAmplitudeOver_of_eq {X S : Scheme.{u}} {k₁ k₂ : X ⟶ S} (h : k₁ = k₂)
    {E : DerivedCategory X.Modules} {c d : ℤ} (hk : HasTorAmplitudeOver k₁ E c d) :
    HasTorAmplitudeOver k₂ E c d :=
  h ▸ hk

namespace Scheme.Hom.DiagonalOpen

variable {X Y S : Scheme.{u}} (g : X ⟶ S) (f : Y ⟶ X)

/-- The map `f × 1 : Y ×_S Y ⟶ X ×_S Y`. -/
abbrev prodLeftMap : pullback (f ≫ g) (f ≫ g) ⟶ pullback g (f ≫ g) :=
  pullback.map (f ≫ g) (f ≫ g) g (f ≫ g) f (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The map `1 × f : X ×_S Y ⟶ X ×_S X`. -/
abbrev prodRightMap : pullback g (f ≫ g) ⟶ pullback g g :=
  pullback.map g (f ≫ g) g g (𝟙 _) f (𝟙 _) (by simp) (by simp)

/-- `f × f = (1 × f) ∘ (f × 1)`. -/
theorem prodLeftMap_comp_prodRightMap : prodLeftMap g f ≫ prodRightMap g f = prodMap g f := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id]

/-- **`Y ×_S Y = Y ×_X (X ×_S Y)`**: the square formed by the two first projections, `f` and
`f × 1` is cartesian. -/
theorem isPullback_prodLeftMap :
    IsPullback (pullback.fst (f ≫ g) (f ≫ g)) (prodLeftMap g f) f (pullback.fst g (f ≫ g)) := by
  refine IsPullback.of_bot ?_ (by rw [pullback.lift_fst])
    (IsPullback.of_hasPullback g (f ≫ g))
  rw [pullback.lift_snd, Category.comp_id]
  exact IsPullback.of_hasPullback (f ≫ g) (f ≫ g)

/-- If `f` is flat, then `1 × f : X ×_S Y ⟶ X ×_S X` is flat. -/
theorem flat_prodRightMap [Flat f] : Flat (prodRightMap g f) :=
  MorphismProperty.pullbackMap (P := @Flat) (inferInstanceAs (Flat (𝟙 X)))
    (inferInstanceAs (Flat f)) rfl rfl

variable {g f} (Dg : DiagonalOpen g) (Df : DiagonalOpen f)

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- **`L pr₁^*M|_{W'}` has locally bounded Tor amplitude over `W` along `f × f`.** For `M`
perfect relative to `X`, every point of the diagonal open `W'` of `f ≫ g` has an open
neighbourhood `U` on which `L pr₁^*M` has Tor amplitude in some `[c, d]` over `𝒪_W`, read along
`f × f : W' ⟶ W`. -/
theorem exists_hasTorAmplitudeOver_compProd [Flat f] [LocallyOfFinitePresentation f]
    (M : DerivedCategory Y.Modules)
    (hM : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage X.toRingedSpace f.base)) M) :
    ∀ w : (Dg.comp Df).W, ∃ U : (Dg.comp Df).W.Opens, w ∈ U ∧ ∃ c d : ℤ,
      HasTorAmplitudeOver (U.ι ≫ Dg.compProd Df)
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
          ((Dg.comp Df).derivedPullbackProj M)) c d := by
  intro w
  have : Flat (prodRightMap g f) := flat_prodRightMap g f
  let ιW : (Dg.comp Df).W ⟶ pullback (f ≫ g) (f ≫ g) := (Dg.compOpen Df).ι
  have : IsOpenImmersion ιW := inferInstanceAs (IsOpenImmersion (Dg.compOpen Df).ι)
  obtain ⟨_, ⟨U, hU, rfl⟩, hwU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((Dg.comp Df).proj.base w)) isOpen_univ
  -- `M|_U` has Tor amplitude in some `[c, d]` over `X`
  have hchart := chartHasFiniteTorDimension_of_locallyHasFiniteTorDimension f M hM.2 U hU
  have e₁ : U ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  obtain ⟨c, d, hcd⟩ := (chartTorSpellingsAgree f M ⊤ U e₁).1 hchart
  have hcd' := (hasTorAmplitudeOver_comp_iff_of_isOpenImmersion _ (⊤ : X.Opens).ι _ c d).2 hcd
  rw [Scheme.Hom.resLE_comp_ι] at hcd'
  -- base change along the cartesian square, then compose with the flat `1 × f`
  let O : (pullback (f ≫ g) (f ≫ g)).Opens := pullback.fst (f ≫ g) (f ≫ g) ⁻¹ᵁ U
  have hO := hasTorAmplitudeOver_comp_of_flat _ (prodRightMap g f) _ c d
    (hasTorAmplitudeOver_restrict_derivedPullback (isPullback_prodLeftMap g f) U M c d hcd')
  rw [Category.assoc, prodLeftMap_comp_prodRightMap] at hO
  -- restrict to `W' ∩ pr₁⁻¹(U)`
  refine ⟨ιW ⁻¹ᵁ O, hwU, c, d, ?_⟩
  have : IsOpenImmersion (ιW ∣_ O) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_morphismRestrict ιW O).flip
      (inferInstanceAs (IsOpenImmersion (Dg.compOpen Df).ι))
  have hmor : (ιW ∣_ O) ≫ O.ι ≫ prodMap g f = ((ιW ⁻¹ᵁ O).ι ≫ Dg.compProd Df) ≫ Dg.ι := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    exact (congrArg ((ιW ⁻¹ᵁ O).ι ≫ ·) (compProd_ι Dg Df).symm).trans (Category.assoc _ _ _).symm
  have hV' := (hasTorAmplitudeOver_comp_iff_of_isOpenImmersion
    ((ιW ⁻¹ᵁ O).ι ≫ Dg.compProd Df) Dg.ι _ c d).1 (hasTorAmplitudeOver_of_eq hmor
      (hasTorAmplitudeOver_derivedPullback_of_isOpenImmersion (O.ι ≫ prodMap g f) (ιW ∣_ O) _ c d
        hO))
  have hs : ιW.toLRSHom.toShHom ≫ (pullback.fst (f ≫ g) (f ≫ g)).toLRSHom.toShHom =
      (Dg.comp Df).proj.toLRSHom.toShHom := rfl
  let e₂ : (derivedPullback ιW.toLRSHom.toShHom).obj
      ((derivedPullback (pullback.fst (f ≫ g) (f ≫ g)).toLRSHom.toShHom).obj M) ≅
        (Dg.comp Df).derivedPullbackProj M :=
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      ιW.toLRSHom.toShHom (pullback.fst (f ≫ g) (f ≫ g)).toLRSHom.toShHom).app M ≪≫
    eqToIso (congrArg (fun k => (derivedPullback k).obj M) hs)
  let e₁ := Scheme.Modules.openRestrictionDerivedPullbackIso (ιW ⁻¹ᵁ O).ι ιW O.ι (ιW ∣_ O)
    (morphismRestrict_ι ιW O).symm
    ((derivedPullback (pullback.fst (f ≫ g) (f ≫ g)).toLRSHom.toShHom).obj M)
  exact hasTorAmplitudeOver_of_iso
    (e₁.symm ≪≫ (Scheme.Modules.restrictFunctor (ιW ⁻¹ᵁ O).ι).mapDerivedCategory.mapIso e₂) c d hV'

end Scheme.Hom.DiagonalOpen

end AlgebraicGeometry

end
