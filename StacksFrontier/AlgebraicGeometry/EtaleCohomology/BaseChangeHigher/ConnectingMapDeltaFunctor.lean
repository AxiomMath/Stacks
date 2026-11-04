module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorConnectingMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapCompatibility

/-!
# The connecting morphisms of the base change ladder are those of the higher direct images

Let `h ≫ f' = e ≫ g` be a commutative square of schemes and let `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` be a short
exact sequence of abelian sheaves on the small étale site of `T`. The base change map of
[Stacks, Tag 0F02] commutes with the two connecting morphisms
`Stacks.EtaleCohomology.higherBaseChangeδSource` of `(f')⁻¹ R ⁿg_*` and
`Stacks.EtaleCohomology.higherBaseChangeδTarget` of `R ⁿh_* e⁻¹`, which are read off the
homology sequences of the images of the triangle of the sequence under the derived composites
`R(f')⁻¹ Rg_*` and `Rh_* Re⁻¹`.

This file identifies those two connecting morphisms with the connecting morphisms of the
`δ`-functor of higher direct images,
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`: the upper one is the inverse
image under `f'` of the connecting morphism of `R ⁿg_*` at the sequence, the lower one is the
connecting morphism of `R ⁿh_*` at the inverse image under `e` of the sequence. In this form they
are natural in the short exact sequence and enter the long exact sequences of the higher direct
images.

Both statements are instances of two general facts about an additive functor `F` and an exact
functor `E` between abelian categories with enough injectives: `E` applied to a connecting
morphism of `R ⁿF` is the connecting morphism of the image under `RF ⋙ RE` of the triangle of the
sequence (`Stacks.EtaleCohomology.map_rightDerivedDelta`), and the connecting morphism of the
image under `RE ⋙ RF` is the one of `R ⁿF` at the image of the sequence
(`Stacks.EtaleCohomology.rightDerivedDelta_map_of_exact`). They rest on the compatibility of the
comparisons of an exact functor with homology and with the degree-zero embedding with the
connecting morphisms, proved in
`StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorConnectingMorphism`.

## Main results

* `Stacks.EtaleCohomology.higherBaseChangeδSource_eq` — the upper connecting morphism of the
  base change ladder is the inverse image of the connecting morphism of the higher direct images.
* `Stacks.EtaleCohomology.higherBaseChangeδTarget_eq` — the lower connecting morphism is the
  connecting morphism of the higher direct images at the inverse image of the sequence.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **The generic connecting morphism of the right derived functors**, the one of
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`. -/
theorem rightDerivedDelta_eq (F : C ⥤ D) [F.Additive] {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) :
    (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F).δ hS n =
      (Stacks.DerivedIndexing.rightDerivedIso F n).hom.app S.X₃ ≫
        (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ
          (F.rightDerivedFunctorPlus.mapTriangle.obj
            (Stacks.Cohomology.BaseChange.singleTrianglePlus hS)) (n : ℤ) ((n + 1 : ℕ) : ℤ) rfl ≫
        (Stacks.DerivedIndexing.rightDerivedIso F (n + 1)).inv.app S.X₁ := rfl

end

/-- The connecting morphism of the image of a triangle under a composite is the one of the
image under the second functor of its image under the first. -/
theorem homologySequenceδ_mapTriangle_comp {𝒜 ℬ 𝒞 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞]
    [HasShift 𝒜 ℤ] [HasShift ℬ ℤ] (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ DerivedCategory.Plus 𝒞) [F.CommShift ℤ]
    [G.CommShift ℤ] (T : Pretriangulated.Triangle 𝒜) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (DerivedCategory.Plus.homologyFunctor 𝒞 0).homologySequenceδ ((F ⋙ G).mapTriangle.obj T)
        n₀ n₁ h =
      (DerivedCategory.Plus.homologyFunctor 𝒞 0).homologySequenceδ
        (G.mapTriangle.obj (F.mapTriangle.obj T)) n₀ n₁ h := by
  have h' : 1 + n₀ = n₁ := by rw [add_comm 1, h]
  exact (congrArg (fun z => ((DerivedCategory.Plus.homologyFunctor 𝒞 0).shift n₀).map z ≫ _)
      (congrArg (G.map (F.map T.mor₃) ≫ ·) (Functor.commShiftIso_comp_hom_app F G 1 T.obj₁))).trans
    (congrArg (fun z => ((DerivedCategory.Plus.homologyFunctor 𝒞 0).shift n₀).map z ≫ _)
      ((congrArg (· ≫ _) (G.map_comp _ _)).trans (Category.assoc _ _ _))).symm

private theorem source_chain {𝒳 𝒴 : Type*} [Category* 𝒳] [Category* 𝒴] (F : 𝒴 ⥤ 𝒳)
    {y₀ y₁ y₂ y₃ : 𝒴} {x₁ x₂ : 𝒳}
    {r₀ : y₀ ⟶ y₁} {δ : y₁ ⟶ y₂} {r₁ : y₂ ⟶ y₃} {c₀ : F.obj y₁ ⟶ x₁} {δR : x₁ ⟶ x₂} {δR' : x₁ ⟶ x₂}
    {c₁ : x₂ ⟶ F.obj y₂} (hδ : δR' = δR) (h : c₀ ≫ δR ≫ c₁ = F.map δ) :
    (F.map r₀ ≫ c₀) ≫ δR' ≫ c₁ ≫ F.map r₁ = F.map (r₀ ≫ δ ≫ r₁) := by
  rw [hδ, Category.assoc, reassoc_of% h, Functor.map_comp, Functor.map_comp]

variable {C D D' : Type*} [Category* C] [Category* D] [Category* D'] [Abelian C] [Abelian D]
  [Abelian D'] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
  [EnoughInjectives C] [EnoughInjectives D]

attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- **(Generic form.)** An exact functor applied to the connecting morphism of the right derived
functors of `F` is the connecting morphism of the image under `R(F) ⋙ R(E)` of the triangle of
the sequence, read through the two identifications of `E ∘ R ⁿF` with `H ⁿ(RE ∘ RF)`. -/
theorem map_rightDerivedDelta (F : C ⥤ D) [F.Additive] (E : D ⥤ D') [E.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E] (q : ℕ) {S : ShortComplex C}
    (hS : S.ShortExact) :
    (Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso F q) E ≪≫
        Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus)
          (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso E (q : ℤ)).symm).hom.app S.X₃ ≫
      (DerivedCategory.Plus.homologyFunctor D' 0).homologySequenceδ
        ((F.rightDerivedFunctorPlus ⋙ E.rightDerivedFunctorPlus).mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hS)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
      (Functor.isoWhiskerRight (Stacks.DerivedIndexing.rightDerivedIso F (q + 1)) E ≪≫
        Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus)
          (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso E ((q + 1 : ℕ) : ℤ)).symm).inv.app
          S.X₁ =
      E.map ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F).δ hS q) := by
  rw [rightDerivedDelta_eq]
  exact source_chain E (homologySequenceδ_mapTriangle_comp _ _ _ _ _ _)
    (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso_homologySequenceδ E
      (F.rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hS)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl)

/-- **The comparison `e(X)[0] ≅ Re(X[0])` as a morphism of triangles**, from the triangle of the
image of a short exact sequence to the image under `Re` of the triangle of the sequence. -/
def exactSingleTriangleHom (e : C ⥤ D) [e.Additive] [PreservesFiniteLimits e]
    [PreservesFiniteColimits e] {S : ShortComplex C} (hS : S.ShortExact) :
    Stacks.Cohomology.BaseChange.singleTrianglePlus (hS.map_of_exact e) ⟶
      e.rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hS) where
  hom₁ := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0).hom.app S.X₁
  hom₂ := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0).hom.app S.X₂
  hom₃ := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0).hom.app S.X₃
  comm₁ := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0).hom.naturality S.f
  comm₂ := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0).hom.naturality S.g
  comm₃ := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_singleδPlus e hS).symm

private theorem target_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {r₀ : o₀ ⟶ o₁} {s₃ : o₁ ⟶ o₂} {δR : o₂ ⟶ o₃} {s₁i : o₃ ⟶ o₄} {r₁ : o₄ ⟶ o₅}
    {δ : o₁ ⟶ o₄} {s₁ : o₄ ⟶ o₃} {δR' : o₂ ⟶ o₃}
    (hδ : δR' = δR) (hnat : s₃ ≫ δR = δ ≫ s₁) (hinv : s₁ ≫ s₁i = 𝟙 _) :
    (r₀ ≫ s₃) ≫ δR' ≫ s₁i ≫ r₁ = r₀ ≫ δ ≫ r₁ := by
  rw [hδ, Category.assoc, reassoc_of% hnat, reassoc_of% hinv]

/-- **(Generic form.)** The connecting morphism of the image under `Re ⋙ RG` of the triangle of a
short exact sequence, read through the identifications of `R ⁿG ∘ e` with `H ⁿ(RG ∘ Re)`, is the
connecting morphism of the right derived functors of `G` at the image of the sequence. -/
theorem rightDerivedDelta_map_of_exact (e : C ⥤ D) [e.Additive] [PreservesFiniteLimits e]
    [PreservesFiniteColimits e] (G : D ⥤ D') [G.Additive] (q : ℕ) {S : ShortComplex C}
    (hS : S.ShortExact) :
    (Functor.isoWhiskerLeft e (Stacks.DerivedIndexing.rightDerivedIso G q) ≪≫
        Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0)
          (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D' (q : ℤ))).hom.app
          S.X₃ ≫
      (DerivedCategory.Plus.homologyFunctor D' 0).homologySequenceδ
        ((e.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hS)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
      (Functor.isoWhiskerLeft e (Stacks.DerivedIndexing.rightDerivedIso G (q + 1)) ≪≫
        Functor.isoWhiskerRight (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0)
          (G.rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.homologyFunctor D' ((q + 1 : ℕ) : ℤ))).inv.app S.X₁ =
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives G).δ
        (hS.map_of_exact e) q := by
  rw [rightDerivedDelta_eq]
  exact target_chain (homologySequenceδ_mapTriangle_comp _ _ _ _ _ _)
    ((DerivedCategory.Plus.homologyFunctor D' 0).homologySequenceδ_naturality
      (G.rightDerivedFunctorPlus.mapTriangle.map (exactSingleTriangleHom e hS)) _ _ _)
    (Iso.map_hom_inv_id (G.rightDerivedFunctorPlus.mapIso
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso e 0).app S.X₁)) _)

section Etale

variable {X' S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S')

/-- **The upper connecting morphism of the base change ladder is the inverse image of the
connecting morphism of the higher direct images.** -/
theorem higherBaseChangeδSource_eq (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact) :
    higherBaseChangeδSource f' g q hS =
      (smallEtalePullbackAb f').map
        ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb g)).δ hS q) :=
  map_rightDerivedDelta (smallEtalePushforwardAb g) (smallEtalePullbackAb f') q hS

variable {Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T)

/-- **The lower connecting morphism of the base change ladder is the connecting morphism of the
higher direct images at the inverse image of the sequence.** -/
theorem higherBaseChangeδTarget_eq (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact) :
    higherBaseChangeδTarget h e q hS =
      (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
        (smallEtalePushforwardAb h)).δ (hS.map_of_exact (smallEtalePullbackAb e)) q :=
  rightDerivedDelta_map_of_exact (smallEtalePullbackAb e) (smallEtalePushforwardAb h) q hS

variable (w : h ≫ f' = e ≫ g)

private theorem ladder_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {bc₃ : o₀ ⟶ o₁} {r₃ : o₁ ⟶ o₂} {δ' : o₂ ⟶ o₃} {δT : o₁ ⟶ o₄} {r₁ : o₄ ⟶ o₃}
    {δS : o₀ ⟶ o₅} {bc₁ : o₅ ⟶ o₄}
    (hcomm : bc₃ ≫ δT = δS ≫ bc₁) (hnat : r₃ ≫ δ' = δT ≫ r₁) :
    bc₃ ≫ r₃ ≫ δ' = δS ≫ bc₁ ≫ r₁ := by
  rw [hnat, reassoc_of% hcomm]

/-- **The base change maps commute with the connecting morphisms of the higher direct images.**
Let `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` be a short exact sequence of abelian sheaves on `T_ét`, let `S'` be a
short exact sequence on `Y_ét` and let `σ : e⁻¹S ⟶ S'` be a morphism of short complexes. Then the
composites of the base change maps with `R ⁿh_*σ` commute with the connecting morphism of
`R ⁿg_*` at `S`, pulled back along `f'`, and with the connecting morphism of `R ⁿh_*` at `S'`. -/
theorem higherBaseChangeMapAb_comp_δ (q : ℕ)
    {S : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S.ShortExact)
    {S' : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1})} (hS' : S'.ShortExact)
    (σ : S.map (smallEtalePullbackAb e) ⟶ S') :
    (higherBaseChangeMapAb f' g h e w q).app S.X₃ ≫
        ((smallEtalePushforwardAb h).rightDerived q).map σ.τ₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb h)).δ hS' q =
      (smallEtalePullbackAb f').map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb g)).δ hS q) ≫
        (higherBaseChangeMapAb f' g h e w (q + 1)).app S.X₁ ≫
        ((smallEtalePushforwardAb h).rightDerived (q + 1)).map σ.τ₁ := by
  refine ladder_chain ?_ ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (smallEtalePushforwardAb h)).δ_naturality (hS.map_of_exact (smallEtalePullbackAb e)) hS' σ q)
  rw [← higherBaseChangeδTarget_eq, ← higherBaseChangeδSource_eq]
  exact higherBaseChangeMapAb_comm' f' g h e w q hS

end Etale

end Stacks.EtaleCohomology
