module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.LadderAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleHigherBaseChangePasting
public import StacksFrontier.CategoryTheory.Triangulated.TStructureThirdSquare

/-!
# The connecting morphisms of higher direct images, and the base change map

For a morphism of schemes `g : T ⟶ S` and a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
abelian sheaves on the small étale site of `T`, this file constructs the connecting morphism
`δ : R^q g_* X₃ ⟶ R^{q+1} g_* X₁` of the long exact sequence of higher direct images, as the
connecting morphism of the long exact homology sequence of the bounded below derived category
attached to the image under `Rg_*` of the triangle `X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[0]⟦1⟧`, read
through the comparison `Stacks.DerivedIndexing.rightDerivedIso` of the two conventions for the
right derived functors of `g_*`.

Its relation to the base change map of [Stacks, Tag 0F02] is the point of the file. For a
commutative square `h ≫ f' = e ≫ g` and a morphism `σ : e⁻¹S ⟶ S'` from the inverse image of a
short exact sequence `S` on `T` to a short exact sequence `S'` on `Y`, the composite of the base
change map with `R^q h_* σ` commutes with the connecting morphisms:
`higherBaseChangeδSource` of `S` on the source, and `δ` of `S'` on the target.

## Main definitions

* `Stacks.EtaleCohomology.directImageTriangleδ` — the connecting morphism
  `R^q g_* X₃ ⟶ R^{q+1} g_* X₁`.

## Main results

* `Stacks.EtaleCohomology.exact_directImage_map_g_δ`,
  `Stacks.EtaleCohomology.epi_directImageTriangleδ` — the long exact sequence at `R^q g_* X₃`,
  and the surjectivity of `δ` when `R^{q+1} g_* X₂` vanishes.
* `Stacks.EtaleCohomology.higherBaseChangeδTarget_comp_map` — the connecting morphism of the
  target `R^q h_* e⁻¹` of the base change map, followed by `R^{q+1} h_* σ₁`, is `R^q h_* σ₃`
  followed by `δ` of `S'`.
* `Stacks.EtaleCohomology.higherBaseChangeδSource_comp_map` — **the base change map followed by
  `R h_* σ` commutes with the connecting morphisms.**

## Implementation notes

The comparison of the triangle `Re⁻¹(X₁[0] ⟶ X₂[0] ⟶ X₃[0] ⟶ X₁[0]⟦1⟧)` with the triangle of
`S'` is built from its three components alone: both triangles are distinguished, the first object
of the source is concentrated in degree `0` and so is the third object of the target, so the
third square commutes once the first two do. That is
`CategoryTheory.Pretriangulated.triangleHomOfIsLEOfIsGE` at the t-structure of the bounded below
derived category.

The bounded below derived categories are those of `HasDerivedCategory.standard`, which the base
declarations `Stacks.EtaleCohomology.higherBaseChangeMapAb` and
`Stacks.EtaleCohomology.higherBaseChangeδTarget`
(`BaseChangeHigher/BaseChangeCondition.lean:154`,
`BaseChangeHigher/ConnectingMapCompatibility.lean:409`) are stated at.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- forced by `Stacks.EtaleCohomology.higherBaseChangeMapAb`
-- (`BaseChangeHigher/BaseChangeCondition.lean:154`)
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-! ### The connecting morphism -/

section Connecting

variable {T S : Scheme.{u}} (g : T ⟶ S) (q : ℕ)
  {E : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})}

/-- **The connecting morphism `R^q g_* X₃ ⟶ R^{q+1} g_* X₁`** of a short exact sequence of
abelian sheaves on the small étale site of `T`: the connecting morphism of the long exact
homology sequence of the image under `Rg_*` of the triangle of the sequence, read through the
comparison of the two conventions for the right derived functors of `g_*`. -/
public def directImageTriangleδ (hE : E.ShortExact) :
    ((smallEtalePushforwardAb g).rightDerived q).obj E.X₃ ⟶
      ((smallEtalePushforwardAb g).rightDerived (q + 1)).obj E.X₁ :=
  (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.app E.X₃ ≫
    (DerivedCategory.Plus.homologyFunctor
        (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0).homologySequenceδ
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
    (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) (q + 1)).inv.app E.X₁

/-- The image under `Rg_*` of the triangle of a short exact sequence is distinguished. -/
public theorem mapTriangle_singleTrianglePlus_distinguished (hE : E.ShortExact) :
    (smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ∈
      distTriang (DerivedCategory.Plus (Sheaf (smallEtaleTopology S) Ab.{u + 1})) :=
  (smallEtalePushforwardAb g).rightDerivedFunctorPlus.map_distinguished _
    (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hE)

/-- The defining property of `directImageTriangleδ`: read through the comparison of the two
conventions, it is the connecting morphism of the homology sequence. -/
public theorem directImageTriangleδ_comp_rightDerivedIso (hE : E.ShortExact) :
    directImageTriangleδ g q hE ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) (q + 1)).hom.app E.X₁ =
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.app E.X₃ ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0).homologySequenceδ
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj
            (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl :=
  Stacks.Cohomology.BaseChange.conj_comp_hom
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).app E.X₃)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) (q + 1)).app E.X₁) _

/-- The long exact sequence is a complex at `R^q g_* X₃`. -/
public theorem directImage_map_g_comp_δ (hE : E.ShortExact) :
    ((smallEtalePushforwardAb g).rightDerived q).map E.g ≫ directImageTriangleδ g q hE = 0 :=
  Stacks.Cohomology.BaseChange.comp_eq_zero_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).app E.X₂)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).app E.X₃)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) (q + 1)).app E.X₁)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.naturality E.g)
    (directImageTriangleδ_comp_rightDerivedIso g q hE)
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0).comp_homologySequenceδ _
      (mapTriangle_singleTrianglePlus_distinguished g hE) _ _ rfl)

/-- **The long exact sequence is exact at `R^q g_* X₃`.** -/
public theorem exact_directImage_map_g_δ (hE : E.ShortExact) :
    (ShortComplex.mk (((smallEtalePushforwardAb g).rightDerived q).map E.g)
      (directImageTriangleδ g q hE) (directImage_map_g_comp_δ g q hE)).Exact :=
  Stacks.Cohomology.BaseChange.exact_of_iso_row
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).app E.X₂)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).app E.X₃)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) (q + 1)).app E.X₁)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.naturality E.g)
    (directImageTriangleδ_comp_rightDerivedIso g q hE) _
    ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0).homologySequence_exact₃ _
      (mapTriangle_singleTrianglePlus_distinguished g hE) _ _ rfl)

/-- **The connecting morphism is surjective when `R^{q+1} g_* X₂` vanishes.** -/
public theorem epi_directImageTriangleδ (hE : E.ShortExact)
    (hX : IsZero (((smallEtalePushforwardAb g).rightDerived (q + 1)).obj E.X₂)) :
    Epi (directImageTriangleδ g q hE) := by
  have hex := (DerivedCategory.Plus.homologyFunctor
    (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0).homologySequence_exact₁ _
    (mapTriangle_singleTrianglePlus_distinguished g hE) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl
  have hzero : IsZero (((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0).shift ((q + 1 : ℕ) : ℤ)).obj
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj E.X₂))) :=
    IsZero.of_iso hX
      ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) (q + 1)).app E.X₂).symm
  have hepi : Epi ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology S) Ab.{u + 1}) 0).homologySequenceδ
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE))
      (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl) :=
    hex.epi_f_iff.2 (hzero.eq_of_tgt _ 0)
  exact Stacks.Cohomology.BaseChange.epi_of_iso_comm
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).app E.X₃)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) (q + 1)).app E.X₁)
    (directImageTriangleδ_comp_rightDerivedIso g q hE) hepi

end Connecting

/-! ### The target of the base change map -/

section Target

variable {X' Y T : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T) (q : ℕ)
  {E : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hE : E.ShortExact)
  {E' : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1})} (hE' : E'.ShortExact)
  (σ : E.map (smallEtalePullbackAb e) ⟶ E')

/-- The component at `X` of the comparison of the image under `Re⁻¹` of `X[0]` with
`(e⁻¹X)[0]`, followed by the image under the degree-zero embedding of a map out of `e⁻¹X`. -/
abbrev singlePullbackComp {X : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    {Z : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (s : (smallEtalePullbackAb e).obj X ⟶ Z) :
    (smallEtalePullbackAb e).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj X) ⟶
      (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj Z :=
  (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso (smallEtalePullbackAb e) 0).inv.app
      X ≫
    (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).map s

/-- The squares of `singlePullbackComp` with the maps of a morphism of short complexes. -/
theorem singlePullbackComp_comm {X₁ X₂ : Sheaf (smallEtaleTopology T) Ab.{u + 1}}
    {Z₁ Z₂ : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (f : X₁ ⟶ X₂) (f' : Z₁ ⟶ Z₂)
    (s₁ : (smallEtalePullbackAb e).obj X₁ ⟶ Z₁) (s₂ : (smallEtalePullbackAb e).obj X₂ ⟶ Z₂)
    (hs : (smallEtalePullbackAb e).map f ≫ s₂ = s₁ ≫ f') :
    (smallEtalePullbackAb e).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).map f) ≫
        singlePullbackComp e s₂ =
      singlePullbackComp e s₁ ≫
        (DerivedCategory.Plus.singleFunctor
          (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).map f' := by
  have hnat := (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
    (smallEtalePullbackAb e) 0).inv.naturality f
  simp only [Functor.comp_map] at hnat
  dsimp only [singlePullbackComp]
  rw [reassoc_of% hnat, ← Functor.map_comp, hs, Functor.map_comp, Category.assoc]

/-- The image under `Re⁻¹` of the triangle of `E` is distinguished. -/
theorem mapTriangle_pullback_distinguished :
    (smallEtalePullbackAb e).rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ∈
      distTriang (DerivedCategory.Plus (Sheaf (smallEtaleTopology Y) Ab.{u + 1})) :=
  (smallEtalePullbackAb e).rightDerivedFunctorPlus.map_distinguished _
    (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hE)

/-- For a sheaf `X` on `T`, the image under `Re⁻¹` of `X` placed in degree `0` is concentrated in
degrees `≤ 0`. -/
instance isLE_pullback_single (X : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (DerivedCategory.Plus.TStructure.t).IsLE
      ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj X))
      0 :=
  haveI : (DerivedCategory.Plus.TStructure.t).IsLE
      ((smallEtalePullbackAb e ⋙
        DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj X) 0 :=
    inferInstanceAs (((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y)
      Ab.{u + 1}) 0).obj ((smallEtalePullbackAb e).obj X)).IsLE 0)
  DerivedCategory.Plus.TStructure.t.isLE_of_iso
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso (smallEtalePullbackAb e) 0).app X)
    0

/-- **The morphism of triangles attached to `σ`**: from the image under `Re⁻¹` of the triangle of
`E` to the triangle of `E'`, with components `singlePullbackComp` of the components of `σ`. -/
def pullbackTriangleHom :
    (smallEtalePullbackAb e).rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ⟶
      Stacks.Cohomology.BaseChange.singleTrianglePlus hE' :=
  haveI : (DerivedCategory.Plus.TStructure.t).IsLE
      ((smallEtalePullbackAb e).rightDerivedFunctorPlus.mapTriangle.obj
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)).obj₁ 0 :=
    isLE_pullback_single e E.X₁
  haveI : (DerivedCategory.Plus.TStructure.t).IsGE
      (Stacks.Cohomology.BaseChange.singleTrianglePlus hE').obj₃ 0 :=
    inferInstanceAs ((DerivedCategory.Plus.TStructure.t).IsGE
      ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0).obj
        E'.X₃) 0)
  triangleHomOfIsLEOfIsGE DerivedCategory.Plus.TStructure.t
    (mapTriangle_pullback_distinguished e hE)
    (Stacks.DerivedIndexing.singleTrianglePlus_distinguished hE')
    (singlePullbackComp e σ.τ₁) (singlePullbackComp e σ.τ₂) (singlePullbackComp e σ.τ₃)
    (singlePullbackComp_comm e E.f E'.f σ.τ₁ σ.τ₂ σ.comm₁₂.symm)
    (singlePullbackComp_comm e E.g E'.g σ.τ₂ σ.τ₃ σ.comm₂₃.symm)

/-- The rearrangement behind `higherBaseChangeδTarget_comp_map`, in an abstract category: the
conjugations by the comparisons of conventions cancel, and what remains is the naturality of the
connecting morphism of the homology sequence. -/
private theorem target_algebra {C : Type*} [Category* C] {P Q Q' M M' N N' K' L P' : C}
    (a : P ⟶ Q) (b : Q ⟶ Q') (d : Q' ⟶ M) (c : M ⟶ M') (a' : M' ⟶ N) (s₁ : N ⟶ N')
    (rh₁ : N ⟶ M') (t₁ : M' ⟶ K') (ri₁ : K' ⟶ N') (θ₁ : M ⟶ K') (θ₃ : Q' ⟶ L) (d' : L ⟶ K')
    (t₃ : Q ⟶ L) (s₃ : P ⟶ P') (rh₃ : P' ⟶ L)
    (h₁ : s₁ = rh₁ ≫ t₁ ≫ ri₁) (h₂ : a' ≫ rh₁ = 𝟙 _) (h₃ : c ≫ t₁ = θ₁)
    (h₄ : θ₃ ≫ d' = d ≫ θ₁) (h₅ : b ≫ θ₃ = t₃) (h₆ : s₃ ≫ rh₃ = a ≫ t₃) :
    (a ≫ b ≫ d ≫ c ≫ a') ≫ s₁ = s₃ ≫ rh₃ ≫ d' ≫ ri₁ := by
  rw [h₁, reassoc_of% h₆, ← h₅]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₃, ← reassoc_of% h₄]

/-- The naturality of the connecting morphism of the homology sequence along the morphism of
triangles `Rh_*(pullbackTriangleHom σ)`, with the triangle `Rh_*(Re⁻¹(…))` read as the image under
the composite `Re⁻¹ ⋙ Rh_*`. -/
theorem homologySequenceδ_pullbackTriangleHom :
    ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).shift
        (q : ℤ)).map ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
          (singlePullbackComp e σ.τ₃)) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1})
          0).homologySequenceδ ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hE')) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl =
    (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1})
          0).homologySequenceδ (((smallEtalePullbackAb e).rightDerivedFunctorPlus ⋙
          (smallEtalePushforwardAb h).rightDerivedFunctorPlus).mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1})
          0).shift ((q + 1 : ℕ) : ℤ)).map ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
          (singlePullbackComp e σ.τ₁)) := by
  have hnat := (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1})
    0).homologySequenceδ_naturality
    ((Functor.mapTriangleCompIso (smallEtalePullbackAb e).rightDerivedFunctorPlus
        (smallEtalePushforwardAb h).rightDerivedFunctorPlus).hom.app
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ≫
      (smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.map
        (pullbackTriangleHom e hE hE' σ)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl
  have h₁ : ((Functor.mapTriangleCompIso (smallEtalePullbackAb e).rightDerivedFunctorPlus
        (smallEtalePushforwardAb h).rightDerivedFunctorPlus).hom.app
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ≫
      (smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.map
        (pullbackTriangleHom e hE hE' σ)).hom₁ =
      (smallEtalePushforwardAb h).rightDerivedFunctorPlus.map (singlePullbackComp e σ.τ₁) :=
    Category.id_comp _
  have h₃ : ((Functor.mapTriangleCompIso (smallEtalePullbackAb e).rightDerivedFunctorPlus
        (smallEtalePushforwardAb h).rightDerivedFunctorPlus).hom.app
        (Stacks.Cohomology.BaseChange.singleTrianglePlus hE) ≫
      (smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.map
        (pullbackTriangleHom e hE hE' σ)).hom₃ =
      (smallEtalePushforwardAb h).rightDerivedFunctorPlus.map (singlePullbackComp e σ.τ₃) :=
    Category.id_comp _
  rw [h₁] at hnat
  exact (congrArg (fun z => ((DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).shift (q : ℤ)).map z ≫
    (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1})
      0).homologySequenceδ ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.mapTriangle.obj
      (Stacks.Cohomology.BaseChange.singleTrianglePlus hE')) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl)
    h₃).symm.trans hnat

/-- `higherBaseChangeδTarget`, with the two identifications it is read through written out. -/
theorem higherBaseChangeδTarget_eq_homologySequenceδ :
    higherBaseChangeδTarget h e q hE =
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) q).hom.app
          ((smallEtalePullbackAb e).obj E.X₃) ≫
        ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).shift
            (q : ℤ)).map ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb e) 0).hom.app E.X₃)) ≫
        (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1})
            0).homologySequenceδ (((smallEtalePullbackAb e).rightDerivedFunctorPlus ⋙
            (smallEtalePushforwardAb h).rightDerivedFunctorPlus).mapTriangle.obj
            (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
        ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0).shift
            ((q + 1 : ℕ) : ℤ)).map ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb e) 0).inv.app E.X₁)) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) (q + 1)).inv.app
          ((smallEtalePullbackAb e).obj E.X₁) := rfl

/-- **The connecting morphism of the target of the base change map.** For a morphism
`σ : e⁻¹E ⟶ E'` of short exact sequences on `Y`, the connecting morphism
`higherBaseChangeδTarget` of `R^q h_* e⁻¹` at `E`, followed by `R^{q+1} h_* σ₁`, is `R^q h_* σ₃`
followed by the connecting morphism `directImageTriangleδ` of `R^q h_*` at `E'`. -/
public theorem higherBaseChangeδTarget_comp_map :
    higherBaseChangeδTarget h e q hE ≫
        ((smallEtalePushforwardAb h).rightDerived (q + 1)).map σ.τ₁ =
      ((smallEtalePushforwardAb h).rightDerived q).map σ.τ₃ ≫ directImageTriangleδ h q hE' := by
  let H := DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) 0
  let Rh := (smallEtalePushforwardAb h).rightDerivedFunctorPlus
  let Re := (smallEtalePullbackAb e).rightDerivedFunctorPlus
  let rD := Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h)
  let ε := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso (smallEtalePullbackAb e) 0
  let sgl := DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) 0
  have hδ := higherBaseChangeδTarget_eq_homologySequenceδ h e q hE
  have hD : directImageTriangleδ h q hE' =
      (rD q).hom.app E'.X₃ ≫
        H.homologySequenceδ (Rh.mapTriangle.obj
          (Stacks.Cohomology.BaseChange.singleTrianglePlus hE')) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl ≫
        (rD (q + 1)).inv.app E'.X₁ := rfl
  have n₁ : ((smallEtalePushforwardAb h).rightDerived (q + 1)).map σ.τ₁ ≫
      (rD (q + 1)).hom.app E'.X₁ =
      (rD (q + 1)).hom.app ((smallEtalePullbackAb e).obj E.X₁) ≫
        (H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (sgl.map σ.τ₁)) :=
    (rD (q + 1)).hom.naturality σ.τ₁
  have n₃ : ((smallEtalePushforwardAb h).rightDerived q).map σ.τ₃ ≫ (rD q).hom.app E'.X₃ =
      (rD q).hom.app ((smallEtalePullbackAb e).obj E.X₃) ≫
        (H.shift (q : ℤ)).map (Rh.map (sgl.map σ.τ₃)) :=
    (rD q).hom.naturality σ.τ₃
  have h₁ : ((smallEtalePushforwardAb h).rightDerived (q + 1)).map σ.τ₁ =
      (rD (q + 1)).hom.app ((smallEtalePullbackAb e).obj E.X₁) ≫
        (H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (sgl.map σ.τ₁)) ≫
          (rD (q + 1)).inv.app E'.X₁ :=
    ((Iso.eq_comp_inv ((rD (q + 1)).app E'.X₁)).mpr n₁).trans (Category.assoc _ _ _)
  have h₃ : (H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (ε.inv.app E.X₁)) ≫
        (H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (sgl.map σ.τ₁)) =
      (H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (singlePullbackComp e σ.τ₁)) := by
    simp only [← Functor.map_comp]
    rfl
  have h₅ : (H.shift (q : ℤ)).map (Rh.map (ε.hom.app E.X₃)) ≫
        (H.shift (q : ℤ)).map (Rh.map (singlePullbackComp e σ.τ₃)) =
      (H.shift (q : ℤ)).map (Rh.map (sgl.map σ.τ₃)) :=
    ((H.shift (q : ℤ)).map_comp _ _).symm.trans
      (congrArg (H.shift (q : ℤ)).map ((Rh.map_comp _ _).symm.trans
        (congrArg Rh.map (ε.hom_inv_id_app_assoc E.X₃ _))))
  have key := target_algebra
    ((rD q).hom.app ((smallEtalePullbackAb e).obj E.X₃))
    ((H.shift (q : ℤ)).map (Rh.map (ε.hom.app E.X₃)))
    (H.homologySequenceδ ((Re ⋙ Rh).mapTriangle.obj
      (Stacks.Cohomology.BaseChange.singleTrianglePlus hE)) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl)
    ((H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (ε.inv.app E.X₁)))
    ((rD (q + 1)).inv.app ((smallEtalePullbackAb e).obj E.X₁))
    (((smallEtalePushforwardAb h).rightDerived (q + 1)).map σ.τ₁)
    ((rD (q + 1)).hom.app ((smallEtalePullbackAb e).obj E.X₁))
    ((H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (sgl.map σ.τ₁)))
    ((rD (q + 1)).inv.app E'.X₁)
    ((H.shift ((q + 1 : ℕ) : ℤ)).map (Rh.map (singlePullbackComp e σ.τ₁)))
    ((H.shift (q : ℤ)).map (Rh.map (singlePullbackComp e σ.τ₃)))
    (H.homologySequenceδ (Rh.mapTriangle.obj
      (Stacks.Cohomology.BaseChange.singleTrianglePlus hE')) (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl)
    ((H.shift (q : ℤ)).map (Rh.map (sgl.map σ.τ₃)))
    (((smallEtalePushforwardAb h).rightDerived q).map σ.τ₃)
    ((rD q).hom.app E'.X₃) h₁
    ((rD (q + 1)).inv_hom_id_app ((smallEtalePullbackAb e).obj E.X₁)) h₃
    (homologySequenceδ_pullbackTriangleHom h e q hE hE' σ) h₅ n₃
  rw [hδ, hD]
  exact key

end Target

/-! ### The base change map and the connecting morphisms -/

section Square

variable {X' Y S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) (q : ℕ)
  {E : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hE : E.ShortExact)
  {E' : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1})} (hE' : E'.ShortExact)
  (σ : E.map (smallEtalePullbackAb e) ⟶ E')

/-- **The base change map followed by `R h_* σ` commutes with the connecting morphisms.** For a
commutative square `h ≫ f' = e ≫ g`, a short exact sequence `E` on `T`, a short exact sequence
`E'` on `Y` and a morphism `σ : e⁻¹E ⟶ E'`, the square

```
(f')⁻¹R^q g_* X₃ ──BC ≫ R^q h_* σ₃──→ R^q h_* X₃'
       │ δSource                            │ δ
(f')⁻¹R^{q+1} g_* X₁ ─BC ≫ R^{q+1} h_* σ₁─→ R^{q+1} h_* X₁'
```

commutes. This is `Stacks.EtaleCohomology.higherBaseChangeMapAb_comm'` followed by
`higherBaseChangeδTarget_comp_map`. -/
public theorem higherBaseChangeδSource_comp_map :
    higherBaseChangeδSource f' g q hE ≫
        ((higherBaseChangeMapAb f' g h e w (q + 1)).app E.X₁ ≫
          ((smallEtalePushforwardAb h).rightDerived (q + 1)).map σ.τ₁) =
      ((higherBaseChangeMapAb f' g h e w q).app E.X₃ ≫
          ((smallEtalePushforwardAb h).rightDerived q).map σ.τ₃) ≫
        directImageTriangleδ h q hE' := by
  rw [← Category.assoc, ← higherBaseChangeMapAb_comm' f' g h e w q hE, Category.assoc,
    higherBaseChangeδTarget_comp_map h e q hE hE' σ, Category.assoc]

end Square

end Stacks.EtaleCohomology

end
