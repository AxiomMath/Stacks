module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalNoetherianReduction
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallAutomorphisms

/-!
# The diagonal of the stack of curves, reduced to H-projective families (Stacks 0DSQ)

The last two paragraphs of the proof of Stacks 0DSQ show that `Isom_U(Y, X) ⟶ U` is
quasi-compact for families of curves `Y` and `X` over a Noetherian affine scheme `U`. The source
does this in two steps:

1. It covers `Curves × Curves` by Noetherian affine schemes carrying polarized families, using
   Stacks 0DQ0.
2. For two polarized families over a Noetherian affine `U`, Riemann–Roch on the fibres
   (Stacks 0AYR, 0AYX, 0BEM, 0B9T) puts `Isom_U(Y, X)` inside `Mor^{P', ℳ}_U(Y, X)`, and that
   space is of finite presentation over `U` (Stacks 0DPR).

This module proves the first step, in its étale-local form, and takes the second as an explicit
input `hproj`.

**The first step.** Over a Noetherian affine base `V`, both families are smooth locally
polarized (`AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized`, the statement of Stacks
0DQ0 about one family). So through every point of `V` there is an affine étale `φ : U ⟶ V` along
which both families are schemes, H-projective over `U`, as in the proof of Stacks 0E6F
(`AlgebraicGeometry.CurveFamily.exists_affine_etale_sections_of_smooth`,
`AlgebraicGeometry.CurveFamily.exists_isPullback_isProjectiveMorphism_of_polarizedChart`). Such a
`U` is Noetherian, being affine and of finite type over `V`. Finitely many of these charts cover
the quasi-compact `V`. The base changes of `Isom_V(Y, X)` to them are quasi-compact algebraic
spaces by `hproj`, and they jointly surject onto `Isom_V(Y, X)`. Hence `Isom_V(Y, X)` is a
quasi-compact algebraic space (Stacks 040W), and its morphism to the affine `V` is quasi-compact
(Stacks 073B).

**The input `hproj`.** For families over a Noetherian affine `U` which are H-projective schemes
over `U`, the projection `Isom_U(Y, X) ⟶ U` is quasi-compact. This is the content of the source's
last paragraph: Stacks 0DPR, applied to `Mor^{P', ℳ}_U(Y, X)` after the Riemann–Roch computation.
It is not stated through `Mor^{P, ℳ}` here, because the invariants of Stacks 0DPQ in this
development are data (`AlgebraicGeometry.Space.HilbertOverEulerData`), not Euler
characteristics. So the Riemann–Roch identity `χ(Y_t, 𝒩_t^n ⊗ f_t^*ℒ_t^n) = Q(n) + P(n) - P(0)`,
which shows `Isom ⊆ Mor^{P', ℳ}`, cannot be stated. The input is stated instead as the
conclusion for the specific open subfunctor of `Mor^{P', ℳ}_U(Y, X)` that the source uses,
namely `Isom_U(Y, X)`, and only its quasi-compactness over `U` is asked for. Stacks 0DPR itself
rests on Stacks 0DPI, the finite presentation of `Hilb^{P, ℳ}_{Y ×_U X / U}` over `U`, which this
development does not have either.

**Algebraicity of `Isom`.** Given the algebraicity of the stack of curves (`h`, Stacks 0D5A) and
the identification `hiso` of its isomorphism spaces with `Isom_U(Y, X)`, every `Isom_U(Y, X)` is
an algebraic space (`AlgebraicGeometry.Stack.isAlgebraicSpace_isomSpace`,
`AlgebraicGeometry.isAlgebraicSpace_viewOver`).

## Main results

* `AlgebraicGeometry.CurveFamily.isQuasiCompact_isomFunctorProjection_of_isSmoothLocallyPolarized`:
  over a Noetherian affine base, `Isom_V(Y, X) ⟶ V` is quasi-compact, from the smooth local
  polarizations and `hproj`.
* `AlgebraicGeometry.curvesSmall.isAlgebraicSpace_isomFunctor_of_isAlgebraicStack`: every
  `Isom_U(Y, X)` is an algebraic space, from `h` and `hiso`.
* In the namespace `AlgebraicGeometry`,
`isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_polarized`
  is Stacks 0DSQ from `h` (0D5A), `hlim` (0D55), `hsep` and `hiso` (`CurvesSmallIsom`), `hpol`
  (0DQ0) and `hproj` (0DPR with Riemann–Roch).

## References

* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Two families of curves are H-projective schemes over a common affine étale chart.** Let `F`
and `G` be smooth locally polarized families of curves over a common base. Through every point
`s` of the base there is an étale `φ : U ⟶ F.base` from an affine `U`, with `s` in its image,
along which both families are schemes that are H-projective over `U`. This is the proof of
Stacks 0E6F at two families, keeping the affineness of the chart. -/
theorem exists_affine_etale_isPullback_isProjectiveMorphism_pair (F G : CurveFamily B hZ)
    (hb : G.base = F.base) (hF : F.IsSmoothLocallyPolarized) (hG : G.IsSmoothLocallyPolarized)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj F.base) :
    ∃ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ F.base)
      (u : (BigFppfOver.toScheme B integerBase hZ).obj U),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ) ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) ∧
      (BigFppfOver.toScheme B integerBase hZ).map φ u = s ∧
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ F.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap φ) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) ∧
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ G.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap (φ ≫ eqToHom hb.symm)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) := by
  obtain ⟨T₁, π₁, hπ₁, hs₁, Z₁, p₁, q₁, hsq₁, L₁, hL₁, hamp₁⟩ := hF.of_base_eq rfl s
  obtain ⟨T₂, π₂, hπ₂, hs₂, Z₂, p₂, q₂, hsq₂, L₂, hL₂, hamp₂⟩ := hG.of_base_eq hb s
  let T' : Bool → BigFppfOver B integerBase hZ := fun b => Bool.rec T₂ T₁ b
  let π : ∀ b, T' b ⟶ F.base := fun b => Bool.rec (motive := fun b => T' b ⟶ F.base) π₂ π₁ b
  obtain ⟨U, φ, u, hφ, hU, hu, hg⟩ := exists_affine_etale_sections_of_smooth s T' π
    (fun b => by cases b <;> assumption) (fun b => by cases b <;> assumption)
  obtain ⟨g₁, hg₁⟩ := hg true
  obtain ⟨g₂, hg₂⟩ := hg false
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) := hU
  refine ⟨U, φ, u, hφ, hU, hu, ?_, ?_⟩
  · obtain ⟨Z', p', q', h1, h2⟩ :=
      exists_isPullback_isProjectiveMorphism_of_polarizedChart F hsq₁ L₁ hamp₁ g₁
    rw [eqToHom_refl, Category.comp_id, hg₁] at h1
    exact ⟨Z', p', q', h1, h2⟩
  · obtain ⟨Z', p', q', h1, h2⟩ :=
      exists_isPullback_isProjectiveMorphism_of_polarizedChart G hsq₂ L₂ hamp₂ g₂
    rw [← Category.assoc, hg₂] at h1
    exact ⟨Z', p', q', h1, h2⟩

/-- **`Isom_V(Y, X) ⟶ V` is quasi-compact over a Noetherian affine base, from H-projective
charts.** Let `F` and `G` be smooth locally polarized families of curves (Stacks 0DQ0) over a
common Noetherian affine base `V`, with `Isom_V(F, G)` an algebraic space (`halg`). Suppose that
for every étale chart `φ : U ⟶ V` from a Noetherian affine `U` along which both families are
schemes, H-projective over `U`, the base change of `Isom_V(F, G) ⟶ V` along `φ` is quasi-compact
(`hproj`, which is the source's last paragraph: Riemann–Roch and Stacks 0DPR). Then
`Isom_V(F, G) ⟶ V` is quasi-compact.

Finitely many such charts cover `V`, by the proof of Stacks 0E6F and quasi-compactness of `V`.
The corresponding base changes of `Isom_V(F, G)` are quasi-compact algebraic spaces and jointly
surject onto it (Stacks 040W), and a morphism from a quasi-compact algebraic space to the affine
`V` is quasi-compact (Stacks 073B). -/
theorem isQuasiCompact_isomFunctorProjection_of_isSmoothLocallyPolarized
    (F G : CurveFamily B hZ) (hb : G.base = F.base)
    (halg : IsAlgebraicSpace B integerBase hZ
      (isomFunctor F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))).toFunctor)
    (hF : F.IsSmoothLocallyPolarized) (hG : G.IsSmoothLocallyPolarized)
    (haff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj F.base))
    (hnoeth : IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj F.base))
    (hproj : ∀ (U : BigFppfOver B integerBase hZ) (φ : U ⟶ F.base),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ F.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap φ) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) →
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ G.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap (φ ≫ eqToHom hb.symm)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) →
      Space.IsQuasiCompact B integerBase hZ
        (pullback.snd (isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb)))
          (yoneda.map φ))) :
    Space.IsQuasiCompact B integerBase hZ
      (isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))) := by
  classical
  set f := isomFunctorProjection F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))
  have hV : IsAlgebraicSpace B integerBase hZ (yoneda.obj F.base) :=
    isAlgebraicSpace_yoneda B integerBase hZ F.base
  choose U φ u hφ hU hu hFp hGp using
    exists_affine_etale_isPullback_isProjectiveMorphism_pair F G hb hF hG
  let toS := BigFppfOver.toScheme B integerBase hZ
  -- the images of the charts are open and cover the quasi-compact base
  have hopen : ∀ s, IsOpen (Set.range (toS.map (φ s))) := fun s => by
    have := hφ s
    exact (toS.map (φ s)).isOpenMap.isOpen_range
  have : CompactSpace (toS.obj F.base) := inferInstance
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s => Set.range (toS.map (φ s)))
    hopen (fun s _ => Set.mem_iUnion.2 ⟨s, u s, hu s⟩)
  -- each chart is Noetherian
  have hUn : ∀ s, IsNoetherian (toS.obj (U s)) := fun s => by
    have := hU s
    have := hφ s
    have : IsLocallyNoetherian (toS.obj (U s)) :=
      LocallyOfFiniteType.isLocallyNoetherian (toS.map (φ s))
    exact { }
  -- the base changes of `Isom` to the charts
  let Fi : t → (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u := fun j => pullback f (yoneda.map (φ j))
  have hFi : ∀ j, IsAlgebraicSpace B integerBase hZ (Fi j) := fun j =>
    isAlgebraicSpace_pullback B integerBase hZ f (yoneda.map (φ j)) halg
      (isAlgebraicSpace_yoneda B integerBase hZ (U j)) hV
  have hFiqc : ∀ j, Space.IsQuasiCompactSpace B integerBase hZ (Fi j) := fun j =>
    Space.isQuasiCompactSpace_source_of_isQuasiCompact B integerBase hZ
      (isAlgebraicSpace_yoneda B integerBase hZ (U j))
      (Space.isQuasiCompactSpace_yoneda_of_isAffine B integerBase hZ (U j) (hU j))
      (hproj (U j) (φ j) (hU j) (hUn j) (hFp j) (hGp j))
  have hsurj : Space.IsJointlySurjective B integerBase hZ Fi (fun j => pullback.fst f _) := by
    rw [Space.isJointlySurjective_iff]
    intro z
    obtain ⟨j, y, hy⟩ := Space.exists_pointsMap_yonedaMap_eq_of_jointly_surjective B integerBase
      hZ (fun j : t => φ j) (fun x => by
        obtain ⟨s, hs, y, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
        exact ⟨⟨s, hs⟩, y, hy⟩) (Space.pointsMap B integerBase hZ _ f z)
    obtain ⟨w, hw, -⟩ := Space.exists_points_of_isPullback B integerBase hZ
      (IsPullback.of_hasPullback f (yoneda.map (φ j))) z y hy.symm
    exact ⟨j, w, hw⟩
  exact Space.isQuasiCompact_of_isQuasiCompactSpace B integerBase hZ B.contains_terminal hV
    (Space.isAbsolutelyQuasiSeparated_yoneda_obj B integerBase hZ B.contains_terminal F.base
      inferInstance)
    (Space.isQuasiCompactSpace_of_finite_jointly_surjective B integerBase hZ hFi halg
      (fun j => pullback.fst f _) hsurj hFiqc) f

end CurveFamily

namespace curvesSmall

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

attribute [local instance] isFibered locallySmall_curveFamily

attribute [local implicit_reducible] schemeSpace ShrinkHoms.fromShrinkHoms ShrinkHoms.inverse
  curvesSmall curvesSmallBased

/-- **`Isom_U(Y, X)` is an algebraic space.** Given that the stack of curves is algebraic (`h`,
Stacks 0D5A) and the identification `hiso` of its isomorphism spaces with `Isom_U(Y, X)` (the
statement of `AlgebraicGeometry.curvesSmall.nonempty_arrowIso_isomFunctorProjection`), the
functor `Isom_U(F, G)` of two families of curves over a common base is an algebraic space: the
isomorphism space of an algebraic stack is one over `U`
(`AlgebraicGeometry.Stack.isAlgebraicSpace_isomSpace`), and so is its view over `Spec(ℤ)`
(Stacks 03I5). -/
theorem isAlgebraicSpace_isomFunctor_of_isAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hiso : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      Nonempty (Arrow.mk (OverShriek.relocalizeToYoneda U.hom
            (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
          yoneda.map (eqToHom y₁.2.symm)) ≅
        Arrow.mk (CurveFamily.isomFunctorProjection
          (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
          (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ)
          ((ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ).toBase.hom ≫
            yoneda.map (eqToHom (y₂.2.trans y₁.2.symm))))))
    (F G : CurveFamily B hZ) (hb : G.base = F.base) :
    IsAlgebraicSpace B integerBase hZ
      (CurveFamily.isomFunctor F G (G.toBase.hom ≫ yoneda.map (eqToHom hb))).toFunctor := by
  let y₁ : (curvesSmall B hZ).val.p.Fiber F.base := ⟨ShrinkHoms.toShrinkHoms F, rfl⟩
  let y₂ : (curvesSmall B hZ).val.p.Fiber F.base := ⟨ShrinkHoms.toShrinkHoms G, hb⟩
  obtain ⟨e⟩ := hiso F.base y₁ y₂
  exact isAlgebraicSpace_of_iso B integerBase hZ (Arrow.leftFunc.mapIso e).symm
    (isAlgebraicSpace_viewOver B _ integerBase _ hZ F.base.hom _
      (Stack.isAlgebraicSpace_isomSpace B integerBase hZ (curvesSmall B hZ)
        (curvesAlgebraicStack B hZ h).property F.base y₁ y₂))

end curvesSmall

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0DSQ, from the smooth local polarizations and the H-projective case.** Given:

* that the stack of curves is algebraic (`h`, Stacks 0D5A) and limit preserving (`hlim`,
  Stacks 0D55);
* that `Isom_𝒳(y₁, y₂) ⟶ U` is separated (`hsep`, Stacks 0DPN and 0DPP) and is
  `Isom_U(Y, X) ⟶ U` (`hiso`) for every pair of objects of the small model over a common `U`;
* that every family of curves is smooth locally polarized (`hpol`, Stacks 0DQ0);
* that `Isom_V(Y, X) ⟶ V`, base changed to an étale chart `U` from a Noetherian affine scheme
  along which both families are H-projective schemes, is quasi-compact (`hproj`, the source's
  last paragraph: Stacks 0DPR with Riemann–Roch, Stacks 0AYR, 0AYX, 0BEM and 0B9T);

the diagonal `Δ : Curves ⟶ Curves ×_{Spec(ℤ)} Curves` is separated and of finite presentation,
both in the sense of Stacks 04XB. -/
theorem
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_polarized
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (hsep : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      letI : (curvesSmall B hZ).val.p.IsFibered :=
        (curvesSmall B hZ).isFiberedInGroupoids.isFibered
      Space.IsSeparated B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)))
    (hiso : ∀ (U : BigFppfOver B integerBase hZ) (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U),
      letI : (curvesSmall B hZ).val.p.IsFibered :=
        (curvesSmall B hZ).isFiberedInGroupoids.isFibered
      Nonempty (Arrow.mk (OverShriek.relocalizeToYoneda U.hom
            (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂) ≫
          yoneda.map (eqToHom y₁.2.symm)) ≅
        Arrow.mk (CurveFamily.isomFunctorProjection
          (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ)
          (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ)
          ((ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ).toBase.hom ≫
            yoneda.map (eqToHom (y₂.2.trans y₁.2.symm))))))
    (hpol : ∀ X : CurveFamily B hZ, X.IsSmoothLocallyPolarized)
    (hproj : ∀ (F G : CurveFamily B hZ) (hb : G.base = F.base) (U : BigFppfOver B integerBase hZ)
      (φ : U ⟶ F.base),
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      IsNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj U) →
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ F.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) F.toBase (schemeSpaceMap φ) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) →
      (∃ (Z : BigFppfOver B integerBase hZ) (p : schemeSpace Z ⟶ G.total) (q : Z ⟶ U),
        IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap (φ ≫ eqToHom hb.symm)) ∧
        IsProjectiveMorphism ((BigFppfOver.toScheme B integerBase hZ).map q)) →
      Space.IsQuasiCompact B integerBase hZ
        (pullback.snd (CurveFamily.isomFunctorProjection F G
          (G.toBase.hom ≫ yoneda.map (eqToHom hb))) (yoneda.map φ))) :
    Stack.IsSeparated B integerBase hZ
        (Stack.relativeDiagonal.{u, u, u + 1} B integerBase hZ (curvesAlgebraicStack B hZ h).val
        (Stack.schemeStack.{u, w} B integerBase hZ (Over.mk (𝟙 (B.obj hZ)))).val
        (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B integerBase hZ
        (Stack.AlgebraicStacks.relativeDiagonal B integerBase hZ
          (Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h))) :=
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_curvesAlgebraicStack_of_noetherian
    B hZ h hlim hsep hiso fun F G hb haff hnoeth =>
      CurveFamily.isQuasiCompact_isomFunctorProjection_of_isSmoothLocallyPolarized F G hb
        (curvesSmall.isAlgebraicSpace_isomFunctor_of_isAlgebraicStack h hiso F G hb)
        (hpol F) (hpol G) haff hnoeth (hproj F G hb)

end AlgebraicGeometry

end
