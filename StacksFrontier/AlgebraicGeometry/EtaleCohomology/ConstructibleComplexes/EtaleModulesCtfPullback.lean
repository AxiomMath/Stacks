module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability

/-!
# Inverse image of constructible complexes of finite Tor dimension

Let `f : Y ⟶ X` be a morphism of schemes and `Λ` a ring. This file proves that inverse image
along `f` carries constructible flat sheaves of `Λ`-modules to constructible flat sheaves, bounded
complexes of them to bounded complexes of them, and `D_ctf(X_étale, Λ)` into
`D_ctf(Y_étale, Λ)`; and that on a quasi-compact and quasi-separated scheme membership of
`D_ctf(X_étale, Λ)` is condition (2) of Tag 03TT.

## Main results

* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_pullback` — on the small étale site of
  Stacks 021B, the inverse image of a constructible flat sheaf of `Λ`-modules is constructible
  flat, for an arbitrary ring `Λ`.
* `Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule.pullback` — the same on Mathlib's small
  étale site.
* `Stacks.EtaleCohomology.IsRepresentedByConstructibleFlatEtaleComplex.pullback` — condition (2)
  of Tag 03TT is stable under derived inverse image.
* `Stacks.EtaleCohomology.IsCtf.pullback` — **Tag 0963 for `D_ctf` at an arbitrary coefficient
  ring**: derived inverse image carries `D_ctf(X_étale, Λ)` into `D_ctf(Y_étale, Λ)`. This
  covers the restrictions `i^{-1}` to a closed subscheme and `j^{-1}` to an open one.
* `Stacks.EtaleCohomology.isCtf_iff_of_qcqs` — on a quasi-compact and quasi-separated scheme an
  object lies in `D_ctf(X_étale, Λ)` exactly when it is represented by a bounded complex of
  constructible flat sheaves.

## Implementation notes

The inverse image of a constructible flat sheaf is handled by the stratified-sheaf machinery of
Tag 095G, `AlgebraicGeometry.isStratifiedSheaf_pullback`, applied to the condition "locally
constant with finite projective values", which is stable under inverse image by
`AlgebraicGeometry.exists_trivializing_cover_smallEtaleSheafPullback`. The passage between the two
presentations of the small étale site is
`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`.

## References

* [Stacks Project, Tag 0963](https://stacks.math.columbia.edu/tag/0963)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- **The inverse image of a constructible flat sheaf of `Λ`-modules is constructible flat**, for
an arbitrary ring `Λ` and an arbitrary morphism `f : Y ⟶ X` of the big étale site. The
stratification of Tag 095G is pulled back, and local constancy with finite projective values on
each stratum survives inverse image. -/
public theorem isConstructibleFlatModuleSheaf_pullback {X Y : B.Scheme} (f : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    IsConstructibleFlatModuleSheaf B Y Λ
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{w} Λ)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Y.obj Y.property)).obj F) := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ)}, (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) G := fun T _ _ e h =>
    Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _ e h
  have hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{w} Λ)),
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T'.obj T'.property) (smallEtalePullObj B q G) := by
    intro T' T q G h U
    obtain ⟨I, V, g, hg, hc⟩ := exists_trivializing_cover_smallEtaleSheafPullback B
      (ModuleCat.{w} Λ) q G (fun E => Module.Finite Λ E ∧ Module.Projective Λ E)
      (fun U => by
        obtain ⟨I, V, g, hg, hc⟩ := h U
        exact ⟨I, V, g, hg, fun i => by
          obtain ⟨E, h₁, h₂, h₃⟩ := hc i
          exact ⟨E, ⟨h₁, h₂⟩, h₃⟩⟩) U
    exact ⟨I, V, g, hg, fun i => by
      obtain ⟨E, ⟨h₁, h₂⟩, h₃⟩ := hc i
      exact ⟨E, h₁, h₂, h₃⟩⟩
  exact isStratifiedSheaf_pullback B f _ hPIso hPPull F hF

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- The transport to the bounded site of the inverse image on Mathlib's site is the inverse image
on the bounded site of the transport. -/
public def etaleModulesToSmallEtalePullbackIso {X Y : B.Scheme} (f : Y ⟶ X)
    (F : EtaleModules.{u, r} Λ X.obj) :
    (etaleModulesToSmallEtale B Y Λ).obj
        ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).obj F) ≅
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B Y.obj Y.property)).obj
          ((etaleModulesToSmallEtale B X Λ).obj F) :=
  let eX := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)
  let eY := SmallEtale.sheafEquiv B Y.obj Y.property (ModuleCat.{max (u + 1) r} Λ)
  let sq := SmallEtale.sheafEquivPullbackBaseChangeIso B f (ModuleCat.{max (u + 1) r} Λ)
    (etaleModuleInverseImageAdj.{u, r} Λ (B.inclusion.map f))
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafAdjunctionContinuous
      (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B Y.obj Y.property))
  eY.inverse.mapIso ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).mapIso
      (eX.counitIso.app F).symm) ≪≫
    eY.inverse.mapIso (sq.app (eX.inverse.obj F)) ≪≫ (eY.unitIso.app _).symm

/-- **The inverse image of a constructible flat sheaf is constructible flat**, on Mathlib's small
étale site, for an arbitrary ring `Λ` and an arbitrary morphism `f : Y ⟶ X`. -/
public theorem IsConstructibleFlatEtaleModule.pullback {X Y : B.Scheme} (f : Y ⟶ X)
    {F : EtaleModules.{u, r} Λ X.obj} (hF : IsConstructibleFlatEtaleModule B X Λ F) :
    IsConstructibleFlatEtaleModule B Y Λ
      ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).obj F) :=
  isConstructibleFlatModuleSheaf_congr B Y Λ
    (etaleModulesToSmallEtalePullbackIso B Λ f F).symm
    (isConstructibleFlatModuleSheaf_pullback B Λ f _ hF)

/-- **Condition (2) of Tag 03TT is stable under derived inverse image**: the inverse image of a
bounded complex of constructible flat sheaves is one, inverse image being exact. -/
public theorem IsRepresentedByConstructibleFlatEtaleComplex.pullback {X Y : B.Scheme}
    (f : Y ⟶ X) {K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)}
    (hK : IsRepresentedByConstructibleFlatEtaleComplex B X Λ K) :
    IsRepresentedByConstructibleFlatEtaleComplex B Y Λ
      ((etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map f)).obj K) := by
  obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := hK
  let G := etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)
  let C' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  have ha' : CochainComplex.IsStrictlyGE C' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => G.map_isZero (C.isZero_of_isStrictlyGE a i hi)
  have hb' : CochainComplex.IsStrictlyLE C' b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => G.map_isZero (C.isZero_of_isStrictlyLE b i hi)
  exact ⟨C', a, b, ha', hb', fun i => (hC i).pullback B Λ f,
    ⟨(G.mapDerivedCategoryFactors.app C).symm ≪≫
      (etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map f)).mapIso e⟩⟩

/-- The derived inverse image along a composite is the composite of the derived inverse images. -/
public def etaleModuleDerivedInverseImageCompIso {X Y Z : B.Scheme} (g : Z ⟶ Y) (f : Y ⟶ X) :
    etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map (g ≫ f)) ≅
      etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map f) ⋙
        etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map g) :=
  eqToIso (by rw [CategoryTheory.Functor.map_comp]) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModuleInverseImageCompIso.{u, r} Λ (B.inclusion.map g) (B.inclusion.map f)) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _

/-- **Tag 0963 for `D_ctf` at an arbitrary coefficient ring.** Derived inverse image along any
morphism `f : Y ⟶ X` of the big étale site carries `D_ctf(X_étale, Λ)` into `D_ctf(Y_étale, Λ)`.
In particular this holds for the restriction to an open or a closed subscheme. -/
public theorem IsCtf.pullback {X Y : B.Scheme} (f : Y ⟶ X)
    {K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)} (hK : IsCtf B X Λ K) :
    IsCtf B Y Λ ((etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map f)).obj K) :=
  fun W g hc hq =>
    (hK W (g ≫ f) hc hq).of_iso B W Λ ((etaleModuleDerivedInverseImageCompIso B Λ g f).app K)

/-- Inverse image along the identity is the identity. -/
public def etaleModuleInverseImageIdIso (X : Scheme.{u}) :
    etaleModuleInverseImage.{u, r} Λ (𝟙 X) ≅ 𝟭 _ :=
  (etaleModuleInverseImageAdj.{u, r} Λ (𝟙 X)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) _ _).symm)

/-- On a scheme the class of a bounded complex of constructible flat sheaves lies in
`D_ctf(X_étale, Λ)`. -/
public theorem IsRepresentedByConstructibleFlatEtaleComplex.isCtf {X : B.Scheme}
    {K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)}
    (hK : IsRepresentedByConstructibleFlatEtaleComplex B X Λ K) : IsCtf B X Λ K :=
  fun _ f _ _ => hK.pullback B Λ f

/-- **On a quasi-compact and quasi-separated scheme, `D_ctf(X_étale, Λ)` is condition (2) of
Tag 03TT**: an object lies in it exactly when it is represented by a bounded complex of
constructible flat sheaves of `Λ`-modules. -/
public theorem isCtf_iff_of_qcqs {X : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)) :
    IsCtf B X Λ K ↔ IsRepresentedByConstructibleFlatEtaleComplex B X Λ K := by
  refine ⟨fun hK => ?_, fun hK => hK.isCtf B Λ⟩
  have h := hK X (𝟙 X) inferInstance inferInstance
  obtain ⟨C, ⟨eC⟩⟩ : ∃ C : CochainComplex (EtaleModules.{u, r} Λ X.obj) ℤ,
      Nonempty (DerivedCategory.Q.obj C ≅ K) := ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  let G := etaleModuleInverseImage.{u, r} Λ (B.inclusion.map (𝟙 X))
  let eG : G ≅ 𝟭 _ :=
    eqToIso (congrArg (etaleModuleInverseImage.{u, r} Λ) (B.inclusion.map_id X)) ≪≫
      etaleModuleInverseImageIdIso Λ X.obj
  refine h.of_iso B X Λ ?_
  exact (etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map (𝟙 X))).mapIso eC.symm ≪≫
    (G.mapDerivedCategoryFactors.app C) ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex eG (ComplexShape.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexIdIso _ _).app C) ≪≫ eC

end Stacks.EtaleCohomology

end
