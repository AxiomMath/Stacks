module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteEtalePushforwardConstructible

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SplitPushforwardProduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianSurjectiveDescentUnconditional
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct images of constructible sheaves along finite étale morphisms

Let `p : T ⟶ S` be a finite étale morphism of a big étale site. The direct image `p_*` of a
constructible sheaf of sets, or of a constructible sheaf of abelian groups, on `T_étale` is
constructible on `S_étale`, with no hypothesis on `S` or `T` and no torsion hypothesis on the
abelian sheaf. Constructibility of sheaves of sets descends along surjective morphisms of
quasi-compact quasi-separated schemes.

## Main results

* `AlgebraicGeometry.setConstructibilityDescendsAlongSurjective`: constructibility of sheaves of
  sets descends along surjective morphisms of quasi-compact quasi-separated schemes.
* `AlgebraicGeometry.isConstructibleSetSheaf_pushforward_unconditional`: the direct image of a
  constructible sheaf of sets along a finite étale morphism is constructible.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_pushforward_unconditional`: the direct image of
  a constructible abelian sheaf along a finite étale morphism is constructible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w r t

namespace Stacks.Etale

end Stacks.Etale

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (p : T ⟶ S)

section Restriction

variable {D : Type w} [Category.{v} D] {FD : D → D → Type*} {CD : D → Type t}
  [∀ A A', FunLike (FD A A') (CD A) (CD A')] [ConcreteCategory.{t} D FD]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous D
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) D]

end Restriction

section EtaleLocal

variable [Etale (B.inclusion.map p)]

section Modules

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) w} Λ)]

end Modules

end EtaleLocal

section ModuleDescent

variable (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]

end ModuleDescent

section SetDescent

/-- **Constructibility of sheaves of sets descends along surjections**: for a morphism
`f : X ⟶ Y` of quasi-compact quasi-separated schemes that is surjective on underlying spaces, a
sheaf of sets on `Y_étale` whose inverse image along `f` is constructible is itself
constructible (`AlgebraicGeometry.SetConstructibilityDescendsAlongSurjective`). -/
public theorem setConstructibilityDescendsAlongSurjective (B : BigEtaleSite.{u}) :
    SetConstructibilityDescendsAlongSurjective B :=
  fun _ _ f hf hXc hXq hYc hYq G hG =>
    (_root_.AlgebraicGeometry.isConstructibleSetSheaf_pullback_iff_unconditional
      B f hf hXc hXq hYc hYq G).2 hG

/-- Let `p : T ⟶ S` be a finite étale morphism of a big étale site with `S` quasi-compact and
quasi-separated and let `ℱ` be a constructible sheaf of sets on `T_étale`. Then `p_*ℱ` is
constructible. -/
@[sga "4 IX 2.14" "(i), special case"]
public theorem isConstructibleSetSheaf_pushforward_of_compactSpace_unconditional
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (hSc : CompactSpace (B.inclusion.obj S)) (hSq : QuasiSeparatedSpace (B.inclusion.obj S))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  classical
  choose V hVa hVm hVsp using fun s => exists_affine_smallEtale_isSplitOver B p s
  obtain ⟨Z, g, ι, hι, σ, k, hZc, hZq, hgsurj, hko, hkcover, hkg⟩ :=
    exists_affine_etale_surjection B S hSc V hVa hVm
  have := hι
  refine setConstructibilityDescendsAlongSurjective B Z S g hgsurj hZc hZq hSc hSq _ ?_
  refine isConstructibleFiniteSheaf_of_openCover B Z _
    (fun a => (V (σ a)).obj.left) k hko hkcover fun a => ?_
  refine isConstructibleSetSheaf_congr B _
    (((smallEtaleSheafPullbackCompIso B _ _ _ (k a) g (Type (u + 1))).app
      ((B.smallPushforward p (Type (u + 1))).obj F)).symm) ?_
  rw [hkg a]
  have hEt : Etale (B.inclusion.map (V (σ a)).obj.hom) := (V (σ a)).property
  exact isConstructibleSetSheaf_congr B _
    ((smallInverseImageIsoPostcomposePushforward B (V (σ a)).obj.hom
      (Type (u + 1))).app _).symm
    (isConstructibleSetSheaf_restriction_pushforward_of_isSplitOver B p (V (σ a))
      (hVsp (σ a)).some F hF)

/-- Let `p : T ⟶ S` be a finite étale morphism of a big étale site and let `ℱ` be a
constructible sheaf of sets on `T_étale`. Then `p_*ℱ` is a constructible sheaf of sets on
`S_étale`. -/
@[stacks 095H "sheaves of sets; nothing granted, no hypothesis on S or T",
  sga "4 IX 2.14" "(i), special case",
  sga "4 XIV 1.1" "special case",
  sga "4 XIV 1.11" "partial",
  sga "4 XIV 1.5" "special case"]
public theorem isConstructibleSetSheaf_pushforward_unconditional
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) (Type (u + 1)))
    (hF : IsConstructibleSetSheaf B T F) :
    IsConstructibleSetSheaf B S ((B.smallPushforward p (Type (u + 1))).obj F) := by
  classical
  have hUaff : ∀ i, IsAffine ((B.inclusion.obj S).affineOpenCover.openCover.X i) := fun i =>
    Scheme.isAffine_affineCover (B.inclusion.obj S) i
  have hUopen : ∀ i, IsOpenImmersion ((B.inclusion.obj S).affineOpenCover.openCover.f i) :=
    fun i => (B.inclusion.obj S).affineOpenCover.openCover.map_prop i
  have hUc : ∀ i, B.Contains ((B.inclusion.obj S).affineOpenCover.openCover.X i) := by
    intro i
    have := hUopen i
    exact Scheme.size_lt_of_isOpenImmersion
      ((B.inclusion.obj S).affineOpenCover.openCover.f i) S.property
  let W : (B.inclusion.obj S).affineOpenCover.openCover.I₀ →
      SmallEtale B S.1 S.property := fun i =>
    ⟨Over.mk (ObjectProperty.homMk
      ((B.inclusion.obj S).affineOpenCover.openCover.f i) :
        B.obj _ (hUc i) ⟶ B.obj S.1 S.property), by
      have := hUopen i
      change Etale ((B.inclusion.obj S).affineOpenCover.openCover.f i)
      infer_instance⟩
  refine isConstructibleFiniteSheaf_of_openCover B S _
    (fun i => (W i).obj.left) (fun i => (W i).obj.hom) (fun i => hUopen i) ?_ fun i => ?_
  · exact ((B.inclusion.obj S).affineOpenCover.openCover.iUnion_range).symm
  · have hEtW : Etale (B.inclusion.map (W i).obj.hom) := (W i).property
    have : IsFinite (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
      MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
    have : Etale (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
      MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
    have : IsAffine (B.inclusion.obj (W i).obj.left) := hUaff i
    refine isConstructibleSetSheaf_congr B _
      ((smallInverseImageIsoPostcomposePushforward B (W i).obj.hom
        (Type (u + 1))).app _).symm ?_
    refine isConstructibleSetSheaf_congr B _
      ((smallEtaleRestrictionPushforwardBaseChangeIso B p (W i) (Type (u + 1))).app F) ?_
    exact isConstructibleSetSheaf_pushforward_of_compactSpace_unconditional B
      (baseChangedEtaleProjection B p (W i))
      (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) _
      (isConstructibleFiniteSheaf_smallEtaleRestriction B T
        ((smallEtaleBaseChange B p).obj (W i)) F hF)

/-- Let `p : T ⟶ S` be a finite étale morphism of a big étale site with `S` quasi-compact and
quasi-separated and let `ℱ` be a constructible abelian sheaf on `T_étale`. Then `p_*ℱ` is
constructible. -/
public theorem isConstructibleAbelianSheaf_pushforward_of_compactSpace_unconditional
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (hSc : CompactSpace (B.inclusion.obj S)) (hSq : QuasiSeparatedSpace (B.inclusion.obj S))
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B T F) :
    IsConstructibleAbelianSheaf B S
      ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F) := by
  classical
  choose V hVa hVm hVsp using fun s => exists_affine_smallEtale_isSplitOver B p s
  obtain ⟨Z, g, ι, hι, σ, k, hZc, hZq, hgsurj, hko, hkcover, hkg⟩ :=
    exists_affine_etale_surjection B S hSc V hVa hVm
  have := hι
  refine (isConstructibleAbelianSheaf_pullback_iff_of_surjective_general B g hZc hZq hSc hSq hgsurj
    _).2 ?_
  refine isConstructibleFiniteSheaf_of_openCover B Z _
    (fun a => (V (σ a)).obj.left) k hko hkcover fun a => ?_
  refine isConstructibleAbelianSheaf_congr B _
    (((smallEtaleSheafPullbackCompIso B _ _ _ (k a) g AddCommGrpCat.{u + 1}).app
      ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F)).symm) ?_
  rw [hkg a]
  have hEt : Etale (B.inclusion.map (V (σ a)).obj.hom) := (V (σ a)).property
  exact isConstructibleAbelianSheaf_congr B _
    ((smallInverseImageIsoPostcomposePushforward B (V (σ a)).obj.hom
      AddCommGrpCat.{u + 1}).app _).symm
    (isConstructibleAbelianSheaf_restriction_pushforward_of_isSplitOver B p (V (σ a))
      (hVsp (σ a)).some F hF)

/-- Let `p : T ⟶ S` be a finite étale morphism of a big étale site and let `ℱ` be a
constructible abelian sheaf on `T_étale`. Then `p_*ℱ` is a constructible abelian sheaf on
`S_étale`. -/
@[stacks 095H "sheaves of abelian groups; nothing granted, no hypothesis on S or T"]
public theorem isConstructibleAbelianSheaf_pushforward_unconditional
    [IsFinite (B.inclusion.map p)] [Etale (B.inclusion.map p)]
    (F : Sheaf (SmallEtale.topology B T.1 T.property) AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B T F) :
    IsConstructibleAbelianSheaf B S
      ((B.smallPushforward p AddCommGrpCat.{u + 1}).obj F) := by
  classical
  have hUaff : ∀ i, IsAffine ((B.inclusion.obj S).affineOpenCover.openCover.X i) := fun i =>
    Scheme.isAffine_affineCover (B.inclusion.obj S) i
  have hUopen : ∀ i, IsOpenImmersion ((B.inclusion.obj S).affineOpenCover.openCover.f i) :=
    fun i => (B.inclusion.obj S).affineOpenCover.openCover.map_prop i
  have hUc : ∀ i, B.Contains ((B.inclusion.obj S).affineOpenCover.openCover.X i) := by
    intro i
    have := hUopen i
    exact Scheme.size_lt_of_isOpenImmersion
      ((B.inclusion.obj S).affineOpenCover.openCover.f i) S.property
  let W : (B.inclusion.obj S).affineOpenCover.openCover.I₀ →
      SmallEtale B S.1 S.property := fun i =>
    ⟨Over.mk (ObjectProperty.homMk
      ((B.inclusion.obj S).affineOpenCover.openCover.f i) :
        B.obj _ (hUc i) ⟶ B.obj S.1 S.property), by
      have := hUopen i
      change Etale ((B.inclusion.obj S).affineOpenCover.openCover.f i)
      infer_instance⟩
  refine isConstructibleFiniteSheaf_of_openCover B S _
    (fun i => (W i).obj.left) (fun i => (W i).obj.hom) (fun i => hUopen i) ?_ fun i => ?_
  · exact ((B.inclusion.obj S).affineOpenCover.openCover.iUnion_range).symm
  · have hEtW : Etale (B.inclusion.map (W i).obj.hom) := (W i).property
    have : IsFinite (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
      MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
    have : Etale (B.inclusion.map (baseChangedEtaleProjection B p (W i))) :=
      MorphismProperty.of_isPullback (isPullback_splitBaseChange B p (W i)) inferInstance
    have : IsAffine (B.inclusion.obj (W i).obj.left) := hUaff i
    refine isConstructibleAbelianSheaf_congr B _
      ((smallInverseImageIsoPostcomposePushforward B (W i).obj.hom
        AddCommGrpCat.{u + 1}).app _).symm ?_
    refine isConstructibleAbelianSheaf_congr B _
      ((smallEtaleRestrictionPushforwardBaseChangeIso B p (W i)
        AddCommGrpCat.{u + 1}).app F) ?_
    exact isConstructibleAbelianSheaf_pushforward_of_compactSpace_unconditional B
      (baseChangedEtaleProjection B p (W i))
      (Scheme.compactSpace_of_isAffine _) (quasiSeparatedSpace_of_isAffine _) _
      (isConstructibleFiniteSheaf_smallEtaleRestriction B T
        ((smallEtaleBaseChange B p).obj (W i)) F hF)

end SetDescent

end AlgebraicGeometry

end
