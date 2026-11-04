module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratumPullback
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible abelian sheaves form a weak Serre subcategory

Let `X` be a scheme. The constructible sheaves of abelian groups on the small étale site of `X`
form a weak Serre subcategory of all abelian sheaves on that site: the zero sheaf is
constructible, constructibility is invariant under isomorphism, and the kernel, the cokernel and
the middle term of a short exact sequence of constructible sheaves are constructible.

## Main results

* `AlgebraicGeometry.constructibleAbelianSheaf_isWeakSerreClass` — Stacks 03RZ for abelian
  sheaves.

## Implementation notes

The five conditions all reduce to the corresponding statement for *finite locally constant*
abelian sheaves on a site, which is Stacks 093U (2)
(`Stacks.ConstantSheaf.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf`), by restricting to
the strata of one stratification trivializing every sheaf in sight. Producing that one
stratification is the whole geometric content: the sheaves involved come with stratifications of
their own, and a common refinement of them is taken by
`AlgebraicGeometry.ConstructibleStratification.inf`.

Restriction to a stratum is exact: it preserves finite colimits because it is a left adjoint, and
finite limits by Stacks 04BH applied to small étale base change, which is left exact and
continuous between sites with finite limits. Exactness is what lets the kernel, cokernel and
extension conditions be checked after restriction.

## References

* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 04BH](https://stacks.math.columbia.edu/tag/04BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf ZeroObject

namespace AlgebraicGeometry

universe u

variable (B : BigEtaleSite.{u})

/-- Sheaves of abelian groups on the small étale site of an object of a big étale site admit
sheafification: the site is essentially small, so Stacks 071H applies. -/
public instance hasSheafify_smallEtale_addCommGrp (X : B.Scheme) :
    HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0}

/-- **Stacks 093U (2) on the small étale site.** The finite locally constant sheaves of abelian
groups on the small étale site of an object of a big étale site form a weak Serre subcategory. -/
public theorem isWeakSerreClass_isFiniteLocallyConstant_smallEtale (Z : B.Scheme) :
    ObjectProperty.IsWeakSerreClass
      (fun F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1} =>
        IsFiniteLocallyConstant (SmallEtale.topology B Z.obj Z.property) F) :=
  isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf.{u, u + 1, 0}
    (SmallEtale.topology B Z.obj Z.property)

section Constructible

variable
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- Inverse image of abelian sheaves along small étale base change. -/
public abbrev smallEtaleAbelianPullback {S T : B.Scheme} (f : T ⟶ S) :
    Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B T.obj T.property) AddCommGrpCat.{u + 1} :=
  smallEtaleSheafPullback B AddCommGrpCat.{u + 1} f

/-- Inverse image of abelian sheaves along small étale base change preserves finite colimits,
being a left adjoint. -/
public instance preservesFiniteColimits_smallEtaleAbelianPullback {S T : B.Scheme} (f : T ⟶ S) :
    PreservesFiniteColimits (smallEtaleAbelianPullback B f) := by
  have : PreservesColimitsOfSize.{u + 1, u + 1} (smallEtaleAbelianPullback B f) :=
    ((smallEtaleBaseChange B f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Stacks 04BH on the small étale site.** Inverse image of abelian sheaves along small étale
base change preserves finite limits: base change is a continuous functor preserving fibre
products and equalizers between sites with finite limits. -/
public instance preservesFiniteLimits_smallEtaleAbelianPullback {S T : B.Scheme} (f : T ⟶ S) :
    PreservesFiniteLimits (smallEtaleAbelianPullback B f) := by
  have : PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback
      (smallEtaleBaseChange B f) AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)) := inferInstance
  exact preservesFiniteLimits_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange B f)
      AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).symm

/-- Inverse image of abelian sheaves along small étale base change is additive, being left
exact. -/
public instance additive_smallEtaleAbelianPullback {S T : B.Scheme} (f : T ⟶ S) :
    (smallEtaleAbelianPullback B f).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (X : B.Scheme)

/-- A sheaf isomorphic to a constructible abelian sheaf is constructible: the same
stratification works, since restriction to a stratum carries the isomorphism along. -/
public theorem isConstructibleAbelianSheaf_congr
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (e : F ≅ G)
    (hF : IsConstructibleAbelianSheaf B X F) : IsConstructibleAbelianSheaf B X G := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  have := hs i
  exact isFiniteLocallyConstant_congr _ ((smallEtaleAbelianPullback B (s.inclusion i)).mapIso e)

/-- **One stratification for two constructible sheaves.** Two constructible abelian sheaves
become finite locally constant on the strata of a single constructible stratification of a given
affine open, namely a common refinement of the stratifications each of them provides. -/
public theorem exists_commonStratification
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleAbelianSheaf B X F) (hG : IsConstructibleAbelianSheaf B X G)
    (U : X.obj.affineOpens) :
    ∃ s : ConstructibleStratification B X U.1, ∀ i,
      IsFiniteLocallyConstant (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
          ((smallEtaleAbelianPullback B (s.inclusion i)).obj F) ∧
        IsFiniteLocallyConstant (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
          ((smallEtaleAbelianPullback B (s.inclusion i)).obj G) := by
  obtain ⟨s, hs⟩ := hF U
  obtain ⟨t, ht⟩ := hG U
  refine ⟨s.inf t, fun i => ⟨?_, ?_⟩⟩
  · exact ConstructibleStratification.isFiniteLocallyConstant_of_refines _ F hs
      (ConstructibleStratification.inf_factorsThroughStrata_left s t) i
  · exact ConstructibleStratification.isFiniteLocallyConstant_of_refines _ G ht
      (ConstructibleStratification.inf_factorsThroughStrata_right s t) i

/-- A sheaf is constructible if its restriction to every piece of a common stratification of two
constructible sheaves is finite locally constant whenever those of the two sheaves are. -/
private theorem isConstructibleAbelianSheaf_of_restrictions
    {F G H : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleAbelianSheaf B X F) (hG : IsConstructibleAbelianSheaf B X G)
    (h : ∀ {Z : B.Scheme} (g : Z ⟶ X),
      IsFiniteLocallyConstant (SmallEtale.topology B Z.obj Z.property)
          ((smallEtaleAbelianPullback B g).obj F) →
        IsFiniteLocallyConstant (SmallEtale.topology B Z.obj Z.property)
          ((smallEtaleAbelianPullback B g).obj G) →
        IsFiniteLocallyConstant (SmallEtale.topology B Z.obj Z.property)
          ((smallEtaleAbelianPullback B g).obj H)) :
    IsConstructibleAbelianSheaf B X H := by
  intro U
  obtain ⟨s, hs⟩ := exists_commonStratification B X hF hG U
  exact ⟨s, fun i => h (s.inclusion i) (hs i).1 (hs i).2⟩

/-- The kernel of a morphism of constructible abelian sheaves is constructible. -/
public theorem isConstructibleAbelianSheaf_kernel
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (hF : IsConstructibleAbelianSheaf B X F) (hG : IsConstructibleAbelianSheaf B X G) :
    IsConstructibleAbelianSheaf B X (kernel f) :=
  isConstructibleAbelianSheaf_of_restrictions B X hF hG fun g h₁ h₂ =>
    have := isWeakSerreClass_isFiniteLocallyConstant_smallEtale B
    ObjectProperty.prop_of_iso _ (PreservesKernel.iso (smallEtaleAbelianPullback B g) f).symm
      (ObjectProperty.prop_kernel _ _ h₁ h₂)

/-- The cokernel of a morphism of constructible abelian sheaves is constructible. -/
public theorem isConstructibleAbelianSheaf_cokernel
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (hF : IsConstructibleAbelianSheaf B X F) (hG : IsConstructibleAbelianSheaf B X G) :
    IsConstructibleAbelianSheaf B X (cokernel f) :=
  isConstructibleAbelianSheaf_of_restrictions B X hF hG fun g h₁ h₂ =>
    have := isWeakSerreClass_isFiniteLocallyConstant_smallEtale B
    ObjectProperty.prop_of_iso _ (PreservesCokernel.iso (smallEtaleAbelianPullback B g) f).symm
      (ObjectProperty.prop_cokernel _ _ h₁ h₂)

/-- The middle term of a short exact sequence whose outer terms are constructible abelian
sheaves is constructible. -/
public theorem isConstructibleAbelianSheaf_of_shortExact
    {S : ShortComplex (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (h₁ : IsConstructibleAbelianSheaf B X S.X₁)
    (h₃ : IsConstructibleAbelianSheaf B X S.X₃) :
    IsConstructibleAbelianSheaf B X S.X₂ :=
  isConstructibleAbelianSheaf_of_restrictions B X h₁ h₃ fun g h h' =>
    (isWeakSerreClass_isFiniteLocallyConstant_smallEtale B _).prop_X₂_of_shortExact
      (hS.map_of_exact (smallEtaleAbelianPullback B g)) h h'

/-- The zero abelian sheaf is constructible: the one-stratum stratification of an affine open
works, and the restriction of a zero sheaf is zero. -/
public theorem isConstructibleAbelianSheaf_zero :
    IsConstructibleAbelianSheaf B X
      (0 : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) := by
  intro U
  refine ⟨ConstructibleStratification.single B X U.1, fun i => ?_⟩
  have hP := isWeakSerreClass_isFiniteLocallyConstant_smallEtale B
    ((ConstructibleStratification.single B X U.1).piece i)
  exact ObjectProperty.prop_of_isZero _
    ((smallEtaleAbelianPullback B
      ((ConstructibleStratification.single B X U.1).inclusion i)).map_isZero (isZero_zero _))

/-- **Stacks 03RZ for abelian sheaves.** The constructible sheaves of abelian groups on the small
étale site of a scheme form a weak Serre subcategory of all abelian sheaves on that site. -/
@[stacks 03RZ "constructible_abelian_weak_serre", sga "4 IX 2.6" "(ii)+ker/coker abelian"]
public instance constructibleAbelianSheaf_isWeakSerreClass :
    ObjectProperty.IsWeakSerreClass
      (fun F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
        IsConstructibleAbelianSheaf B X F) where
  exists_zero := ⟨0, isZero_zero _, isConstructibleAbelianSheaf_zero B X⟩
  of_iso e hF := isConstructibleAbelianSheaf_congr B X e hF
  kernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact isConstructibleAbelianSheaf_congr B X
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      (isConstructibleAbelianSheaf_kernel B X f hf.1 hf.2)
  cokernels_le := by
    rintro _ ⟨f, k, hk, hf⟩
    exact isConstructibleAbelianSheaf_congr B X
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (isConstructibleAbelianSheaf_cokernel B X f hf.1 hf.2)
  prop_X₂_of_shortExact hS h₁ h₃ := isConstructibleAbelianSheaf_of_shortExact B X hS h₁ h₃

end Constructible

end AlgebraicGeometry

end
