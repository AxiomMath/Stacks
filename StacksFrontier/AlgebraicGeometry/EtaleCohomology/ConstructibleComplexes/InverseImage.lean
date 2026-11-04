module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Derived inverse image of a complex with constructible cohomology

Let `Λ` be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. If a complex of étale
sheaves of `Λ`-modules on `Y` has constructible cohomology sheaves, then so does its derived
inverse image along `f`. This is Tag 095Y.

The argument is the one of the source. Inverse image of module sheaves between the small étale
sites is exact, so the derived inverse image is computed termwise: it is the functor
`CategoryTheory.Functor.mapDerivedCategory` induced by inverse image, and its degree-`i`
cohomology sheaf is the inverse image of the degree-`i` cohomology sheaf. Tag 095G for sheaves of
modules over a Noetherian ring then says that each of those is constructible.

## Main results

* `Stacks.EtaleCohomology.isConstructible_derivedPullback` — **Tag 095Y**: derived inverse image
  carries the constructible derived category of `Y` into that of `X`.
* `AlgebraicGeometry.isConstructibleModuleSheaf_congr` — constructibility of a sheaf of modules
  transfers along an isomorphism of sheaves.

## Implementation notes

`D_c(X_étale, Λ)` is `Stacks.EtaleCohomology.ConstructibleDerivedCategory`, the full subcategory
of the unbounded derived category cut out by the predicate
`Stacks.EtaleCohomology.IsConstructible`; the statement below is the one about that predicate,
from which membership of the subcategory is immediate. The derived category is the standard model
`CategoryTheory.HasDerivedCategory.standard`, the model at which
`Stacks.EtaleCohomology.IsConstructible` is stated; the comparison of cohomology with an exact
functor, `CategoryTheory.Functor.mapDerivedCategoryCompHomologyFunctorIso`, is model-independent
and is used here at that one model.

Exactness of inverse image is not assumed: it is
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat` and its two
companions, made local instances here so that `mapDerivedCategory` is available. Those are
theorems rather than global instances for the reason recorded in their file — their conclusions
name the coefficient universe, and as global instances the universe unifier gets stuck on them.
The coefficient universe is therefore theirs, `ModuleCat.{max (u + 1) w} Λ`, the universe in which
the coefficient category receives the colimits computing the inverse image.

## References

* [Stacks Project, Tag 095Y](https://stacks.math.columbia.edu/tag/095Y)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

section Congr

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

omit [IsNoetherianRing Λ] in
/-- A sheaf of modules isomorphic to a constructible one is constructible: the same
constructible stratification works, since restriction to a stratum carries the isomorphism
along and finite-type local constancy is closed under isomorphism. -/
public theorem isConstructibleModuleSheaf_congr (X : B.Scheme)
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)} (e : F ≅ G)
    (hF : IsConstructibleModuleSheaf B X Λ F) : IsConstructibleModuleSheaf B X Λ G :=
  isStratifiedSheaf_congr B X
    (fun T F => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (SmallEtale.topology B T.obj T.property) F)
    (fun T _ _ e' h => Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr
      (SmallEtale.topology B T.obj T.property) Λ e' h)
    e hF

end Congr

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  preservesFiniteLimits_smallEtaleSheafPullback_moduleCat
  preservesFiniteColimits_smallEtaleSheafPullback_moduleCat
  additive_smallEtaleSheafPullback_moduleCat

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 095Y.** Let `Λ` be a Noetherian ring and `f : X ⟶ Y` a morphism of schemes. If a
complex of étale sheaves of `Λ`-modules on `Y` lies in `D_c(Y_étale, Λ)`, that is has
constructible cohomology sheaves in every degree, then its derived inverse image `Lf^*K` lies in
`D_c(X_étale, Λ)`. -/
@[stacks 095Y]
public theorem isConstructible_derivedPullback {X Y : B.Scheme} (f : X ⟶ Y)
    [HasSheafify (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) w} Λ)]
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) w} Λ)]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B Y.obj Y.property)
      (ModuleCat.{max (u + 1) w} Λ)))
    (hK : IsConstructible B Y Λ K) :
    IsConstructible B X Λ
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property)).mapDerivedCategory.obj K) := by
  intro i
  refine isConstructibleModuleSheaf_congr B Λ X
    ((((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).mapDerivedCategoryCompHomologyFunctorIso
        i).app K).symm ?_
  exact isConstructibleModuleSheaf_pullback B Λ f _ (hK i)

/-- **Stacks 095Y, for the full subcategory.** Derived inverse image along `f : X ⟶ Y` carries an
object of `D_c(Y_étale, Λ)` to an object of `D_c(X_étale, Λ)`. -/
public def constructibleDerivedCategoryPullback {X Y : B.Scheme} (f : X ⟶ Y)
    [HasSheafify (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) w} Λ)]
    [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
        (ModuleCat.{max (u + 1) w} Λ)]
    (K : ConstructibleDerivedCategory B Y Λ) :
    ConstructibleDerivedCategory B X Λ :=
  ⟨((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)).mapDerivedCategory.obj K.obj,
    isConstructible_derivedPullback B Λ f K.obj K.property⟩

end Stacks.EtaleCohomology

end
