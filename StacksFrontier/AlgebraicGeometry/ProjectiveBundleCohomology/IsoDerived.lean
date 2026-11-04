module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoCompatibility
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.DirectImageDelta
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde

/-!
# Higher direct images along an isomorphism of schemes over a base

Let `p : X ⟶ S` and `p' : X' ⟶ S` be morphisms of schemes and `f : X' ⟶ X` an isomorphism with
`f ≫ p = p'`. Pullback along `f` is an exact equivalence `X.Modules ≌ X'.Modules`, and
`p_* ≅ p'_* ∘ f^*`. The higher direct images of `p` form a universal δ-functor, and so do those of
`p'` precomposed with `f^*`; the identification in degree zero extends uniquely to an isomorphism
of δ-functors `R^q p_* ≅ R^q p'_* ∘ f^*`, compatible with the connecting morphisms of every short
exact sequence. The construction only uses that `f^*` is exact and preserves injectives.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.directImageComparison`: for an exact
  functor `Φ` preserving injectives and `p_* ≅ p'_* ∘ Φ`, the isomorphism of δ-functors
  `R^• p_* ≅ R^• p'_* ∘ Φ`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.higherDirectImagePullback`: its value on
  `R^q p_*` for `Φ` the pullback along an isomorphism over `S` and an integer `q`, in the indexing
  `CategoryTheory.Functor.rightDerivedPlus`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open Stacks.AlgebraicGeometry.LerayAffineBase (pushDelta)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Transport

variable {X X' S : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S) (Φ : X.Modules ⥤ X'.Modules)
  [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [Φ.PreservesInjectiveObjects]
  (α : Scheme.Modules.pushforward p ≅ Φ ⋙ Scheme.Modules.pushforward p')

/-- The higher direct images of `p'`, precomposed with an exact functor `Φ`. -/
public abbrev directImageDeltaComp : DeltaFunctor X.Modules S.Modules :=
  (pushDelta p').precomp Φ

/-- The higher direct images of `p'` precomposed with `Φ` form a universal δ-functor. -/
public instance isUniversal_directImageDeltaComp : (directImageDeltaComp p' Φ).IsUniversal :=
  haveI : (directImageDeltaComp p' Φ).Effaceable :=
    DeltaFunctor.Effaceable.precomp _ _ fun M =>
      ⟨Injective.under M, Injective.ι M, inferInstance, fun n =>
        Functor.isZero_rightDerived_obj_injective_succ _ n _⟩
  DeltaFunctor.isUniversal_of_effaceable _

/-- The comparison `R⁰ p_* ≅ R⁰ p'_* ∘ Φ` in degree zero induced by `α`. -/
public def directImageComparisonZero :
    (pushDelta p).functor 0 ≅ (directImageDeltaComp p' Φ).functor 0 :=
  rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p) ≪≫ α ≪≫
    Functor.isoWhiskerLeft Φ (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).symm

/-- **The isomorphism of δ-functors `R^• p_* ≅ R^• p'_* ∘ Φ`** extending `α` in degree zero. -/
public def directImageComparison : pushDelta p ≅ directImageDeltaComp p' Φ :=
  DeltaFunctor.IsUniversal.isoOfIso (directImageComparisonZero p p' Φ α)

/-- The comparison in degree `q` at a module. -/
public def directImageComparisonApp (q : ℕ) (M : X.Modules) :
    ((Scheme.Modules.pushforward p).rightDerived q).obj M ≅
      ((Scheme.Modules.pushforward p').rightDerived q).obj (Φ.obj M) where
  hom := ((directImageComparison p p' Φ α).hom.app q).app M
  inv := ((directImageComparison p p' Φ α).inv.app q).app M
  hom_inv_id := congrArg (fun η : pushDelta p ⟶ pushDelta p => (η.app q).app M)
    (directImageComparison p p' Φ α).hom_inv_id
  inv_hom_id := congrArg
    (fun η : directImageDeltaComp p' Φ ⟶ directImageDeltaComp p' Φ => (η.app q).app M)
    (directImageComparison p p' Φ α).inv_hom_id

/-- The comparison in degree zero is `α`, through `R⁰ = (-)_*`. -/
public theorem directImageComparisonApp_zero (M : X.Modules) :
    (directImageComparisonApp p p' Φ α 0 M).hom =
      (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p)).hom.app M ≫ α.hom.app M ≫
        (rightDerivedZeroIsoPlus (Scheme.Modules.pushforward p')).inv.app (Φ.obj M) :=
  congrArg (fun η => NatTrans.app η M)
    (DeltaFunctor.IsUniversal.isoOfIso_hom_app_zero (directImageComparisonZero p p' Φ α))

/-- The comparison is natural in the module. -/
@[reassoc]
public theorem directImageComparisonApp_naturality (q : ℕ) {M N : X.Modules} (φ : M ⟶ N) :
    ((Scheme.Modules.pushforward p).rightDerived q).map φ ≫
        (directImageComparisonApp p p' Φ α q N).hom =
      (directImageComparisonApp p p' Φ α q M).hom ≫
        ((Scheme.Modules.pushforward p').rightDerived q).map (Φ.map φ) :=
  ((directImageComparison p p' Φ α).hom.app q).naturality φ

/-- **The comparison commutes with the connecting morphisms.** -/
@[reassoc]
public theorem directImageComparisonApp_δ {T : ShortComplex X.Modules} (hT : T.ShortExact)
    (q : ℕ) :
    (directImageComparisonApp p p' Φ α q T.X₃).hom ≫
        (pushDelta p').δ (hT.map_of_exact Φ) q =
      (pushDelta p).δ hT q ≫ (directImageComparisonApp p p' Φ α (q + 1) T.X₁).hom :=
  (directImageComparison p p' Φ α).hom.comm hT q

end Transport

section Iso

variable {X X' S : Scheme.{u}} (f : X' ⟶ X) [IsIso f] (p : X ⟶ S) (p' : X' ⟶ S)
  (hbase : f ≫ p = p')

/-- For an isomorphism `f`, the unit of `f^* ⊣ f_*` is an isomorphism. -/
public instance isIso_pullbackPushforwardAdjunction_unit :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).unit :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit_isIso_of_L_fully_faithful

include hbase in
/-- **`p_* ≅ p'_* ∘ f^*`** for an isomorphism `f` over `S`: the unit of `f^* ⊣ f_*`. -/
public def pushforwardPullbackIso :
    Scheme.Modules.pushforward p ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward p' :=
  Functor.isoWhiskerRight (asIso (Scheme.Modules.pullbackPushforwardAdjunction f).unit)
      (Scheme.Modules.pushforward p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.pushforwardComp f p ≪≫ Scheme.Modules.pushforwardCongr hbase)

/-- **The map `R^q p_* M ⟶ R^q p'_*(f^* M)` induced by an isomorphism `f` over `S`**, for an
integer `q`, in the indexing `CategoryTheory.Functor.rightDerivedPlus`: zero in negative degrees,
where both sides vanish. -/
public def higherDirectImagePullback : (q : ℤ) → (M : X.Modules) →
    (((Scheme.Modules.pushforward p).rightDerivedPlus q).obj M ⟶
      ((Scheme.Modules.pushforward p').rightDerivedPlus q).obj
        ((Scheme.Modules.pullback f).obj M))
  | Int.ofNat q, M =>
      ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p) q).app M).inv ≫
        (directImageComparisonApp p p' (Scheme.Modules.pullback f)
          (pushforwardPullbackIso f p p' hbase) q M).hom ≫
        ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward p') q).app _).hom
  | Int.negSucc _, _ => 0

end Iso

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
