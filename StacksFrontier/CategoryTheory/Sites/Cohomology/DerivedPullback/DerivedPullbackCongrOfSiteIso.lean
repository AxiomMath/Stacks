module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi

/-!
# Derived pullback along isomorphic morphisms of ringed topoi

Let `φ, ψ : X ⟶ Y` be morphisms of ringed topoi presented by continuous functors
`φ.u, ψ.u : Y.C ⥤ X.C`. Suppose `e : ψ.u ≅ φ.u` is an isomorphism of the underlying functors
that carries the structure map of `φ` to that of `ψ`. Then the pushforwards, the pullbacks and
the derived pullbacks of sheaves of modules along `φ` and `ψ` are canonically isomorphic.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.pushforwardToposIsoOfIso`: `φ_* ≅ ψ_*` on sheaves of
  modules.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposIsoOfIso`: `φ^* ≅ ψ^*` on sheaves of modules.
* `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackIsoOfIso`:
  `Lφ^* ≅ Lψ^*`.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedToposSiteHom

universe w

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (φ ψ : RingedToposSiteHom X Y) (e : ψ.u ≅ φ.u)

/-- The condition that `e : ψ.u ≅ φ.u` carries the structure map of `φ` to that of `ψ`:
`φ^♯ : 𝒪_Y ⟶ φ_*𝒪_X` followed by the map `φ_*𝒪_X ⟶ ψ_*𝒪_X` induced by `e` is `ψ^♯`. -/
def FSharpCompatible : Prop :=
  φ.fSharp ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom CommRingCat.{w} Y.J X.J).app X.O =
    ψ.fSharp

variable {φ ψ e}

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The compatibility of the structure maps, read on sheaves of not necessarily commutative
rings. -/
theorem fSharpRing_comp_of_fSharpCompatible (he : FSharpCompatible φ ψ e) :
    φ.fSharpRing ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} Y.J X.J).app
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) = ψ.fSharpRing := by
  ext U : 3
  exact congrArg (forget₂ CommRingCat.{w} RingCat.{w}).map
    (congrArg (fun t => t.hom.app U) he)

variable (he : FSharpCompatible φ ψ e)

/-- **The pushforwards along isomorphic morphisms of ringed topoi are isomorphic**: `φ_* ≅ ψ_*` on
sheaves of modules, induced by `e` on sections. -/
def pushforwardToposIsoOfIso : φ.pushforwardTopos ≅ ψ.pushforwardTopos :=
  SheafOfModules.pushforwardCongr₂ _ e (fSharpRing_comp_of_fSharpCompatible he)

/-- **The pullbacks along isomorphic morphisms of ringed topoi are isomorphic**: `φ^* ≅ ψ^*` on
sheaves of modules, the left adjoints of two isomorphic pushforwards. -/
def pullbackToposIsoOfIso : φ.pullbackTopos ≅ ψ.pullbackTopos :=
  ((φ.pullbackPushforwardAdjunctionTopos).ofNatIsoRight
    (pushforwardToposIsoOfIso he)).leftAdjointUniq ψ.pullbackPushforwardAdjunctionTopos

end AlgebraicGeometry.RingedToposSiteHom

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe w

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {φ ψ : RingedToposSiteHom X Y} {e : ψ.u ≅ φ.u}
  (he : RingedToposSiteHom.FSharpCompatible φ ψ e)

/-- Degreewise pullback followed by localization, along isomorphic morphisms of ringed topoi. -/
def pullbackOnHomotopyIsoOfIso : pullbackOnHomotopy φ ≅ pullbackOnHomotopy ψ :=
  Functor.isoWhiskerRight
    { hom := NatTrans.mapHomotopyCategory (RingedToposSiteHom.pullbackToposIsoOfIso he).hom _
      inv := NatTrans.mapHomotopyCategory (RingedToposSiteHom.pullbackToposIsoOfIso he).inv _
      hom_inv_id := by simp [← NatTrans.mapHomotopyCategory_comp]
      inv_hom_id := by simp [← NatTrans.mapHomotopyCategory_comp] }
    DerivedCategory.Qh

variable [(pullbackOnHomotopy φ).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))]
  [(pullbackOnHomotopy ψ).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))]

/-- **The derived pullbacks along isomorphic morphisms of ringed topoi are isomorphic**:
`Lφ^* ≅ Lψ^*`, the isomorphism of total left derived functors induced by `φ^* ≅ ψ^*`. -/
def derivedPullbackIsoOfIso : derivedPullback φ ≅ derivedPullback ψ :=
  Functor.leftDerivedNatIso (derivedPullback φ) (derivedPullback ψ)
    (derivedPullbackComparison φ) (derivedPullbackComparison ψ)
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (.up ℤ))
    (pullbackOnHomotopyIsoOfIso he)

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

end
