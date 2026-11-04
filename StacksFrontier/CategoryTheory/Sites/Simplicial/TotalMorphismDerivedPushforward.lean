module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentKInjective
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.CohomologyOnAnOpenSubspace

/-!
# The derived direct image of a morphism between simplicial sites, in one degree

Let `h` be a morphism between simplicial sites in the cocontinuous case, as in Stacks 0D96.
It induces a morphism of the total topoi and, in every simplicial degree `n`, a morphism of the
component topoi, and these fit in a square with the two component morphisms `g_n` and `g'_n` of
that degree. On abelian sheaves the comparison of Stacks 0D96, `(g'_n)^{-1} h_{total,*} =
h_{n,*} g_n^{-1}`, holds, and so does its derived form: for `K` in the unbounded derived
category of abelian sheaves on the total site,

`(g'_n)^{-1} Rh_{total,*} K = Rh_{n,*} g_n^{-1} K`.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.abelianTotalPushforward` and
  `.abelianComponentPushforward`: the direct images of abelian sheaves along the total morphism
  and along the morphism of simplicial degree `n`.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.derivedAbelianTotalPushforward` and
  `.derivedAbelianComponentPushforward`: their unbounded derived functors, with the canonical
  comparisons `.derivedAbelianTotalPushforwardUnit` and
  `.derivedAbelianComponentPushforwardUnit`.
* `CategoryTheory.abelianPullbackCocontinuous` and `.abelianCocontinuousAdjunction`: the
  inverse image of abelian sheaves along a cocontinuous site functor and its adjunction with the
  direct image.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.Morphism.abelianTotalPushforwardRestrictIso`: the
  last assertion of Stacks 0D96, on abelian sheaves.
* `CategoryTheory.CocontinuousSimplicialSite.Morphism.derivedTotalPushforwardRestrictIso`:
  `(g'_n)^{-1} Rh_{total,*} ≅ Rh_{n,*} g_n^{-1}`, Stacks 0D97 in case (B).

## References

* [Stacks Project, Tag 0D97](https://stacks.math.columbia.edu/tag/0D97)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

/-! ### The direct image of abelian sheaves along a cocontinuous site functor -/

section AbelianCocontinuous

variable {X Y : Type u} [SmallCategory X] [SmallCategory Y] (J : GrothendieckTopology X)
  (L : GrothendieckTopology Y) (w : X ⥤ Y) [w.IsCocontinuous J L]

/-- The inverse image of abelian sheaves along a cocontinuous site functor: restrict along the
functor and sheafify. -/
def abelianPullbackCocontinuous : Sheaf L Ab.{u} ⥤ Sheaf J Ab.{u} :=
  sheafToPresheaf L Ab.{u} ⋙ (Functor.whiskeringLeft Xᵒᵖ Yᵒᵖ Ab.{u}).obj w.op ⋙
    presheafToSheaf J Ab.{u}

/-- For a cocontinuous site functor, the inverse image of abelian sheaves is left adjoint to the
direct image. -/
def abelianCocontinuousAdjunction :
    abelianPullbackCocontinuous J L w ⊣ w.sheafPushforwardCocontinuous Ab.{u} J L :=
  Adjunction.restrictFullyFaithful
    ((w.op.ranAdjunction Ab.{u}).comp (sheafificationAdjunction J Ab.{u}))
    (fullyFaithfulSheafToPresheaf L Ab.{u})
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    ((Functor.leftUnitor _).trans
      (w.sheafPushforwardCocontinuousCompSheafToPresheafIso Ab.{u} J L).symm)

/-- The direct image of abelian sheaves along a cocontinuous site functor is additive. -/
theorem additive_sheafPushforwardCocontinuous_ab :
    (w.sheafPushforwardCocontinuous Ab.{u} J L).Additive := by
  let _ := (abelianCocontinuousAdjunction J L w).isRightAdjoint
  exact Functor.additive_of_preserves_binary_products _

end AbelianCocontinuous

namespace CocontinuousSimplicialSite.Morphism

open SimplicialSiteSituation

variable {C C' : CocontinuousSimplicialSite.{u}}

/-! ### The direct images of abelian sheaves -/

/-- The direct image of abelian sheaves along the total morphism of a morphism between
simplicial sites in the cocontinuous case. -/
def abelianTotalPushforward (h : CocontinuousSimplicialSite.Morphism C C') :
    Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u} ⥤
      Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u} := by
  letI := h.totalFunctor_isCocontinuous
  exact h.totalFunctor.sheafPushforwardCocontinuous Ab.{u}
    (SimplicialCoverings.totalTopology C.underlying C.coverage)
    (SimplicialCoverings.totalTopology C'.underlying C'.coverage)

/-- The direct image of abelian sheaves in simplicial degree `n`. -/
def abelianComponentPushforward (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u} ⥤
      Sheaf ((⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u} := by
  letI : (h.hom.app (Opposite.op n)).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n))) :=
    h.isCocontinuous (Opposite.op n)
  exact (h.hom.app (Opposite.op n)).toFunctor.sheafPushforwardCocontinuous Ab.{u}
    (topologyOfCoverings (C.coverage (Opposite.op n)))
    (topologyOfCoverings (C'.coverage (Opposite.op n)))

/-- The direct image of abelian sheaves along the total morphism is additive. -/
theorem additive_abelianTotalPushforward (h : CocontinuousSimplicialSite.Morphism C C') :
    h.abelianTotalPushforward.Additive := by
  let _ := h.totalFunctor_isCocontinuous
  exact additive_sheafPushforwardCocontinuous_ab _ _ h.totalFunctor

/-- The direct image of abelian sheaves in a simplicial degree is additive. -/
theorem additive_abelianComponentPushforward (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    (h.abelianComponentPushforward n).Additive := by
  let _ : (h.hom.app (Opposite.op n)).toFunctor.IsCocontinuous
      (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C'.coverage (Opposite.op n))) :=
    h.isCocontinuous (Opposite.op n)
  exact additive_sheafPushforwardCocontinuous_ab _ _ (h.hom.app (Opposite.op n)).toFunctor

attribute [local instance] additive_abelianTotalPushforward additive_abelianComponentPushforward

/-- On abelian sheaves, in case (B) of Stacks 0D96: restriction to the component of simplicial
degree `n`, applied to the direct image along the total morphism, is the direct image in degree
`n` applied to restriction to the component of that degree. -/
def abelianTotalPushforwardRestrictIso (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward ⋙
        abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n ≅
      abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n ⋙
        h.abelianComponentPushforward n := by
  let v := (h.hom.app (Opposite.op n)).toFunctor
  let i := Grothendieck.ι C.underlying (Opposite.op n)
  let i' := Grothendieck.ι C'.underlying (Opposite.op n)
  let Jn := topologyOfCoverings (C.coverage (Opposite.op n))
  let Jn' := topologyOfCoverings (C'.coverage (Opposite.op n))
  let K := SimplicialCoverings.totalTopology C.underlying C.coverage
  let K' := SimplicialCoverings.totalTopology C'.underlying C'.coverage
  letI : v.IsCocontinuous Jn Jn' := h.isCocontinuous (Opposite.op n)
  letI : i.IsContinuous Jn K :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsContinuous Jn' K' :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  letI := h.totalFunctor_isCocontinuous
  let q : TwoSquare i v h.totalFunctor i' :=
    (Grothendieck.ιCompMap h.hom (Opposite.op n)).hom
  letI : q.GuitartExact := Grothendieck.guitartExact_ιCompMap h.hom (Opposite.op n)
  change h.totalFunctor.sheafPushforwardCocontinuous Ab.{u} K K' ⋙
      i'.sheafPushforwardContinuous Ab.{u} Jn' K' ≅
    i.sheafPushforwardContinuous Ab.{u} Jn K ⋙ v.sheafPushforwardCocontinuous Ab.{u} Jn Jn'
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf Jn' Ab.{u})
    (Functor.isoWhiskerLeft (sheafToPresheaf K Ab.{u})
      (asIso (q.op.ranBaseChange (D := Ab.{u}))))

/-- On abelian sheaves, in case (B) of Stacks 0D96: restriction to the component of simplicial
degree `n`, applied to the direct image along the total morphism, is the direct image in degree
`n` applied to restriction to the component of that degree, with restriction written as
`CategoryTheory.SimplicialSiteSituation.restrictAb`. -/
def abelianTotalPushforwardRestrictIso' (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward ⋙
        restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n ≅
      restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n ⋙
        h.abelianComponentPushforward n := by
  let v := (h.hom.app (Opposite.op n)).toFunctor
  let i := Grothendieck.ι C.underlying (Opposite.op n)
  let i' := Grothendieck.ι C'.underlying (Opposite.op n)
  let Jn := topologyOfCoverings (C.coverage (Opposite.op n))
  let Jn' := topologyOfCoverings (C'.coverage (Opposite.op n))
  let K := SimplicialCoverings.totalTopology C.underlying C.coverage
  let K' := SimplicialCoverings.totalTopology C'.underlying C'.coverage
  letI : v.IsCocontinuous Jn Jn' := h.isCocontinuous (Opposite.op n)
  letI : i.IsContinuous Jn K :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsContinuous Jn' K' :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
  letI := h.totalFunctor_isCocontinuous
  let q : TwoSquare i v h.totalFunctor i' :=
    (Grothendieck.ιCompMap h.hom (Opposite.op n)).hom
  letI : q.GuitartExact := Grothendieck.guitartExact_ιCompMap h.hom (Opposite.op n)
  change h.totalFunctor.sheafPushforwardCocontinuous Ab.{u} K K' ⋙
      i'.sheafPushforwardContinuous Ab.{u} Jn' K' ≅
    i.sheafPushforwardContinuous Ab.{u} Jn K ⋙ v.sheafPushforwardCocontinuous Ab.{u} Jn Jn'
  exact Functor.fullyFaithfulCancelRight (sheafToPresheaf Jn' Ab.{u})
    (Functor.isoWhiskerLeft (sheafToPresheaf K Ab.{u})
      (asIso (q.op.ranBaseChange (D := Ab.{u}))))

/-! ### The derived direct images -/

/-- The degreewise direct image of abelian sheaves along the total morphism, followed by
localization: a right derived functor of this functor is the derived direct image
`Rh_{total,*}`. -/
abbrev homotopyAbelianTotalPushforward (h : CocontinuousSimplicialSite.Morphism C C') :
    HomotopyCategory
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ) ⥤
      DerivedCategory
        (Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :=
  h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The degreewise direct image of abelian sheaves in simplicial degree `n`, followed by
localization: a right derived functor of this functor is the derived direct image
`Rh_{n,*}`. -/
abbrev homotopyAbelianComponentPushforward (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    HomotopyCategory
        (Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
        (ComplexShape.up ℤ) ⥤
      DerivedCategory
        (Sheaf ((⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :=
  (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute the derived direct image along the total morphism
pointwise. -/
theorem hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforward
    (h : CocontinuousSimplicialSite.Morphism C C') :
    h.homotopyAbelianTotalPushforward.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
    Stacks.Cohomology.Localization.enoughKInjectives).1

/-- K-injective resolutions compute the derived direct image in simplicial degree `n`
pointwise. -/
theorem hasPointwiseRightDerivedFunctor_homotopyAbelianComponentPushforward
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.homotopyAbelianComponentPushforward n).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
    Stacks.Cohomology.Localization.enoughKInjectives).1

attribute [local instance] hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforward
  hasPointwiseRightDerivedFunctor_homotopyAbelianComponentPushforward

/-- **The derived direct image along the total morphism exists**, with no hypothesis beyond the
morphism between simplicial sites. -/
theorem hasRightDerivedFunctor_homotopyAbelianTotalPushforward
    (h : CocontinuousSimplicialSite.Morphism C C') :
    h.homotopyAbelianTotalPushforward.HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **The derived direct image in simplicial degree `n` exists**, with no hypothesis beyond the
morphism between simplicial sites. -/
theorem hasRightDerivedFunctor_homotopyAbelianComponentPushforward
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.homotopyAbelianComponentPushforward n).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
        (ComplexShape.up ℤ)) :=
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

attribute [local instance] hasRightDerivedFunctor_homotopyAbelianTotalPushforward
  hasRightDerivedFunctor_homotopyAbelianComponentPushforward

/-- `Rh_{total,*}`: the unbounded derived direct image along the total morphism. -/
abbrev derivedAbelianTotalPushforward (h : CocontinuousSimplicialSite.Morphism C C') :
    DerivedCategory (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) ⥤
      DerivedCategory
        (Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :=
  h.homotopyAbelianTotalPushforward.totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (ComplexShape.up ℤ))

/-- The canonical comparison from the degreewise direct image along the total morphism to
`Rh_{total,*}`. -/
abbrev derivedAbelianTotalPushforwardUnit (h : CocontinuousSimplicialSite.Morphism C C') :
    h.homotopyAbelianTotalPushforward ⟶
      DerivedCategory.Qh ⋙ h.derivedAbelianTotalPushforward :=
  h.homotopyAbelianTotalPushforward.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (ComplexShape.up ℤ))

/-- `Rh_{n,*}`: the unbounded derived direct image in simplicial degree `n`. -/
abbrev derivedAbelianComponentPushforward (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    DerivedCategory
        (Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) ⥤
      DerivedCategory
        (Sheaf ((⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :=
  (h.homotopyAbelianComponentPushforward n).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
      (ComplexShape.up ℤ))

/-- The canonical comparison from the degreewise direct image in simplicial degree `n` to
`Rh_{n,*}`. -/
abbrev derivedAbelianComponentPushforwardUnit (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.homotopyAbelianComponentPushforward n ⟶
      DerivedCategory.Qh ⋙ h.derivedAbelianComponentPushforward n :=
  (h.homotopyAbelianComponentPushforward n).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
      (ComplexShape.up ℤ))

/-- The underived comparison of Stacks 0D96, read on the unbounded homotopy categories. -/
def homotopyAbelianTotalPushforwardRestrictIso (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (h.abelianTotalPushforwardRestrictIso n)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n ⋙
        h.abelianComponentPushforward n)) (ComplexShape.up ℤ)).symm

/-- The underived comparison of Stacks 0D96, read on the unbounded homotopy categories, with
restriction written as `CategoryTheory.SimplicialSiteSituation.restrictAb`. -/
def homotopyAbelianTotalPushforwardRestrictIso' (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (h.abelianTotalPushforwardRestrictIso' n)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n ⋙
        h.abelianComponentPushforward n)) (ComplexShape.up ℤ)).symm

/-- The comparison from the degreewise total direct image followed by degreewise restriction
into `Rh_{total,*}` followed by the derived restriction. -/
def derivedTotalPushforwardRestrictUnit (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (h.derivedAbelianTotalPushforward ⋙
        (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory) :=
  Functor.whiskerLeft (h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ))
      (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
        ).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (h.derivedAbelianTotalPushforwardUnit)
      (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory

/-- The comparison from the degreewise total direct image followed by degreewise restriction
into `Rh_{total,*}` followed by the derived restriction, with restriction written as
`CategoryTheory.SimplicialSiteSituation.restrictAb`. -/
def derivedTotalPushforwardRestrictUnit' (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (h.derivedAbelianTotalPushforward ⋙
        (restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory) :=
  Functor.whiskerLeft (h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ))
      (restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n
        ).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (h.derivedAbelianTotalPushforwardUnit)
      (restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory

/-- The comparison from degreewise restriction followed by the degreewise direct image of degree
`n` into the derived restriction followed by `Rh_{n,*}`. -/
def derivedRestrictTotalPushforwardUnit (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    (abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        ((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
          h.derivedAbelianComponentPushforward n) :=
  Functor.whiskerLeft
      ((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (h.derivedAbelianComponentPushforwardUnit n) ≫
    Functor.whiskerRight
      (abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
        ).mapDerivedCategoryFactorsh.inv
      (h.derivedAbelianComponentPushforward n)

/-- The comparison from degreewise restriction followed by the degreewise direct image of degree
`n` into the derived restriction followed by `Rh_{n,*}`, with restriction written as
`CategoryTheory.SimplicialSiteSituation.restrictAb`. -/
def derivedRestrictTotalPushforwardUnit' (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    (restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        ((restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
          h.derivedAbelianComponentPushforward n) :=
  Functor.whiskerLeft
      ((restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (h.derivedAbelianComponentPushforwardUnit n) ≫
    Functor.whiskerRight
      (restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n
        ).mapDerivedCategoryFactorsh.inv
      (h.derivedAbelianComponentPushforward n)

/-- For an exact functor `R` out of the abelian sheaves on the target total site, `Rh_{total,*}`
followed by the derived functor of `R` is a right derived functor of the degreewise total direct
image followed by `R`. -/
private theorem isRightDerivedFunctor_total_pushforward_mapDerivedCategory
    (h : CocontinuousSimplicialSite.Morphism C C')
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (R : Sheaf (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u} ⥤ A)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] :
    (h.derivedAbelianTotalPushforward ⋙ R.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerLeft (h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ))
          R.mapDerivedCategoryFactorsh.inv ≫
        Functor.whiskerRight h.derivedAbelianTotalPushforwardUnit R.mapDerivedCategory)
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have _ := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    h.homotopyAbelianTotalPushforward h.derivedAbelianTotalPushforward
    (h.derivedAbelianTotalPushforwardUnit) I
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- `Rh_{total,*}` followed by the derived restriction to simplicial degree `n` is a right
derived functor of degreewise total direct image followed by degreewise restriction. -/
theorem isRightDerivedFunctor_derivedTotalPushforwardRestrictUnit
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.derivedAbelianTotalPushforward ⋙
        (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u})
          n).mapDerivedCategory).IsRightDerivedFunctor
      (h.derivedTotalPushforwardRestrictUnit n)
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_total_pushforward_mapDerivedCategory h _

/-- `Rh_{total,*}` followed by the derived restriction to simplicial degree `n` is a right
derived functor of degreewise total direct image followed by degreewise restriction, with
restriction written as `CategoryTheory.SimplicialSiteSituation.restrictAb`. -/
theorem isRightDerivedFunctor_derivedTotalPushforwardRestrictUnit'
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.derivedAbelianTotalPushforward ⋙
        (restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u})
          n).mapDerivedCategory).IsRightDerivedFunctor
      (h.derivedTotalPushforwardRestrictUnit' n)
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_total_pushforward_mapDerivedCategory h _

/-- If `R` is an exact functor out of the abelian sheaves on the source total site preserving
K-injective complexes, then `R.mapDerivedCategory` followed by `Rh_{n,*}` is a right derived
functor of `R` followed by the degreewise direct image of degree `n`. -/
private theorem isRightDerivedFunctor_mapDerivedCategory_component_pushforward
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory)
    (R : Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u} ⥤
      Sheaf ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (hR : ∀ I : CochainComplex
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) ℤ,
      I.IsKInjective → CochainComplex.IsKInjective ((R.mapHomologicalComplex _).obj I)) :
    (R.mapDerivedCategory ⋙ h.derivedAbelianComponentPushforward n).IsRightDerivedFunctor
      (Functor.whiskerLeft (R.mapHomotopyCategory (ComplexShape.up ℤ))
          (h.derivedAbelianComponentPushforwardUnit n) ≫
        Functor.whiskerRight R.mapDerivedCategoryFactorsh.inv
          (h.derivedAbelianComponentPushforward n))
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have _ : IsIso ((h.derivedAbelianComponentPushforwardUnit n).app
      ((R.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
          (ComplexShape.up ℤ)).obj I))) := by
    have _ := hR I hI
    exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (h.homotopyAbelianComponentPushforward n) (h.derivedAbelianComponentPushforward n)
      (h.derivedAbelianComponentPushforwardUnit n) ((R.mapHomologicalComplex _).obj I)
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- The derived restriction to simplicial degree `n` followed by `Rh_{n,*}` is a right derived
functor of degreewise restriction followed by the degreewise direct image of degree `n`. -/
theorem isRightDerivedFunctor_derivedRestrictTotalPushforwardUnit
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    ((abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
        h.derivedAbelianComponentPushforward n).IsRightDerivedFunctor
      (h.derivedRestrictTotalPushforwardUnit n)
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_mapDerivedCategory_component_pushforward h n _ fun I _ =>
    SimplicialSiteSituation.isKInjective_componentRestriction _ n I

/-- The derived restriction to simplicial degree `n` followed by `Rh_{n,*}` is a right derived
functor of degreewise restriction followed by the degreewise direct image of degree `n`, with
restriction written as `CategoryTheory.SimplicialSiteSituation.restrictAb`. -/
theorem isRightDerivedFunctor_derivedRestrictTotalPushforwardUnit'
    (h : CocontinuousSimplicialSite.Morphism C C') (n : SimplexCategory) :
    ((restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
        h.derivedAbelianComponentPushforward n).IsRightDerivedFunctor
      (h.derivedRestrictTotalPushforwardUnit' n)
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_mapDerivedCategory_component_pushforward h n _ fun I _ =>
    SimplicialSiteSituation.isKInjective_componentRestriction _ n I

/-- In case (B), with notation and hypotheses as in Stacks 0D96: the natural isomorphism
`(g'_n)^{-1} Rh_{total,*} K ≅ Rh_{n,*} g_n^{-1} K` for `K` in the unbounded derived category of
abelian sheaves on the total site. -/
@[stacks 0D97 "case (B)"]
def derivedTotalPushforwardRestrictIso (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.derivedAbelianTotalPushforward ⋙
        (abelianComponent (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ≅
      (abelianComponent (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
        h.derivedAbelianComponentPushforward n :=
  have _ := h.isRightDerivedFunctor_derivedTotalPushforwardRestrictUnit n
  have _ := h.isRightDerivedFunctor_derivedRestrictTotalPushforwardUnit n
  Functor.rightDerivedNatIso _ _ (h.derivedTotalPushforwardRestrictUnit n)
    (h.derivedRestrictTotalPushforwardUnit n)
    (HomotopyCategory.quasiIso
      (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (h.homotopyAbelianTotalPushforwardRestrictIso n)
      DerivedCategory.Qh)

/-- In case (B), with notation and hypotheses as in Stacks 0D96: the natural isomorphism
`(g'_n)^{-1} Rh_{total,*} K ≅ Rh_{n,*} g_n^{-1} K` for `K` in the unbounded derived category of
abelian sheaves on the total site, with restriction written as
`CategoryTheory.SimplicialSiteSituation.restrictAb`. -/
@[stacks 0D97 "case (B)"]
def derivedTotalPushforwardRestrictIso' (h : CocontinuousSimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.derivedAbelianTotalPushforward ⋙
        (restrictAb (⟨Sum.inr C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ≅
      (restrictAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
        h.derivedAbelianComponentPushforward n :=
  have _ := h.isRightDerivedFunctor_derivedTotalPushforwardRestrictUnit' n
  have _ := h.isRightDerivedFunctor_derivedRestrictTotalPushforwardUnit' n
  Functor.rightDerivedNatIso _ _ (h.derivedTotalPushforwardRestrictUnit' n)
    (h.derivedRestrictTotalPushforwardUnit' n)
    (HomotopyCategory.quasiIso
      (Sheaf (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (h.homotopyAbelianTotalPushforwardRestrictIso' n)
      DerivedCategory.Qh)

end CocontinuousSimplicialSite.Morphism

end CategoryTheory

end
