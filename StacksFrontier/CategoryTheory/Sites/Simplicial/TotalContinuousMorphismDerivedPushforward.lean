module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalMorphismDerivedPushforward

/-!
# The derived direct image of a morphism between simplicial sites in one degree, case (A)

Let `h` be a morphism between simplicial sites in case (A) of Stacks 09WE: in each simplicial
degree `n` a morphism of sites `h_n : C_n → C'_n` given by a continuous functor
`v_n : C'_n ⥤ C_n`, the `v_n` commuting with the transition functors, and `v_total` the induced
continuous functor of total sites. The morphism of total topoi `h_{total}`, the morphisms `h_n`
and the two component morphisms `g_n`, `g'_n` satisfy `(g'_n)^{-1} h_{total,*} = h_{n,*} g_n^{-1}`
(Stacks 0D96), and this module derives it on abelian sheaves: for `K` in the unbounded derived
category of abelian sheaves on the total site,

`(g'_n)^{-1} Rh_{total,*} K = Rh_{n,*} g_n^{-1} K`.

## Main definitions

* `CategoryTheory.SimplicialSite.Morphism.abelianTotalPushforward` and
  `.abelianComponentPushforward`: the direct images of abelian sheaves along the total morphism
  and along the morphism of simplicial degree `n`, restriction along `v_total` and along `v_n`.
* `CategoryTheory.SimplicialSite.Morphism.derivedAbelianTotalPushforward` and
  `.derivedAbelianComponentPushforward`: their unbounded derived functors, with the canonical
  comparisons `.derivedAbelianTotalPushforwardUnit` and
  `.derivedAbelianComponentPushforwardUnit`.

## Main results

* `CategoryTheory.SimplicialSite.Morphism.abelianTotalPushforwardRestrictIso`:
  `(g'_n)^{-1} h_{total,*} ≅ h_{n,*} g_n^{-1}` on abelian sheaves.
* `CategoryTheory.SimplicialSite.Morphism.derivedTotalPushforwardRestrictIso`:
  `(g'_n)^{-1} Rh_{total,*} ≅ Rh_{n,*} g_n^{-1}` on the unbounded derived categories.

## References

* [Stacks Project, Tag 0D97](https://stacks.math.columbia.edu/tag/0D97)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

namespace SimplicialSite.Morphism

open SimplicialSiteSituation

variable {C C' : SimplicialSite.{u}}

/-! ### The direct images of abelian sheaves -/

/-- The direct image of abelian sheaves along the total morphism of a morphism between
simplicial sites in case (A): restriction along the functor between the total categories. -/
def abelianTotalPushforward (h : SimplicialSite.Morphism C C') :
    Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u} ⥤
      Sheaf (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u} := by
  letI := h.totalFunctor_isContinuous
  exact h.totalFunctor.sheafPushforwardContinuous Ab.{u} C'.totalTopology C.totalTopology

/-- The direct image of abelian sheaves in simplicial degree `n`: restriction along the functor
representing the morphism of sites of that degree. -/
def abelianComponentPushforward (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u} ⥤
      Sheaf ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u} := by
  letI := (h.isMorphismOfSites n).isContinuous
  exact (h.hom.app n).toFunctor.sheafPushforwardContinuous Ab.{u}
    (C'.coverage n).toGrothendieck (C.coverage n).toGrothendieck

/-- The direct image of abelian sheaves along the total morphism is additive. -/
theorem additive_abelianTotalPushforward (h : SimplicialSite.Morphism C C') :
    h.abelianTotalPushforward.Additive := by
  let := h.totalFunctor_isContinuous
  exact Functor.additive_sheafPushforwardContinuous h.totalFunctor C'.totalTopology
    C.totalTopology Ab.{u}

/-- The direct image of abelian sheaves in a simplicial degree is additive. -/
theorem additive_abelianComponentPushforward (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    (h.abelianComponentPushforward n).Additive := by
  let := (h.isMorphismOfSites n).isContinuous
  exact Functor.additive_sheafPushforwardContinuous (h.hom.app n).toFunctor
    (C'.coverage n).toGrothendieck (C.coverage n).toGrothendieck Ab.{u}

attribute [local instance] additive_abelianTotalPushforward additive_abelianComponentPushforward

/-- In case (A), on abelian sheaves, restriction to the component of simplicial degree `n`,
applied to the direct image along the total morphism, is the direct image in degree `n` applied
to restriction to the component of that degree. -/
def abelianTotalPushforwardRestrictIso (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward ⋙
        abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n ≅
      abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n ⋙
        h.abelianComponentPushforward n := by
  let v := (h.hom.app n).toFunctor
  let i := CoGrothendieck.ι C.totalPseudofunctor (Opposite.op n)
  let i' := CoGrothendieck.ι C'.totalPseudofunctor (Opposite.op n)
  let Jn := (C.coverage n).toGrothendieck
  let Jn' := (C'.coverage n).toGrothendieck
  letI : v.IsContinuous Jn' Jn := (h.isMorphismOfSites n).isContinuous
  letI : i.IsContinuous Jn C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  letI : i'.IsContinuous Jn' C'.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
  letI : @Functor.IsContinuous (C.underlying.obj n) (C.underlying.obj n).str
      (CoGrothendieck C.totalPseudofunctor) _
      i Jn C.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
  letI : @Functor.IsContinuous (C'.underlying.obj n) (C'.underlying.obj n).str
      (CoGrothendieck C'.totalPseudofunctor) _
      i' Jn' C'.totalTopology :=
    SimplicialSiteSituation.componentFunctor_isContinuous
      (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
  letI := h.totalFunctor_isContinuous
  letI : (v ⋙ i).IsContinuous Jn' C.totalTopology :=
    Functor.isContinuous_comp v i Jn' Jn C.totalTopology
  change h.totalFunctor.sheafPushforwardContinuous Ab.{u} C'.totalTopology C.totalTopology ⋙
      i'.sheafPushforwardContinuous Ab.{u} Jn' C'.totalTopology ≅
    i.sheafPushforwardContinuous Ab.{u} Jn C.totalTopology ⋙
      v.sheafPushforwardContinuous Ab.{u} Jn' Jn
  exact Functor.sheafPushforwardContinuousComp' (h.componentIso (Opposite.op n)).symm Ab.{u}
      Jn' C'.totalTopology C.totalTopology ≪≫
    (Functor.sheafPushforwardContinuousComp v i Ab.{u} Jn' Jn C.totalTopology).symm

/-! ### The derived direct images -/

/-- The degreewise direct image of abelian sheaves along the total morphism, followed by
localization: a right derived functor of this functor is `Rh_{total,*}`. -/
abbrev homotopyAbelianTotalPushforward (h : SimplicialSite.Morphism C C') :
    HomotopyCategory
        (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ) ⥤
      DerivedCategory
        (Sheaf (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :=
  h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The degreewise direct image of abelian sheaves in simplicial degree `n`, followed by
localization: a right derived functor of this functor is `Rh_{n,*}`. -/
abbrev homotopyAbelianComponentPushforward (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    HomotopyCategory
        (Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
        (ComplexShape.up ℤ) ⥤
      DerivedCategory
        (Sheaf ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :=
  (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- K-injective resolutions compute the derived direct image along the total morphism
pointwise. -/
@[sga "4½ Etat_0 4.2.3" "clause a), special case"]
theorem hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforward
    (h : SimplicialSite.Morphism C C') :
    h.homotopyAbelianTotalPushforward.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
    Stacks.Cohomology.Localization.enoughKInjectives).1

/-- K-injective resolutions compute the derived direct image in simplicial degree `n`
pointwise. -/
theorem hasPointwiseRightDerivedFunctor_homotopyAbelianComponentPushforward
    (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.homotopyAbelianComponentPushforward n).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
        (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
    Stacks.Cohomology.Localization.enoughKInjectives).1

attribute [local instance] hasPointwiseRightDerivedFunctor_homotopyAbelianTotalPushforward
  hasPointwiseRightDerivedFunctor_homotopyAbelianComponentPushforward

/-- `Rh_{total,*}`: the unbounded derived direct image along the total morphism. -/
abbrev derivedAbelianTotalPushforward (h : SimplicialSite.Morphism C C') :
    DerivedCategory (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) ⥤
      DerivedCategory
        (Sheaf (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u}) :=
  h.homotopyAbelianTotalPushforward.totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (ComplexShape.up ℤ))

/-- The canonical comparison from the degreewise direct image along the total morphism to
`Rh_{total,*}`. -/
abbrev derivedAbelianTotalPushforwardUnit (h : SimplicialSite.Morphism C C') :
    h.homotopyAbelianTotalPushforward ⟶
      DerivedCategory.Qh ⋙ h.derivedAbelianTotalPushforward :=
  h.homotopyAbelianTotalPushforward.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (ComplexShape.up ℤ))

/-- `Rh_{n,*}`: the unbounded derived direct image in simplicial degree `n`. -/
abbrev derivedAbelianComponentPushforward (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    DerivedCategory
        (Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) ⥤
      DerivedCategory
        (Sheaf ((⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u}) :=
  (h.homotopyAbelianComponentPushforward n).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
      (ComplexShape.up ℤ))

/-- The canonical comparison from the degreewise direct image in simplicial degree `n` to
`Rh_{n,*}`. -/
abbrev derivedAbelianComponentPushforwardUnit (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.homotopyAbelianComponentPushforward n ⟶
      DerivedCategory.Qh ⋙ h.derivedAbelianComponentPushforward n :=
  (h.homotopyAbelianComponentPushforward n).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n) Ab.{u})
      (ComplexShape.up ℤ))

/-- `abelianTotalPushforwardRestrictIso`, applied degreewise, on the unbounded homotopy
categories. -/
def homotopyAbelianTotalPushforwardRestrictIso (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      (abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (h.abelianTotalPushforwardRestrictIso n)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n ⋙
        h.abelianComponentPushforward n)) (ComplexShape.up ℤ)).symm

/-- The comparison from the degreewise total direct image followed by degreewise restriction
into `Rh_{total,*}` followed by the derived restriction. -/
def derivedTotalPushforwardRestrictUnit (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (h.derivedAbelianTotalPushforward ⋙
        (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory) :=
  Functor.whiskerLeft (h.abelianTotalPushforward.mapHomotopyCategory (ComplexShape.up ℤ))
      (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n
        ).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (h.derivedAbelianTotalPushforwardUnit)
      (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory

/-- The comparison from degreewise restriction followed by the degreewise direct image of degree
`n` into the derived restriction followed by `Rh_{n,*}`. -/
def derivedRestrictTotalPushforwardUnit (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    (abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        (h.abelianComponentPushforward n).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        ((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
          h.derivedAbelianComponentPushforward n) :=
  Functor.whiskerLeft
      ((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (h.derivedAbelianComponentPushforwardUnit n) ≫
    Functor.whiskerRight
      (abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n
        ).mapDerivedCategoryFactorsh.inv
      (h.derivedAbelianComponentPushforward n)

/-- `Rh_{total,*}` followed by the derived restriction to simplicial degree `n` is a right
derived functor of degreewise total direct image followed by degreewise restriction. -/
theorem isRightDerivedFunctor_derivedTotalPushforwardRestrictUnit
    (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    (h.derivedAbelianTotalPushforward ⋙
        (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u})
          n).mapDerivedCategory).IsRightDerivedFunctor
      (h.derivedTotalPushforwardRestrictUnit n)
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have _ := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    h.homotopyAbelianTotalPushforward h.derivedAbelianTotalPushforward
    h.derivedAbelianTotalPushforwardUnit I
  rw [derivedTotalPushforwardRestrictUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- The derived restriction to simplicial degree `n` followed by `Rh_{n,*}` is a right derived
functor of degreewise restriction followed by the degreewise direct image of degree `n`. -/
theorem isRightDerivedFunctor_derivedRestrictTotalPushforwardUnit
    (h : SimplicialSite.Morphism C C') (n : SimplexCategory) :
    ((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
        h.derivedAbelianComponentPushforward n).IsRightDerivedFunctor
      (h.derivedRestrictTotalPushforwardUnit n)
      (HomotopyCategory.quasiIso
        (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
        (ComplexShape.up ℤ)) := by
  apply Stacks.Cohomology.Localization.rightDerived_of_kInjectives
  intro I hI
  have _ : IsIso ((h.derivedAbelianComponentPushforwardUnit n).app
      (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient
          (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
          (ComplexShape.up ℤ)).obj I))) := by
    have _ : CochainComplex.IsKInjective
        (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
      SimplicialSiteSituation.isKInjective_componentRestriction
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n I
    exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
      (h.homotopyAbelianComponentPushforward n) (h.derivedAbelianComponentPushforward n)
      (h.derivedAbelianComponentPushforwardUnit n)
      (((abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)
  rw [derivedRestrictTotalPushforwardUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  infer_instance

/-- For a morphism between simplicial sites built from morphisms of sites (case (A)), and `K` in
the unbounded derived category of abelian sheaves on the total site,
`(g'_n)^{-1} Rh_{total,*} K = Rh_{n,*} g_n^{-1} K`, as a natural isomorphism of functors on the
derived categories. -/
@[stacks 0D97 "case (A)"]
def derivedTotalPushforwardRestrictIso (h : SimplicialSite.Morphism C C')
    (n : SimplexCategory) :
    h.derivedAbelianTotalPushforward ⋙
        (abelianComponent (⟨Sum.inl C'⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ≅
      (abelianComponent (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n).mapDerivedCategory ⋙
        h.derivedAbelianComponentPushforward n :=
  have _ := h.isRightDerivedFunctor_derivedTotalPushforwardRestrictUnit n
  have _ := h.isRightDerivedFunctor_derivedRestrictTotalPushforwardUnit n
  Functor.rightDerivedNatIso _ _ (h.derivedTotalPushforwardRestrictUnit n)
    (h.derivedRestrictTotalPushforwardUnit n)
    (HomotopyCategory.quasiIso
      (Sheaf (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology Ab.{u})
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (h.homotopyAbelianTotalPushforwardRestrictIso n)
      DerivedCategory.Qh)

end SimplicialSite.Morphism

end CategoryTheory

end
