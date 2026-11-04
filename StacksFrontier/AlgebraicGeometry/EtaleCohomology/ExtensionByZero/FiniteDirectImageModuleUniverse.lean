module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.ModuleCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero commutes with a finite direct image, at every coefficient universe

Let
```
V --j'--> V̄
|f        |f̄
v         v
U --j---> Ū
```
be a cartesian square of schemes with `j` an open immersion and `f̄` finite, and let `Λ` be a
ring in an arbitrary universe. For sheaves of `Λ`-modules on the small étale sites,
`j_! ∘ f_* ≅ f̄_* ∘ j'_!` ([Stacks, Tag 0GJ1]).

The library has this isomorphism for rings in `Type`
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroDirectImageIsoOfIsIntegralHom`, through
integral base change at the coefficients `AddCommGrpCat.{u + 1}`) and for torsion rings in every
universe (`Stacks.EtaleCohomology.etaleModuleDirectImageExtensionByZeroIso`). Here the ring is
arbitrary and in an arbitrary universe: the comparison map is the adjoint of the unit of `j'_!`
followed by the étale base change `f_* j'^{-1} ≅ j^{-1} f̄_*`
(`Stacks.EtaleCohomology.etaleRestrictionPushforwardIsoOfIsPullback`), and it is invertible
because it is so over `U` by construction while both sides vanish over the closed complement of
`U`: the source because it is an extension by zero from `U`, the target by proper base change in
degree zero (`Stacks.EtaleCohomology.isZero_etaleModuleInverseImage_directImage_of_isProper_univ`,
[Stacks, Tag 0A3U]).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroFiniteDirectImageMap`: the comparison
  `j_! ∘ f_* ⟶ f̄_* ∘ j'_!`.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroFiniteDirectImageIso`: **Tag 0GJ1** for
  sheaves of modules over a ring in an arbitrary universe.

## References

* [Stacks Project, Tag 0GJ1](https://stacks.math.columbia.edu/tag/0GJ1)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [-instance] etaleModules_enoughInjectives_univZero

variable (Λ : Type r) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [IsOpenImmersion j]
  (j' : V ⟶ Vb) [IsOpenImmersion j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) (sq : IsPullback f j' j fb)

/-- **The comparison `j_! ∘ f_* ⟶ f̄_* ∘ j'_!`**: for a sheaf `M` on `V_étale`, the map
`j_!(f_* M) ⟶ f̄_*(j'_! M)` adjoint under `j_! ⊣ j^{-1}` to the image under `f_*` of the unit of
`j'_! ⊣ j'^{-1}` followed by the étale base change `f_* j'^{-1} ≅ j^{-1} f̄_*`. -/
def etaleModuleExtensionByZeroFiniteDirectImageMap :
    etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ⟶
      etaleModuleExtensionByZero.{u, r} Λ j' ⋙ etaleModuleDirectImage.{u, r} Λ fb :=
  Functor.whiskerRight ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (etaleModuleExtensionByZeroAdj.{u, r} Λ j').unit
        (etaleModuleDirectImage.{u, r} Λ f) ≫
      Functor.whiskerLeft (etaleModuleExtensionByZero.{u, r} Λ j')
        (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) sq).hom)
      (etaleModuleExtensionByZero.{u, r} Λ j) ≫
    Functor.whiskerLeft (etaleModuleExtensionByZero.{u, r} Λ j' ⋙
      etaleModuleDirectImage.{u, r} Λ fb) (etaleModuleExtensionByZeroAdj.{u, r} Λ j).counit

/-- The components of `etaleModuleExtensionByZeroFiniteDirectImageMap` are adjoint, under
`j_! ⊣ j^{-1}`, to the unit of `j'_! ⊣ j'^{-1}` followed by the étale base change. -/
theorem etaleModuleExtensionByZeroFiniteDirectImageMap_app (M : EtaleModules.{u, r} Λ V) :
    (etaleModuleExtensionByZeroFiniteDirectImageMap Λ j j' f fb sq).app M =
      ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).homEquiv _ _).symm
        ((etaleModuleDirectImage.{u, r} Λ f).map
            ((etaleModuleExtensionByZeroAdj.{u, r} Λ j').unit.app M) ≫
          (etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) sq).hom.app
            ((etaleModuleExtensionByZero.{u, r} Λ j').obj M)) := by
  simp [etaleModuleExtensionByZeroFiniteDirectImageMap, Adjunction.homEquiv_counit]

variable [IsFinite fb]

/-- The comparison is invertible at every sheaf, given a closed immersion `i` onto the
complement of `U`. -/
@[sga "4 IX 5.2.1" "special case"]
theorem isIso_etaleModuleExtensionByZeroFiniteDirectImageMap_app {Z : Scheme.{u}} (i : Z ⟶ Ub)
    [IsClosedImmersion i] (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (M : EtaleModules.{u, r} Λ V) :
    IsIso ((etaleModuleExtensionByZeroFiniteDirectImageMap Λ j j' f fb sq).app M) := by
  set γ := (etaleModuleExtensionByZeroFiniteDirectImageMap Λ j j' f fb sq).app M
  set ρ := etaleRestrictionPushforwardIsoOfIsPullback (ModuleCat.{max (u + 1) r} Λ) sq
  have hU : IsIso ((etaleModuleInverseImage.{u, r} Λ j).map γ) := by
    have hR : IsIso ((etaleModuleRestriction.{u, r} Λ j).map γ) := by
      have h' : ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).homEquiv _ _) γ =
          (etaleModuleDirectImage.{u, r} Λ f).map
            ((etaleModuleExtensionByZeroAdj.{u, r} Λ j').unit.app M) ≫
            ρ.hom.app ((etaleModuleExtensionByZero.{u, r} Λ j').obj M) := by
        simp only [γ, etaleModuleExtensionByZeroFiniteDirectImageMap_app]
        exact Equiv.apply_symm_apply _ _
      have : IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app
          ((etaleModuleDirectImage.{u, r} Λ f).obj M) ≫
            (etaleModuleRestriction.{u, r} Λ j).map γ) := by
        rw [← Adjunction.homEquiv_unit (etaleModuleExtensionByZeroAdj.{u, r} Λ j) _ _ γ, h']
        infer_instance
      exact IsIso.of_isIso_comp_left ((etaleModuleExtensionByZeroAdj.{u, r} Λ j).unit.app
        ((etaleModuleDirectImage.{u, r} Λ f).obj M)) _
    exact (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, r} Λ j) γ).mpr hR
  have hZ : IsIso ((etaleModuleInverseImage.{u, r} Λ i).map γ) := by
    have h₁ := isZero_etaleModuleInverseImage_extensionByZero Λ i j hij
      ((etaleModuleDirectImage.{u, r} Λ f).obj M)
    have h₂ : IsZero ((etaleModuleInverseImage.{u, r} Λ i).obj
        ((etaleModuleDirectImage.{u, r} Λ fb).obj
          ((etaleModuleExtensionByZero.{u, r} Λ j').obj M))) := by
      refine isZero_etaleModuleInverseImage_directImage_of_isProper_univ Λ fb i _ ?_
      intro T t ht
      refine isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ t j' ?_ M
      rw [Set.disjoint_left]
      rintro _ ⟨y, rfl⟩ ⟨v, hv⟩
      have h1 : fb.base (t.base y) ∈ Set.range i.base := ht ⟨y, rfl⟩
      have h2 : fb.base (t.base y) ∈ Set.range j.base :=
        ⟨f.base v, by rw [← hv, ← Scheme.Hom.comp_apply, sq.w, Scheme.Hom.comp_apply]⟩
      rw [hij] at h2
      exact h2 h1
    exact ⟨0, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij γ

/-- **Stacks Project, Tag 0GJ1**, for sheaves of modules over a ring in an arbitrary universe.
For a cartesian square `f ≫ j = j' ≫ f̄` of schemes with `j` an open immersion and `f̄` finite,
`j_! ∘ f_* ≅ f̄_* ∘ j'_!` as functors from sheaves of `Λ`-modules on `V_étale` to sheaves of
`Λ`-modules on `Ū_étale`. -/
def etaleModuleExtensionByZeroFiniteDirectImageIso :
    etaleModuleDirectImage.{u, r} Λ f ⋙ etaleModuleExtensionByZero.{u, r} Λ j ≅
      etaleModuleExtensionByZero.{u, r} Λ j' ⋙ etaleModuleDirectImage.{u, r} Λ fb := by
  let Zc : Ub.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have hij : Set.range j.base = (Set.range Zc.subschemeι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl _).symm
  have : ∀ M, IsIso ((etaleModuleExtensionByZeroFiniteDirectImageMap Λ j j' f fb sq).app M) :=
    fun M => isIso_etaleModuleExtensionByZeroFiniteDirectImageMap_app Λ j j' f fb sq
      Zc.subschemeι hij M
  have : IsIso (etaleModuleExtensionByZeroFiniteDirectImageMap Λ j j' f fb sq) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (etaleModuleExtensionByZeroFiniteDirectImageMap Λ j j' f fb sq)

end Stacks.EtaleCohomology

end
