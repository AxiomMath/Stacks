module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotArtinOpenness
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorLimitPreserving

/-!
# Axiom [1] for the Quot functor: limit preservation

A model of the Quot presheaf over a base with at most one point over every scheme of the site is
limit preserving along cofiltered limits of affine schemes, for `F` of finite presentation: a
quotient over the limit comes from a stage
(`AlgebraicGeometry.Space.QuotSituation.exists_stage_quotientPullback_eq`), and two quotients over
a stage which agree over the limit agree at a later stage
(`AlgebraicGeometry.Space.QuotSitePresheafModel.exists_stage_eq`).

## Main results

* `AlgebraicGeometry.Space.QuotSitePresheafModel.limitPreserving`: limit preservation of a model.
* `AlgebraicGeometry.Space.limitPreserving_quotOverBase`: **Stacks 0CZW, axiom [1]**.

## References

* [Stacks Project, Tag 0CZW](https://stacks.math.columbia.edu/tag/0CZW)
* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSitePresheafModel

variable {D : QuotSituation B S hS} (M : QuotSitePresheafModel D)

/-- **A section of a model of the Quot presheaf over a cofiltered limit of affine schemes comes
from a stage**, for `F` of finite presentation and a base with exactly one point over every
scheme of the site. -/
theorem exists_stage_of_isLimit
    (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
    [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
    (hF : D.F.IsFinitePresentationOnSite)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (Dg : I ⥤ BigFppfOver B S hS)
    (c : Cone Dg) (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (haff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (Dg.obj i)))
    (haffc : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (x : M.presheaf.obj (op c.pt)) :
    ∃ (i : I) (y : M.presheaf.obj (op (Dg.obj i))), M.presheaf.map (c.π.app i).op y = x := by
  let E : I ⥤ BigAffineFppf B S hS := ObjectProperty.lift _ Dg haff
  let cE : Cone E :=
    { pt := ⟨c.pt, haffc⟩
      π :=
        { app := fun i => ObjectProperty.homMk (c.π.app i)
          naturality := fun i i' f => by
            apply ObjectProperty.hom_ext
            exact c.π.naturality f } }
  have hcE : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone cE) := hc
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  let g : (schemeSpaceFunctor B S hS).obj ((BigAffineFppf.inclusion B S hS).obj (E.obj i)) ⟶
      D.Y := ι (Dg.obj i)
  generalize hq : M.iso.hom.app (op c.pt) (ULift.up x) = q
  obtain ⟨b, K, hK⟩ := q
  obtain rfl : b = (schemeSpaceFunctor B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (cE.π.app i)) ≫ g := Subsingleton.elim _ _
  obtain ⟨m, K', hK', hpull⟩ := D.exists_stage_quotientPullback_eq E cE hcE hF g K hK
  let zm : QuotFamilyOver D (Dg.obj m.left) :=
    ⟨((D.toCoherentSituation.stageTestSystem E g).obj m).hom, K', hK'⟩
  have hzm : zm.baseChange (c.π.app m.left) = ⟨_, K, hK⟩ := by
    refine (QuotSituation.quotFamily_eq_baseChange_of D (c.π.app m.left) ⟨_, K, hK⟩ zm ?_
      ((D.toCoherentSituation.stageTestCone E cE g).π.app m) rfl hpull.symm).symm
    change (schemeSpaceFunctor B S hS).map (c.π.app i) ≫ g =
      (schemeSpaceFunctor B S hS).map (c.π.app m.left) ≫
        (schemeSpaceFunctor B S hS).map (Dg.map m.hom) ≫ g
    rw [← Functor.map_comp_assoc, c.w]
  refine ⟨m.left, (M.iso.inv.app (op (Dg.obj m.left)) zm).down, ?_⟩
  apply M.iso_hom_app_injective (op c.pt)
  have h₅ : M.iso.hom.app (op (Dg.obj m.left))
      (ULift.up (M.iso.inv.app (op (Dg.obj m.left)) zm).down) = zm :=
    types_congr_hom (M.iso.inv_hom_id_app (op (Dg.obj m.left))) zm
  have e := M.iso_hom_app_map (c.π.app m.left) (M.iso.inv.app (op (Dg.obj m.left)) zm).down
  rw [h₅] at e
  exact e.trans (hzm.trans hq.symm)

/-- **A model of the Quot presheaf is limit preserving** (axiom [1]) for `F` of finite
presentation, over a base with exactly one point over every scheme of the site. -/
theorem limitPreserving
    (ι : ∀ T : BigFppfOver B S hS, (schemeSpaceFunctor B S hS).obj T ⟶ D.Y)
    [∀ T : BigFppfOver B S hS, Subsingleton ((schemeSpaceFunctor B S hS).obj T ⟶ D.Y)]
    (hY : ∀ a : BigFppfOver B S hS, Subsingleton (D.Y.1.obj (op a)))
    (hF : D.F.IsFinitePresentationOnSite) :
    AlgebraicGeometry.LimitPreserving.{u, u, u, u} (BigFppfOver.toScheme B S hS) M.presheaf := by
  have := hF
  exact M.limitPreserving_of_exists_stage hY inferInstance
    fun _ _ _ Dg c hc haff haffc x => M.exists_stage_of_isLimit ι hF Dg c hc haff haffc x

end QuotSitePresheafModel

section OverBase

variable (X : AlgebraicSpaces B S hS) (f : X ⟶ schemeSpace (BigFppfOver.terminalObj B S hS))
  (hf : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
  (hF : F.IsQuasicoherentOnSite)

/-- **Stacks 0CZW, axiom [1].** In the situation of the remark (`F` of finite presentation),
`Quot_{F/X/S}` is limit preserving: for every cofiltered system of affine schemes `Tᵢ` of the site
with limit `T` in schemes, the map `colim Quot(Tᵢ) ⟶ Quot(T)` is bijective. A quotient over the
limit descends to a stage (Stacks 082Q, with the descent of flatness and of proper support), and
two quotients over a stage agreeing over the limit agree at a later stage. -/
@[stacks 0CZW "axiom [1]: Quot_{F/X/S} is limit preserving"]
theorem limitPreserving_quotOverBase (hFfp : F.IsFinitePresentationOnSite) :
    AlgebraicGeometry.LimitPreserving.{u, u, u, u} (BigFppfOver.toScheme B S hS)
      (quotOverBasePresheaf X f hf F hF) :=
  (quotOverBase X f hf F hF).quotSitePresheafModel.limitPreserving
    (fun T => ObjectProperty.homMk (yoneda.map (Over.homMk T.hom (by simp))))
    (fun a => inferInstanceAs (Subsingleton (a ⟶ BigFppfOver.terminalObj B S hS))) hFfp

end OverBase

end AlgebraicGeometry.Space
