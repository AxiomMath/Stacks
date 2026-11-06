module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull.BoundaryZero
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull.Keystone

/-!
# The six-term sequence of a 2-fibre product: the assembled statement

Third of three parts of `StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull`.
It contains the boundary map
`Deformation.infBoundaryLinearMap` on the `Inf`-row model of `Inf(ℱ)`, exactness at `Inf(ℱ)`
(`Deformation.exact_infLegDiff_infBoundaryLinearMap`), and part (2) of Tag 06L5 in one statement,
`Deformation.twoFibreProduct_sixTermExact`.

## References

* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

/-! ### The six-term sequence -/


section SixTerm
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]

variable (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)

/-- **The boundary map `δ : Inf(ℱ) → T𝒲` of the six-term sequence, read on the `Inf`-row's own
model of `Inf(ℱ)`.** `Deformation.boundaryLinearMap` has for its source the value at the
rank-one coordinate module of the canonical linear lift of the infinitesimal automorphisms,
while the three `Inf`-terms of the row are tangent spaces of automorphism functors; the two are
identified by `Deformation.tangentCarrierLinearEquiv`, and this is `δ` transported along that
identification, so that the composite `Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → T𝒲` is a composite of maps
of the same model. -/
public noncomputable def infBoundaryLinearMap
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x)
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x)) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    localizedAutomorphismFunctorTangent.{u, v, w, u₃, v₃} PF →ₗ[k]
      ↥((productTangentLift.{u, v, w} pF f g hH hG hF).obj (FGModuleCat.of k (ULift.{v} k))) :=
  letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  (boundaryLinearMap.{u, v, w} pF f g hH hG hF (w₀.hy.trans w₀.hx.symm)
      (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QH QG PF
      (FGModuleCat.of k (ULift.{v} k))).comp
    (tangentCarrierLinearEquiv PF hF.satisfiesRS).symm.toLinearMap

attribute [local implicit_reducible] squareZeroCrossUnder

/-- **Stacks Project, Tag 06L5, part (2): exactness at `Inf(ℱ)`.** In the six-term sequence of
the `2`-fibre product `𝒲 = ℋ ×_ℱ 𝒢`, the kernel of the boundary map `δ : Inf(ℱ) → T𝒲` is the
image of the difference `b : Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ)` of the two outer legs.

This is the source's "if `α` gives the trivial deformation `(k[ε], y'₀, z'₀, c' ∘ α ∘ b')` of
`w₀`, then the isomorphism `w'₀ → δ(α)` produces a pair `(β, γ)` which is a preimage of `α`",
together with its converse. The class of the quadruple `δ(α)` vanishes exactly when `α`
satisfies the boundary square for some pair of automorphisms of `y'₀` and `z'₀`
(`Deformation.tangentClassAt_boundaryObject_eq_zero_iff`), and the boundary square says exactly
that `α` is the value of `b` on the pair those automorphisms define
(`Deformation.eq_comp_inv_iff_boundary_square`): the two maps `b` is the difference of are
conjugation by the comparisons of Tag 07W6 and Tag 06JV (2) at the dual numbers, and the three
transports `Deformation.transportAut_comp_boundaryCompareFst`,
`Deformation.map_cross_comp_boundaryCompareSnd` and
`Deformation.transportAut_comp_boundaryCompareSnd` carry those conjugations to the re-based
square-zero extension at which `δ` is built.

Every automorphism of a chosen pushforward to the dual numbers is infinitesimal, the special
fibre of a predeformation category being thin
(`Deformation.ker_transportAutHom_eq_top_of_isThin`), so the pair of automorphisms the square
produces does come from `Inf(ℋ) ⊕ Inf(𝒢)`. The sign the source defers is absorbed by reading
the difference as `-c(g(γ)) + f(β)`; the two orders agree because the tangent space is an
abelian group. -/
@[stacks 06L5 "part (2), exactness at `Inf(ℱ)` of the six-term exact sequence, for the map \
`Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ)` and the boundary map `Inf(ℱ) → T𝒲`"]
public theorem exact_infLegDiff_infBoundaryLinearMap
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (PW : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x)
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x))
    (PF' : ChosenPushforwardsAt pF (g.obj w₀.y))
    (hw₀ : (f ⋙ pF).obj w₀.x = residueFieldObject.{u, v, w} Λ k) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    Function.Exact (infLegDiff.{u, v, w} pF f g hH hG hF QH QG PF PF' hw₀)
      (infBoundaryLinearMap.{u, v, w} pF f g hH hG hF QH QG PF) := by
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF' hF.satisfiesRS
  let := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF' hF.satisfiesRS
  obtain ⟨H₃, hl₃, hi₃, hc₃⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso.{u, v, w}
    (firstLegBased.{u, v, w} pF f).toFunctor (firstLegBased.{u, v, w} pF f).w
    hH.satisfiesRS hF.satisfiesRS QH PF
  obtain ⟨H₄, hl₄, hi₄, hc₄⟩ := inducedInfinitesimalLinearMapOfEq_spec_iso.{u, v, w}
    (secondLegBased.{u, v, w} pF g).toFunctor (secondLegBased.{u, v, w} pF g).w
    hG.satisfiesRS hF.satisfiesRS QG PF'
  obtain ⟨-, Hε, -, hiε, hcarr, hcε⟩ :=
    canonicalLocalizedTangentAutomorphismLinearEquiv_spec.{u, v, w} hF.satisfiesRS
      w₀.iso.inv hw₀ PF' PF
  have hlεhom : pF.IsHomLift
      (𝟙 (dualNumbersUnder.{u, v, w, u₁, v₁} (p := f ⋙ pF) (x := w₀.x)).right) Hε.hom :=
    isHomLift_id_of_map_apply_heq.{u, v, w} Hε.hom
      (PF'.obj (dualNumbersUnder.{u, v, w, u₂, v₂} (p := g ⋙ pF) (x := w₀.y))).2
      (PF.obj (dualNumbersUnder.{u, v, w, u₁, v₁} (p := f ⋙ pF) (x := w₀.x))).2
      (dualNumbersUnder_right_eq.{u, v, w} (w₀.hy.trans w₀.hx.symm))
      (fun t => heq_of_eq (hcarr t))
  obtain ⟨hadd, -⟩ := naturalLocalizedTangentModule_spec PF hF.satisfiesRS
  -- `δ` on the `Inf`-row's model, read as the class of the quadruple it produces
  have hval : ∀ s, infBoundaryLinearMap.{u, v, w} pF f g hH hG hF QH QG PF s =
      tangentClassAt.{u, v, w} (productBased.{u, v, w} pF f g)
        (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF)
        (FGModuleCat.of k (ULift.{v} k))
        ⟨boundaryObject.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QH QG PF
          hF.predeformation.cofibered (FGModuleCat.of k (ULift.{v} k))
          (PF.transportAut
            (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
              (FGModuleCat.of k (ULift.{v} k))).hom
            (localizedTangentEquivKernel PF s).1), rfl⟩ := by
    intro s
    have h1 : infBoundaryLinearMap.{u, v, w} pF f g hH hG hF QH QG PF s =
        boundaryFun.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QH QG PF
          hF.predeformation.cofibered
          (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).predeformation
          (tangentConditionS2.{u, v, w}
            (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF))
          (FGModuleCat.of k (ULift.{v} k))
          (PF.transportAut
            (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
              (FGModuleCat.of k (ULift.{v} k))).hom
            (localizedTangentEquivKernel PF s).1) := by
      rw [← cast_tangentCarrierLinearEquiv_symm PF hF.satisfiesRS s]
      rfl
    rw [h1]
    exact boundaryFun_eq_tangentClassAt.{u, v, w} pF f g hH hG hF (w₀.hy.trans w₀.hx.symm)
      (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QH QG PF _ _
  -- the dictionary between a pair of infinitesimal automorphisms and the boundary square
  have key : ∀ (x : localizedAutomorphismFunctorTangent.{u, v, w, u₁, v₁} QH)
      (y : localizedAutomorphismFunctorTangent.{u, v, w, u₂, v₂} QG)
      (s : localizedAutomorphismFunctorTangent.{u, v, w, u₃, v₃} PF),
      (s = infLegDiff.{u, v, w} pF f g hH hG hF QH QG PF PF' hw₀ (x, y)) ↔
      (f.map (QH.transportAut
              (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
                (FGModuleCat.of k (ULift.{v} k))).hom
              (localizedTangentEquivKernel QH x).1).asIso.hom.val ≫
            (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered
              (FGModuleCat.of k (ULift.{v} k))).inv ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                hF.predeformation.cofibered (FGModuleCat.of k (ULift.{v} k))).hom =
          (boundaryCompareFst.{u, v, w} f QH PF hF.predeformation.cofibered
              (FGModuleCat.of k (ULift.{v} k))).inv ≫
            (PF.transportAut
                (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
                  (FGModuleCat.of k (ULift.{v} k))).hom
                (localizedTangentEquivKernel PF s).1).asIso.hom.val ≫
              (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
                  (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF
                  hF.predeformation.cofibered (FGModuleCat.of k (ULift.{v} k))).hom ≫
                g.map (QG.transportAut
                  (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y)
                    (FGModuleCat.of k (ULift.{v} k))).hom
                  (localizedTangentEquivKernel QG y).1).asIso.hom.val) := by
    intro x y s
    set e := (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
      (FGModuleCat.of k (ULift.{v} k))).hom
    have hA1 := transportAut_comp_boundaryCompareFst.{u, v, w} f QH PF
      hF.predeformation.cofibered (FGModuleCat.of k (ULift.{v} k)) H₃ hi₃ hl₃
      (localizedTangentEquivKernel PF
        (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₁, v₁, u₃, v₃}
          (firstLegBased.{u, v, w} pF f).toFunctor (firstLegBased.{u, v, w} pF f).w
          hH.satisfiesRS hF.satisfiesRS QH PF x)).1
      (localizedTangentEquivKernel QH x).1 (hc₃ x)
    have hcg : (localizedTangentEquivKernel PF
            ((canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w, u₃, v₃} hF.satisfiesRS
              w₀.iso.inv hw₀ PF' PF)
              (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₂, v₂, u₃, v₃}
                (secondLegBased.{u, v, w} pF g).toFunctor (secondLegBased.{u, v, w} pF g).w
                hG.satisfiesRS hF.satisfiesRS QG PF' y))).1.asIso.hom.val ≫ Hε.inv ≫ H₄.hom =
        (Hε.inv ≫ H₄.hom) ≫ g.map (localizedTangentEquivKernel QG y).1.asIso.hom.val := by
      have h2 := inv_comp_eq_of_hom_conj Hε (hcε
        (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₂, v₂, u₃, v₃}
          (secondLegBased.{u, v, w} pF g).toFunctor (secondLegBased.{u, v, w} pF g).w
          hG.satisfiesRS hF.satisfiesRS QG PF' y))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ H₄.hom) h2.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => Hε.inv ≫ z) (hc₄ y)).trans (Category.assoc _ _ _).symm)))
    have hA2 := transportAut_comp_boundaryCompareSnd.{u, v, w} f g QG PF PF'
      hF.predeformation.cofibered (FGModuleCat.of k (ULift.{v} k)) Hε hiε hlεhom H₄ hi₄ hl₄
      (localizedTangentEquivKernel PF
        ((canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w, u₃, v₃} hF.satisfiesRS
          w₀.iso.inv hw₀ PF' PF)
          (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₂, v₂, u₃, v₃}
            (secondLegBased.{u, v, w} pF g).toFunctor (secondLegBased.{u, v, w} pF g).w
            hG.satisfiesRS hF.satisfiesRS QG PF' y))).1
      (localizedTangentEquivKernel QG y).1 hcg
    have hcomm : ∀ a b : localizedAutomorphismFunctorTangent.{u, v, w, u₃, v₃} PF,
        localizedTangentEquivKernel PF a * localizedTangentEquivKernel PF b =
          localizedTangentEquivKernel PF b * localizedTangentEquivKernel PF a := by
      intro a b
      rw [← hadd, ← hadd, add_comm]
    have hTr : ∀ a b : localizedAutomorphismFunctorTangent.{u, v, w, u₃, v₃} PF,
        (PF.transportAut e (localizedTangentEquivKernel PF (a + -b)).1).asIso.hom.val =
          (PF.transportAut e (localizedTangentEquivKernel PF a).1).asIso.hom.val ≫
            (PF.transportAut e (localizedTangentEquivKernel PF b).1).asIso.inv.val := by
      intro a b
      have h : (localizedTangentEquivKernel PF (a + -b)).1 =
          (localizedTangentEquivKernel PF b).1⁻¹ * (localizedTangentEquivKernel PF a).1 := by
        rw [hadd, hcomm a (-b), localizedTangentEquivKernel_neg PF hF.satisfiesRS]
        rfl
      rw [h]
      exact congrArg (fun z => z.asIso.hom.val)
        (((PF.transportAutHom e).map_mul _ _).trans
          (congrArg (· * _) ((PF.transportAutHom e).map_inv _)))
    refine Iff.trans ?_ (eq_comp_inv_iff_boundary_square _ _
      (Functor.Fiber.fiberInclusion.mapIso
        (PF.transportAut e (localizedTangentEquivKernel PF
          (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₁, v₁, u₃, v₃}
            (firstLegBased.{u, v, w} pF f).toFunctor (firstLegBased.{u, v, w} pF f).w
            hH.satisfiesRS hF.satisfiesRS QH PF x)).1).asIso)
      (Functor.Fiber.fiberInclusion.mapIso
        (PF.transportAut e (localizedTangentEquivKernel PF
          ((canonicalLocalizedTangentAutomorphismLinearEquiv.{u, v, w, u₃, v₃} hF.satisfiesRS
            w₀.iso.inv hw₀ PF' PF)
            (inducedInfinitesimalLinearMapOfEq.{u, v, w, u₂, v₂, u₃, v₃}
              (secondLegBased.{u, v, w} pF g).toFunctor (secondLegBased.{u, v, w} pF g).w
              hG.satisfiesRS hF.satisfiesRS QG PF' y))).1).asIso) hA1 hA2)
    have hinj : Function.Injective (PF.transportAut e) := by
      intro a b hab
      rw [← PF.transportAut_inv_transportAut_hom _ a, hab, PF.transportAut_inv_transportAut_hom]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h]
      exact hTr _ _
    · exact (localizedTangentEquivKernel PF).injective
        (Subtype.ext (hinj (Aut.ext (Iso.ext (Functor.Fiber.hom_ext (h.trans (hTr _ _).symm))))))
  intro t
  rw [hval t, tangentClassAt_boundaryObject_eq_zero_iff.{u, v, w} pF f g hH hG hF PW QH QG PF
    (FGModuleCat.of k (ULift.{v} k))
    (PF.transportAut
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
        (FGModuleCat.of k (ULift.{v} k))).hom
      (localizedTangentEquivKernel PF t).1)]
  constructor
  · rintro ⟨β, γ, hsq⟩
    have hkerH : MonoidHom.ker (QH.transportAutHom
        (tangentReduction (p := f ⋙ pF) (x := w₀.x))) = ⊤ :=
      ker_transportAutHom_eq_top_of_isThin.{u, v, w} hH.predeformation.cofibered QH
        (isThin_specialFiber.{u, v, w} hH.predeformation)
        (tangentReduction (p := f ⋙ pF) (x := w₀.x))
    have hkerG : MonoidHom.ker (QG.transportAutHom
        (tangentReduction (p := g ⋙ pF) (x := w₀.y))) = ⊤ :=
      ker_transportAutHom_eq_top_of_isThin.{u, v, w} hG.predeformation.cofibered QG
        (isThin_specialFiber.{u, v, w} hG.predeformation)
        (tangentReduction (p := g ⋙ pF) (x := w₀.y))
    refine ⟨((localizedTangentEquivKernel QH).symm
        ⟨QH.transportAut
          (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
            (FGModuleCat.of k (ULift.{v} k))).inv β, by
          simp [hkerH]⟩,
      (localizedTangentEquivKernel QG).symm
        ⟨QG.transportAut
          (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y)
            (FGModuleCat.of k (ULift.{v} k))).inv γ, by
          simp [hkerG]⟩), ?_⟩
    refine ((key _ _ t).mpr ?_).symm
    have hβ : QH.transportAut
          (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
            (FGModuleCat.of k (ULift.{v} k))).hom
          (localizedTangentEquivKernel QH ((localizedTangentEquivKernel QH).symm
            ⟨QH.transportAut
              (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
                (FGModuleCat.of k (ULift.{v} k))).inv β, by
              simp [hkerH]⟩)).1 = β := by
      rw [Equiv.apply_symm_apply]
      exact QH.transportAut_hom_transportAut_inv
        (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj w₀.x)
          (FGModuleCat.of k (ULift.{v} k))) β
    have hγ : QG.transportAut
          (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y)
            (FGModuleCat.of k (ULift.{v} k))).hom
          (localizedTangentEquivKernel QG ((localizedTangentEquivKernel QG).symm
            ⟨QG.transportAut
              (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y)
                (FGModuleCat.of k (ULift.{v} k))).inv γ, by
              simp [hkerG]⟩)).1 = γ := by
      rw [Equiv.apply_symm_apply]
      exact QG.transportAut_hom_transportAut_inv
        (squareZeroCrossUnderIso.{u, v, w} ((g ⋙ pF).obj w₀.y)
          (FGModuleCat.of k (ULift.{v} k))) γ
    rw [hβ, hγ]
    exact hsq
  · rintro ⟨⟨x, y⟩, hxy⟩
    exact ⟨_, _, (key x y t).mp hxy.symm⟩

/-- **Stacks Project, Tag 06L5, part (2): the six-term sequence**

`0 → Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢 → Tℱ`

of the `2`-fibre product `𝒲 = ℋ ×_ℱ 𝒢` of deformation categories, with all five of its
`k`-linear maps and the exactness at every one of its five spots in one statement.

The five conjuncts are, in order: injectivity of `a` at `Inf(𝒲)` (the source's `0 →`,
`Deformation.injective_infProjPair`), exactness at `Inf(ℋ) ⊕ Inf(𝒢)`
(`Deformation.exact_infProjPair_infLegDiff`), exactness at `Inf(ℱ)`
(`Deformation.exact_infLegDiff_infBoundaryLinearMap`), exactness at `T𝒲`
(`Deformation.exact_boundaryLinearMap_tangentProjPair`, read through the model bridge of
`Deformation.infBoundaryLinearMap`) and exactness at `Tℋ ⊕ T𝒢`
(`Deformation.exact_tangentProjPair_tangentLegDiff`).

The basepoints are the images of one object `w₀` of `𝒲`, as in the source's "let `x₀, y₀, z₀`
be the image of `w₀`", and the tangent terms are taken at the rank-one coordinate module, at
which they are the tangent spaces of Tag 06IH. -/
@[stacks 06L5 "part (2), the six-term exact sequence `0 → Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → \
T𝒲 → Tℋ ⊕ T𝒢 → Tℱ` of a 2-fibre product of deformation categories, with its five `k`-linear \
maps and the exactness at all five of its spots: at `Inf(𝒲)`, at `Inf(ℋ) ⊕ Inf(𝒢)`, at \
`Inf(ℱ)`, at `T𝒲` and at `Tℋ ⊕ T𝒢`"]
public theorem twoFibreProduct_sixTermExact
    (hH : IsDeformationCategory.{u, v, w} (f ⋙ pF))
    (hG : IsDeformationCategory.{u, v, w} (g ⋙ pF))
    (hF : IsDeformationCategory.{u, v, w} pF)
    {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
    (PW : ChosenPushforwardsAt
      (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
    (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x)
    (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
    (PF : ChosenPushforwardsAt pF (f.obj w₀.x))
    (PF' : ChosenPushforwardsAt pF (g.obj w₀.y))
    (hw₀ : (f ⋙ pF).obj w₀.x = residueFieldObject.{u, v, w} Λ k) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w} PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w} PW
      (isDeformationCategory_productBased.{u, v, w} pF f g hH hG hF).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} QH hH.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₂, v₂} QG hG.satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    letI := naturalLocalizedTangentModule.{u, v, w, u₃, v₃} PF hF.satisfiesRS
    Function.Injective (infProjPair.{u, v, w} pF f g hH hG hF PW QH QG) ∧
      Function.Exact (infProjPair.{u, v, w} pF f g hH hG hF PW QH QG)
          (infLegDiff.{u, v, w} pF f g hH hG hF QH QG PF PF' hw₀) ∧
        Function.Exact (infLegDiff.{u, v, w} pF f g hH hG hF QH QG PF PF' hw₀)
            (infBoundaryLinearMap.{u, v, w} pF f g hH hG hF QH QG PF) ∧
          Function.Exact (infBoundaryLinearMap.{u, v, w} pF f g hH hG hF QH QG PF)
              (tangentProjPair.{u, v, w} pF f g hH hG hF (FGModuleCat.of k (ULift.{v} k))) ∧
            Function.Exact
              (tangentProjPair.{u, v, w} pF f g hH hG hF (FGModuleCat.of k (ULift.{v} k)))
              (tangentLegDiff.{u, v, w} pF f g hH hG hF (FGModuleCat.of k (ULift.{v} k))) := by
  refine ⟨injective_infProjPair.{u, v, w} pF f g hH hG hF PW QH QG,
    exact_infProjPair_infLegDiff.{u, v, w} pF f g hH hG hF PW QH QG PF PF' hw₀,
    exact_infLegDiff_infBoundaryLinearMap.{u, v, w} pF f g hH hG hF PW QH QG PF PF' hw₀, ?_,
    exact_tangentProjPair_tangentLegDiff.{u, v, w} pF f g hH hG hF (FGModuleCat.of k (ULift.{v} k))⟩
  exact exact_comp_of_surjective
    (exact_boundaryLinearMap_tangentProjPair.{u, v, w} pF f g hH hG hF
      (w₀.hy.trans w₀.hx.symm) (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀)
      QH QG PF (FGModuleCat.of k (ULift.{v} k)))
    (surjective_tangentCarrierLinearEquiv_symm.{u, v, w, u₃, v₃} PF hF.satisfiesRS)

end SixTerm

end Deformation

end
