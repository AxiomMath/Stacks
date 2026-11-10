module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.StructureMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeAtlasSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingOnObjectsCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointSizeBound
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingProductSupplement
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilitySmallerBase
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.PhToFppfComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoveringsComparison
public import StacksFrontier.CategoryTheory.Sites.Stack.CoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge
import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf

/-!
# The diagonal is representable once the fibres of the diagonal are algebraic spaces

This is the first paragraph of the proof of Stacks 07Y5, with the set-theoretic detail its
footnote omits. Let `𝒳` be a category fibred in groupoids over the big fppf site of `S` which is
limit preserving and a stack in groupoids for the étale topology, and whose fibres over finite
type fields have a bounded set of arrows (axiom [-1]). Suppose that for every affine `V` locally
of finite presentation over `S` and every point `y` of `𝒳 × 𝒳` over `V`, the functor `Y` of
isomorphism classes of `𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` is an algebraic space locally of
finite type over `S`. Then `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces.

The proof is Stacks 07WH. Its three hypotheses are discharged as follows.

* `𝒳 × 𝒳 ⟶ (Sch/S)_{fppf}` is limit preserving on objects because `𝒳` is limit preserving
  (`AlgebraicGeometry.Stack.isLimitPreservingOverTerminal_product`).
* `𝒳` and `𝒳 × 𝒳` are stacks for the Zariski topology, which is coarser than the étale one.
* Over an affine `V` locally of finite presentation, `𝒴` viewed over `(Sch/V)_{fppf}` is
  represented by an algebraic space `F` over `V` (Stacks 04SG applied to `Y`), and `F` has an
  étale atlas of bounded size: `F → V` is locally of finite type (it is a base change of the
  restriction of `Y → S`, Stacks 03XH), the values of `F` on finite type fields over `V` are
  bounded by the arrows of the fibres of `𝒳` (an isomorphism class of `𝒴` over `U` is determined by
  its twist, an arrow of `𝒳_U`), and `size V ≤ size S` (Stacks 04T7); so
  `AlgebraicGeometry.Space.exists_atlas_size_le_of_isLocallyOfFiniteType` gives an atlas of size
  at most `max (2 ^ size S) κ`, `κ` the bound of axiom [-1] for `𝒳`. This is the footnote's
  "`Y → S` will be locally of finite type and `Y` will satisfy axiom [-1]".

## Main results

* `AlgebraicGeometry.Stack.mk_isoClasses_diagonalPointFibre_le`.
* `Stack.hasRepresentableDiagonal_of_isAlgebraicSpace_diagonalPointFunctorOverBase`.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
* [Stacks Project, Tag 07WH](https://stacks.math.columbia.edu/tag/07WH)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

namespace CategoryTheory.TwoFibreProductOver.DiagonalPoint

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]
  {pT : 𝒯 ⥤ 𝒞} {p : 𝒮 ⥤ 𝒞} {y : 𝒯 ⥤ TwoFibreProductOver p p (𝟭 𝒞) p p}

/-- The twist of an object of a fibre of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮 ⟶ 𝒯` over `x`, transported to `x`,
is vertical over `pT x`. -/
lemma isHomLift_fiberTwist {x : 𝒯}
    (P : (fst pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber x) :
    p.IsHomLift (𝟙 (pT.obj x)) (fiberTwist P) := by
  obtain ⟨P, hP⟩ := P
  change P.x = x at hP
  subst hP
  have h := isHomLift_twist P
  rw [P.hx]
  simpa [fiberTwist] using h

end CategoryTheory.TwoFibreProductOver.DiagonalPoint

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {V : BigFppfOver B S hS}
  {y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj}

/-- **The isomorphism classes of a fibre of `𝒴` over `(Sch/V)_{fppf}`** are at most as many as the
arrows of the fibre of `𝒳` over the same object viewed over `S`: a class is determined by its
twist. -/
theorem mk_isoClasses_diagonalPointFibre_le (U : BigFppfOver B V.left.1 V.left.2) :
    #(_root_.Quotient (isIsomorphicSetoid ((diagonalPointFibre B S hS 𝒳 V y).Fiber U))) ≤
      #(Σ a b : 𝒳.val.p.Fiber ((Over.map V.hom).obj U), a ⟶ b) := by
  refine mk_le_of_injective (f := fun q =>
    have := TwoFibreProductOver.DiagonalPoint.isHomLift_fiberTwist q.out
    ⟨_, _, Functor.Fiber.homMk 𝒳.val.p ((Over.map V.hom).obj U)
      (TwoFibreProductOver.DiagonalPoint.fiberTwist q.out)⟩) ?_
  intro q q' h
  have h₁ := (Sigma.mk.inj_iff.1 h).2
  have h₂ := (Sigma.mk.inj_iff.1 (eq_of_heq h₁)).2
  have h₃ := congrArg (fun k => Functor.Fiber.fiberInclusion.map k) (eq_of_heq h₂)
  simp only [Functor.Fiber.fiberInclusion_homMk] at h₃
  rw [← _root_.Quotient.out_eq q, ← _root_.Quotient.out_eq q']
  exact Functor.isoClassMk_eq_of_iso
    (TwoFibreProductOver.DiagonalPoint.nonempty_iso_of_fiberTwist_eq _ _ h₃).some

/-- A morphism of schemes out of a finite scheme is quasi-compact. -/
theorem quasiCompact_of_finite {X Y : Scheme.{u}} [Finite X] (f : X ⟶ Y) : QuasiCompact f :=
  ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩

variable (B S hS) in
/-- The Zariski topology of a chosen big fppf site is coarser than its étale topology. -/
theorem zariskiTopology_le_etaleTopology_of_bigFppfSite :
    B.zariskiTopology ≤ AlgebraicGeometry.etaleTopology B :=
  B.zariskiTopology_le_etaleTopology

/-- **The diagonal of `𝒳` is representable by algebraic spaces once the functors `Y` are
algebraic spaces locally of finite type** (the first paragraph of the proof of Stacks 07Y5, via
Stacks 07WH, with the set-theoretic condition of its footnote). -/
theorem hasRepresentableDiagonal_of_isAlgebraicSpace_diagonalPointFunctorOverBase
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (κ : Cardinal.{u}) (hκ : κ < B.cutoff)
    (hsize : ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
      U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        Cardinal.lift.{u, u + 1} (#(Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) ≤
          Cardinal.lift.{u + 1, u} κ)
    (hY : ∀ (V : BigFppfOver B S hS), IsAffine V.left.1 →
      LocallyOfFinitePresentation (B.inclusion.map V.hom) →
      ∀ (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)
        (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom),
        IsAlgebraicSpace B S hS (diagonalPointFunctorOverBase hy) ∧
          ∃ t : diagonalPointFunctorOverBase hy ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))),
            Space.IsLocallyOfFiniteType B S hS t) :
    HasRepresentableDiagonal B S hS 𝒳 := by
  classical
  let μ := max (2 ^ S.size) κ
  have hμ : μ < B.cutoff := max_lt (B.cutoff_isStrongPrelimit hS) hκ
  -- an object of the site bounding the atlases
  have hTex : ∃ T : BigFppfOver B S hS, ∀ A : BigFppfOver B S hS,
      A.left.1.size ≤ μ → A.left.1.size ≤ T.left.1.size := by
    rcases isEmpty_or_nonempty S with hSe | hSne
    · refine ⟨Over.mk (𝟙 (B.obj hS)), fun A _ => ?_⟩
      refine (size_le_aleph0_of_isEmpty _ ⟨fun a => ?_⟩).trans (Scheme.aleph0_le_size _)
      exact hSe.false ((B.inclusion.map A.hom) a)
    · obtain ⟨T, hT⟩ := BigFppfOver.exists_size_ge B S hS hSne μ
        ((cantor S.size).le.trans (le_max_left _ _)) hμ
      exact ⟨T, fun A hA => hA.trans hT⟩
  obtain ⟨T, hT⟩ := hTex
  -- the Zariski stack conditions
  have hsub : (B.zariskiTopology).Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le
      ((zariskiTopology_le_etaleTopology_of_bigFppfSite B).trans (etaleTopology_le_topology B))
  have hzar : 𝒳.val.p.IsStackInGroupoids.{u + 1} ((B.zariskiTopology).over (B.obj hS)) :=
    hstack.of_le (GrothendieckTopology.over_le_over_of_le
      (zariskiTopology_le_etaleTopology_of_bigFppfSite B) (B.obj hS))
  have hS' : Presheaf.IsSheaf B.zariskiTopology (yoneda.obj (B.obj hS)) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have hid : (𝟭 (BigFppfOver B S hS)).IsStack ((B.zariskiTopology).over (B.obj hS)) :=
    Over.isStack_of_comp_forget (𝟭 (BigFppfOver B S hS)) hS'
      ((Over.isStack_forget_iff_isSheaf (U := B.obj hS) B.zariskiTopology).mpr hS')
  let := 𝒳.isFiberedInGroupoids.isFibered
  have h𝒳 : 𝒳.val.p.IsStack ((B.zariskiTopology).over (B.obj hS)) :=
    Functor.isStack_of_isStackInGroupoids hzar
  have hprod : (CatFiberedInGroupoids.product 𝒳 𝒳).val.p.IsStackInGroupoids.{u + 1}
      ((B.zariskiTopology).over (B.obj hS)) :=
    Functor.IsStack.isStackInGroupoids
      (TwoFibreProductOver.isStack_isFiberedInGroupoids_structureFunctor h𝒳 h𝒳 hid
        𝒳.isFiberedInGroupoids 𝒳.isFiberedInGroupoids Functor.isFiberedInGroupoids_id
        (Functor.comp_id _) (Functor.comp_id _)).1
      (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids
  -- limit preservation of `𝒳 × 𝒳` on objects
  have hlim := (isLimitPreservingOverTerminal_iff B S hS (CatFiberedInGroupoids.product 𝒳 𝒳)).1
    (isLimitPreservingOverTerminal_product B S hS 𝒳 hlimit)
  rw [hasRepresentableDiagonal_iff]
  refine isRepresentableByAlgebraicSpaces_of_limitPreservingOnObjects B S hS T 𝒳
    (CatFiberedInGroupoids.product 𝒳 𝒳) (diagonal.{u, u, u} B S hS 𝒳) hlim ?_ hzar hprod
  intro V hVaff hVlfp
  dsimp only
  intro y hy
  have : LocallyOfFinitePresentation (B.inclusion.map V.hom) := hVlfp
  obtain ⟨hYalg, t, ht⟩ := hY V hVaff hVlfp y hy
  have hqf : (diagonalPointFibre B S hS 𝒳 V y).IsFiberedInGroupoids :=
    (diagonalPointFibre_isFiberedInSetoids hy).isFiberedInGroupoids
  let := hqf.isFibered
  have e := StacksRepresentableCFG.EquivalenceOver.ofEq
    (diagonalPointFibre_comp_overMap B S hS 𝒳 V y).symm
    (diagonalPointFibreOverBaseEquivalenceOver hy)
  obtain ⟨F, τ, ι, π, ρ, hpb, ⟨eF⟩⟩ :=
    PresheafOfCategories.exists_isPullback_nonempty_equivalenceOver_of_comp_overMap V.hom _ hqf e
  have hR := isAlgebraicSpace_relocalizeRestrict B V.left.1 S V.left.2 hS V.hom _ hYalg
  have hH := isAlgebraicSpace_relocalizeRestrict_yoneda B S hS V
  have hFalg : IsAlgebraicSpace B V.left.1 V.left.2 F :=
    isAlgebraicSpace_of_isPullback hR
      (isAlgebraicSpace_yoneda B V.left.1 V.left.2 (Over.mk (𝟙 V.left)))
      hH.isSheaf hH.diagonal_representable hpb
  -- `F` is locally of finite type over `V`
  have hτ : Space.IsLocallyOfFiniteType B V.left.1 V.left.2 τ := by
    apply Space.isLocallyOfFiniteType_of_comp B V.left.1 V.left.2 hR hH
      (isAlgebraicSpace_yoneda B V.left.1 V.left.2 _) τ
      ((Space.baseYoneda_isTerminal B V.left.1 V.left.2).from _)
    convert Space.isLocallyOfFiniteType_toBase_relocalizeRestrict B V.left.1 S V.left.2 hS
      V.hom hYalg t ht using 1
    exact (Space.baseYoneda_isTerminal B V.left.1 V.left.2).hom_ext _ _
  have hπ : Space.IsLocallyOfFiniteType B V.left.1 V.left.2 π :=
    Space.IsLocallyOfFiniteType.of_isPullback B V.left.1 V.left.2 hpb.flip hR hH hτ
  -- axiom [-1] for `F` over `V`
  have hFsize : ∀ (U : BigFppfOver B V.left.1 V.left.2) (k : Type u) [Field k],
      U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B V.left.1 V.left.2 U →
        #(F.obj (op U)) ≤ κ := by
    intro U k _ hU hft
    have hftS : Deformation.Artin.IsFiniteTypeOver B S hS ((Over.map V.hom).obj U) := by
      have : LocallyOfFiniteType (B.inclusion.map U.hom) := hft.1
      have hfin : Finite (B.inclusion.obj ((Over.map V.hom).obj U).left) := by
        change Finite U.left.1
        rw [hU]
        infer_instance
      refine ⟨?_, @quasiCompact_of_finite _ _ hfin _⟩
      change LocallyOfFiniteType (B.inclusion.map (U.hom ≫ V.hom))
      rw [Functor.map_comp]
      infer_instance
    have h₁ := mk_isoClasses_diagonalPointFibre_le (y := y) U
    have h₂ := hsize ((Over.map V.hom).obj U) k hU hftS
    have h₃ : Cardinal.lift.{u + 1} #(F.obj (op U)) =
        Cardinal.lift.{u} #(_root_.Quotient (isIsomorphicSetoid
          ((diagonalPointFibre B S hS 𝒳 V y).Fiber U))) :=
      (Cardinal.lift_mk_eq'.2 ⟨PresheafOfCategories.elementsIsoClassEquiv F eF U⟩).symm
    refine Cardinal.lift_le.{u + 1}.1 ?_
    rw [h₃]
    exact (Cardinal.lift_le.2 h₁).trans h₂
  -- the atlas
  obtain ⟨A, a, hsa, hea, hA⟩ := Space.exists_atlas_size_le_of_isLocallyOfFiniteType hFalg π hπ
    κ hκ hFsize
  have hVS : V.left.1.size ≤ S.size := by
    have : IsAffine (B.inclusion.obj V.left) := hVaff
    exact Scheme.size_le_of_locallyOfFiniteType (B.inclusion.map V.hom)
  have hAμ : ((Over.map V.hom).obj A).left.1.size ≤ μ :=
    hA.trans (max_le_max (power_le_power_left two_ne_zero hVS) le_rfl)
  exact ⟨F, hFalg, ⟨eF⟩, A, a, hT ((Over.map V.hom).obj A) hAμ, hsa, hea⟩

end AlgebraicGeometry.Stack

end
