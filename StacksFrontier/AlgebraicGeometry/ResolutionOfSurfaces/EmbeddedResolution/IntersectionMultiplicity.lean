module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.RingTheory.Length.Comparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Intersection multiplicity of two curves at a point

Let `Y` and `Z` be closed subschemes of a locally Noetherian scheme `X`. If `Y` is an integral
curve, its generic point does not lie on `Z`, and `p` is a closed point of their intersection,
then the intersection multiplicity at `p` is the length of the local ring of the
scheme-theoretic intersection as a module over `𝒪_{X,p}`.

## Main definitions

* `AlgebraicGeometry.IntersectionMultiplicityContext` packages the standing hypotheses on `X`,
  `Y`, `Z` and `p`.
* `AlgebraicGeometry.IntersectionMultiplicityContext.intersectionMultiplicity` is the
  intersection multiplicity at `p`.

## Main results

* `AlgebraicGeometry.IntersectionMultiplicityContext.intersectionMultiplicity_natCast_eq_length`
  identifies the intersection multiplicity with the relevant module length.

## Implementation notes

Closed subschemes are represented by `Scheme.IdealSheafData`, so `Y ⊔ Z` cuts out their
scheme-theoretic intersection. Mathlib's `Module.length` is extended-natural-valued; the
intersection multiplicity is natural-valued, and the main result says that its coercion back
to `ℕ∞` is exactly that length. The hypotheses in the context ensure this length is finite.

## References

* [Stacks Project, Tag 0BI6](https://stacks.math.columbia.edu/tag/0BI6)
-/

@[expose] public section

noncomputable section

open TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The standing situation for the intersection multiplicity of two closed subschemes at a
closed point, when the first subscheme is an integral curve not contained in the second. -/
structure IntersectionMultiplicityContext where
  /-- The ambient locally Noetherian scheme. -/
  X : Scheme.{u}
  /-- The ambient scheme is locally Noetherian. -/
  locallyNoetherian : IsLocallyNoetherian X
  /-- The ideal sheaf defining the integral curve `Y`. -/
  y : X.IdealSheafData
  /-- The ideal sheaf defining the closed subscheme `Z`. -/
  z : X.IdealSheafData
  /-- The closed subscheme `Y` is integral. -/
  integralY : IsIntegral y.subscheme
  /-- The integral closed subscheme `Y` has dimension one. -/
  dimensionY : topologicalKrullDim y.subscheme = 1
  /-- The point at which the intersection multiplicity is taken. -/
  p : X
  /-- The point lies in the scheme-theoretic intersection of `Y` and `Z`. -/
  p_mem_intersection : p ∈ (y ⊔ z).support
  /-- The point is closed in `X`. -/
  p_isClosed : IsClosed ({p} : Set X)
  /-- The generic point of `Y` does not lie on `Z`. -/
  genericPoint_not_mem : ∀ η : y.subscheme,
    η ∈ genericPoints y.subscheme → y.subschemeι η ∉ z.support

namespace IntersectionMultiplicityContext

/-- On the integral curve `Y`, a point lying on `Z` is closed: it cannot be the generic
point. -/
private lemma closed_singleton_of_not_in_generic_intersection
    (S : IntersectionMultiplicityContext) (q : S.y.subscheme)
    (hqz : S.y.subschemeι q ∈ S.z.support) : IsClosed ({q} : Set S.y.subscheme) := by
  have := S.integralY
  let C : IrreducibleCloseds S.y.subscheme :=
    ⟨closure ({q} : Set S.y.subscheme), isIrreducible_singleton.closure, isClosed_closure⟩
  let Ctop : IrreducibleCloseds S.y.subscheme :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hdim : Order.krullDim (IrreducibleCloseds S.y.subscheme) ≤ 1 := S.dimensionY.le
  have hCne : C ≠ Ctop := by
    intro htop
    have hgen : IsGenericPoint q (Set.univ : Set S.y.subscheme) := by
      apply isGenericPoint_def.mpr
      simpa [C, Ctop] using congrArg
        (fun D : IrreducibleCloseds S.y.subscheme => (D : Set S.y.subscheme)) htop
    obtain rfl : q = genericPoint S.y.subscheme := hgen.eq (genericPoint_spec S.y.subscheme)
    exact S.genericPoint_not_mem _ (by simp [genericPoints_eq_singleton]) hqz
  have hCtop : C ≤ Ctop := fun _ _ => trivial
  have hCmin : IsMin C := (Order.krullDim_le_one_iff.mp hdim C).resolve_right fun hmax =>
    hCne (le_antisymm hCtop (hmax hCtop))
  have hCeq : (C : Set S.y.subscheme) = {q} := by
    apply Set.Subset.antisymm
    · intro r hr
      let D : IrreducibleCloseds S.y.subscheme :=
        ⟨closure ({r} : Set S.y.subscheme), isIrreducible_singleton.closure, isClosed_closure⟩
      have hr' : r ∈ closure ({q} : Set S.y.subscheme) := hr
      have hDC : D ≤ C := by
        change closure ({r} : Set S.y.subscheme) ⊆ closure ({q} : Set S.y.subscheme)
        exact closure_minimal (Set.singleton_subset_iff.mpr hr') isClosed_closure
      have hqr : q ∈ closure ({r} : Set S.y.subscheme) := by
        have hqC : q ∈ (C : Set S.y.subscheme) := subset_closure rfl
        rwa [le_antisymm (hCmin hDC) hDC] at hqC
      exact Set.mem_singleton_iff.mpr
        ((specializes_iff_mem_closure.mpr hr').antisymm
          (specializes_iff_mem_closure.mpr hqr)).eq.symm
    · exact subset_closure
  exact hCeq ▸ C.isClosed

/-- The point of the scheme-theoretic intersection lying over `p`. -/
noncomputable def intersectionPoint (S : IntersectionMultiplicityContext) :
    (S.y ⊔ S.z).subscheme :=
  ⟨S.p, S.p_mem_intersection⟩

/-- The local ring `𝒪_{Y ∩ Z,p}` of the scheme-theoretic intersection. -/
noncomputable abbrev intersectionLocalRing (S : IntersectionMultiplicityContext) :=
  (S.y ⊔ S.z).subscheme.presheaf.stalk S.intersectionPoint

/-- The local ring `𝒪_{Y ∩ Z,p}` is an algebra over `𝒪_{X,p}` via the stalk map of the closed
immersion of the intersection. -/
noncomputable instance (S : IntersectionMultiplicityContext) :
    Algebra (S.X.presheaf.stalk S.p) S.intersectionLocalRing :=
  ((S.y ⊔ S.z).subschemeι.stalkMap S.intersectionPoint).hom.toAlgebra

/-- A point of the scheme-theoretic intersection lies on both `Y` and `Z`. -/
private lemma mem_support_of_mem_support_sup (S : IntersectionMultiplicityContext) {x : S.X}
    (h : x ∈ (S.y ⊔ S.z).support) : x ∈ S.y.support ∧ x ∈ S.z.support := by
  have h' : x ∈ S.y.support ⊓ S.z.support := by
    simpa [Scheme.IdealSheafData.support_sup] using h
  exact h'

/-- The point `p` is a closed point of the scheme-theoretic intersection. -/
private lemma isMax_intersectionPoint (S : IntersectionMultiplicityContext) :
    IsMax S.intersectionPoint := by
  let i := (S.y ⊔ S.z).subschemeι
  let q := S.intersectionPoint
  intro r hr
  have hrYZ := S.mem_support_of_mem_support_sup r.2
  have hbase : r.1 ⤳ S.p := by
    have h := i.isClosedEmbedding.isInducing.specializes_iff.mpr
      (Scheme.le_iff_specializes.mp hr)
    change r.1 ⤳ S.p at h
    exact h
  let rY : S.y.subscheme := ⟨r.1, hrYZ.1⟩
  let qY : S.y.subscheme := ⟨S.p, (S.mem_support_of_mem_support_sup S.p_mem_intersection).1⟩
  have hYspec : rY ⤳ qY := S.y.subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp hbase
  have hrYz : S.y.subschemeι rY ∈ S.z.support := by
    rw [Scheme.IdealSheafData.subschemeι_apply]
    exact hrYZ.2
  have hEq : qY = rY := Set.mem_singleton_iff.mp <| hYspec.mem_closed
    (closed_singleton_of_not_in_generic_intersection S rY hrYz) (Set.mem_singleton rY)
  have hspec : q ⤳ r := by
    apply i.isClosedEmbedding.isInducing.specializes_iff.mp
    change S.p ⤳ r.1
    exact specializes_of_eq (congrArg Subtype.val hEq)
  exact Scheme.le_iff_specializes.mpr hspec

/-- The local ring of the scheme-theoretic intersection has finite length over the local ring
of the ambient scheme at `p`. -/
private lemma isFiniteLength_intersectionLocalRing (S : IntersectionMultiplicityContext) :
    IsFiniteLength (S.X.presheaf.stalk S.p) S.intersectionLocalRing := by
  let T := (S.y ⊔ S.z).subscheme
  let i := (S.y ⊔ S.z).subschemeι
  let q : T := S.intersectionPoint
  have : IsLocallyNoetherian S.X := S.locallyNoetherian
  let : Module (S.X.presheaf.stalk S.p) (T.presheaf.stalk q) :=
    Module.compHom (T.presheaf.stalk q) (i.stalkMap q).hom
  have hsurj : Function.Surjective (i.stalkMap q).hom := i.stalkMap_surjective q
  have : IsNoetherianRing (T.presheaf.stalk q) :=
    isNoetherianRing_of_surjective (S.X.presheaf.stalk S.p) (T.presheaf.stalk q)
      (i.stalkMap q).hom hsurj
  have hdim : Ring.KrullDimLE 0 (T.presheaf.stalk q) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le
      (Order.coheight_eq_zero.mpr S.isMax_intersectionPoint).le
  have : IsArtinianRing (T.presheaf.stalk q) := isArtinianRing_iff_krullDimLE_zero.mpr hdim
  apply Module.length_ne_top_iff.mp
  change Module.length (S.X.presheaf.stalk S.p) (T.presheaf.stalk q) ≠ ⊤
  rw [length_restrictScalars_eq_of_surjective (S.X.presheaf.stalk S.p)
    (T.presheaf.stalk q) (i.stalkMap q).hom hsurj (T.presheaf.stalk q)]
  exact Module.length_ne_top_iff.mpr ((isArtinianRing_iff_isFiniteLength _).mp inferInstance)

/-- The intersection multiplicity of `Y` and `Z` at `p`. -/
noncomputable def intersectionMultiplicity (S : IntersectionMultiplicityContext) : ℕ :=
  (Module.length (S.X.presheaf.stalk S.p) S.intersectionLocalRing).toNat

/-- **Stacks Project, Tag 0BI6.** The intersection multiplicity at `p` is the length of the
local ring of the scheme-theoretic intersection as an `𝒪_{X,p}`-module. -/
@[stacks 0BI6]
theorem intersectionMultiplicity_natCast_eq_length
    (S : IntersectionMultiplicityContext) :
    (S.intersectionMultiplicity : ℕ∞) =
      Module.length (S.X.presheaf.stalk S.p) S.intersectionLocalRing :=
  ENat.natCast_toNat (Module.length_ne_top_iff.mpr (isFiniteLength_intersectionLocalRing S))

end IntersectionMultiplicityContext

end AlgebraicGeometry

end
