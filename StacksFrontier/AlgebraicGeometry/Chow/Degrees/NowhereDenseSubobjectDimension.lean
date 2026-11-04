module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.SchemeTheoreticSupportDimension
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.NowhereDense

/-!
# The delta-dimension of a nowhere dense coherent subsheaf

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, let
`ℱ` be a coherent `𝒪_X`-module whose support has delta-dimension at most `k + 1`, and let
`𝒦 ⊆ ℱ` be a coherent subsheaf whose support is nowhere dense in the support of `ℱ` — the
subsheaf [Stacks, Tag 02OL] produces. Then the support of `𝒦` has delta-dimension at most `k`:
the drop is strict.

The reason is the one Tag 02P2 gives for its exceptional subset. A point `x` of `Supp(𝒦)` lies on
an irreducible component of `Supp(ℱ)`, whose generic point avoids the nowhere dense `Supp(𝒦)`
and is therefore a *proper* generization of `x`; the dimension function of [Stacks, Tag 02JW]
drops strictly along a proper specialization, and the generic point has relative dimension at
most `k + 1`.

## The transport, which is the work

`Stacks.AlgebraicGeometry.CoherentSubquotients.IsNowhereDenseCoherentSubobject` states the
nowhere density in the subspace topology on `Supp(ℱ)`, while the lemma that a generic point of an
irreducible component avoids a closed nowhere dense subset,
`Stacks.AlgebraicGeometry.CoherentSubquotients.genericPoint_notMem_of_nowhereDense`, is stated
for a locally Noetherian *scheme*. The scheme to run it on is `Stacks.Chow.reducedSupport ℱ`,
whose space is homeomorphic to `Supp(ℱ)` — its structural morphism is a closed embedding with
that range — so the nowhere density is carried across by
`Stacks.Chow.reducedSupportHomeomorph` and `Topology.IsInducing.isNowhereDense_image`.

## Main definitions

* `Stacks.Chow.reducedSupportHomeomorph` — the space of the reduced support is the support.

## Main results

* `Stacks.Chow.relativeDimension_le_of_mem_supp_isNowhereDenseCoherentSubobject` — a point of the
  support of a nowhere dense coherent subsheaf has relative dimension at most `k`.
* `Stacks.Chow.schemeDeltaDimension_isNowhereDenseCoherentSubobject_le` — the support of a
  nowhere dense coherent subsheaf has delta-dimension at most `k`.

## References

* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.AlgebraicGeometry.CoherentSubquotients

variable {X : Scheme.{u}}

/-! ### The space of the reduced support -/

/-- **The space of the reduced support of a coherent module is its support.** The closed
immersion of the reduced support is a closed embedding whose range is the support. -/
def reducedSupportHomeomorph (F : X.Modules) [F.IsCoherent] :
    (reducedSupport F).subscheme ≃ₜ ↥(SheafOfModules.supp F) :=
  ((reducedSupport F).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr
      (by rw [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]))

/-- The image of a point `y` of the reduced support under `reducedSupportHomeomorph`, viewed as a
point of `X`, is the image of `y` under the closed immersion of the reduced support. -/
@[simp]
theorem reducedSupportHomeomorph_apply_coe (F : X.Modules) [F.IsCoherent]
    (y : (reducedSupport F).subscheme) :
    ((reducedSupportHomeomorph F y : ↥(SheafOfModules.supp F)) : X) =
      (reducedSupport F).subschemeι.base y :=
  rfl

/-! ### The strict drop -/

/-- **A point of the support of a nowhere dense coherent subsheaf has relative dimension at most
`k`.** It lies on an irreducible component of the reduced support of `ℱ`, whose generic point
avoids the nowhere dense support of `𝒦` and is therefore a proper generization of it, and the
dimension function drops strictly along a proper specialization. -/
theorem relativeDimension_le_of_mem_supp_isNowhereDenseCoherentSubobject (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (K : Subobject F) (hK : IsNowhereDenseCoherentSubobject F K) {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt))
    {x : X} (hx : x ∈ SheafOfModules.supp (K : X.Modules)) :
    relativeDimension C.dimensionFunction f x ≤ k := by
  have hXnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set Y := (reducedSupport F).subscheme with hY
  set ι := (reducedSupport F).subschemeι with hι
  have hYnoeth : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ f)
  -- the point, read on the reduced support of `F`
  have hKcoh : (K : X.Modules).IsCoherent := hK.1
  have : (K : X.Modules).IsFiniteType := isFiniteType_of_isCoherent (K : X.Modules)
  have hxF : x ∈ SheafOfModules.supp F := supp_subset_of_mono K.arrow hx
  set e := reducedSupportHomeomorph F with he
  set y : Y := e.symm ⟨x, hxF⟩ with hy
  have hcoe : ∀ w : ↥(SheafOfModules.supp F), ι.base (e.symm w) = w := fun w =>
    congrArg Subtype.val (e.apply_symm_apply w)
  have hey : ι.base y = x := hcoe ⟨x, hxF⟩
  -- the nowhere dense subset, carried to the reduced support
  set A : Set ↥(SheafOfModules.supp F) :=
    {z | (z : X) ∈ SheafOfModules.supp (K : X.Modules)} with hA
  have hAnd : IsNowhereDense A := hK.2
  set A' : Set Y := e.symm '' A with hA'
  have hA'nd : IsNowhereDense A' := e.symm.isInducing.isNowhereDense_image hAnd
  have hA'closed : IsClosed A' := by
    have hc : A' = ι.base ⁻¹' SheafOfModules.supp (K : X.Modules) := by
      refine Set.ext fun z => ⟨?_, ?_⟩
      · rintro ⟨w, hw, rfl⟩
        change ι.base (e.symm w) ∈ SheafOfModules.supp (K : X.Modules)
        rw [hcoe]; exact hw
      · intro hz
        exact ⟨e z, hz, Homeomorph.symm_apply_apply e z⟩
    rw [hc]
    exact (SheafOfModules.isClosed_supp (K : X.Modules)).preimage ι.continuous
  have hyA' : y ∈ A' := ⟨⟨x, hxF⟩, hx, rfl⟩
  -- the generic point of a component through `y`
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction (ι ≫ f)
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({y} : Set Y)) isIrreducible_singleton.closure
  have hyW : y ∈ W := hsub (subset_closure rfl)
  have hgen : IsGenericPoint hW.1.genericPoint W :=
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
  have hne : hW.1.genericPoint ≠ y := fun h =>
    genericPoint_notMem_of_nowhereDense Y hW hgen hA'closed hA'nd (h ▸ hyA')
  rw [schemeDeltaDimension_eq_iSup] at hdim
  have hWle : relativeDimension C.dimensionFunction (ι ≫ f) hW.1.genericPoint ≤ k + 1 := by
    have hle := WithBotTop.coe_le_coe.mp ((le_iSup
      (fun V : irreducibleComponents Y => (deltaDimension C (ι ≫ f) ⟨(V : Set Y), V.2.1,
        isClosed_of_mem_irreducibleComponents (V : Set Y) V.2⟩ : EInt))
      (⟨W, hW⟩ : irreducibleComponents Y)).trans hdim)
    rwa [deltaDimension_eq_of_isGenericPoint C (ι ≫ f) _ _ hgen] at hle
  have hlt := d.strictAnti_specializes (hgen.specializes hyW) hne
  rw [hd y, hd hW.1.genericPoint] at hlt
  have hyrel : relativeDimension C.dimensionFunction (ι ≫ f) y =
      relativeDimension C.dimensionFunction f x := by
    rw [relativeDimension_comp_closedImmersion C.dimensionFunction ι f y, hey]
  omega

/-- **The support of a nowhere dense coherent subsheaf has delta-dimension at most `k`.** This is
the dimension drop that makes one application of Stacks 02OL enough for the membership assertion
of Stacks 02SX. -/
theorem schemeDeltaDimension_isNowhereDenseCoherentSubobject_le (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (K : Subobject F) (hK : IsNowhereDenseCoherentSubobject F K) {k : ℤ}
    (hdim : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ ((k + 1 : ℤ) : EInt)) :
    haveI : (K : X.Modules).IsCoherent := hK.1
    schemeDeltaDimension C ((reducedSupport (K : X.Modules)).subschemeι ≫ f) ≤ (k : EInt) :=
  have : (K : X.Modules).IsCoherent := hK.1
  schemeDeltaDimension_reducedSupport_le C f _ fun _ hx =>
    relativeDimension_le_of_mem_supp_isNowhereDenseCoherentSubobject C f F K hK hdim hx

end Stacks.Chow

end
