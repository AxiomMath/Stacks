module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreStalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FibreUnramifiedAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.QuasiFiniteSlice
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The slice cut by a generating sequence of the fibre is unramified over the base

Let `f : X ⟶ S` be a morphism of schemes, let `x` be a point of `X`, let `h₁, …, h_r ∈ 𝒪_{X, x}`
have images **generating** the maximal ideal of the local ring of the fibre `X_{f x}` at `x`, and
let `ι : Z ⟶ X` be a preimmersion through `x` on which all the `h_i` vanish — the slice
`Z = V(h₁, …, h_r)`. This file proves that `Z ⟶ S` is **unramified at** the point `z` of `Z` over
`x`, as soon as the residue field extension `κ(x)/κ(f x)` is finite separable.

Both clauses by which **Stacks 02GF** recognizes unramifiedness are then in hand:

* `𝔪_{f x} 𝒪_{Z, z} = 𝔪_z` is
  `Stacks.AlgebraicGeometry.map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk`, the
  source's computation `𝒪_{T, v} = 𝒪_{V, v}/(φ(f₁), …, φ(f_d)) = κ(v)`;
* `κ(z)/κ(f x)` finite separable is the given extension transported along the residue field
  **isomorphism** `κ(x) ≅ κ(z)` that the preimmersion supplies, which is the source's transport
  of the separability of `κ(v)/k` along the surjection `𝒪_{V, v} ↠ 𝒪_{T, v}`.

This is the second of the two inputs the chart construction of **Stacks 06N3** needs at a finite
type point: the slice is flat and locally of finite presentation by **Stacks 06MD**, and
unramified over the field-valued point by this, which is what **Stacks 06N2** consumes to make
it étale.

## Main results

* `Stacks.AlgebraicGeometry.bijective_residueFieldMap_of_isPreimmersion`: a preimmersion induces
  an isomorphism on residue fields, its stalk maps being surjective.
* `Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk`: **the slice
  is unramified over the base at the sliced point.**
* `Stacks.AlgebraicGeometry.ofList_eq_maximalIdeal_fiberStalk_of_ofList_eq_maximalIdeal`: over a
  point whose local ring is a field — a field-valued point of the base, as in the chart
  construction of **Stacks 06N3** — a sequence generating the maximal ideal of `𝒪_{X, x}`
  generates that of the fibre's local ring.
* `Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk`: the two together,
  so that the generating sequence may be given in `𝒪_{X, x}` — which is where the slicing
  sequence of the chart construction is produced.

## Implementation notes

The residue field extension is stated for `f` at `x` and not for `ι ≫ f` at `z`, because that is
the form in which **Stacks 056U**
(`AlgebraicGeometry.dense_closedPoints_with_finite_separable_residueField_of_smooth`) delivers
it: at a closed point of a scheme smooth over a field, before any slicing. The transport to `z`
is `Algebra.IsSeparable.of_equiv_equiv` and `Module.Finite.equiv` along the residue field
isomorphism of the preimmersion, whose compatibility with the two structure maps is
`AlgebraicGeometry.Scheme.residueFieldMap_comp`.

No `@[stacks]` attribute is claimed: Stacks 02GF is registered on
`AlgebraicGeometry.unramifiedAt_tfae`, and this is the implication from its seventh entry to its
first for one morphism.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.AlgebraicGeometry

variable {X S Z : Scheme.{u}}

/-- **A preimmersion is an isomorphism on residue fields.** Its stalk maps are surjective, so the
induced maps of residue fields are surjective, and a homomorphism out of a field is injective. -/
theorem bijective_residueFieldMap_of_isPreimmersion (ι : Z ⟶ X) [IsPreimmersion ι] (z : Z) :
    Function.Bijective (ι.residueFieldMap z).hom := by
  refine ⟨(ι.residueFieldMap z).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨c, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective ι z b
  exact ⟨IsLocalRing.residue _ c, rfl⟩

/-- **The slice cut out by a generating sequence of the fibre is unramified over the base.** Let
`f : X ⟶ S` be a morphism of schemes, let `h₁, …, h_r ∈ 𝒪_{X, ι z}` have images generating the
maximal ideal of the local ring of the fibre of `f` through `ι z`, let `ι : Z ⟶ X` be a
preimmersion on which the `h_i` vanish at `z`, and suppose `κ(ι z)/κ(f (ι z))` is finite
separable. If `ι ≫ f` is locally of finite type then it is **unramified at** `z`.

This is the implication from the seventh entry of `AlgebraicGeometry.unramifiedAt_tfae`
(**Stacks 02GF**) to its first, at `ι ≫ f` and `z`. Its first clause is
`Stacks.AlgebraicGeometry.map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk`, the
source's `𝒪_{T, v} = κ(v)`; its second is the given residue field extension transported along
the residue field isomorphism of the preimmersion. -/
@[sga "3 XI 1.3" "(ii)"]
theorem unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk
    (ι : Z ⟶ X) [IsPreimmersion ι] (f : X ⟶ S) [LocallyOfFiniteType (ι ≫ f)] (z : Z)
    {r : ℕ} (h : Fin r → X.presheaf.stalk (ι z))
    (hzero : ∀ k, (ι.stalkMap z).hom (h k) = 0)
    (hgen : Ideal.ofList
        (List.ofFn fun k => ((f.fiberι (f (ι z))).stalkMap (f.asFiber (ι z))).hom
          ((f.fiberι_asFiber (ι z)).symm ▸ h k)) =
      maximalIdeal ((f.fiber (f (ι z))).presheaf.stalk (f.asFiber (ι z))))
    (hsep : letI := (f.residueFieldMap (ι z)).hom.toAlgebra
      Module.Finite (S.residueField (f (ι z))) (X.residueField (ι z)) ∧
        Algebra.IsSeparable (S.residueField (f (ι z))) (X.residueField (ι z))) :
    UnramifiedAt (ι ≫ f) z := by
  let algX : Algebra (S.residueField (f (ι z))) (X.residueField (ι z)) :=
    (f.residueFieldMap (ι z)).hom.toAlgebra
  let algZ : Algebra (S.residueField (f (ι z))) (Z.residueField z) :=
    ((ι ≫ f).residueFieldMap z).hom.toAlgebra
  obtain ⟨hfin, hsepa⟩ := hsep
  have hbij := bijective_residueFieldMap_of_isPreimmersion ι z
  have hcomm : (algebraMap (S.residueField (f (ι z))) (Z.residueField z)).comp
      (RingEquiv.refl (S.residueField (f (ι z)))).toRingHom =
      (RingEquiv.ofBijective (ι.residueFieldMap z).hom hbij :
          X.residueField (ι z) →+* Z.residueField z).comp
        (algebraMap (S.residueField (f (ι z))) (X.residueField (ι z))) := by
    ext c
    change ((ι ≫ f).residueFieldMap z).hom c =
      (ι.residueFieldMap z).hom ((f.residueFieldMap (ι z)).hom c)
    rw [Scheme.residueFieldMap_comp]
    rfl
  let E : X.residueField (ι z) ≃ₐ[S.residueField (f (ι z))] Z.residueField z :=
    { RingEquiv.ofBijective (ι.residueFieldMap z).hom hbij with
      commutes' := fun c => (congrArg (fun k => k c) hcomm).symm }
  have hclause : Ideal.map ((ι ≫ f).stalkMap z).hom
        (maximalIdeal (S.presheaf.stalk ((ι ≫ f) z))) = maximalIdeal (Z.presheaf.stalk z) ∧
      Module.Finite (S.residueField (f (ι z))) (Z.residueField z) ∧
        Algebra.IsSeparable (S.residueField (f (ι z))) (Z.residueField z) :=
    ⟨map_maximalIdeal_comp_eq_of_ofList_eq_maximalIdeal_fiberStalk ι f z (ι z) rfl h hzero hgen,
      Module.Finite.equiv E.toLinearEquiv,
      Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl _)
        (RingEquiv.ofBijective (ι.residueFieldMap z).hom hbij) hcomm⟩
  exact ((unramifiedAt_tfae (ι ≫ f) z).out 1 7).mpr hclause

/-- **Over a point whose local ring is a field, generating the maximal ideal of `𝒪_{X, x}` is
generating that of the fibre's local ring.** The fibre is cut out by the maximal ideal of the
target's local ring, so when that ideal vanishes the canonical map
`𝒪_{X, x} ⟶ 𝒪_{X_{f x}, x}` is an isomorphism
(`AlgebraicGeometry.stalkEquivFiberStalk`), and an isomorphism carries the maximal ideal onto the
maximal ideal.

The hypothesis holds at a **field-valued point** of the base, which is the situation of the chart
construction of **Stacks 06N3**: there `S = Spec k` and the fibre of `V ⟶ Spec k` is `V`
itself. -/
theorem ofList_eq_maximalIdeal_fiberStalk_of_ofList_eq_maximalIdeal (f : X ⟶ S) (x : X)
    (hfield : maximalIdeal (S.presheaf.stalk (f x)) = ⊥)
    {r : ℕ} (h : Fin r → X.presheaf.stalk x)
    (hgen : Ideal.ofList (List.ofFn h) = maximalIdeal (X.presheaf.stalk x)) :
    Ideal.ofList
        (List.ofFn fun k => ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
          ((f.fiberι_asFiber x).symm ▸ h k)) =
      maximalIdeal ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  have hlist : (List.ofFn fun k => ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
        ((f.fiberι_asFiber x).symm ▸ h k)) =
      (List.ofFn h).map (stalkEquivFiberStalk f x hfield).toRingHom := by
    rw [List.map_ofFn]
    refine congrArg List.ofFn (funext fun k => ?_)
    change ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom ((f.fiberι_asFiber x).symm ▸ h k) =
      stalkEquivFiberStalk f x hfield (h k)
    rw [stalkEquivFiberStalk_apply]
    exact congrArg ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom
      (stalkCongr_hom_eq_cast X.presheaf (f.fiberι_asFiber x).symm (h k)).symm
  rw [hlist, ← Ideal.map_ofList, hgen,
    map_maximalIdeal_of_surjective _ (stalkEquivFiberStalk f x hfield).surjective]

/-- **The slice cut out by a generating sequence of `𝒪_{X, x}` is unramified over a field-valued
point of the base at the sliced point.** This is
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk` with its
generating hypothesis read in `𝒪_{X, x}` rather than in the local ring of the fibre, the two
being the same over a point whose local ring is a field
(`Stacks.AlgebraicGeometry.ofList_eq_maximalIdeal_fiberStalk_of_ofList_eq_maximalIdeal`).

It is the form the chart construction of **Stacks 06N3** produces: the slicing sequence of
`AlgebraicGeometry`
`.exists_fn_mem_maximalIdeal_isRegular_ofList_eq_maximalIdeal_stalk_of_unramifiedAt`
generates the maximal ideal of `𝒪_{V, v}`, and the base is the spectrum of a field. -/
theorem unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk
    (ι : Z ⟶ X) [IsPreimmersion ι] (f : X ⟶ S) [LocallyOfFiniteType (ι ≫ f)] (z : Z)
    (hfield : maximalIdeal (S.presheaf.stalk (f (ι z))) = ⊥)
    {r : ℕ} (h : Fin r → X.presheaf.stalk (ι z))
    (hzero : ∀ k, (ι.stalkMap z).hom (h k) = 0)
    (hgen : Ideal.ofList (List.ofFn h) = maximalIdeal (X.presheaf.stalk (ι z)))
    (hsep : letI := (f.residueFieldMap (ι z)).hom.toAlgebra
      Module.Finite (S.residueField (f (ι z))) (X.residueField (ι z)) ∧
        Algebra.IsSeparable (S.residueField (f (ι z))) (X.residueField (ι z))) :
    UnramifiedAt (ι ≫ f) z :=
  unramifiedAt_comp_of_ofList_eq_maximalIdeal_fiberStalk ι f z h hzero
    (ofList_eq_maximalIdeal_fiberStalk_of_ofList_eq_maximalIdeal f (ι z) hfield h hgen) hsep

end Stacks.AlgebraicGeometry

end
