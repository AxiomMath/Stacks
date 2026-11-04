module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernel
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSupportDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistSupport
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport

/-!
# The support of the quotient triple of the induction step of Tag 0F27

The induction step of [Stacks, Tag 0F27] bounds the dimension of the support of the quotient
`G` it builds by that of the support of `F`, and the bound is consumed in the two forms
`Stacks.Algebraization.CoherentTriple.dimension_drop_of_isNowhereDense` delivers. That lemma
asks for three things about `Supp G`: containment in `Supp F`, closedness, and nowhere density
inside `Supp F`. This file discharges the first two, for the quotient of *any* morphism of
coherent triples, and then for the quotient of a morphism between two twists -- which is the
shape multiplication by a section of the invertible triple
(`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`) has.

Both come from the stalkwise description of the support. The stalk functor preserves colimits,
so at a point where the target has vanishing stalk the cokernel has vanishing stalk too, and a
quotient of a module of finite type is of finite type.

Nowhere density is not proved outright here, but its *geometric* half is. The hypothesis the
dimension drop consumes is that no irreducible component of `Supp F` lies inside `Supp G`, and a
component has a generic point -- the punctured spectrum is a scheme, hence sober -- which is an
associated point of `F` by [Stacks, Tag 05AL]. So the hypothesis follows from the *pointwise*
statement that no associated point of `F` lies in `Supp G`, which is exactly what the source's
choice of a section not vanishing at any associated point of `F` is about. That reduction is
`Algebraization.CoherentTriple.forall_irreducibleComponents_notSubset_of_notMem_associatedPoints`
below, and the stalkwise statement that multiplication by the section is surjective on the
stalk at a point where the section does not vanish is supplied in
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelNonvanishing`, which
therefore closes both forms of the dimension drop for
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`.

## Main results

* `Stacks.Algebraization.CoherentTriple.supp_cokernelTriple_F_subset`: the support of the
  punctured-spectrum member of a quotient triple lies in the support of the member of the
  target.
* `Stacks.Algebraization.CoherentTriple.isClosed_supp_cokernelTriple_F`: that support is closed.
* `Stacks.Algebraization.CoherentTriple.supp_cokernelTriple_twistZ_subset` and
  `Stacks.Algebraization.CoherentTriple.isClosed_supp_cokernelTriple_twistZ_F`: the same for a
  morphism between two twists of a coherent triple, with the containment read against the
  support of the untwisted member -- twisting does not move the support, by
  `Stacks.Algebraization.CoherentTriple.supp_twistZ_F`.
* `Stacks.Algebraization.CoherentTriple.dimension_drop_cokernelTriple_twistZ`: **the dimension
  drop of the induction step of [Stacks, Tag 0F27] for the quotient of a morphism of twists, in
  the two forms the induction consumes, owing nothing but the nowhere density.**
* `Algebraization.CoherentTriple.forall_irreducibleComponents_notSubset_of_notMem_associatedPoints`:
  **no irreducible component of `Supp F` is contained in a set avoiding every associated point of
  `F`** -- the geometric half of the nowhere density.
* `Algebraization.CoherentTriple.dimension_drop_cokernelTriple_twistZ_of_notMem_associatedPoints`:
  **the dimension drop owing only the pointwise statement that no associated point of `F` lies in
  the support of the quotient.**

## Implementation notes

The general statements are about `Stacks.Algebraization.CoherentTriple.cokernelTriple` of an
arbitrary morphism rather than about multiplication by a section. That is deliberate and it is
what keeps the long compatibility hypothesis of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` out of the statements: its specialisation
to that morphism is the general statement applied to it, with no further argument.

The support bound used is
`AlgebraicGeometry.Scheme.Modules.supp_cokernel_subset_supp`, and the closedness is
`AlgebraicGeometry.Scheme.Modules.isClosed_supp_cokernel`; both are about a cokernel in
`X.Modules` with no hypothesis beyond finite type of the target, and
`Stacks.Algebraization.CoherentTriple.cokernelTriple` is `@[reducible]`, so its
punctured-spectrum member *is* that cokernel and the two apply directly.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing Set TopologicalSpace

universe u

namespace Stacks.Algebraization

section

variable {A : Type u} [CommRing A] [IsLocalRing A] {f : A}

/-! ### The support of a quotient triple -/

/-- **The support of the punctured-spectrum member of a quotient triple is contained in the
support of the member of the target.** The member of the quotient is the cokernel of the member
of the morphism, and taking stalks preserves colimits. -/
public theorem CoherentTriple.supp_cokernelTriple_F_subset {T S : CoherentTriple A f}
    (φ : T.Hom S) (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) :
    SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F ⊆ SheafOfModules.supp S.F :=
  AlgebraicGeometry.Scheme.Modules.supp_cokernel_subset_supp φ.onPunctured

/-- **The support of the punctured-spectrum member of a quotient triple is closed.** Both
members of a coherent triple are coherent, hence of finite type, and a quotient of a module of
finite type is of finite type. -/
public theorem CoherentTriple.isClosed_supp_cokernelTriple_F {T S : CoherentTriple A f}
    (φ : T.Hom S) (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) :
    IsClosed (SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F) :=
  have : _root_.SheafOfModules.IsCoherent S.F := S.coherent_F
  AlgebraicGeometry.Scheme.Modules.isClosed_supp_cokernel φ.onPunctured
    _root_.SheafOfModules.IsCoherent.isFiniteType

/-! ### The support of the quotient of a morphism of twists -/

/-- **The support of the punctured-spectrum member of the quotient of a morphism between two
twists of a coherent triple is contained in the support of the untwisted member.** Twisting does
not move the support, by `Stacks.Algebraization.CoherentTriple.supp_twistZ_F`, so the bound of
`Stacks.Algebraization.CoherentTriple.supp_cokernelTriple_F_subset` may be read against `T.F`
itself. This is the hypothesis `hsub` of
`Stacks.Algebraization.CoherentTriple.dimension_drop_of_isNowhereDense`. -/
public theorem CoherentTriple.supp_cokernelTriple_twistZ_subset (T L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) {m n : ℤ}
    (φ : (T.twistZ L hL m).Hom (T.twistZ L hL n))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) :
    SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F ⊆ SheafOfModules.supp T.F :=
  (CoherentTriple.supp_cokernelTriple_F_subset φ htf).trans
    (T.supp_twistZ_F L hL n).subset

/-- **The support of the punctured-spectrum member of the quotient of a morphism between two
twists is closed.** This is the hypothesis `hclosed` of
`Stacks.Algebraization.CoherentTriple.dimension_drop_of_isNowhereDense`. -/
public theorem CoherentTriple.isClosed_supp_cokernelTriple_twistZ_F (T L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) {m n : ℤ}
    (φ : (T.twistZ L hL m).Hom (T.twistZ L hL n))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured)) :
    IsClosed (SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F) :=
  CoherentTriple.isClosed_supp_cokernelTriple_F φ htf

/-! ### The dimension drop, owing nothing but the nowhere density -/

/-- **The dimension drop of the induction step of [Stacks, Tag 0F27] for the quotient of a
morphism between two twists of a coherent triple, in the two forms the induction consumes.**

This is `Stacks.Algebraization.CoherentTriple.dimension_drop_of_isNowhereDense` with its two
support hypotheses discharged, so that the only thing left to supply is the nowhere density --
the geometric content of the source's choice of a section not vanishing at any associated point
of `F`.

The morphism is arbitrary; multiplication by a global section of the invertible triple,
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`, is the instance the induction step
uses, and no part of its compatibility datum is needed here. -/
public theorem CoherentTriple.dimension_drop_cokernelTriple_twistZ [IsNoetherianRing A]
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) {m n : ℤ}
    (φ : (T.twistZ L hL m).Hom (T.twistZ L hL n))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured))
    (hnd : IsNowhereDense ((Subtype.val : ↥(SheafOfModules.supp T.F) →
      (Stacks.Divisors.puncturedSpectrum A).toScheme) ⁻¹'
        SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F)) :
    (∀ e : ℕ, topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim
          ↥(SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F) ≤
            ((e : ℕ) : WithBot ℕ∞)) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F = ∅) :=
  T.dimension_drop_of_isNowhereDense _
    (T.supp_cokernelTriple_twistZ_subset L hL φ htf)
    (T.isClosed_supp_cokernelTriple_twistZ_F L hL φ htf) hnd

/-- **The dimension drop for the quotient of a morphism of twists, with the nowhere-density
hypothesis in the shape a supplier checks**: the support of the quotient contains no irreducible
component of `Supp F`. That is what the source's choice of a section not vanishing at any
associated point of `F` delivers, a generic point of a component of `Supp F` being an associated
point of `F`. -/
public theorem CoherentTriple.dimension_drop_cokernelTriple_twistZ_of_forall_irreducibleComponents
    [IsNoetherianRing A] (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) {m n : ℤ}
    (φ : (T.twistZ L hL m).Hom (T.twistZ L hL n))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured))
    (hcomp : ∀ Z ∈ irreducibleComponents ↥(SheafOfModules.supp T.F),
      ¬ ((Subtype.val : ↥(SheafOfModules.supp T.F) →
        (Stacks.Divisors.puncturedSpectrum A).toScheme) '' Z ⊆
          SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F)) :
    (∀ e : ℕ, topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim
          ↥(SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F) ≤
            ((e : ℕ) : WithBot ℕ∞)) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F = ∅) :=
  T.dimension_drop_of_forall_irreducibleComponents _
    (T.supp_cokernelTriple_twistZ_subset L hL φ htf)
    (T.isClosed_supp_cokernelTriple_twistZ_F L hL φ htf) hcomp

/-! ### The nowhere density, reduced to the associated points -/

/-- **No irreducible component of `Supp F` is contained in a set that avoids every associated
point of `F`.** The component is a closed irreducible subset of the closed set `Supp F`, hence a
closed irreducible subset of the punctured spectrum, which is a scheme and therefore sober; so it
has a generic point, and that generic point is an associated point of `F` by [Stacks, Tag 05AL],
`AlgebraicGeometry.mem_associatedPoints_of_isGenericPoint_irreducibleComponent_supp`. A set
containing the component would contain that point.

This is the reduction the choice of the section of the induction step of [Stacks, Tag 0F27] is
waiting for: it turns the `hcomp` hypothesis of
`CoherentTriple.dimension_drop_cokernelTriple_twistZ_of_forall_irreducibleComponents`
-- a statement about irreducible components -- into the *pointwise* statement that no associated
point of `F` lies in `Supp G`, which is what
`Stacks.Algebraization.exists_sectionPair_nonvanishing_on_associatedPoints_depthFree` is about.
The geometric half of the nowhere density is therefore discharged; the stalkwise half, that the
quotient has vanishing stalk where the section does not vanish, is
`Stacks.Algebraization.CoherentTriple.notMem_supp_cokernelTriple_mulSectionTwistZ`. -/
public theorem CoherentTriple.forall_irreducibleComponents_notSubset_of_notMem_associatedPoints
    [IsNoetherianRing A] (T : CoherentTriple A f)
    (S : Set (Stacks.Divisors.puncturedSpectrum A).toScheme)
    (hS : ∀ p ∈ Stacks.Divisors.associatedPoints T.F, p ∉ S) :
    ∀ Z ∈ irreducibleComponents ↥(SheafOfModules.supp T.F),
      ¬ ((Subtype.val : ↥(SheafOfModules.supp T.F) →
        (Stacks.Divisors.puncturedSpectrum A).toScheme) '' Z ⊆ S) := by
  have : IsLocallyNoetherian (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (Stacks.Divisors.puncturedSpectrum A).ι
  have : _root_.SheafOfModules.IsCoherent T.F := T.coherent_F
  intro Z hZ hsub
  have hclosed : IsClosed (SheafOfModules.supp T.F) :=
    Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent T.F T.coherent_F
  have himg : IsClosed ((Subtype.val : ↥(SheafOfModules.supp T.F) →
      (Stacks.Divisors.puncturedSpectrum A).toScheme) '' Z) :=
    hclosed.isClosedEmbedding_subtypeVal.isClosedMap Z
      (isClosed_of_mem_irreducibleComponents Z hZ)
  have hirr : IsIrreducible ((Subtype.val : ↥(SheafOfModules.supp T.F) →
      (Stacks.Divisors.puncturedSpectrum A).toScheme) '' Z) :=
    hZ.1.image _ continuous_subtype_val.continuousOn
  obtain ⟨x, hx⟩ := QuasiSober.sober hirr himg
  refine hS x (mem_associatedPoints_of_isGenericPoint_irreducibleComponent_supp
    (Stacks.Divisors.puncturedSpectrum A).toScheme T.F hZ hx) (hsub ?_)
  rw [← hx.def]
  exact subset_closure (by simp)

/-- **The dimension drop of the induction step of [Stacks, Tag 0F27] for the quotient of a
morphism of twists, owing only a pointwise statement about associated points**: that no
associated point of `F` lies in the support of the quotient. This is
`CoherentTriple.dimension_drop_cokernelTriple_twistZ_of_forall_irreducibleComponents` with its
hypothesis fed from
`CoherentTriple.forall_irreducibleComponents_notSubset_of_notMem_associatedPoints`.

The remaining hypothesis is the stalkwise one, and for multiplication by a section it is what the
nonvanishing of the section gives: at a point where the section does not vanish, multiplication
by it is bijective on the stalk, so the cokernel has vanishing stalk there -- the composite of
`Stacks.SectionProduct.bijective_mapFun_mulRight_of_le_nonvanishingLocus` with
`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`, the
punctured-spectrum member of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` being put
into the shape `mulRight` by `Stacks.Algebraization.tensorModulesMap_id_eq_whiskerLeft`,
`Stacks.Algebraization.whiskerLeft_mulSectionPowScheme` and
`Stacks.Algebraization.rightUnitor_inv_comp_whiskerLeft` with the trailing isomorphisms absorbed
by `AlgebraicGeometry.Scheme.Modules.supp_cokernel_comp_isIso`. That composition is carried out
in `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelNonvanishing`; it needed
no bridge between `Stacks.ModuleStalk.mapFun` and `AlgebraicGeometry.stalkLinearMap`, those being
the same function, and no quasi-coherence. -/
public theorem CoherentTriple.dimension_drop_cokernelTriple_twistZ_of_notMem_associatedPoints
    [IsNoetherianRing A] (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) {m n : ℤ}
    (φ : (T.twistZ L hL m).Hom (T.twistZ L hL n))
    (htf : IsFTorsionFree A f (cokernel φ.onPunctured))
    (hass : ∀ p ∈ Stacks.Divisors.associatedPoints T.F,
      p ∉ SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F) :
    (∀ e : ℕ, topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) →
        topologicalKrullDim
          ↥(SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F) ≤
            ((e : ℕ) : WithBot ℕ∞)) ∧
      (topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞) →
        SheafOfModules.supp (CoherentTriple.cokernelTriple φ htf).F = ∅) :=
  T.dimension_drop_cokernelTriple_twistZ_of_forall_irreducibleComponents L hL φ htf
    (T.forall_irreducibleComponents_notSubset_of_notMem_associatedPoints _ hass)

end

end Stacks.Algebraization

end
