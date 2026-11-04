module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SourceMap
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.Topology.Dimension.MaximalPointDrop
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop
public import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# A vertical locally principal closed subscheme fills up components of a fibre

Let `f : X ⟶ S` be a dominant morphism locally of finite type between irreducible schemes with
`X` locally Noetherian, and let `Z ⊆ X` be the closed subscheme cut out by a locally principal
ideal sheaf `I`. Assume `Z` misses the generic fibre. Then at any fibre `X_s` whose dimension
does not exceed that of the generic fibre, the support of `Z` in `X_s` is set-theoretically a
union of irreducible components of `X_s`.

This is the locally Noetherian case of Stacks 053R. The source's own statement, with no
Noetherian hypothesis, is
`Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_general` in
`StacksFrontier.AlgebraicGeometry.FibreDimension.GeneralCase`: it descends the affine situation to a
finitely generated `ℤ`-algebra and applies the theorem below there.

The argument is the one of the source, with its shrinking step replaced by upper
semicontinuity. Let `ξ` be a generic point of an irreducible component of `Z ∩ X_s` and suppose
it is not a generic point of an irreducible component of `X_s`. Every fibre has local dimension
exactly `d = dim X_η` at every point, so the dimension of `Z ∩ X_s` at `ξ` drops: `ξ` is maximal
in `Z ∩ X_s` while some other point of `X_s` specializes to it. Let `ξ'` be a generic point of
the irreducible component of the support of `I` through the image of `ξ`. Then `ξ'` specializes
to that image, so it lies in *every* open neighbourhood of it, in particular in the open locus
where the fibre of `Z` has small local dimension; this is what the source achieves by replacing
`X` by an open neighbourhood. On the other hand Krull's principal ideal theorem makes `ξ'` a
generic point of an irreducible component of its own fibre `X_{s'}`, so a whole neighbourhood of
`ξ'` in `X_{s'}` lies in `Z`, and the local dimension of `Z ∩ X_{s'}` at `ξ'` is that of
`X_{s'}`, which is at least `d`. The two bounds contradict each other.

## Main results

* `AlgebraicGeometry.exists_nat_topologicalKrullDim_fiber_genericPoint_eq`: the generic fibre of
  a dominant morphism locally of finite type between irreducible schemes has finite dimension.
* `Stacks.Divisors.topologicalKrullDimAt_fiber_subscheme_eq`: the local dimension of the fibre
  of the closed subscheme cut out by an ideal sheaf, read inside the ambient fibre.
* `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents`: **Stacks 053R, locally
  Noetherian case.** The Noetherian-free statement is
  `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_general` in
  `StacksFrontier.AlgebraicGeometry.FibreDimension.GeneralCase`.
* `Stacks.Divisors.exists_mem_irreducibleComponents_subset_fiber_support`: its pointwise form,
  which is what the equation of supports asserts at each point of the support.
* `Stacks.Divisors.fiber_support_ne_union_irreducibleComponents_of_irreducibleSpace`: the
  equation *fails* when the fibre is irreducible and the support meets it in a nonempty proper
  subset, so the hypotheses of the theorem are doing work and the equation is not a tautology.

## Implementation notes

The set-theoretic fibre of the closed subscheme is identified with the part of the ambient fibre
lying in the support by `AlgebraicGeometry.Scheme.IdealSheafData.fiberHomeo`, so that the
semicontinuity statement `AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le` for the composite
`I.subschemeι ≫ f` becomes a statement about `f.fiberι t ⁻¹' I.support`. The transfer is
`topologicalKrullDimAt_fiber_subscheme_eq`; it takes the base point `t` together with an
equation `(I.subschemeι ≫ f) w = t` so that the equation can be substituted away, rather than
being stated for the base point `(I.subschemeι ≫ f) w` itself, which would force every use to
transport a point of `f.fiber t` along an equality of base points.

The hypothesis `[IsLocallyNoetherian X]` is what the appeal to Krull's principal ideal theorem
needs, and is exactly the restriction to the Noetherian case. No Noetherian hypothesis is needed
on the fibres: they are locally of finite type over a residue field, hence locally Noetherian.

## References

* [Stacks Project, Tag 053R](https://stacks.math.columbia.edu/tag/053R)
* [Stacks Project, Tag 00KV](https://stacks.math.columbia.edu/tag/00KV)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/- `natCast_ne_top_withBot` was re-proved here. It is public in
`StacksFrontier/Data/ENat/WithBotNatCast.lean:23`, the module that exists for exactly this --
its docstring records that several modules had each proved the `WithBot ℕ∞` form for
themselves. The uses below name that one. -/


/-- The fibre of a morphism locally of finite type is locally of finite type over the residue
field of its base point. -/
private theorem locallyOfFiniteType_fiberToSpecResidueField_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
  locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) inferInstance

/-- The fibre of a morphism locally of finite type is locally Noetherian. -/
private theorem isLocallyNoetherian_fiber_of_locallyOfFiniteType' {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) : IsLocallyNoetherian (f.fiber s) :=
  have := locallyOfFiniteType_fiberToSpecResidueField_of_locallyOfFiniteType f s
  LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)

/-- The generic fibre of a dominant morphism locally of finite type between irreducible schemes
has finite dimension: it is nonempty, irreducible and locally of finite type over the residue
field at the generic point of the target, so its dimension is its local dimension at any
point. -/
public theorem exists_nat_topologicalKrullDim_fiber_genericPoint_eq {X S : Scheme.{u}}
    (f : X ⟶ S) [IrreducibleSpace X] [IrreducibleSpace S] [IsDominant f]
    [LocallyOfFiniteType f] :
    ∃ d : ℕ, topologicalKrullDim (f.fiber (genericPoint S)) = (d : WithBot ℕ∞) := by
  have hirr : IrreducibleSpace (f.fiber (genericPoint S)) :=
    apply_genericPoint_eq_genericPoint f ▸ irreducibleSpace_fiber_apply_genericPoint f
  have := locallyOfFiniteType_fiberToSpecResidueField_of_locallyOfFiniteType f (genericPoint S)
  obtain ⟨p⟩ := hirr.toNonempty
  obtain ⟨n, hn⟩ := exists_topologicalKrullDimAt_le
    (f.fiber (genericPoint S)) (S.residueField (genericPoint S))
    (f.fiberToSpecResidueField (genericPoint S)) p
  have heq : topologicalKrullDim (f.fiber (genericPoint S))
      = topologicalKrullDimAt (f.fiber (genericPoint S)) p :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      (S.residueField (genericPoint S)) _ (f.fiberToSpecResidueField (genericPoint S)) p
  have hbot : topologicalKrullDim (f.fiber (genericPoint S)) ≠ ⊥ := by
    rw [Ne, topologicalKrullDim_eq_bot_iff_isEmpty]
    exact fun h => h.elim p
  have htop : topologicalKrullDim (f.fiber (genericPoint S)) ≠ ⊤ := by
    rw [heq]
    intro h
    rw [h, top_le_iff] at hn
    exact natCast_ne_top_withBot n hn
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have ha' : a ≠ ⊤ := by
    rintro rfl
    exact htop (by rw [← ha, WithBot.coe_top])
  obtain ⟨e, rfl⟩ := ENat.ne_top_iff_exists.mp ha'
  exact ⟨e, by rw [← ha]; norm_cast⟩

end AlgebraicGeometry

namespace Stacks.Divisors

open AlgebraicGeometry

/-- The local dimension of the scheme-theoretic fibre of the closed subscheme cut out by an
ideal sheaf `I`, read inside the ambient fibre: at a point `w` of the subscheme lying over `t`
whose image in `X` is the image of a point `p` of `f.fiber t`, it is the local dimension at `p`
of the part of `f.fiber t` lying in the support of `I`. -/
public theorem topologicalKrullDimAt_fiber_subscheme_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (w : I.subscheme) {t : S} (ht : (I.subschemeι ≫ f) w = t)
    (p : f.fiber t) (hp : f.fiberι t p = I.subschemeι w)
    (hmem : p ∈ f.fiberι t ⁻¹' (I.support : Set X)) :
    topologicalKrullDimAt ((I.subschemeι ≫ f).fiber ((I.subschemeι ≫ f) w))
        ((I.subschemeι ≫ f).asFiber w)
      = topologicalKrullDimAt ↥(f.fiberι t ⁻¹' (I.support : Set X)) ⟨p, hmem⟩ := by
  subst ht
  rw [topologicalKrullDimAt_eq_of_homeomorph
    (I.fiberHomeo f ((I.subschemeι ≫ f) w)) ((I.subschemeι ≫ f).asFiber w)]
  congr 1
  refine Subtype.ext ((f.fiberι ((I.subschemeι ≫ f) w)).isEmbedding.injective ?_)
  rw [Scheme.IdealSheafData.fiberHomeo_apply, Scheme.Hom.fiberι_fiberMap,
    Scheme.Hom.fiberι_asFiber, hp]

/-- **Stacks 053R, the Noetherian case.** Let `f : X ⟶ S` be a dominant morphism locally of
finite type between irreducible schemes with `X` locally Noetherian, let `I` be a locally
principal ideal sheaf on `X` whose closed subscheme misses the generic fibre, and let `s ∈ S` be
a point whose fibre has dimension at most that of the generic fibre. Then the support of the
closed subscheme inside `f.fiber s` is set-theoretically the union of the irreducible components
of `f.fiber s` that it contains. -/
@[stacks 053R "the locally Noetherian case, the form in which Krull's principal ideal theorem
applies to `f` directly. The statement without `[IsLocallyNoetherian X]`, which is the source's
own, is `Stacks.Divisors.fiber_support_eq_union_irreducibleComponents_general` in
`StacksFrontier/AlgebraicGeometry/FibreDimension/GeneralCase.lean:352`; it applies this one to a
finitely generated ℤ-algebra that the affine situation descends to, by
`StacksFrontier.AlgebraicGeometry.FibreDimension.AffineGeneralCase`."]
public theorem fiber_support_eq_union_irreducibleComponents {X S : Scheme.{u}} (f : X ⟶ S)
    [IrreducibleSpace S] [IrreducibleSpace X] [IsDominant f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (hI : IsLocallyPrincipal I)
    (hgeneric : IsEmpty ((I.subschemeι ≫ f).fiber (genericPoint S))) (s : S)
    (hdim : topologicalKrullDim (f.fiber s) ≤
      topologicalKrullDim (f.fiber (genericPoint S))) :
    (f.fiberι s) ⁻¹' (I.support : Set X) =
      ⋃₀ {C : Set (f.fiber s) | C ∈ irreducibleComponents (f.fiber s) ∧
        C ⊆ (f.fiberι s) ⁻¹' (I.support : Set X)} := by
  have hgen : ∀ y ∈ (I.support : Set X), f y ≠ genericPoint S :=
    (I.isEmpty_fiber_comp_iff f (genericPoint S)).mp hgeneric
  obtain ⟨d, hd⟩ := exists_nat_topologicalKrullDim_fiber_genericPoint_eq f
  have hWclosed : IsClosed (f.fiberι s ⁻¹' (I.support : Set X)) :=
    I.isClosed_supportSet.preimage (f.fiberι s).continuous
  refine Set.eq_sUnion_irreducibleComponents_of_forall _ fun y hy => ?_
  obtain ⟨ξ, hξW, hξy, hξmax⟩ := exists_specializes_forall_specializes_imp_eq hWclosed hy
  -- The point `ξ` is a generic point of an irreducible component of the whole fibre.
  have hmaxfib : ∀ q : f.fiber s, q ⤳ ξ → q = ξ := by
    intro z hz
    by_contra hzx
    have := isLocallyNoetherian_fiber_of_locallyOfFiniteType' f s
    obtain ⟨N, hNopen, hξN, hNnoeth⟩ :=
      isLocallyNoetherianSpace_of_isLocallyNoetherian (f.fiber s) ξ
    have hdimξ : topologicalKrullDimAt (f.fiber s) ξ ≤ (d : WithBot ℕ∞) :=
      le_of_eq ((topologicalKrullDimAt_fiber_eq_of_le f s hdim ξ).trans hd)
    obtain ⟨k, hkd, hkdim⟩ :=
      exists_le_topologicalKrullDimAt_of_specializes hWclosed hξW hξmax hz hzx hNopen hξN hdimξ
    -- Transport the bound to the fibre of the closed subscheme.
    have hsξ : f (f.fiberι s ξ) = s := (f.range_fiberι s).le ⟨ξ, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : I.subscheme, I.subschemeι w = f.fiberι s ξ :=
      (I.range_subschemeι ▸ hξW : f.fiberι s ξ ∈ Set.range I.subschemeι)
    have hwdim : topologicalKrullDimAt ((I.subschemeι ≫ f).fiber ((I.subschemeι ≫ f) w))
        ((I.subschemeι ≫ f).asFiber w) ≤ (k : WithBot ℕ∞) := by
      rw [topologicalKrullDimAt_fiber_subscheme_eq f I w
        (show (I.subschemeι ≫ f) w = s by rw [Scheme.Hom.comp_apply, hw, hsξ]) ξ hw.symm hξW]
      exact hkdim
    -- A generic point of the irreducible component of the support through the image of `ξ`.
    obtain ⟨ξ', hξ'supp, hξ'x, hξ'max⟩ :=
      exists_specializes_forall_specializes_imp_eq I.isClosed_supportSet hξW
    obtain ⟨w', hw'⟩ : ∃ w' : I.subscheme, I.subschemeι w' = ξ' :=
      (I.range_subschemeι ▸ hξ'supp : ξ' ∈ Set.range I.subschemeι)
    have hsp : w' ⤳ w := I.subschemeι.isEmbedding.isInducing.specializes_iff.mp
      (by rw [hw, hw']; exact hξ'x)
    have hw'dim : topologicalKrullDimAt ((I.subschemeι ≫ f).fiber ((I.subschemeι ≫ f) w'))
        ((I.subschemeι ≫ f).asFiber w') ≤ (k : WithBot ℕ∞) :=
      hsp.mem_open (isOpen_setOf_fiberDimensionAt_le (I.subschemeι ≫ f) k) hwdim
    -- At `ξ'` the local dimension of the fibre of the subscheme is that of the ambient fibre.
    have hfibξ' : f.fiberι (f ξ') (f.asFiber ξ') = ξ' := f.fiberι_asFiber ξ'
    have hmemW' : f.asFiber ξ' ∈ f.fiberι (f ξ') ⁻¹' (I.support : Set X) := by
      rw [Set.mem_preimage, hfibξ']; exact hξ'supp
    have hmaxξ' : ∀ q : f.fiber (f ξ'), q ⤳ f.asFiber ξ' → q = f.asFiber ξ' := by
      intro q hq
      refine (f.fiberι (f ξ')).isEmbedding.injective ?_
      rw [hfibξ']
      refine eq_of_specializes_of_isLocallyPrincipal f hI hgen hξ'supp hξ'max
        ((f.range_fiberι (f ξ')).le ⟨q, rfl⟩) ?_
      have hmap := hq.map (f.fiberι (f ξ')).continuous
      rwa [hfibξ'] at hmap
    have := isLocallyNoetherian_fiber_of_locallyOfFiniteType' f (f ξ')
    obtain ⟨N', hN'open, hξ'N', hN'noeth⟩ :=
      isLocallyNoetherianSpace_of_isLocallyNoetherian (f.fiber (f ξ')) (f.asFiber ξ')
    have hW'closed : IsClosed (f.fiberι (f ξ') ⁻¹' (I.support : Set X)) :=
      I.isClosed_supportSet.preimage (f.fiberι (f ξ')).continuous
    have hlower : (d : WithBot ℕ∞) ≤
        topologicalKrullDimAt ↥(f.fiberι (f ξ') ⁻¹' (I.support : Set X))
          ⟨f.asFiber ξ', hmemW'⟩ := by
      rw [topologicalKrullDimAt_subtype_eq_of_isMax hmaxξ' hN'open hξ'N' hW'closed hmemW',
        ← hd]
      exact topologicalKrullDim_fiber_genericPoint_le f ξ'
    rw [topologicalKrullDimAt_fiber_subscheme_eq f I w'
      (show (I.subschemeι ≫ f) w' = f ξ' by rw [Scheme.Hom.comp_apply, hw'])
      (f.asFiber ξ') (hfibξ'.trans hw'.symm) hmemW'] at hw'dim
    have hdk : d ≤ k := by exact_mod_cast hlower.trans hw'dim
    omega
  exact ⟨closure {ξ},
    closure_singleton_mem_irreducibleComponents_of_forall_specializes hmaxfib,
    specializes_iff_mem_closure.mp hξy,
    hWclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξW)⟩

/-- The pointwise form of `fiber_support_eq_union_irreducibleComponents`: through every point of
the fibre lying in the support of `I` there is an irreducible component of the fibre all of whose
points lie in the support.

This is the content of the equation of supports; the equation itself is an identity between two
sets which are both empty exactly when no point of the support lies over `s`, in which case it
carries no information. The present form exhibits what is asserted at each point of the
support. -/
public theorem exists_mem_irreducibleComponents_subset_fiber_support {X S : Scheme.{u}}
    (f : X ⟶ S) [IrreducibleSpace S] [IrreducibleSpace X] [IsDominant f] [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (hI : IsLocallyPrincipal I)
    (hgeneric : IsEmpty ((I.subschemeι ≫ f).fiber (genericPoint S))) (s : S)
    (hdim : topologicalKrullDim (f.fiber s) ≤
      topologicalKrullDim (f.fiber (genericPoint S)))
    (y : f.fiber s) (hy : f.fiberι s y ∈ (I.support : Set X)) :
    ∃ C ∈ irreducibleComponents (f.fiber s), y ∈ C ∧
      ∀ q ∈ C, f.fiberι s q ∈ (I.support : Set X) := by
  have hmem : y ∈ (f.fiberι s) ⁻¹' (I.support : Set X) := hy
  rw [fiber_support_eq_union_irreducibleComponents f I hI hgeneric s hdim] at hmem
  obtain ⟨C, ⟨hC, hCsub⟩, hyC⟩ := hmem
  exact ⟨C, hC, hyC, fun q hq => hCsub hq⟩

/-- **The conclusion of Stacks 053R is a genuine constraint, not an identity that holds for
every ideal sheaf.** If the fibre over `s` is irreducible and the support of `I` meets it in a
nonempty proper subset, then the equation of
`fiber_support_eq_union_irreducibleComponents` *fails*: an irreducible space has only one
irreducible component, which is not contained in a proper subset, so the union on the right is
empty while the left side is not.

This is the statement that rules out a degenerate reading of the theorem. The configuration it
describes — source `𝔸²`, target `𝔸¹`, projection, `I = (v)` a horizontal divisor and `s` the
origin, where the fibre is `𝔸¹` and the support meets it in the single origin — satisfies every
hypothesis of `fiber_support_eq_union_irreducibleComponents` except `hgeneric`. So `hgeneric`
is load-bearing and the equation is not a tautology. -/
public theorem fiber_support_ne_union_irreducibleComponents_of_irreducibleSpace
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (s : S)
    [IrreducibleSpace (f.fiber s)]
    (hne : ((f.fiberι s) ⁻¹' (I.support : Set X)).Nonempty)
    (hproper : (f.fiberι s) ⁻¹' (I.support : Set X) ≠ Set.univ) :
    (f.fiberι s) ⁻¹' (I.support : Set X) ≠
      ⋃₀ {C : Set (f.fiber s) | C ∈ irreducibleComponents (f.fiber s) ∧
        C ⊆ (f.fiberι s) ⁻¹' (I.support : Set X)} :=
  ne_sUnion_irreducibleComponents_of_ne_univ _ hne hproper

end Stacks.Divisors

end
