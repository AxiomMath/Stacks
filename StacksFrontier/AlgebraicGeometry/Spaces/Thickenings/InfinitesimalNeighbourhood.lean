module

public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Thickenings.InfinitesimalTower

/-!
# Infinitesimal neighbourhoods of a closed subspace of an algebraic space

Let `X` be an algebraic space over a scheme `S`, let `φ : U ⟶ X` be a surjective étale chart,
and let `J ⊆ 𝒪_U` be a sheaf of ideals on the *scheme* `U` which is invariant under the
relation `R = U ×_X U`, so that `V(J) ⊆ U` descends to a closed subspace `Z ⊆ X`. The *`n`th
order infinitesimal neighbourhood* of `Z` in `X` is the closed subspace of `X` cut out on the
chart by `J ^ (n + 1)`, and the *first order* neighbourhood is the case `n = 1`.

## Main definitions

* `AlgebraicGeometry.Space.IsInvariantIdealSheaf` is invariance of a sheaf of ideals on a chart
  under the relation presented by that chart, as an equality of its two inverse images.
* `AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood` is the `n`th order infinitesimal
  neighbourhood of the closed subspace cut out by an invariant sheaf of ideals on a chart.
* `AlgebraicGeometry.Space.firstOrderInfinitesimalNeighbourhood` is the case `n = 1`.

## Main results

* `Stacks.IdealSheaf.ker_inclusion_pow_succ_eq_bot` and
  `Stacks.IdealSheaf.isNthOrderThickening_inclusion`: on a scheme, `V(I) ⊆ V(I ^ (n + 1))` is an
  `n`th order thickening.
* `AlgebraicGeometry.Space.isInvariantIdealSheaf_pow`: a power of an invariant sheaf of ideals
  is invariant.
* `AlgebraicGeometry.Space.isClosedSubspace_nthOrderInfinitesimalNeighbourhood`: the `n`th order
  infinitesimal neighbourhood is a closed subspace of `X`.
* `AlgebraicGeometry.Space.definingIdealAt_nthOrderInfinitesimalNeighbourhood`: its defining
  ideal, at any étale chart lying over the given one, is cut out by the inverse image of
  `J ^ (n + 1)`.
* `AlgebraicGeometry.Space.le_nthOrderInfinitesimalNeighbourhood`: the closed subspace is
  contained in each of its infinitesimal neighbourhoods,
  `AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood_zero`: the zeroth is the subspace
  itself, and `AlgebraicGeometry.Space.nthOrderInfinitesimalNeighbourhood_mono`: the
  neighbourhoods grow with their order.

## References

* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.IdealSheaf

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A positive power of a sheaf of ideals is contained in it. -/
theorem pow_succ_le_self (I : X.IdealSheafData) (n : ℕ) : I ^ (n + 1) ≤ I :=
  Scheme.IdealSheafData.le_def.mpr fun _ ↦ Ideal.pow_le_self (by simp)

/-- The kernel ideal sheaf of the inclusion `V(I) ⟶ V(K)` of subschemes attached to `K ≤ I`
pushes forward along `V(K) ⟶ X` to `I`. -/
theorem ker_inclusion_map {K I : X.IdealSheafData} (h : K ≤ I) :
    (Scheme.IdealSheafData.inclusion h).ker.map K.subschemeι = I := by
  rw [← Scheme.Hom.ker_comp, Scheme.IdealSheafData.inclusion_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι]

/-- The inclusion `V(I) ⟶ V(K)` of subschemes attached to `K ≤ I` is a closed immersion. -/
theorem isClosedImmersion_inclusion {K I : X.IdealSheafData} (h : K ≤ I) :
    IsClosedImmersion (Scheme.IdealSheafData.inclusion h) := by
  have hcomp : IsClosedImmersion (Scheme.IdealSheafData.inclusion h ≫ K.subschemeι) := by
    rw [Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (Scheme.IdealSheafData.inclusion h) K.subschemeι

/-- The `(n + 1)`st power of the kernel ideal sheaf of the inclusion `V(I) ⟶ V(I ^ (n + 1))`
vanishes. -/
theorem ker_inclusion_pow_succ_eq_bot (I : X.IdealSheafData) (n : ℕ) :
    (Scheme.IdealSheafData.inclusion (pow_succ_le_self I n)).ker ^ (n + 1) = ⊥ := by
  set c := Scheme.IdealSheafData.inclusion (pow_succ_le_self I n)
  set p := (I ^ (n + 1)).subschemeι
  have hker : c.ker.map p = I := ker_inclusion_map (pow_succ_le_self I n)
  have hpow : I ^ (n + 1) = p.ker := (Scheme.IdealSheafData.ker_subschemeι _).symm
  have _ : IsClosedImmersion c := isClosedImmersion_inclusion (pow_succ_le_self I n)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun V : X.affineOpens ↦ (⟨p ⁻¹ᵁ V.1, V.2.preimage p⟩ : (I ^ (n + 1)).subscheme.affineOpens))
    (by simpa using congrArg (fun V : X.Opens ↦ p ⁻¹ᵁ V) (iSup_affineOpens_eq_top X))
    fun V ↦ ?_
  show (c.ker ^ (n + 1)).ideal ⟨p ⁻¹ᵁ V.1, V.2.preimage p⟩ = ⊥
  have hKloc : I.ideal V = (c.ker.ideal ⟨p ⁻¹ᵁ V.1, V.2.preimage p⟩).comap (p.app V).hom :=
    (congrArg (fun K : X.IdealSheafData ↦ K.ideal V) hker).symm.trans
      (Scheme.IdealSheafData.ideal_map (I := c.ker) p V (V.2.preimage p))
  have hpV : p.ker.ideal V = RingHom.ker (p.app V).hom := by
    simp [Scheme.Hom.ker_apply]
  have hpowV : I.ideal V ^ (n + 1) = RingHom.ker (p.app V).hom := by
    simpa [Scheme.IdealSheafData.ideal_pow, hpV] using
      congrArg (fun K : X.IdealSheafData ↦ K.ideal V) hpow
  have hsurj := (I ^ (n + 1)).subschemeι_app_surjective V
  have hnil : c.ker.ideal ⟨p ⁻¹ᵁ V.1, V.2.preimage p⟩ ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_comap_of_surjective (p.app V).hom hsurj
      (c.ker.ideal ⟨p ⁻¹ᵁ V.1, V.2.preimage p⟩), ← Ideal.map_pow, ← hKloc, hpowV,
      RingHom.ker_eq_comap_bot, Ideal.map_comap_of_surjective (p.app V).hom hsurj]
  simpa [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using hnil

/-- The subscheme of a sheaf of ideals is an `n`th order thickening inside the subscheme of its
`(n + 1)`st power. -/
@[stacks 05ZV "the order asserted by the definition, read on an étale chart"]
theorem isNthOrderThickening_inclusion (I : X.IdealSheafData) (n : ℕ) :
    _root_.Stacks.Thickenings.IsNthOrderThickening n
      (Scheme.IdealSheafData.inclusion (pow_succ_le_self I n)) :=
  ⟨isClosedImmersion_inclusion _, ker_inclusion_pow_succ_eq_bot I n⟩

/-- The subscheme of a sheaf of ideals is a first order thickening inside the subscheme of its
square. -/
theorem isFirstOrderThickening_inclusion (I : X.IdealSheafData) :
    _root_.Stacks.Thickenings.IsFirstOrderThickening
      (Scheme.IdealSheafData.inclusion (pow_succ_le_self I 1)) :=
  isNthOrderThickening_inclusion I 1

end Stacks.IdealSheaf

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Invariance

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

/-- A sheaf of ideals on a chart `U` of `X` is *invariant* when its two scheme-theoretic
inverse images along the legs of the relation `R = U ×_X U` agree. -/
abbrev IsInvariantIdealSheaf (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) :
    Prop :=
  J.comap ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)) =
    J.comap ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs))

/-- An invariant sheaf of ideals cuts out an invariant subscheme of the chart. -/
theorem isInvariantSubscheme_of_isInvariantIdealSheaf
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J) :
    IsInvariantSubscheme B S hS hs (Subobject.mk J.subschemeι) := by
  rw [IsInvariantSubscheme, Scheme.IdealSheafData.pullback_subobject_mk_subschemeι,
    Scheme.IdealSheafData.pullback_subobject_mk_subschemeι, hJ]

/-- A power of an invariant sheaf of ideals is invariant. -/
theorem isInvariantIdealSheaf_pow
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J) (n : ℕ) :
    IsInvariantIdealSheaf B S hS hs (J ^ n) := by
  rw [IsInvariantIdealSheaf, Stacks.IdealSheaf.comap_pow, Stacks.IdealSheaf.comap_pow, hJ]

end Invariance

/-! ### The infinitesimal neighbourhoods -/

section Neighbourhood

variable {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X.1}

/-- The `n`th order infinitesimal neighbourhood of the closed subspace cut out by a sheaf of
ideals `J` on a chart `φ : U ⟶ X`: the subspace of `X` cut out on that chart by `J ^ (n + 1)`. -/
@[stacks 05ZV "part (2); the ideal of `Z` is given on an étale chart, 03MB being unavailable"]
def nthOrderInfinitesimalNeighbourhood (φ : yoneda.obj U ⟶ X.1)
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) (n : ℕ) : Subfunctor X.1 :=
  invariantSubspace B S hS φ (Subobject.mk (J ^ (n + 1)).subschemeι)

/-- The first order infinitesimal neighbourhood of the closed subspace cut out by a sheaf of
ideals on a chart: the subspace cut out there by the square of that sheaf of ideals. -/
@[stacks 05ZV "part (1); the ideal of `Z` is given on an étale chart, 03MB being unavailable"]
abbrev firstOrderInfinitesimalNeighbourhood (φ : yoneda.obj U ⟶ X.1)
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) : Subfunctor X.1 :=
  nthOrderInfinitesimalNeighbourhood B S hS φ J 1

/-- The zeroth order infinitesimal neighbourhood of a closed subspace is that subspace. -/
theorem nthOrderInfinitesimalNeighbourhood_zero
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) :
    nthOrderInfinitesimalNeighbourhood B S hS φ J 0 =
      invariantSubspace B S hS φ (Subobject.mk J.subschemeι) :=
  congrArg
    (fun K : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData =>
      invariantSubspace B S hS φ (Subobject.mk K.subschemeι)) (pow_one J)

/-- The invariant subspace attached to a sheaf of ideals shrinks when the ideal sheaf grows. -/
private theorem invariantSubspace_subschemeι_le_of_le
    {K I : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData} (h : K ≤ I) :
    invariantSubspace B S hS φ (Subobject.mk I.subschemeι) ≤
      invariantSubspace B S hS φ (Subobject.mk K.subschemeι) :=
  invariantSubspace_mono B S hS φ _ _
    (Subobject.mk_le_mk_of_comm (Scheme.IdealSheafData.inclusion h)
      (Scheme.IdealSheafData.inclusion_subschemeι _))

/-- A closed subspace is contained in each of its infinitesimal neighbourhoods. -/
theorem le_nthOrderInfinitesimalNeighbourhood
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) (n : ℕ) :
    invariantSubspace B S hS φ (Subobject.mk J.subschemeι) ≤
      nthOrderInfinitesimalNeighbourhood B S hS φ J n :=
  invariantSubspace_subschemeι_le_of_le B S hS (Stacks.IdealSheaf.pow_succ_le_self J n)

/-- The infinitesimal neighbourhoods of a closed subspace grow with their order. -/
theorem nthOrderInfinitesimalNeighbourhood_mono
    (J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData) {m n : ℕ} (h : m ≤ n) :
    nthOrderInfinitesimalNeighbourhood B S hS φ J m ≤
      nthOrderInfinitesimalNeighbourhood B S hS φ J n :=
  invariantSubspace_subschemeι_le_of_le B S hS
    (Stacks.Thickenings.idealSheaf_pow_le_pow_right (I := J) (Nat.succ_le_succ h))

variable (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- The `n`th order infinitesimal neighbourhood of the closed subspace cut out by an invariant
sheaf of ideals is a closed subspace of `X`. -/
theorem isClosedSubspace_nthOrderInfinitesimalNeighbourhood
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J) (n : ℕ) :
    IsClosedSubspace B S hS (nthOrderInfinitesimalNeighbourhood B S hS φ J n) :=
  isClosedSubspace_invariantSubspace_subschemeι B S hS X hs he (J ^ (n + 1))
    (isInvariantSubscheme_of_isInvariantIdealSheaf B S hS hs
      (isInvariantIdealSheaf_pow B S hS hs hJ (n + 1)))

include hs he in
/-- The defining ideal of the `n`th order infinitesimal neighbourhood, at an étale chart `A` of
`X` lying over the given chart, is the ideal of global functions cut out by the inverse image of
`J ^ (n + 1)` along `A ⟶ U`. -/
theorem definingIdealAt_nthOrderInfinitesimalNeighbourhood
    {J : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData}
    (hJ : IsInvariantIdealSheaf B S hS hs J) (n : ℕ)
    (hZ : IsClosedSubspace B S hS (nthOrderInfinitesimalNeighbourhood B S hS φ J n))
    (A : SmallEtale B S hS X.1)
    (m : A ⟶ (⟨CostructuredArrow.mk φ, he⟩ : SmallEtale B S hS X.1)) :
    definingIdealAt B S hS X
        ⟨nthOrderInfinitesimalNeighbourhood B S hS φ J n, hZ⟩ (op A) =
      RingHom.ker (((J ^ (n + 1)).comap ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS X.1).map m))).subschemeι.appTop).hom :=
  definingIdealAt_invariantSubspace_subschemeι B S hS X hs he (J ^ (n + 1))
    (isInvariantSubscheme_of_isInvariantIdealSheaf B S hS hs
      (isInvariantIdealSheaf_pow B S hS hs hJ (n + 1))) hZ A m

end Neighbourhood

end AlgebraicGeometry.Space

end
