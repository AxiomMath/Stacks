module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An irreducible étale neighbourhood of a point over the generic point

Let `Z` be an irreducible locally Noetherian scheme with generic point `η`, let `W → Z` be étale
and let `w ∈ W` lie over `η`. Then `w` has an open neighbourhood `W' ⊆ W` which is irreducible
with generic point `w`.

This is the strengthening of connectedness that the argument of Stacks 09BG needs: that statement
asks for a sheaf on a site whose ambient scheme is *irreducible*, so a trivialising étale
neighbourhood has to be made irreducible before it can be used as such an ambient scheme.
Connectedness does not suffice — a nodal curve has connected étale covers which are reducible.

The proof is topological once two inputs are in place. An étale morphism is locally quasi-finite,
so its fibres are discrete; combined with the fact that the generic point is a generalisation of
every point of `Z`, this says that `w` has no proper generalisation in `W`: a generalisation `v`
of `w` has `f v` inseparable from `η`, hence equal to it, so `v` lies in the same fibre as `w` and
discreteness of the fibre forces `v = w`. A point with no proper generalisation in a Noetherian
quasi-sober space is the generic point of the unique irreducible component through it, and
deleting the finitely many other components leaves an open neighbourhood inside that component.
Noetherianness is only needed near `w`, and is supplied by an affine open neighbourhood: `W` is
locally Noetherian because `W → Z` is locally of finite type.

## Main results

* `Topology.exists_isOpen_subset_closure_singleton_of_noetherianSpace`: in a Noetherian
  quasi-sober space, a point with no proper generalisation has an open neighbourhood contained in
  its closure.
* `Topology.exists_isOpen_subset_closure_singleton_of_noetherian_nhds`: the same conclusion from
  a Noetherian open neighbourhood of the point, rather than a Noetherian ambient space.
* `AlgebraicGeometry.eq_of_specializes_of_etale_of_genericPoint`: a point of an étale scheme over
  an irreducible scheme lying over the generic point has no proper generalisation.
* `AlgebraicGeometry.exists_opens_isGenericPoint_of_etale`: the open irreducible neighbourhood,
  as an open subscheme of `W`.
* `AlgebraicGeometry.exists_opens_contains_isGenericPoint_of_etale`: the same neighbourhood
  together with the size witness that makes it an object of a big étale site containing `W`.

## Implementation notes

The neighbourhood is returned as a `AlgebraicGeometry.Scheme.Opens` of `W`, with irreducibility
and the generic-point property stated for its underlying space; this is the form Stacks 09BG
consumes, whose hypothesis is literally `IsGenericPoint η Set.univ` for the ambient scheme. The
size witness is `AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit` applied to the open
immersion of the neighbourhood, which is a monomorphism.

## References

* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace Topology

/-- An open subset contained in the closure of one of its points has that point as a generic
point. -/
public theorem isGenericPoint_univ_subtype {α : Type*} [TopologicalSpace α] {U : Set α}
    (hU : IsOpen U) {x : α} (hxU : x ∈ U) (hUx : U ⊆ closure {x}) :
    IsGenericPoint (⟨x, hxU⟩ : U) Set.univ := by
  have hmap : (Subtype.val : U → α) ⁻¹' closure {x} =
      closure ((Subtype.val : U → α) ⁻¹' {x}) :=
    hU.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val _
  have hpre : (Subtype.val : U → α) ⁻¹' {x} = {(⟨x, hxU⟩ : U)} := by
    ext z
    simp [Subtype.ext_iff]
  rw [isGenericPoint_def, ← hpre, ← hmap, Set.eq_univ_iff_forall]
  exact fun z => hUx z.2

/-- **A point with no proper generalisation in a Noetherian quasi-sober space has an open
neighbourhood contained in its closure.** Such a point is the generic point of every irreducible
component through it, hence of exactly one component, and a Noetherian space has only finitely
many components, so deleting the others leaves an open set between the point and its closure.
This is Stacks 0052 (3) for the component through `x`, with the extra information that `x` itself
lies in the open set. -/
@[sga "1 IV 6.3" "special case"]
public theorem exists_isOpen_subset_closure_singleton_of_noetherianSpace {α : Type*}
    [TopologicalSpace α] [NoetherianSpace α] [QuasiSober α] {x : α}
    (hx : ∀ y : α, y ⤳ x → y = x) :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ⊆ closure {x} := by
  have hfin : (irreducibleComponents α).Finite := NoetherianSpace.finite_irreducibleComponents
  have key : ∀ Z ∈ irreducibleComponents α, x ∈ Z → Z = closure {x} := by
    intro Z hZ hxZ
    obtain ⟨z, hz⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
    rw [← hz.def, hx z (hz.specializes hxZ)]
  have hmem : closure ({x} : Set α) ∈ irreducibleComponents α := by
    rw [← key _ (irreducibleComponent_mem_irreducibleComponents x) mem_irreducibleComponent]
    exact irreducibleComponent_mem_irreducibleComponents x
  refine ⟨(⋃₀ (irreducibleComponents α \ {closure ({x} : Set α)}))ᶜ, ?_, ?_, ?_⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  · rintro ⟨Z, hZ, hxZ⟩
    exact hZ.2 (key Z hZ.1 hxZ)
  · exact subset_closure.trans
      (closure_sUnion_irreducibleComponents_sdiff_singleton hfin _ hmem).le

/-- **A point with no proper generalisation and a Noetherian open neighbourhood has an open
neighbourhood contained in its closure.** This is the local form of
`Topology.exists_isOpen_subset_closure_singleton_of_noetherianSpace`: the hypothesis is only that
*some* open neighbourhood of the point is a Noetherian space, which is what a locally Noetherian
scheme provides. -/
public theorem exists_isOpen_subset_closure_singleton_of_noetherian_nhds {α : Type*}
    [TopologicalSpace α] [QuasiSober α] {x : α} (hx : ∀ y : α, y ⤳ x → y = x) {V : Set α}
    (hV : IsOpen V) (hxV : x ∈ V) [NoetherianSpace V] :
    ∃ U : Set α, IsOpen U ∧ x ∈ U ∧ U ⊆ closure {x} := by
  have : QuasiSober V := hV.isOpenEmbedding_subtypeVal.quasiSober
  have hx' : ∀ y : V, y ⤳ (⟨x, hxV⟩ : V) → y = ⟨x, hxV⟩ := fun y hy =>
    Subtype.ext (hx y.1 ((subtype_specializes_iff _ _).1 hy))
  obtain ⟨U, hUopen, hxU, hUsub⟩ :=
    exists_isOpen_subset_closure_singleton_of_noetherianSpace hx'
  refine ⟨Subtype.val '' U, hV.isOpenEmbedding_subtypeVal.isOpenMap _ hUopen, ⟨_, hxU, rfl⟩, ?_⟩
  calc Subtype.val '' U ⊆ Subtype.val '' closure {(⟨x, hxV⟩ : V)} := Set.image_mono hUsub
    _ ⊆ closure (Subtype.val '' {(⟨x, hxV⟩ : V)}) :=
        image_closure_subset_closure_image continuous_subtype_val
    _ = closure {x} := by rw [Set.image_singleton]

end Topology

namespace AlgebraicGeometry

/-- **A point of an étale scheme over an irreducible scheme lying over the generic point has no
proper generalisation.** A generalisation `v` of `w` maps to a generalisation of the generic
point, which is itself a generalisation of every point, so `v` and `w` lie in one fibre; an étale
morphism is locally quasi-finite, so that fibre is discrete and `v = w`. -/
public theorem eq_of_specializes_of_etale_of_genericPoint {W Z : Scheme.{u}} (f : W ⟶ Z) [Etale f]
    [IrreducibleSpace Z] {w : W} (hw : f.base w = genericPoint Z) (v : W) (hv : v ⤳ w) : v = w := by
  have hqf := locallyQuasiFinite_of_etale f
  have : LocallyOfFiniteType f := hqf.1
  have : LocallyQuasiFinite f := hqf.2
  have hd := f.isDiscrete_preimage_singleton (f.base w)
  have himg : f.base v = f.base w :=
    (Specializes.antisymm (hv.map f.continuous) (by rw [hw]; exact genericPoint_specializes _)).eq
  exact hd.eq_of_specializes hv (by simpa using himg) (by simp)

/-- **An irreducible open étale neighbourhood of a point over the generic point.** For `W → Z`
étale with `Z` irreducible and locally Noetherian, a point `w` of `W` lying over the generic point
of `Z` has an open neighbourhood in `W` which is irreducible with generic point `w`. -/
public theorem exists_opens_isGenericPoint_of_etale {W Z : Scheme.{u}} (f : W ⟶ Z) [Etale f]
    [IrreducibleSpace Z] [IsLocallyNoetherian Z] {w : W} (hw : f.base w = genericPoint Z) :
    ∃ (W' : W.Opens) (hw' : w ∈ W'), IrreducibleSpace W' ∧
      IsGenericPoint (⟨w, hw'⟩ : W') Set.univ := by
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hV, hwV, -⟩ := exists_isAffineOpen_mem_and_subset (X := W) (U := ⊤) (x := w) (by simp)
  have : IsNoetherianRing Γ(W, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hVnoeth : NoetherianSpace (V : Set W) := noetherianSpace_of_isAffineOpen V hV
  obtain ⟨U, hUopen, hwU, hUsub⟩ :=
    Topology.exists_isOpen_subset_closure_singleton_of_noetherian_nhds
      (fun v hv => eq_of_specializes_of_etale_of_genericPoint f hw v hv) V.2 hwV
  have hgen := Topology.isGenericPoint_univ_subtype hUopen hwU hUsub
  exact ⟨⟨U, hUopen⟩, hwU, (irreducibleSpace_def _).2 (Set.top_eq_univ ▸ hgen.isIrreducible), hgen⟩

/-- **The irreducible open étale neighbourhood is an object of a big étale site containing `W`.**
The neighbourhood of `AlgebraicGeometry.exists_opens_isGenericPoint_of_etale` is an open subscheme
of `W`, so its structure morphism to `W` is a monomorphism; the size cutoff of a big étale site is
closed under powersets, so the neighbourhood again lies below the cutoff. -/
public theorem exists_opens_contains_isGenericPoint_of_etale (B : BigEtaleSite.{u})
    {W Z : Scheme.{u}} (hW : B.Contains W) (f : W ⟶ Z) [Etale f] [IrreducibleSpace Z]
    [IsLocallyNoetherian Z] {w : W} (hw : f.base w = genericPoint Z) :
    ∃ (W' : W.Opens) (hw' : w ∈ W'), B.Contains W'.toScheme ∧ IrreducibleSpace W' ∧
      IsGenericPoint (⟨w, hw'⟩ : W') Set.univ := by
  obtain ⟨W', hw', hirr, hgen⟩ := exists_opens_isGenericPoint_of_etale f hw
  exact ⟨W', hw', Scheme.size_lt_of_mono_of_isStrongPrelimit B.cutoff_isStrongPrelimit W'.ι hW,
    hirr, hgen⟩

end AlgebraicGeometry

end
