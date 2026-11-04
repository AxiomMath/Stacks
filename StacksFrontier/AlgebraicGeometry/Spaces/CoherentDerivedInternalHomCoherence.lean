module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedInternalHom

/-! # Coherence of the cohomology of a complex of coherent modules on an algebraic space

Let `X` be an algebraic space over a scheme `S`. The coherent `𝒪_X`-modules on the small étale
site of `X` are stable under kernels and cokernels (Stacks 01BY(3)), hence under passing to the
cohomology of a complex: if every term of a complex of `𝒪_X`-modules is coherent, so is every
one of its cohomology modules.

The cokernel clause of Stacks 01BY(3) on a site is available only when the module universe is
the universe of the sections of the sheaf of rings, and the internal Hom complex of Stacks 0A8Z
raises the module universe of the small étale site of `X` above that of its structure sheaf.
This file reproves the cokernel clause with the two universes independent, which is what makes
the statement about cohomology available at the module universe in which `RSheafHom(K, L)` is
formed.

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_cokernel'`: **Stacks 01BY(3) for cokernels on a site,
  with the module universe independent of the universe of the sections of the sheaf of rings.**
* `Stacks.SheafOfModules.isCoherentOnSite_cycles` and
  `Stacks.SheafOfModules.isCoherentOnSite_homology`: **the cocycles and the cohomology of a
  cochain complex of coherent sheaves of modules on a site are coherent.**
* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_forall_isCoherentOnSite`: the same for
  `𝒪_X`-modules on the small étale site of an algebraic space, at the module universe
  `max (u + 1) m` in which the internal Hom complex of two complexes of `𝒪_X`-modules with
  sections in `max (u + 1) m` is formed.
* `AlgebraicGeometry.Space.isCoherentOnSite_homology_of_forall_affine_restrict_terms`: the same
  from coherence of the terms of the restrictions of the complex to the affine étale charts
  only.

## Implementation notes

**The coherent clause of Stacks 0D0S is not proved here and no `@[stacks 0D0S]` attribute is
carried**; it is
`AlgebraicGeometry.Space.derivedCategoryBPlus_isCoherentOnSite_sheafHomComplex` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedInternalHomCoherentCohomology`, at the
module universe of the structure rings. The tag asserts that `RSheafHom(K, L)` lies in
`D⁺_Coh(𝒪_X)` for `K` in `D⁻_Coh` and `L` in `D⁺_Coh`; the `D⁺` clause is
`AlgebraicGeometry.Space.isBoundedBelow_derivedSheafHomOnSpace`. Read on models, as that clause
reads it, the coherent clause is coherence of the cohomology modules of `SheafHom(A, J)` for `A` a
model of `K` and `J` a K-injective model of `L`. The statements below reduce that to coherence
of the *terms* of `SheafHom(A, J)`, and those terms are not coherent: in degree `n` the term is
the product over `p + n = q` of `SheafHom(A^p, J^q)` (Stacks 0A8X), and the terms `J^q` of a
K-injective complex are injective, not coherent. Turning `L` into a complex with coherent terms
is not a formal manoeuvre — the correct argument instead replaces `A` locally by a bounded
complex of finite free modules and filters `SheafHom(A, J)` by the brutal truncations of `A`,
whose graded pieces are shifts of finite products of `J` and so have coherent cohomology.

The constructions that a proof of the coherent clause along the route reduced to here would
still be missing are:

* a local finite free model for a bounded-above complex with coherent cohomology, that is
  existence étale-locally of a quasi-isomorphism `E → A` with `E` bounded above and degreewise a
  finite coproduct of copies of the structure sheaf. Nothing of this kind is stated for an
  algebraic space;
* the brutal truncation filtration of the internal Hom complex in its first variable, together
  with the long exact cohomology sequences it produces. Only the degreewise description of
  `AlgebraicGeometry.RingedSite.sheafHomComplex` (Stacks 0A8X) is available;
* quasi-coherence of the cohomology of the internal Hom complex, clause (6) of Stacks 03M1,
  whose state is recorded in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartLocal`. It is needed by the
  route through finiteness of the sections over an affine chart, because
  `AlgebraicGeometry.Space.moduleFinite_sections_of_isFiniteType` asks for the base change
  property `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` and the only source of that
  property is quasi-coherence, by
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`.

**That route is also closed by a universe constraint which no instantiation removes.** The small
étale ringed site of an algebraic space over `Scheme.{u}` is
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects lie in `Type (u + 1)` and the sections
of its structure sheaf in `Type u`. The internal Hom complex of Stacks 0A8Z carries module
universe `m` to `max (u + 1) m`, so `SheafHom(A, J)` lies in the same category as `A` and `J`
only when `m = max (u + 1) m`, which forces `u + 1 ≤ m`. Both
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and
`AlgebraicGeometry.Space.moduleFinite_sections_of_isCoherent` are stated at module universe `u`,
and `u < m` leaves no instantiation of either universe at which the two conditions meet. The
same constraint, for the same reason, is what obstructs
`AlgebraicGeometry.Space.isCoherent_iff_isCoherentOnSite`; coherence is therefore read
throughout as `SheafOfModules.IsCoherentOnSite`, coherence on the site (Stacks 01BW), as in
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedInternalHom`.

The universe of the module sections is kept independent of the universe of the sections of the
sheaf of rings in the general statements below. For the closure of coherence under kernels
(`Stacks.SheafOfModules.isCoherentOnSite_kernel`) and under isomorphism that independence is
already available; for cokernels it is not, because
`Stacks.SheafOfModules.isCoherentOnSite_cokernel` and the three statements it rests on are
stated with the two universes equal. The reproofs are the same arguments: the relations clause
is `Stacks.SheafOfModules.isFiniteType_relations_of_lift`, which already leaves the module
universe free, and the only genuine requirement is that sheaves of modules with sections in the
module universe form an abelian category and that their epimorphisms be the locally surjective
maps, which is exactly what the two sheafification hypotheses supply.

## References

* [Stacks Project, Tag 0D0S](https://stacks.math.columbia.edu/tag/0D0S)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-! ### Cokernels of maps of coherent sheaves of modules, at an independent module universe -/

/-- An epimorphism of sheaves of modules is locally surjective on underlying presheaves.

This is `Stacks.SheafOfModules.LocalCokernel.locallySurjective_of_epi` with the universe of the
module sections independent of the universe of the sections of the sheaf of rings. -/
public theorem locallySurjective_val_of_epi {M N : SheafOfModules.{m} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
  have h := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat
    ((SheafOfModules.toSheaf R).map f)).mpr inferInstance
  exact (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff
    ((SheafOfModules.toSheaf R).map f)).mp h

/-- An epimorphism of sheaves of modules is surjective on sections after restriction to the
members of a covering sieve, namely the image sieve of the section.

This is `Stacks.SheafOfModules.exists_cover_preimage_of_epi` with the universe of the module
sections independent of the universe of the sections of the sheaf of rings. -/
public theorem exists_cover_preimage_of_epi' {M N : SheafOfModules.{m} R} (f : M ⟶ N) [Epi f]
    (V : C) (x : N.val.obj (op V)) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), T g →
      ∃ y : M.val.obj (op W), f.val.app (op W) y = N.val.restrictₛₗ g.op x := by
  have hls : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map f.val) := locallySurjective_val_of_epi f
  refine ⟨Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map f.val)
    (show ((PresheafOfModules.toPresheaf R.obj).obj N.val).obj (op V) from x),
    Presheaf.imageSieve_mem J _ _, ?_⟩
  intro W g hg
  obtain ⟨y, hy⟩ := hg
  exact ⟨y, hy⟩

/-- The underlying presheaf of modules of a cokernel is of finite type as soon as that of the
target is.

This is `Stacks.SheafOfModules.isFiniteType_presheaf_cokernel` with the universe of the module
sections independent of the universe of the sections of the sheaf of rings. -/
public theorem isFiniteType_presheaf_cokernel' {M N : SheafOfModules.{m} R} (φ : M ⟶ N)
    (hN : PresheafOfModules.IsFiniteType J N.val) :
    PresheafOfModules.IsFiniteType J (cokernel φ).val :=
  isFiniteType_of_locallySurjective (cokernel.π φ).val
    (exists_cover_preimage_of_epi' (cokernel.π φ)) hN

/-- The kernel of the projection onto a cokernel — that is, the image of the map — is of finite
type as soon as the source is.

This is `Stacks.SheafOfModules.isFiniteType_kerObj_cokernelπ` with the universe of the module
sections independent of the universe of the sections of the sheaf of rings. -/
public theorem isFiniteType_kerObj_cokernelπ' {M N : SheafOfModules.{m} R} (φ : M ⟶ N)
    (hM : PresheafOfModules.IsFiniteType J M.val) :
    PresheafOfModules.IsFiniteType J (_root_.SheafOfModules.kerObj (cokernel.π φ)).val := by
  let e : _root_.SheafOfModules.kerObj (cokernel.π φ) ≅ kernel (cokernel.π φ) :=
    (_root_.SheafOfModules.kerIsLimit (cokernel.π φ)).conePointUniqueUpToIso
      (limit.isLimit (parallelPair (cokernel.π φ) 0))
  have hι : e.hom ≫ kernel.ι (cokernel.π φ) = _root_.SheafOfModules.kerIota (cokernel.π φ) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hfac : _root_.SheafOfModules.kerLift φ (cokernel.condition φ) ≫ e.hom
      = Abelian.factorThruImage φ := by
    rw [← cancel_mono (kernel.ι (cokernel.π φ)), Category.assoc, hι,
      _root_.SheafOfModules.kerLift_comp, kernel.lift_ι]
  have hepi : Epi (_root_.SheafOfModules.kerLift φ (cokernel.condition φ)) := by
    have h1 : _root_.SheafOfModules.kerLift φ (cokernel.condition φ)
        = Abelian.factorThruImage φ ≫ e.inv := by
      rw [← hfac, Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [h1]
    infer_instance
  exact isFiniteType_of_locallySurjective
    (_root_.SheafOfModules.kerLift φ (cokernel.condition φ)).val
    (exists_cover_preimage_of_epi' (_root_.SheafOfModules.kerLift φ (cokernel.condition φ))) hM

/-- **Stacks 01BY(3) for cokernels on a site, at an independent module universe.** The cokernel
of a map of coherent sheaves of modules is coherent.

This is `Stacks.SheafOfModules.isCoherentOnSite_cokernel` with the universe of the module
sections independent of the universe of the sections of the sheaf of rings. -/
public theorem isCoherentOnSite_cokernel' {M N : SheafOfModules.{m} R} (φ : M ⟶ N)
    (hM : _root_.SheafOfModules.IsCoherentOnSite M)
    (hN : _root_.SheafOfModules.IsCoherentOnSite N) :
    _root_.SheafOfModules.IsCoherentOnSite (cokernel φ) := by
  classical
  refine ⟨isFiniteType_presheaf_cokernel' φ hN.isFiniteType, ?_⟩
  intro U n t
  choose Tl hTl hTlift using fun j : Fin n ↦
    exists_cover_preimage_of_epi' (cokernel.π φ) U (t j)
  obtain ⟨I, A, hA, hgenL⟩ :=
    (isFiniteType_kerObj_cokernelπ' φ hM.isFiniteType).exists_generators
  have hS1 : (Finset.univ.inf Tl) ∈ J U := by
    have hfin : ∀ s : Finset (Fin n), s.inf Tl ∈ J U := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        simpa [Finset.inf_insert, hi] using J.intersection_covering (hTl i) ih
    exact hfin Finset.univ
  refine isFiniteType_relations_of_cover _ t (J.intersection_covering hS1 (hA U)) ?_
  intro V g hg
  have hlift : ∀ j : Fin n, ∃ y : N.val.obj (op V),
      (cokernel.π φ).val.app (op V) y = (cokernel φ).val.restrictₛₗ g.op (t j) := by
    intro j
    have hle : Finset.univ.inf Tl ≤ Tl j := Finset.inf_le (Finset.mem_univ j)
    exact hTlift j V g (hle _ hg.1)
  choose t' ht' using hlift
  obtain ⟨i, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff A g).mp hg.2
  obtain ⟨q, l, hl⟩ := hgenL i
  exact isFiniteType_relations_of_lift (cokernel.π φ).val
    (_root_.SheafOfModules.kerSubmodule (cokernel.π φ)).toSubmodule
    (_root_.SheafOfModules.mem_kerSubmodule (cokernel.π φ))
    _ t' ht'
    (fun k ↦ (_root_.SheafOfModules.kerObj (cokernel.π φ)).val.restrictₛₗ a.op (l k))
    (generates_restrict a l hl) hN.kernel_isFiniteType

/-! ### Cohomology of a complex of coherent sheaves of modules -/

/-- **The cocycles of a cochain complex of coherent sheaves of modules on a site are coherent.**
In degree `n` they are the kernel of the differential `Mⁿ ⟶ Mⁿ⁺¹`, so this is the kernel clause
of Stacks 01BY(3). -/
public theorem isCoherentOnSite_cycles (M : CochainComplex (SheafOfModules.{m} R) ℤ)
    (h : ∀ i, _root_.SheafOfModules.IsCoherentOnSite (M.X i)) (n : ℤ) :
    _root_.SheafOfModules.IsCoherentOnSite (M.cycles n) :=
  isCoherentOnSite_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel (M.d n (n + 1)))
      (M.cyclesIsKernel n (n + 1) (CochainComplex.next ℤ n)))
    (isCoherentOnSite_kernel (h n) (h (n + 1)) (M.d n (n + 1)))

/-- **The cohomology of a cochain complex of coherent sheaves of modules on a site is
coherent.** In degree `n` it is the cokernel of the map `Mⁿ⁻¹ ⟶ Zⁿ` to the cocycles, so this is
the cokernel clause of Stacks 01BY(3) applied to two coherent sheaves, the second of them
coherent by `Stacks.SheafOfModules.isCoherentOnSite_cycles`. -/
public theorem isCoherentOnSite_homology (M : CochainComplex (SheafOfModules.{m} R) ℤ)
    (h : ∀ i, _root_.SheafOfModules.IsCoherentOnSite (M.X i)) (n : ℤ) :
    _root_.SheafOfModules.IsCoherentOnSite (M.homology n) :=
  isCoherentOnSite_of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (M.toCycles (n - 1) n))
      (M.homologyIsCokernel (n - 1) n (CochainComplex.prev ℤ n)))
    (isCoherentOnSite_cokernel' (M.toCycles (n - 1) n) (h (n - 1))
      (isCoherentOnSite_cycles M h n))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

-- Sheafification of presheaves of abelian groups with sections in `max (u + 1) m`, and the
-- identification of the morphisms it inverts, on the small étale site: these make
-- `𝒪_X`-modules with sections in that universe an abelian category.
attribute [local instance] hasSheafify_smallEtaleRingedSite
  wEqualsLocallyBijective_smallEtaleRingedSite hasSheafify_smallEtaleRingedSite_over
  wEqualsLocallyBijective_smallEtaleRingedSite_over

/-- **The cohomology of a complex of coherent `𝒪_X`-modules on an algebraic space is coherent**,
at the module universe `max (u + 1) m` in which the internal Hom complex of two complexes of
`𝒪_X`-modules with sections in `max (u + 1) m` is formed.

Coherence is coherence on the small étale site (Stacks 01BW); see the implementation notes for
why the module universe admits no other reading. -/
public theorem isCoherentOnSite_homology_of_forall_isCoherentOnSite
    (M : CochainComplex (Modules.{u, max (u + 1) m} B S hS F hF) ℤ)
    (h : ∀ i, SheafOfModules.IsCoherentOnSite (M.X i)) (n : ℤ) :
    SheafOfModules.IsCoherentOnSite (M.homology n) :=
  Stacks.SheafOfModules.isCoherentOnSite_homology M h n

/-- **Coherence of the cohomology of a complex of `𝒪_X`-modules follows from coherence of the
terms of its restrictions to the affine étale charts.** If the restriction of `M` to the slice
at every affine étale chart has coherent terms, then every cohomology module of `M` is
coherent.

This is strictly weaker a hypothesis than coherence of the terms of `M` itself, and it is the
form a chart-local description of `M` supplies. The two halves are Stacks 07UB, through
`AlgebraicGeometry.Space.isCoherentOnSite_homology_of_forall_affine_restrict`, and the kernel
and cokernel clauses of Stacks 01BY(3) on the slice. -/
public theorem isCoherentOnSite_homology_of_forall_affine_restrict_terms
    (M : CochainComplex (Modules.{u, max (u + 1) m} B S hS F hF) ℤ) (n : ℤ)
    (h : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
      ∀ i, SheafOfModules.IsCoherentOnSite
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O))
        ((RingedSite.restrictComplex (smallEtaleRingedSite B S hS F hF) M U).X i)) :
    SheafOfModules.IsCoherentOnSite (M.homology n) :=
  isCoherentOnSite_homology_of_forall_affine_restrict B S hS F hF M n fun U hU =>
    Stacks.SheafOfModules.isCoherentOnSite_homology
      (RingedSite.restrictComplex (smallEtaleRingedSite B S hS F hF) M U) (h U hU) n

end AlgebraicGeometry.Space

end
