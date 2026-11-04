module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriplePreparedSection
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CanonicalSectionsSurjective
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleHomGlue

/-!
# Extending the transported section over the whole chart, up to a power of `f`

`Stacks.Algebraization.PreparedExtension.sectionOnIdealComplement` transports a global section
`s` of `T.F` to a section of `P.F'` over the ideal-sheaf complement of the closed point.
`Stacks.Algebraization.exists_idealPow_hom_of_preparedExtension` extends that section to a
`Γ(Spec A, ⊤)`-linear map out of a power of the closed point's ideal, agreeing with
multiplication by the section on the basic open of each generator of a chosen finite generating
family. Evaluating that map at a chosen power of `f` itself (which lies in the ideal, since
`f` lies in the maximal ideal) produces a single global section `t` of `P.F'` which, restricted
back to the ideal-sheaf complement, recovers `f ^ N` times the transported section -- the two
sides agree on the basic open of every generator of the family, by construction, and those basic
opens cover the whole complement, so the sheaf condition identifies them on all of it.

## Main results

* `Stacks.Algebraization.PreparedExtension.exists_pow_smul_eq_sectionOnIdealComplement`: for
  some `N`, a global section `t` of `P.F'` restricting on the ideal-sheaf complement to
  `f ^ N` times the transported section.

## References

* [Stacks Project, Tag 0F23](https://stacks.math.columbia.edu/tag/0F23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- **The transported section extends over the whole chart, up to a power of `f`.** Given a
prepared extension `P` of `L` at `f ∈ 𝔪`, and a global section `s` of `L.F`, some power `f ^ N`
of `f` times the section of `P.F'` transported from `s` along the ideal-sheaf complement of the
closed point is the restriction of a global section `t` of `P.F'`.

The section `t` is obtained by evaluating the `Γ(Spec A, ⊤)`-linear map furnished by
`exists_idealPow_hom_of_preparedExtension` at `(ΓSpecIso A).inv f ^ N`, which lies in the `N`-th
power of the closed point's ideal since `f` lies in the maximal ideal. The two sides of the
displayed equation agree after restricting to the basic open of each generator `a i` of the
chosen finite generating family -- on one side by the defining property `hφ` of the linear map,
on the other by `Scheme.Modules.map_smul` and functoriality of restriction -- and those basic
opens cover the whole ideal-sheaf complement by
`Stacks.LocalCohomology.affine_inf_idealComplement_eq_iSup_basicOpen_of_span`, so the sheaf
condition (`Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.eq_of_locally_eq`) identifies the
two sides on all of it. -/
public theorem PreparedExtension.exists_pow_smul_eq_sectionOnIdealComplement
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A)
    {L : CoherentTriple A f} (P : PreparedExtension A f L) (s : Γ(L.F, ⊤)) :
    ∃ (N : ℕ) (t : Γ(P.F', ⊤)),
      P.F'.presheaf.map (homOfLE (le_top : Stacks.LocalCohomology.idealComplement
          (Scheme.Hom.ker (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ≤ ⊤)).op t =
        ((Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top :
              Stacks.LocalCohomology.idealComplement
                (Scheme.Hom.ker (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) ≤ ⊤)).op
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f ^ N)) •
          P.sectionOnIdealComplement s := by
  set I : (Spec (CommRingCat.of A)).IdealSheafData :=
    Scheme.Hom.ker (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) with hI
  set U : (Spec (CommRingCat.of A)).affineOpens :=
    ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ with hU
  obtain ⟨ι, hι, a, hspan, ha, N, φ, hφ⟩ :=
    exists_idealPow_hom_of_preparedExtension hf P (P.sectionOnIdealComplement s)
  have hfmem : (Scheme.ΓSpecIso (CommRingCat.of A)).inv f ∈ I.ideal U := by
    rw [hI, closedPointIdealSheaf_ideal_top]
    exact Ideal.mem_map_of_mem _ hf
  have hx₀mem : (Scheme.ΓSpecIso (CommRingCat.of A)).inv f ^ N ∈ I.ideal U ^ N :=
    Ideal.pow_mem_pow hfmem N
  set x₀ : Γ(Spec (CommRingCat.of A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv f ^ N
    with hx₀
  refine ⟨N, φ ⟨x₀, hx₀mem⟩, ?_⟩
  set W : ι → (Spec (CommRingCat.of A)).Opens :=
    fun i => (Spec (CommRingCat.of A)).basicOpen (a i) with hW
  have hWV : ∀ i, W i ≤ Stacks.LocalCohomology.idealComplement I :=
    fun i => Stacks.LocalCohomology.basicOpen_le_idealComplement I U (ha i)
  have hcov : Stacks.LocalCohomology.idealComplement I ≤ ⨆ i, W i := by
    have h : (⊤ : (Spec (CommRingCat.of A)).Opens) ⊓ Stacks.LocalCohomology.idealComplement I =
        ⨆ i, W i :=
      Stacks.LocalCohomology.affine_inf_idealComplement_eq_iSup_basicOpen_of_span I U a hspan
    rw [top_inf_eq] at h
    exact h.le
  refine Stacks.AlgebraicGeometry.SubmoduleHomGlue.LocalData.eq_of_locally_eq
    (G := P.F') W hWV hcov (fun i => ?_)
  have hcomp : (homOfLE (le_top :
        Stacks.LocalCohomology.idealComplement I ≤ ⊤)).op ≫ (homOfLE (hWV i)).op =
      (homOfLE ((Spec (CommRingCat.of A)).basicOpen_le (a i))).op :=
    Subsingleton.elim _ _
  rw [← Functor.map_comp_apply, hcomp, hφ i ⟨x₀, hx₀mem⟩, Scheme.Modules.map_smul,
    ← Functor.map_comp_apply, hcomp]

end Stacks.Algebraization

end
