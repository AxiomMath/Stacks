module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineCoversTop
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleWeaklyContractible
public import StacksCore.Tactic.StacksAttribute

/-!
# Coverings of the big pro-étale site by affine w-contractible objects

Every object `T` of a chosen big pro-étale site admits a chosen covering family `{T_i → T}`
whose members are affine with w-contractible ring of global sections, hence are weakly
contractible objects of the site.

The family is the composite of two coverings. The chosen affine open cover of the underlying
scheme of `T` is a Zariski cover, so a pro-étale cover, and each of its members is again an
object of the chosen big site, being the source of an open immersion into one. Each such affine
member is then covered by a single affine object with w-contractible global sections, by
`AlgebraicGeometry.ProEtale.exists_affine_indEtale_wContractible_cover`. Composing gives a
pro-étale covering family of `T`, which need not satisfy the index bound of the chosen covering
system; a combinatorially equivalent chosen representative has the same sources, so it inherits
the two properties of the members.

## Main results

* `AlgebraicGeometry.ProEtale.exists_covering_affine_wContractible` — every object of a chosen
  big pro-étale site has a chosen covering family all of whose members are affine with
  w-contractible global sections and weakly contractible in the site.

## Implementation notes

An affine scheme is canonically the spectrum of its ring of global sections, so the source's
requirement that a member be *affine and the spectrum of a w-contractible ring* is expressed
as `AlgebraicGeometry.IsAffine` together with
`ProetaleWContractible.IsWContractible` of its ring of global sections. The final clause of the
source is the implication `(1) → (2)` of
`AlgebraicGeometry.ProEtale.isWContractible_globalSections_tfae`.

## References

* [Stacks Project, Tag 098I](https://stacks.math.columbia.edu/tag/098I)
-/

@[expose] public noncomputable section

open CategoryTheory ProetaleWContractible

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T : B.Scheme)

/-- A member of the chosen affine open cover of the underlying scheme of an object `T` of a
chosen big pro-étale site, as an object of that site: it is the source of an open immersion
into an object of the site, hence satisfies the size cutoff. -/
private def affineMember (i : T.obj.affineCover.I₀) : B.Scheme :=
  ⟨T.obj.affineCover.X i,
    Scheme.size_lt_of_isOpenImmersion (T.obj.affineCover.f i) T.property⟩

private instance isAffine_affineMember (i : T.obj.affineCover.I₀) :
    IsAffine (affineMember B T i).obj :=
  inferInstanceAs (IsAffine (T.obj.affineCover.X i))

/-- The open immersion of a member of the chosen affine open cover of the underlying scheme of
`T` into `T`, as a morphism of the chosen big pro-étale site. -/
private def affineMemberHom (i : T.obj.affineCover.I₀) : affineMember B T i ⟶ T :=
  ObjectProperty.homMk (T.obj.affineCover.f i)

private lemma map_affineMemberHom (i : T.obj.affineCover.I₀) :
    B.inclusion.map (affineMemberHom B T i) = T.obj.affineCover.f i :=
  rfl

/-- **Stacks 098I.** Every object `T` of a chosen big pro-étale site admits a chosen covering
family `{T_i → T}` of that site with each `T_i` affine and the spectrum of a w-contractible
ring; in particular each `T_i` is a weakly contractible object of the site.

The covering is the chosen representative of the composite of the chosen affine open cover of
the underlying scheme of `T` with the single affine w-contractible cover of each of its
members. -/
@[stacks 098I]
theorem exists_covering_affine_wContractible :
    ∃ E : PreZeroHypercover.{u + 1} T,
      B.covering ⟨T, E⟩ ∧
        ∀ i : E.I₀,
          IsAffine (E.X i).obj ∧
            IsWContractible.{u, u} Γ((E.X i).obj, ⊤) ∧
            B.topology.IsWeaklyContractible (E.X i) := by
  classical
  have hdata : ∀ i : T.obj.affineCover.I₀,
      ∃ (W : B.Scheme) (p : W ⟶ affineMember B T i),
        B.covering ⟨affineMember B T i, PreZeroHypercover.singleton p⟩ ∧
          IsAffine W.obj ∧ IsWContractible.{u, u} Γ(W.obj, ⊤) := by
    intro i
    obtain ⟨W, p, hcov, haff, hw, -, -⟩ :=
      exists_affine_indEtale_wContractible_cover B (affineMember B T i)
    exact ⟨W, p, hcov, haff, hw⟩
  choose V q hqcov hVaff hVw using hdata
  -- The composite of the affine cover of `T` with the chosen cover of each of its members.
  let Q : PreZeroHypercover.{u + 1} T :=
    { I₀ := Σ _ : T.obj.affineCover.I₀, PUnit.{u + 2}
      X p := V p.1
      f p := q p.1 ≫ affineMemberHom B T p.1 }
  have hQpro : B.IsProetaleCovering ⟨T, Q⟩ := by
    have hzar : Presieve.ofArrows T.obj.affineCover.X T.obj.affineCover.f ∈
        Scheme.proetalePrecoverage.coverings T.obj :=
      zariskiPrecoverage_le_proetalePrecoverage _ T.obj.affineCover.mem₀
    have hsing : ∀ i : T.obj.affineCover.I₀,
        Presieve.ofArrows (fun _ : PUnit.{u + 2} => (V i).obj)
            (fun _ => B.inclusion.map (q i)) ∈
          Scheme.proetalePrecoverage.coverings (T.obj.affineCover.X i) := fun i =>
      (hqcov i).1
    have hcomp := Precoverage.comp_mem_coverings (J := Scheme.proetalePrecoverage.{u})
      (f := T.obj.affineCover.f) hzar
      (g := fun i (_ : PUnit.{u + 2}) => B.inclusion.map (q i)) hsing
    exact hcomp
  obtain ⟨R, hR, hcomb⟩ := B.covering_representatives ⟨T, Q⟩ hQpro
  obtain ⟨Rt, Rfam⟩ := R
  have htarget : T = Rt := hcomb.1
  cases htarget
  have hcomb' : PreZeroHypercover.CombinatoriallyEquivalent Q Rfam := hcomb.2
  obtain ⟨-, β, hβ, -⟩ := hcomb'
  refine ⟨Rfam, hR, fun j => ?_⟩
  have hXj : Rfam.X j = V (β j).1 := hβ j
  rw [hXj]
  have haff : IsAffine (V (β j).1).obj := hVaff (β j).1
  exact ⟨haff, hVw (β j).1,
    ((isWContractible_globalSections_tfae B (V (β j).1)).out 1 2).mp (hVw (β j).1)⟩

end AlgebraicGeometry.ProEtale

end
