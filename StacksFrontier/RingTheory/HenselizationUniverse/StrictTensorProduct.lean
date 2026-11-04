module

public import StacksFrontier.RingTheory.HenselizationUniverse.TensorProduct

/-!
# The strict henselization after a ring map, at full source universe strength

Let `R → S` be a ring map and let `q ⊆ S` be a prime lying over `p ⊆ R`. Choose separable
algebraic closures of `κ(p)` and `κ(q)` — here the residue fields of the two strict
henselizations themselves — and a map `φ` between them compatible with the residue maps out of
`R`. The local ring map `R^sh → S^sh` of Lemma 04GU inducing `φ` identifies `S^sh` with the
strict henselization of `R^sh ⊗_R S` at the prime induced by that map.

**This is the source-strength statement of tag 08HV**: the six rings `R`, `R_p`, `R^sh`, `S`,
`S_q`, `S^sh` carry six independent universes, as the source's own statement does. The existing
provider of the tag,
`IsLocalRing.IsHenselization.exists_prime_isStrictHenselization_tensorProduct` in
`StacksFrontier/RingTheory/Henselian/StrictHenselization/TensorProduct.lean`, is weaker: it pins all
six rings to a single `Type u` in its `variable` block. The tag is therefore registered **here**,
on `StacksDraft.strictHenselization_tensorProduct_at_induced_prime`; the weaker declaration's
`@[stacks 08HV]` is dropped, so that one tag keeps one provider. That removal lands in the
module named above, which this cluster does not own.

## Main results

* `StacksDraft.strictHenselization_tensorProduct_at_induced_prime`: Stacks 08HV at six
  independent universes.

## Implementation notes

Two ingredients do the universe work, neither of them in a file this cluster owns:

* `StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale`, the independent-universe form
  of Lemma 04GU, which produces the map `f : R^sh → S^sh` inducing `φ`. The single-universe form
  `HenselianLocalRing.indEtaleAlgHomOfResidue` takes
  `{R Rsh : Type u}`, which is what forced `R_p` and `R^sh` into one universe.
* `StacksDraft.exists_isHenselization_localization_tensorProduct`, the shared tensor-product
  engine of tag 08HU, instantiated at `Lr = κ(R^sh)` and `Ls = κ(S^sh)`. Its last conjunct is
  exactly the statement that a separable algebraic closure of `κ(q)` stays one of `κ(Q)`, which
  is the extra content of 08HV over 08HU.

The prescribed residue field is then replaced by the actual residue field of `(R^sh ⊗_R S)_Q`
with `IsLocalRing.IsHenselization.exists_residueFieldAlgebra`, which is already universe-general.

## References

* [StacksProject 08HV](https://stacks.math.columbia.edu/tag/08HV)
* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)

## Tags

strict henselization, tensor product, separable algebraic closure, ind-étale, universe
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe uR uRp uRsh uS uSq uSsh

namespace StacksDraft

/-- **Strict henselization after a ring map** (Stacks 08HV), at six independent universes. For
primes `q` over `p` and compatible separable closures of their residue fields, the canonical local
map between strict henselizations identifies the target with the strict henselization of
`Rsh ⊗[R] S` at the prime induced by that map.

This is the source-strength form of tag 08HV, and the provider of that tag. The weaker
single-universe statement
`IsLocalRing.IsHenselization.exists_prime_isStrictHenselization_tensorProduct` pins all six rings
to one `Type u`; its `@[stacks 08HV]` attribute is dropped in favour of this one. See the module
docstring. -/
@[stacks 08HV "Stated over six independent universes, as the source requires: the tag's six
rings `R`, `R_p`, `R^sh`, `S`, `S_q`, `S^sh` are unconstrained relative to one another."]
theorem strictHenselization_tensorProduct_at_induced_prime
    {R : Type uR} {Rp : Type uRp} {Rsh : Type uRsh}
    {S : Type uS} {Sq : Type uSq} {Ssh : Type uSsh}
    [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [CommRing Rp] [IsLocalRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p]
    [CommRing Sq] [IsLocalRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [Algebra R Sq] [Algebra Rp Sq] [IsScalarTower R S Sq] [IsScalarTower R Rp Sq]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rp Rsh]
    [IsScalarTower R Rp Rsh]
    [Algebra (ResidueField Rp) (ResidueField Rsh)]
    [IsSepClosure (ResidueField Rp) (ResidueField Rsh)]
    [IsHenselization Rp (ResidueField Rsh) Rsh]
    [CommRing Ssh] [IsLocalRing Ssh] [Algebra R Ssh] [Algebra S Ssh] [Algebra Rp Ssh]
    [Algebra Sq Ssh] [IsScalarTower R S Ssh] [IsScalarTower S Sq Ssh]
    [IsScalarTower R Rp Ssh] [IsScalarTower Rp Sq Ssh]
    [Algebra (ResidueField Sq) (ResidueField Ssh)]
    [IsSepClosure (ResidueField Sq) (ResidueField Ssh)]
    [IsHenselization Sq (ResidueField Ssh) Ssh]
    (phi : ResidueField Rsh →+* ResidueField Ssh)
    (hphi : phi.comp ((residue Rsh).comp (algebraMap R Rsh)) =
      (residue Ssh).comp (algebraMap R Ssh)) :
    ∃ f : Rsh →ₐ[R] Ssh,
      IsLocalHom f ∧
      (residue Ssh).comp f.toRingHom = phi.comp (residue Rsh) ∧
      (∀ f' : Rsh →ₐ[R] Ssh, IsLocalHom f' →
        (residue Ssh).comp f'.toRingHom = phi.comp (residue Rsh) → f' = f) ∧
      let g : Rsh ⊗[R] S →ₐ[R] Ssh :=
        Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Ssh)
          (fun _ _ => Commute.all _ _)
      ∃ (Q : Ideal (Rsh ⊗[R] S)) (_hQ : Q.IsPrime),
        Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rsh) (B := S)) =
            maximalIdeal Rsh ∧
        Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rsh) (B := S)).toRingHom = q ∧
        Q = (maximalIdeal Ssh).comap g.toRingHom ∧
        ∃ alg : Algebra (Localization.AtPrime Q) Ssh,
          letI : Algebra (Localization.AtPrime Q) Ssh := alg
          ∃ _ : IsLocalHom (algebraMap (Localization.AtPrime Q) Ssh),
            ∃ algRes : Algebra (ResidueField (Localization.AtPrime Q)) (ResidueField Ssh),
              letI : Algebra (ResidueField (Localization.AtPrime Q)) (ResidueField Ssh) := algRes
              IsSepClosure (ResidueField (Localization.AtPrime Q)) (ResidueField Ssh) ∧
                IsHenselization (Localization.AtPrime Q) (ResidueField Ssh) Ssh ∧
                (∀ x : Localization.AtPrime Q,
                  algebraMap (ResidueField (Localization.AtPrime Q)) (ResidueField Ssh)
                      (residue (Localization.AtPrime Q) x) =
                    residue Ssh (algebraMap (Localization.AtPrime Q) Ssh x)) ∧
                (algebraMap (Localization.AtPrime Q) Ssh).comp
                    (algebraMap (Rsh ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom := by
  have hRp : phi.comp ((residue Rsh).comp (algebraMap Rp Rsh)) =
      (residue Ssh).comp (algebraMap Rp Ssh) :=
    IsLocalization.ringHom_ext p.primeCompl <| by
      simpa only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] using hphi
  have : HenselianLocalRing Ssh := IsHenselization.henselian (R := Sq) (L := ResidueField Ssh)
  obtain ⟨fRp, ⟨hf, hfres⟩, hu⟩ :=
    existsUnique_isLocalHom_comp_residue_of_indEtale (A := Rp) (B := Rsh) (C := Ssh)
      (indEtale_of_isHenselization (R := Rp) (ResidueField Rsh) (Rh := Rsh)) phi hRp
  have hfR : IsLocalHom (fRp.restrictScalars R) := ⟨hf.map_nonunit⟩
  refine ⟨fRp.restrictScalars R, hfR, hfres, fun f' hf' hf'res => ?_, ?_⟩
  · have hbase : f'.toRingHom.comp (algebraMap Rp Rsh) = algebraMap Rp Ssh :=
      IsLocalization.ringHom_ext p.primeCompl <| RingHom.ext fun x => by
        simp [← IsScalarTower.algebraMap_apply]
    exact AlgHom.ext fun x => AlgHom.congr_fun
      (hu { f'.toRingHom with commutes' := RingHom.congr_fun hbase } ⟨⟨hf'.map_nonunit⟩, hf'res⟩) x
  · obtain ⟨Q, hQ, hl, hr, hQdef, alg, hloc, algRes, hhens, hsep, hcomp⟩ :=
      exists_isHenselization_localization_tensorProduct p q (Rp := Rp) (Sq := Sq)
        (Lr := ResidueField Rsh) (Ls := ResidueField Ssh) (fRp.restrictScalars R) hfR
    let := alg
    let := algRes
    let := hhens
    obtain ⟨algRes', hhens', hsep', hres⟩ := IsHenselization.exists_residueFieldAlgebra
      (R := Localization.AtPrime Q) (L := ResidueField Ssh) (Rh := Ssh)
    exact ⟨Q, hQ, hl, hr, hQdef, alg, hloc, algRes', hsep' (hsep inferInstance), hhens',
      hres, hcomp⟩

end StacksDraft

end
