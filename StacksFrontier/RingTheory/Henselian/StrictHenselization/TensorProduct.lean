module

public import StacksFrontier.RingTheory.Henselian.Henselization.TensorProduct
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Henselian.StrictHenselization

/-!
# The strict henselization after a ring map

Let `R → S` be a ring map and let `q ⊆ S` be a prime lying over `p ⊆ R`. Choose separable
algebraic closures `κ(p) ⊆ κ₁^sep` and `κ(q) ⊆ κ₂^sep` and a map `φ : κ₁^sep → κ₂^sep` over
`κ(p) → κ(q)`, and let `R^sh`, `S^sh` be the corresponding strict henselizations of `R_p` and
`S_q`. The local ring map `R^sh → S^sh` of Lemma 04GU inducing `φ` identifies `S^sh` with the
strict henselization of `R^sh ⊗_R S` at a prime lying over `q` and over the maximal ideal of
`R^sh`.

## Main results

* `IsLocalRing.IsHenselization.exists_prime_isStrictHenselization_tensorProduct`: Stacks 08HV.

## Implementation notes

The separable algebraic closures are the residue fields of the strict henselizations themselves,
with their `κ(p)`- and `κ(q)`-algebra structures; `φ` is a map between them compatible with the
residue maps out of `R`. That `κ(R^sh)` is separably closed is not needed. The prime is the inverse
image of the maximal ideal of `S^sh` under the map `R^sh ⊗_R S → S^sh` induced by the map
`R^sh → S^sh`.

## References

* [StacksProject 08HV](https://stacks.math.columbia.edu/tag/08HV)
* [StacksProject 04GU](https://stacks.math.columbia.edu/tag/04GU)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u

namespace IsLocalRing.IsHenselization

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) (q : Ideal S)
  [p.IsPrime] [q.IsPrime]
  {Rp : Type u} [CommRing Rp] [IsLocalRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p]
  {Sq : Type u} [CommRing Sq] [IsLocalRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
  {Rsh : Type u} [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra Rp Rsh]
  [IsScalarTower R Rp Rsh] [Algebra (ResidueField Rp) (ResidueField Rsh)]
  [IsHenselization Rp (ResidueField Rsh) Rsh]
  {Ssh : Type u} [CommRing Ssh] [IsLocalRing Ssh] [Algebra R Ssh] [Algebra S Ssh]
  [Algebra Sq Ssh] [IsScalarTower R S Ssh] [IsScalarTower S Sq Ssh]
  [Algebra (ResidueField Sq) (ResidueField Ssh)]
  [IsSepClosure (ResidueField Sq) (ResidueField Ssh)] [IsHenselization Sq (ResidueField Ssh) Ssh]

include p in
/-- **The strict henselization after a ring map** (Stacks 08HV). Let `R → S` be a ring map and
let `q ⊆ S` lie over `p ⊆ R`. Let `Rsh` and `Ssh` be strict henselizations of `R_p` and `S_q`,
with respect to the separable algebraic closures `κ(Rsh)` of `κ(p)` and `κ(Ssh)` of `κ(q)`, and
let `φ : κ(Rsh) → κ(Ssh)` be compatible with the residue maps out of `R`. The local map
`f : Rsh → Ssh` of Lemma 04GU inducing `φ` identifies `Ssh` with the strict henselization of
`Rsh ⊗[R] S` at the prime `Q = g⁻¹(𝔪_Ssh)`, where `g : Rsh ⊗[R] S → Ssh` is induced by `f`; `Q`
lies over `𝔪_Rsh` and over `q`. -/
@[stacks 08HV "The separable algebraic closures are the residue fields of `R^sh` and `S^sh`, and
the commutative square is the compatibility `hphi` of `φ` with the residue maps out of `R`. The map
of 04GU is pinned as the unique local `R`-algebra map inducing `φ`. The prime is `g⁻¹(𝔪_{S^sh})`
with its two contractions; that `S^sh` is the strict henselization of `(R^sh ⊗_R S)_Q` is
`IsHenselization` with residue field `κ(S^sh)`, separably closed over `κ(Q)`. All rings share one
universe, as `IsHenselization` requires."]
theorem exists_prime_isStrictHenselization_tensorProduct [Algebra R Sq] [Algebra Rp Sq]
    [IsScalarTower R S Sq] [IsScalarTower R Rp Sq] [Algebra Rp Ssh] [IsScalarTower R Rp Ssh]
    [IsScalarTower Rp Sq Ssh] (phi : ResidueField Rsh →+* ResidueField Ssh)
    (hphi : phi.comp ((residue Rsh).comp (algebraMap R Rsh)) =
      (residue Ssh).comp (algebraMap R Ssh)) :
    ∃ f : Rsh →ₐ[R] Ssh, IsLocalHom f ∧
      (residue Ssh).comp f.toRingHom = phi.comp (residue Rsh) ∧
      (∀ f' : Rsh →ₐ[R] Ssh, IsLocalHom f' →
        (residue Ssh).comp f'.toRingHom = phi.comp (residue Rsh) → f' = f) ∧
      let g : Rsh ⊗[R] S →ₐ[R] Ssh :=
        Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Ssh) fun _ _ => .all _ _
      ∃ (Q : Ideal (Rsh ⊗[R] S)) (_ : Q.IsPrime),
        Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rsh) (B := S)) =
          maximalIdeal Rsh ∧
        Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rsh) (B := S)).toRingHom = q ∧
        Q = (maximalIdeal Ssh).comap g.toRingHom ∧
        ∃ _ : Algebra (Localization.AtPrime Q) Ssh,
          IsLocalHom (algebraMap (Localization.AtPrime Q) Ssh) ∧
          ∃ _ : Algebra (ResidueField (Localization.AtPrime Q)) (ResidueField Ssh),
            IsSepClosure (ResidueField (Localization.AtPrime Q)) (ResidueField Ssh) ∧
            IsHenselization (Localization.AtPrime Q) (ResidueField Ssh) Ssh ∧
            (∀ x, algebraMap (ResidueField (Localization.AtPrime Q)) (ResidueField Ssh)
              (residue (Localization.AtPrime Q) x) =
                residue Ssh (algebraMap (Localization.AtPrime Q) Ssh x)) ∧
            (algebraMap (Localization.AtPrime Q) Ssh).comp
              (algebraMap (Rsh ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom := by
  have hRp : phi.comp ((residue Rsh).comp (algebraMap Rp Rsh)) =
      (residue Ssh).comp (algebraMap Rp Ssh) := by
    refine IsLocalization.ringHom_ext p.primeCompl ?_
    simpa only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq] using hphi
  have := henselian (R := Sq) (L := ResidueField Ssh) (Rh := Ssh)
  have hind := ind_etale (R := Rp) (L := ResidueField Rsh) (Rh := Rsh)
  let fRp : Rsh →ₐ[Rp] Ssh := HenselianLocalRing.indEtaleAlgHomOfResidue hind phi hRp
  have hf : IsLocalHom fRp := HenselianLocalRing.isLocalHom_indEtaleAlgHomOfResidue hind phi hRp
  have hfres : (residue Ssh).comp (fRp : Rsh →+* Ssh) = phi.comp (residue Rsh) :=
    HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hind phi hRp
  have hu : ∀ g : Rsh →ₐ[Rp] Ssh, IsLocalHom g →
      (residue Ssh).comp (g : Rsh →+* Ssh) = phi.comp (residue Rsh) → g = fRp :=
    HenselianLocalRing.indEtaleAlgHomOfResidue_unique hind phi hRp
  have hfR : IsLocalHom (fRp.restrictScalars R) := ⟨hf.map_nonunit⟩
  refine ⟨fRp.restrictScalars R, hfR, hfres, fun f' hf' hf'res => ?_, ?_⟩
  · have hbase : f'.toRingHom.comp (algebraMap Rp Rsh) = algebraMap Rp Ssh :=
      IsLocalization.ringHom_ext p.primeCompl <| RingHom.ext fun x => by
        simp [← IsScalarTower.algebraMap_apply]
    exact AlgHom.ext fun x => AlgHom.congr_fun
      (hu { f'.toRingHom with commutes' := RingHom.congr_fun hbase }
        ⟨hf'.map_nonunit⟩ hf'res) x
  · obtain ⟨hl, hr, alg, hloc, hcomp, algRes, hhens, hsep⟩ :=
      exists_isHenselization_localization_tensorProduct p q (Rp := Rp) (Sq := Sq)
        (Lr := ResidueField Rsh) (Ls := ResidueField Ssh) (fRp.restrictScalars R) hfR
    let Q := (maximalIdeal Ssh).comap (Algebra.TensorProduct.lift (fRp.restrictScalars R)
      (IsScalarTower.toAlgHom R S Ssh) fun _ _ => .all _ _).toRingHom
    obtain ⟨algRes', hhens', hsep', hres⟩ := exists_residueFieldAlgebra
      (R := Localization.AtPrime Q) (L := ResidueField Ssh) (Rh := Ssh)
    exact ⟨_, inferInstance, hl, hr, rfl, alg, hloc, algRes', hsep' (hsep inferInstance), hhens',
      hres, hcomp⟩

end IsLocalRing.IsHenselization
