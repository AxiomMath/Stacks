module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
import StacksFrontier.RingTheory.Henselian.Henselization.TensorProduct

/-!
# The henselization after a ring map, at full source universe strength

Let `R → S` be a ring map and let `q ⊆ S` be a prime lying over `p ⊆ R`. Let `R_p → R^h` and
`S_q → S^h` be the henselizations. The local ring map `R^h → S^h` of Lemma 04GS identifies `S^h`
with the henselization of `R^h ⊗_R S` at the unique prime lying over the maximal ideal of `R^h`
and over `q`.

**This is the source-strength statement of tag 08HU**: the six rings `R`, `R_p`, `R^h`, `S`,
`S_q`, `S^h` carry six independent universes, as the source's own statement does. The existing
provider of the tag,
`IsLocalRing.IsHenselization.exists_unique_prime_isHenselization_tensorProduct` in
`StacksFrontier/RingTheory/Henselian/Henselization/TensorProduct.lean`, is weaker: it pins all six
rings to a single `Type u` in its `variable` block. The tag is therefore registered **here**, on
`StacksDraft.henselization_tensorProduct_at_unique_prime`; the weaker declaration's
`@[stacks 08HU]` is dropped, so that one tag keeps one provider. That removal lands in the
module named above, which this cluster does not own.

## Main results

* `StacksDraft.henselization_tensorProduct_at_unique_prime`: Stacks 08HU at six independent
  universes.
* `StacksDraft.exists_isHenselization_localization_tensorProduct`: the shared engine — for any
  local `R`-algebra map `f : R^h → S^h` between henselizations with prescribed residue fields
  `Lr` and `Ls`, the prime `Q = g⁻¹(𝔪_{S^h})` of `R^h ⊗_R S` lies over `𝔪_{R^h}` and over `q`,
  and `S^h` is a henselization of `(R^h ⊗_R S)_Q` with residue field `Ls`. A separable algebraic
  closure of `κ(q)` remains one of `κ(Q)`, which is what tag 08HV needs.

## Implementation notes

The whole argument is the single-universe one; the only step that pins universes is the
ind-étale bookkeeping, and it is carried out here in the universe-independent predicate
`StacksDraft.IndEtale` of `StacksFrontier/RingTheory/Etale/IndEtaleUniverse.lean`:

* `R^h` is ind-étale over `R` because `R_p` is (`indEtale_atPrime`) and `R^h` is ind-étale over
  `R_p` (the `ind_etale` field of `IsHenselization`), by `indEtale_comp`;
* `R^h ⊗_R S` is ind-étale over `S` by cobase change, `indEtale_tensorProduct`;
* `(R^h ⊗_R S)_Q` is ind-étale over `S` by `indEtale_comp` again;
* `S^h` is ind-étale over `(R^h ⊗_R S)_Q` by cancellation, `indEtale_of_comp`, since `S^h` is
  ind-étale over `S`.

The universal property of the henselization is taken from
`StacksDraft.existsUnique_henselization_map`, the independent-universe form of Lemma 04GS.
The prime-theoretic lemmas (`StacksDraft.tensorProduct_prime_eq_of_residue`,
`StacksDraft.surjectiveOnStalks_residue_of_localization`,
`StacksDraft.isLocalHom_of_localizations`) are universe-polymorphic already, and are imported
from `StacksFrontier/RingTheory/Henselian/Henselization/TensorProduct.lean`.

## References

* [StacksProject 08HU](https://stacks.math.columbia.edu/tag/08HU)
* [StacksProject 04GS](https://stacks.math.columbia.edu/tag/04GS)

## Tags

henselization, tensor product, unique prime, ind-étale, universe
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe uR uRp uRh uS uSq uSh uLr uLs

namespace StacksDraft

/-! ### Primes of a tensor product and algebras over their localizations -/

/-- A ring map into a local ring extends to a local map out of the localization at the
contraction of the maximal ideal. -/
@[ega "IV 18.6.7" "partial"]
private theorem exists_algebra_atPrime
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
    (g : A →+* B) (Q : Ideal A) [Q.IsPrime] (hQ : Q = (maximalIdeal B).comap g)
    (Aq : Type*) [CommRing Aq] [IsLocalRing Aq] [Algebra A Aq]
    [IsLocalization.AtPrime Aq Q] :
    ∃ alg : Algebra Aq B,
      letI := alg
      IsLocalHom (algebraMap Aq B) ∧ (algebraMap Aq B).comp (algebraMap A Aq) = g := by
  have hu : ∀ y : Q.primeCompl, IsUnit (g y) := fun y =>
    notMem_maximalIdeal.mp fun hy => y.2 (hQ ▸ hy)
  refine ⟨(IsLocalization.lift hu).toAlgebra, ?_, IsLocalization.lift_comp hu⟩
  apply ((local_hom_TFAE (IsLocalization.lift hu)).out 1 4).mpr
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q Aq, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap, IsLocalization.lift_comp hu, hQ]

/-- For a local `f : A → C`, the prime `Q = g⁻¹(𝔪_C)` of `A ⊗[R] S` lies over `𝔪_A` and over `q`,
where `g` is induced by `f` and `S → S_q → C`; and `C` is a local algebra over `(A ⊗[R] S)_Q`
compatibly with `g`. -/
private theorem exists_prime_tensorProduct
    {R A S B C : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] [Algebra R A] [Algebra R S] [Algebra R C]
    [Algebra S C] [IsScalarTower R S C] [Algebra S B] [Algebra B C] [IsScalarTower S B C]
    [IsLocalHom (algebraMap B C)]
    (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime B q]
    (f : A →ₐ[R] C) (hf : IsLocalHom f) :
    let g : A ⊗[R] S →ₐ[R] C :=
      Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S C) fun _ _ => .all _ _
    ∃ (Q : Ideal (A ⊗[R] S)) (_ : Q.IsPrime),
      Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := S)) =
        maximalIdeal A ∧
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).toRingHom = q ∧
      Q = (maximalIdeal C).comap g.toRingHom ∧
      ∃ alg : Algebra (Localization.AtPrime Q) C,
        letI := alg
        IsLocalHom (algebraMap (Localization.AtPrime Q) C) ∧
          (algebraMap (Localization.AtPrime Q) C).comp
            (algebraMap (A ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom := by
  intro g
  have hleft : g.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = f.toRingHom := by
    ext a
    simp [g]
  have hright : g.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).toRingHom =
      algebraMap S C := by
    ext a
    simp [g]
  have hf' : IsLocalHom f.toRingHom := ⟨hf.map_nonunit⟩
  have hBC : (maximalIdeal C).comap (algebraMap B C) = maximalIdeal B :=
    ((local_hom_TFAE (algebraMap B C)).out 1 5).mp ‹IsLocalHom (algebraMap B C)›
  refine ⟨(maximalIdeal C).comap g.toRingHom, inferInstance, ?_, ?_, rfl,
    exists_algebra_atPrime g.toRingHom _ rfl (Localization.AtPrime _)⟩
  · rw [Ideal.comap_comap, hleft]
    exact ((local_hom_TFAE f.toRingHom).out 1 5).mp hf'
  · rw [Ideal.comap_comap, hright, IsScalarTower.algebraMap_eq S B C, ← Ideal.comap_comap, hBC]
    exact IsLocalization.AtPrime.under_maximalIdeal B q

/-- The localization of `T` at a prime `Q` contracting to `q` is a local `S_q`-algebra in a tower
over `S`. -/
private theorem exists_algebra_localization_tower
    {S T C Sq : Type*} [CommRing S] [CommRing T] [CommRing C] [CommRing Sq]
    [IsLocalRing C] [IsLocalRing Sq] [Algebra S T] [Algebra S C] [Algebra T C]
    [IsScalarTower S T C] [Algebra S Sq]
    (q : Ideal S) (Q : Ideal T) [q.IsPrime] [Q.IsPrime]
    [IsLocalization.AtPrime Sq q] [IsLocalization.AtPrime C Q]
    (hQ : Q.comap (algebraMap S T) = q) :
    ∃ alg : Algebra Sq C,
      letI := alg
      IsLocalHom (algebraMap Sq C) ∧ IsScalarTower S Sq C := by
  have hc : q = (maximalIdeal C).comap (algebraMap S C) := by
    rw [IsScalarTower.algebraMap_eq S T C, ← Ideal.comap_comap,
      show (maximalIdeal C).comap (algebraMap T C) = Q from
        IsLocalization.AtPrime.under_maximalIdeal C Q, hQ]
  obtain ⟨alg, hl, he⟩ := exists_algebra_atPrime (algebraMap S C) q hc Sq
  exact ⟨alg, hl, IsScalarTower.of_algebraMap_eq' he.symm⟩

/-! ### The ind-étale localization of the tensor product -/

/-- The ind-étale core of Stacks 08HU, at independent universes. Given a local `R`-algebra map
`f : A → C` with `A` ind-étale over `R` and `C` ind-étale over `S`, the prime
`Q = g⁻¹(𝔪_C)` of `A ⊗[R] S` lies over `𝔪_A` and over `q`, and `C` is ind-étale over
`(A ⊗[R] S)_Q`, which is in turn a local `S_q`-algebra in a tower `S_q → (A ⊗[R] S)_Q → C`. -/
private theorem exists_indEtale_localization_tensorProduct
    {R A S B C : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C] [Algebra R A] [Algebra R S] [Algebra R C]
    [Algebra S C] [IsScalarTower R S C] [Algebra S B] [Algebra B C] [IsScalarTower S B C]
    [IsLocalHom (algebraMap B C)]
    (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime B q]
    (hA : IndEtale R A) (hC : IndEtale S C)
    (f : A →ₐ[R] C) (hf : IsLocalHom f) :
    let g : A ⊗[R] S →ₐ[R] C :=
      Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S C) fun _ _ => .all _ _
    ∃ (Q : Ideal (A ⊗[R] S)) (_ : Q.IsPrime),
      Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := S)) =
        maximalIdeal A ∧
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := S)).toRingHom = q ∧
      Q = (maximalIdeal C).comap g.toRingHom ∧
      ∃ alg : Algebra (Localization.AtPrime Q) C,
        letI := alg
        ∃ _ : IsLocalHom (algebraMap (Localization.AtPrime Q) C),
          (algebraMap (Localization.AtPrime Q) C).comp
            (algebraMap (A ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom ∧
          IndEtale (Localization.AtPrime Q) C ∧
          ∃ algB : Algebra B (Localization.AtPrime Q),
            letI := algB
            IsLocalHom (algebraMap B (Localization.AtPrime Q)) ∧
              IsScalarTower B (Localization.AtPrime Q) C := by
  intro g
  obtain ⟨Q, hQ, hl, hr, hQg, alg, hc, hcomp⟩ := exists_prime_tensorProduct (B := B) q f hf
  let U := Localization.AtPrime Q
  let := alg
  let : Algebra S (A ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower S (A ⊗[R] S) U := inferInstance
  have hSUC : IsScalarTower S U C := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun s => ?_)
    change algebraMap S C s = algebraMap U C (algebraMap (A ⊗[R] S) U (algebraMap S (A ⊗[R] S) s))
    rw [← RingHom.comp_apply, hcomp]
    change algebraMap S C s = g ((1 : A) ⊗ₜ[R] s)
    simp [g]
  let := hSUC
  obtain ⟨algB, hBU, hSBU⟩ :=
    exists_algebra_localization_tower (S := S) (T := A ⊗[R] S) (C := U) (Sq := B) q Q hr
  let := algB
  let := hSBU
  have hBUC : IsScalarTower B U C := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext q.primeCompl
      (RingHom.ext fun s => ?_))
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply S B C,
      ← IsScalarTower.algebraMap_apply S B U, ← IsScalarTower.algebraMap_apply S U C]
  have hT : IndEtale S (A ⊗[R] S) :=
    indEtale_of_equiv (RingEquiv.refl S) (Algebra.TensorProduct.comm R S A).toRingEquiv
      (fun _ => rfl) (indEtale_tensorProduct S hA)
  have hU : IndEtale S U := indEtale_comp hT (indEtale_atPrime Q)
  exact ⟨Q, hQ, hl, hr, hQg, alg, hc, hcomp, indEtale_of_comp hU hC, algB, hBU, hBUC⟩

/-! ### The henselization at the induced prime -/

/-- A henselization of the localization of `A` at a prime is ind-étale over `A`. -/
private theorem indEtale_isHenselization_atPrime
    {A : Type*} (Ap : Type*) {Ah : Type*} [CommRing A] [CommRing Ap] [IsLocalRing Ap]
    [Algebra A Ap] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime Ap p]
    (L : Type*) [Field L] [Algebra (ResidueField Ap) L]
    [CommRing Ah] [IsLocalRing Ah] [Algebra Ap Ah] [Algebra A Ah] [IsScalarTower A Ap Ah]
    [IsHenselization Ap L Ah] : IndEtale A Ah :=
  indEtale_comp (indEtale_atPrime (B := Ap) p) (indEtale_of_isHenselization (R := Ap) L (Rh := Ah))

/-- **The henselization at the prime induced by a local map**, at independent universes. Let `Rh`
and `Sh` be henselizations of `R_p` and `S_q` with residue fields `Lr` and `Ls`, and let
`f : Rh → Sh` be a local `R`-algebra map. Let `g : Rh ⊗[R] S → Sh` be induced by `f` and
`S → Sh`, and let `Q = g⁻¹(𝔪_Sh)`. Then `Q` lies over `𝔪_Rh` and over `q`, and `Sh` is a
henselization of `(Rh ⊗[R] S)_Q` with residue field `Ls`, compatibly with `g`; a separable
algebraic closure of `κ(q)` stays one. -/
theorem exists_isHenselization_localization_tensorProduct
    {R : Type uR} {Rp : Type uRp} {Rh : Type uRh}
    {S : Type uS} {Sq : Type uSq} {Sh : Type uSh}
    [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime]
    [CommRing Rp] [IsLocalRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p]
    [CommRing Sq] [IsLocalRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [Algebra Rp Rh] [IsScalarTower R Rp Rh]
    [CommRing Sh] [IsLocalRing Sh] [Algebra R Sh] [Algebra S Sh] [Algebra Sq Sh]
    [IsScalarTower R S Sh] [IsScalarTower S Sq Sh]
    {Lr : Type uLr} [Field Lr] [Algebra (ResidueField Rp) Lr] [IsHenselization Rp Lr Rh]
    {Ls : Type uLs} [Field Ls] [Algebra (ResidueField Sq) Ls] [IsHenselization Sq Ls Sh]
    (f : Rh →ₐ[R] Sh) (hf : IsLocalHom f) :
    let g : Rh ⊗[R] S →ₐ[R] Sh :=
      Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Sh) fun _ _ => .all _ _
    ∃ (Q : Ideal (Rh ⊗[R] S)) (_ : Q.IsPrime),
      Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rh) (B := S)) =
        maximalIdeal Rh ∧
      Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom = q ∧
      Q = (maximalIdeal Sh).comap g.toRingHom ∧
      ∃ alg : Algebra (Localization.AtPrime Q) Sh,
        letI := alg
        ∃ _ : IsLocalHom (algebraMap (Localization.AtPrime Q) Sh),
          ∃ algRes : Algebra (ResidueField (Localization.AtPrime Q)) Ls,
            letI := algRes
            IsHenselization (Localization.AtPrime Q) Ls Sh ∧
              (IsSepClosure (ResidueField Sq) Ls →
                IsSepClosure (ResidueField (Localization.AtPrime Q)) Ls) ∧
              (algebraMap (Localization.AtPrime Q) Sh).comp
                (algebraMap (Rh ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom := by
  have hRh : IndEtale R Rh := indEtale_isHenselization_atPrime Rp p Lr
  have hSh : IndEtale S Sh := indEtale_isHenselization_atPrime Sq q Ls
  have : IsLocalHom (algebraMap Sq Sh) := IsHenselization.isLocalHom (L := Ls)
  obtain ⟨Q, hQ, hl, hr, hQg, alg, hc, hcomp, hi, algB, hBU, hBUC⟩ :=
    exists_indEtale_localization_tensorProduct (B := Sq) q hRh hSh f hf
  let := alg
  let := algB
  let := hBU
  let := hBUC
  obtain ⟨algRes, hh, hs⟩ := exists_isHenselization_of_indEtale (A := Sq) (L := Ls) hi
  exact ⟨Q, hQ, hl, hr, hQg, alg, hc, algRes, hh, hs, hcomp⟩

/-! ### Stacks 08HU -/

/-- **Henselization after a ring map** (Stacks 08HU), at six independent universes. For primes
`q` over `p`, the canonical local map between henselizations of `R_p` and `S_q` identifies the
latter with the henselization of `Rh ⊗[R] S` at its unique prime lying over both the maximal
ideal of `Rh` and `q`. The final equality says that the henselization map is induced by the
canonical map from the tensor product.

This is the source-strength form of tag 08HU, and the provider of that tag. The weaker
single-universe statement
`IsLocalRing.IsHenselization.exists_unique_prime_isHenselization_tensorProduct` pins all six
rings to one `Type u`; its `@[stacks 08HU]` attribute is dropped in favour of this one. See the
module docstring. -/
@[stacks 08HU "Stated over six independent universes, as the source requires: the tag's six
rings `R`, `R_p`, `R^h`, `S`, `S_q`, `S^h` are unconstrained relative to one another."]
theorem henselization_tensorProduct_at_unique_prime
    {R : Type uR} {Rp : Type uRp} {Rh : Type uRh}
    {S : Type uS} {Sq : Type uSq} {Sh : Type uSh}
    [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [CommRing Rp] [IsLocalRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp p]
    [CommRing Sq] [IsLocalRing Sq] [Algebra S Sq] [IsLocalization.AtPrime Sq q]
    [Algebra R Sq] [Algebra Rp Sq] [IsScalarTower R S Sq] [IsScalarTower R Rp Sq]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [Algebra Rp Rh]
    [IsScalarTower R Rp Rh] [IsHenselization Rp (ResidueField Rp) Rh]
    [CommRing Sh] [IsLocalRing Sh] [Algebra R Sh] [Algebra S Sh] [Algebra Rp Sh]
    [Algebra Sq Sh] [IsScalarTower R S Sh] [IsScalarTower S Sq Sh]
    [IsScalarTower Rp Sq Sh] [IsHenselization Sq (ResidueField Sq) Sh] :
    ∃ f : Rh →ₐ[R] Sh,
      IsLocalHom f ∧
      f.toRingHom.comp (algebraMap Rp Rh) = algebraMap Rp Sh ∧
      (∀ f' : Rh →ₐ[R] Sh, IsLocalHom f' →
        f'.toRingHom.comp (algebraMap Rp Rh) = algebraMap Rp Sh → f' = f) ∧
      let g : Rh ⊗[R] S →ₐ[R] Sh :=
        Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom R S Sh)
          (fun _ _ => Commute.all _ _)
      ∃ (Q : Ideal (Rh ⊗[R] S)) (_hQ : Q.IsPrime),
        Q.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rh) (B := S)) =
            maximalIdeal Rh ∧
        Q.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom = q ∧
        Q = (maximalIdeal Sh).comap g.toRingHom ∧
        (∀ (Q' : Ideal (Rh ⊗[R] S)), Q'.IsPrime →
          Q'.comap (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := Rh) (B := S)) =
              maximalIdeal Rh →
          Q'.comap (Algebra.TensorProduct.includeRight (R := R) (A := Rh) (B := S)).toRingHom =
              q → Q' = Q) ∧
        ∃ alg : Algebra (Localization.AtPrime Q) Sh,
          letI : Algebra (Localization.AtPrime Q) Sh := alg
          ∃ _ : IsLocalHom (algebraMap (Localization.AtPrime Q) Sh),
            IsHenselization (Localization.AtPrime Q)
                (ResidueField (Localization.AtPrime Q)) Sh ∧
              (algebraMap (Localization.AtPrime Q) Sh).comp
                  (algebraMap (Rh ⊗[R] S) (Localization.AtPrime Q)) = g.toRingHom := by
  have hRh : IndEtale R Rh := indEtale_isHenselization_atPrime Rp p (ResidueField Rp)
  have hSh : IndEtale S Sh := indEtale_isHenselization_atPrime Sq q (ResidueField Sq)
  have : HenselianLocalRing Sh := IsHenselization.henselian (R := Sq) (L := ResidueField Sq)
  have : IsLocalHom (algebraMap Sq Sh) := IsHenselization.isLocalHom (L := ResidueField Sq)
  have : IsLocalHom (algebraMap Rp Sq) := isLocalHom_of_localizations p q
  have : IsLocalHom (algebraMap Rp Sh) := by
    rw [IsScalarTower.algebraMap_eq Rp Sq Sh]; infer_instance
  have : IsScalarTower R Rp Sh := IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => by
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply Rp Sq Sh, ← IsScalarTower.algebraMap_apply R Rp Sq,
      IsScalarTower.algebraMap_apply R S Sq, ← IsScalarTower.algebraMap_apply S Sq Sh,
      ← IsScalarTower.algebraMap_apply R S Sh])
  obtain ⟨f, hf, hRp, huniq⟩ :=
    existsUnique_henselization_map (R := R) (A := Rp) (Ah := Rh) (B := Sh)
  refine ⟨f, hf, hRp, huniq, ?_⟩
  obtain ⟨Q, hQ, hl, hr, hQg, alg, hc, hcomp, hi, algB, hBU, hBUC⟩ :=
    exists_indEtale_localization_tensorProduct (B := Sq) q hRh hSh f hf
  let := alg
  let := hc
  let := algB
  let := hBU
  let := hBUC
  have hres : Function.Surjective
      (ResidueField.map (algebraMap (Localization.AtPrime Q) Sh)) :=
    residueFieldMap_surjective_of_tower (A := Sq)
      (IsHenselization.residueField_map_bijective (R := Sq) (Rh := Sh)).2
  refine ⟨Q, hQ, hl, hr, hQg, ?_, alg, hc,
    isHenselization_of_indEtale_of_surjective hi hres, hcomp⟩
  intro Q' hQ' hleft hright
  have : IsLocalHom (algebraMap Rp Rh) := IsHenselization.isLocalHom (L := ResidueField Rp)
  exact tensorProduct_prime_eq_of_residue
    (surjectiveOnStalks_residue_of_localization p.primeCompl
      (IsHenselization.residueField_map_bijective (R := Rp) (Rh := Rh)).2) Q' Q hleft hl
    (hright.trans hr.symm)

end StacksDraft

end
