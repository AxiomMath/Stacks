module

public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory

/-!
# The adic quotients of an Artinian local algebra

An Artinian local `Λ`-algebra maps canonically onto every adic truncation of the complete
local algebra it defines, by reduction modulo the corresponding power of the maximal ideal;
these maps are compatible with the truncation transitions and natural in the algebra.

## Main definitions

* `Deformation.artinianAdicQuotient`: the canonical map from an Artinian local algebra to the
  `n`-th adic truncation of the complete local algebra it defines.
* `Deformation.artinianTruncationIso`: that map as an isomorphism, at a level where the
  corresponding power of the maximal ideal vanishes.
-/

@[expose] public section

namespace Deformation

/-! ### The adic quotients of an Artinian local algebra -/

section
open CategoryTheory IsLocalRing

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A power of the maximal ideal of an Artinian local algebra vanishes, the ring being
Artinian local. -/
public theorem exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    ∃ n : ℕ, maximalIdeal A ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp inferInstance
  exact ⟨n, le_antisymm ((Ideal.pow_le_pow_right (Nat.le_succ n)).trans_eq hn) bot_le⟩

/-- The least level at which the maximal-adic filtration of an Artinian local algebra
vanishes. -/
public noncomputable def vanishingIndex (A : ArtinianLocalAlgCat.{u, v, w} Λ k) : ℕ :=
  Nat.find (exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian A)

/-- The maximal-adic filtration vanishes at `Deformation.vanishingIndex`. -/
public theorem vanishingIndex_spec (A : ArtinianLocalAlgCat.{u, v, w} Λ k) :
    maximalIdeal A ^ (vanishingIndex A + 1) = ⊥ :=
  Nat.find_spec (exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian A)

/-- The canonical map from an Artinian local algebra to the `n`-th adic truncation of the
complete local algebra it defines, given by reduction modulo `m ^ (n + 1)`. -/
public noncomputable def artinianAdicQuotient
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    A ⟶ AdicTruncation.obj (artinianToComplete.obj A) n := by
  let R := artinianToComplete.obj A
  let I := AdicTruncation.ideal R n
  let q := Ideal.Quotient.mkₐ Λ I
  have hI : I < ⊤ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact
    { hom := q
      isLocal := IsLocalHom.of_surjective q.toRingHom Ideal.Quotient.mk_surjective
      residue_comm := fun x => AdicTruncation.residueEquiv_residue_mk R n x }

/-- The underlying algebra map of `artinianAdicQuotient` is the quotient homomorphism. -/
public theorem artinianAdicQuotient_hom
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    (artinianAdicQuotient A n).hom =
      Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal (artinianToComplete.obj A) n) :=
  rfl

/-- At a level where the truncation ideal vanishes, the quotient map identifies an
Artinian local algebra with that truncation. -/
public noncomputable def artinianTruncationIso
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (hn : AdicTruncation.ideal (artinianToComplete.obj A) n = ⊥) :
    A ≅ AdicTruncation.obj (artinianToComplete.obj A) n := by
  let q := artinianAdicQuotient A n
  have hbij : Function.Bijective q.hom := by
    change Function.Bijective (Ideal.Quotient.mkₐ Λ
      (AdicTruncation.ideal (artinianToComplete.obj A) n))
    simpa [artinianToComplete] using (Ideal.Quotient.mk_bijective_iff_eq_bot _).2 hn
  let e := AlgEquiv.ofBijective q.hom hbij
  let qi : AdicTruncation.obj (artinianToComplete.obj A) n ⟶ A := {
    hom := e.symm
    isLocal := ⟨fun x hx => by simpa using IsUnit.map e.toAlgHom hx⟩
    residue_comm := fun x => by
      simpa [show q.hom (e.symm x) = x from e.apply_symm_apply x] using
        (q.residue_comm (e.symm x)).symm
  }
  exact ⟨q, qi, ArtinianLocalAlgCat.hom_ext (AlgHom.ext e.symm_apply_apply),
    ArtinianLocalAlgCat.hom_ext (AlgHom.ext e.apply_symm_apply)⟩

/-- The adic quotients of an Artinian local algebra are compatible with the transition maps
between adjacent truncations. -/
public theorem artinianAdicQuotient_transition
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    artinianAdicQuotient A (n + 1) ≫
        AdicTruncation.transition (artinianToComplete.obj A) n =
      artinianAdicQuotient A n :=
  ArtinianLocalAlgCat.hom_ext <| AlgHom.ext fun _ => rfl

/-- The adic quotients of an Artinian local algebra are natural in the algebra. -/
public theorem artinianAdicQuotient_naturality
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) (n : ℕ) :
    artinianAdicQuotient A n ≫
        (AdicTruncation.functor n).map (artinianToComplete.map f) =
      f ≫ artinianAdicQuotient B n :=
  ArtinianLocalAlgCat.hom_ext <| AlgHom.ext fun _ => rfl

end

end Deformation
