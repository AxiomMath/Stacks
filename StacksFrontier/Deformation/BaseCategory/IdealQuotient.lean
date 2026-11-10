module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Basic

/-!
# Quotients by an ideal in the category of Artinian local algebras

Dividing an object `A` of `𝒞_Λ` by an ideal `I ⊆ m_A` again gives an object of `𝒞_Λ`: the
quotient stays Artinian and local, and because `I` is contained in the maximal ideal the
residue field does not change, so the chosen identification with `k` transports. This file
builds that quotient object, its projection, the morphism it induces from a morphism of
`𝒞_Λ` preserving the chosen ideals, and the factorization of a surjection through the
quotient by an ideal inside its kernel.

Nothing here is a statement of the Stacks Project; it is the shared construction used by
the criteria for essential surjections and by the extension of Schlessinger's condition
(S2) to finite-dimensional square-zero extensions.

## Main definitions

* `Deformation.ArtinianLocalAlgCat.idealQuotientResidueEquiv`: the residue-field
  identification of a quotient by an ideal inside the maximal ideal.
* `Deformation.ArtinianLocalAlgCat.idealQuotientObj`: the quotient, as an object of `𝒞_Λ`.
* `Deformation.ArtinianLocalAlgCat.idealQuotientProjection`: its projection from `A`.
* `Deformation.ArtinianLocalAlgCat.idealQuotientMap`: the morphism of quotients induced by
  a morphism carrying the one chosen ideal into the other.
* `Deformation.ArtinianLocalAlgCat.idealQuotientFactor`: the factorization of a surjection
  through the quotient by an ideal inside its kernel.

## Main results

* `Deformation.ArtinianLocalAlgCat.idealQuotientResidueEquiv_residue_mk`: the identification
  is compatible with the residues of representatives.
* `Deformation.ArtinianLocalAlgCat.idealQuotientProjection_comp_idealQuotientMap`: the
  induced morphism commutes with the projections.
* `Deformation.ArtinianLocalAlgCat.idealQuotientMap_surjective`: it is surjective when the
  original morphism is.
* `Deformation.ArtinianLocalAlgCat.idealQuotientProjection_comp_idealQuotientFactor`: the
  factorization recovers the original surjection.
* `Deformation.ArtinianLocalAlgCat.isIso_of_bijective_hom`: a morphism of `𝒞_Λ` whose
  underlying algebra map is bijective is an isomorphism.
* `Deformation.ArtinianLocalAlgCat.ker_le_maximalIdeal`: the kernel of a morphism of `𝒞_Λ`
  lies in the maximal ideal of its source.

## Implementation notes

The hypothesis `I ≤ m_A` is what makes `A ⧸ I` nontrivial, hence local with the same residue
field; it is carried explicitly rather than packaged, because the two consumers supply
different ideals (`m_A²`, `m_Λ A + m_A²`, and the kernel of a coordinate map). The
residue-field identification is defined as the inverse of the map induced on residue fields
by the projection, composed with the identification already chosen on `A`.
-/

@[expose] public section

namespace Deformation

namespace ArtinianLocalAlgCat

section
open CategoryTheory IsLocalRing
universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The residue field of `A` is unchanged by dividing out an ideal inside the maximal ideal,
so the chosen identification with `k` transports to the quotient. -/
noncomputable def idealQuotientResidueEquiv
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (I : Ideal A)
    (hI : I ≤ maximalIdeal A) :
    letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt hI (maximalIdeal.isMaximal A).lt_top).ne
    letI : IsLocalRing (A ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ResidueField (A ⧸ I) ≃ₐ[Λ] k := by
  letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hI (maximalIdeal.isMaximal A).lt_top).ne
  letI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ I
  letI : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  have hbij : Function.Bijective (ResidueField.mapAlgHom q) := by
    refine ⟨RingHom.injective _, fun y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨residue A r, rfl⟩
  exact (AlgEquiv.ofBijective (ResidueField.mapAlgHom q) hbij).symm.trans A.residueEquiv

/-- The transported identification sends the residue of the class of `r` to the image of the
residue of `r`. -/
@[simp] theorem idealQuotientResidueEquiv_residue_mk
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (I : Ideal A)
    (hI : I ≤ maximalIdeal A) (r : A) :
    letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt hI (maximalIdeal.isMaximal A).lt_top).ne
    letI : IsLocalRing (A ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    idealQuotientResidueEquiv A I hI (residue _ (Ideal.Quotient.mk I r)) =
      A.residueEquiv (residue A r) := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hI (maximalIdeal.isMaximal A).lt_top).ne
  let _ : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ I
  let _ : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  change A.residueEquiv
    ((AlgEquiv.ofBijective (ResidueField.mapAlgHom q) _).symm
      (residue _ (q r))) = _
  exact congrArg A.residueEquiv
    ((AlgEquiv.ofBijective (ResidueField.mapAlgHom q) _).symm_apply_apply (residue A r))

/-- The quotient of an object of `𝒞_Λ` by an ideal inside its maximal ideal, as an object of
`𝒞_Λ`. -/
noncomputable def idealQuotientObj
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (I : Ideal A)
    (hI : I ≤ maximalIdeal A) : ArtinianLocalAlgCat.{u, v, w} Λ k := by
  letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hI (maximalIdeal.isMaximal A).lt_top).ne
  letI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact { carrier := A ⧸ I, residueEquiv := idealQuotientResidueEquiv A I hI }

/-- The projection from an object of `𝒞_Λ` onto its quotient by an ideal inside the maximal
ideal. -/
noncomputable def idealQuotientProjection
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (I : Ideal A)
    (hI : I ≤ maximalIdeal A) : A ⟶ idealQuotientObj A I hI := by
  letI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hI (maximalIdeal.isMaximal A).lt_top).ne
  letI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ I
  exact { hom := q
          isLocal := IsLocalHom.of_surjective q.toRingHom Ideal.Quotient.mk_surjective
          residue_comm := idealQuotientResidueEquiv_residue_mk A I hI }

/-- A morphism of `𝒞_Λ` carrying the ideal chosen on its source into the ideal chosen on its
target induces a morphism of the two quotients. -/
noncomputable def idealQuotientMap
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (IB : Ideal B) (IA : Ideal A)
    (hB : IB ≤ maximalIdeal B) (hA : IA ≤ maximalIdeal A)
    (hmap : IB ≤ IA.comap f.hom) :
    idealQuotientObj B IB hB ⟶ idealQuotientObj A IA hA := by
  letI : Nontrivial (B ⧸ IB) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hB (maximalIdeal.isMaximal B).lt_top).ne
  letI : IsLocalRing (B ⧸ IB) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IB) Ideal.Quotient.mk_surjective
  letI : Nontrivial (A ⧸ IA) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hA (maximalIdeal.isMaximal A).lt_top).ne
  letI : IsLocalRing (A ⧸ IA) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IA) Ideal.Quotient.mk_surjective
  let g := Ideal.quotientMapₐ IA f.hom hmap
  have hg : IsLocalHom g.toRingHom := by
    refine ⟨fun x hx ↦ ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.mk IB).isUnit_map (f.isLocal.map_nonunit r
      ((IsLocalHom.of_surjective (Ideal.Quotient.mk IA) Ideal.Quotient.mk_surjective).map_nonunit
        (f.hom r) hx))
  refine { hom := g, isLocal := hg, residue_comm := ?_ }
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change idealQuotientResidueEquiv A IA hA
      (residue _ (Ideal.Quotient.mk IA (f.hom r))) =
    idealQuotientResidueEquiv B IB hB (residue _ (Ideal.Quotient.mk IB r))
  rw [idealQuotientResidueEquiv_residue_mk, idealQuotientResidueEquiv_residue_mk]
  exact f.residue_comm r

/-- The induced morphism of quotients commutes with the two projections. -/
@[simp] theorem idealQuotientProjection_comp_idealQuotientMap
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (IB : Ideal B) (IA : Ideal A)
    (hB : IB ≤ maximalIdeal B) (hA : IA ≤ maximalIdeal A)
    (hmap : IB ≤ IA.comap f.hom) :
    idealQuotientProjection B IB hB ≫ idealQuotientMap f IB IA hB hA hmap =
      f ≫ idealQuotientProjection A IA hA := by
  apply hom_ext; ext x; rfl

/-- The morphism induced on quotients by a surjection is surjective. -/
theorem idealQuotientMap_surjective
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (IB : Ideal B) (IA : Ideal A)
    (hB : IB ≤ maximalIdeal B) (hA : IA ≤ maximalIdeal A)
    (hmap : IB ≤ IA.comap f.hom)
    (hf : Function.Surjective f.hom) :
    Function.Surjective (idealQuotientMap f IB IA hB hA hmap).hom := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨b, hb⟩ := hf a
  exact ⟨Ideal.Quotient.mk IB b, congrArg (Ideal.Quotient.mk IA) hb⟩

/-- The kernel of a morphism of `𝒞_Λ` is contained in the maximal ideal of its source,
because the morphism respects the chosen identifications of the residue fields. -/
theorem ker_le_maximalIdeal
    {A A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ A₀) :
    RingHom.ker f.hom.toRingHom ≤ maximalIdeal A := by
  intro x hx
  have hzero : A.residueEquiv (residue A x) = A.residueEquiv 0 := by
    simpa [show f.hom x = 0 from hx] using (f.residue_comm x).symm
  exact (residue_eq_zero_iff x).1 (A.residueEquiv.injective hzero)

/-- A surjection of `𝒞_Λ` factors through the quotient of its source by any ideal contained
in its kernel. -/
noncomputable def idealQuotientFactor
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) (J : Ideal B)
    (hJker : J ≤ RingHom.ker f.hom.toRingHom)
    (hJmax : J ≤ maximalIdeal B) :
    idealQuotientObj B J hJmax ⟶ A := by
  letI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt hJmax (maximalIdeal.isMaximal B).lt_top).ne
  letI : IsLocalRing (B ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let q : B →ₐ[Λ] B ⧸ J := Ideal.Quotient.mkₐ Λ J
  have hker : RingHom.ker q.toRingHom ≤ RingHom.ker f.hom.toRingHom :=
    fun b hb ↦ hJker (by simpa [q] using hb)
  let g : B ⧸ J →ₐ[Λ] A := AlgHom.liftOfSurjective q
    Ideal.Quotient.mk_surjective f.hom hker
  have hg_apply (b : B) : g (q b) = f.hom b := by
    simpa [g] using
      (AlgHom.liftOfSurjective_apply q Ideal.Quotient.mk_surjective f.hom hker b)
  have hg : Function.Surjective g := fun a ↦
    let ⟨b, hb⟩ := hf a
    ⟨q b, (hg_apply b).trans hb⟩
  refine ⟨g, IsLocalHom.of_surjective g.toRingHom hg, ?_⟩
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  calc
    A.residueEquiv (residue A (g (q b))) =
        A.residueEquiv (residue A (f.hom b)) := by rw [hg_apply]
    _ = B.residueEquiv (residue B b) := f.residue_comm b
    _ = (idealQuotientObj B J hJmax).residueEquiv
        (residue (idealQuotientObj B J hJmax) (q b)) :=
      ((idealQuotientProjection B J hJmax).residue_comm b).symm

/-- The factorization through the quotient recovers the original surjection. -/
theorem idealQuotientProjection_comp_idealQuotientFactor
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) (J : Ideal B)
    (hJker : J ≤ RingHom.ker f.hom.toRingHom)
    (hJmax : J ≤ maximalIdeal B) :
    idealQuotientProjection B J hJmax ≫ idealQuotientFactor f hf J hJker hJmax = f :=
  hom_ext <| AlgHom.ext fun b ↦ AlgHom.liftOfSurjective_apply (Ideal.Quotient.mkₐ Λ J)
    Ideal.Quotient.mk_surjective f.hom (fun x hx ↦ hJker (by simpa using hx)) b

/-- A morphism of `𝒞_Λ` whose underlying algebra homomorphism is bijective is an
isomorphism: the inverse algebra equivalence is again local and respects the chosen
residue-field identifications. -/
theorem isIso_of_bijective_hom
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B)
    (hf : Function.Bijective f.hom) : IsIso f := by
  let e : A ≃ₐ[Λ] B := AlgEquiv.ofBijective f.hom hf
  let s : B ⟶ A :=
    { hom := e.symm.toAlgHom
      isLocal := ⟨fun b hb ↦ by simpa using hb.map e.toRingHom⟩
      residue_comm := fun b ↦ (f.residue_comm (e.symm b)).symm.trans
        (congrArg (fun z : B ↦ B.residueEquiv (residue B z)) (e.apply_symm_apply b)) }
  exact ⟨s, hom_ext (AlgHom.ext e.symm_apply_apply), hom_ext (AlgHom.ext e.apply_symm_apply)⟩

end

end ArtinianLocalAlgCat

end Deformation

end
