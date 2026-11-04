module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField

/-!
# Strict henselizations are unchanged by an étale morphism

Let `f : U → X` be an étale morphism of schemes and let `u` be a point of `U`. A strict
henselization of the local ring of `X` at `f u` is canonically a local algebra over the local ring
of `U` at `u`, and is a strict henselization of that local ring. Thus the strict henselization of
a local ring of a scheme only depends on the étale site, which is what makes it the local ring of
the small étale site at a geometric point.

The ring-theoretic content is the same statement for a local ind-étale extension `A → B`: a strict
henselization of `A` is one of `B`. The map `B → A^{sh}` is produced by the lifting lemma for
ind-étale algebras into a henselian local ring, whose residue datum is supplied by embedding the
separable algebraic extension `κ(B)/κ(A)` into the separably closed residue field of `A^{sh}`.

## Main results

* `StacksDraft.exists_isLocalHom_algHom_of_indEtale`: a local ind-étale algebra over `A` maps,
  by a local `A`-algebra map, into a henselization of `A` with separably closed residue
  extension.
* `StacksDraft.exists_isHenselization_of_indEtale_base`: a henselization of a local ring `A` with
  separably closed residue extension `L` is a henselization of any local ind-étale `A`-algebra `B`
  with residue extension `L`.
* `AlgebraicGeometry.exists_isHenselization_stalk_of_etale`: a strict henselization of the local
  ring of `X` at `f u` is a strict henselization of the local ring of `U` at `u`, for `f` étale.

## Implementation notes

The residue datum of the lifting lemma is indexed by the residue field `(𝔪 A).ResidueField` of the
maximal ideal of `A` viewed as a prime, rather than by `IsLocalRing.ResidueField A`; the two are
canonically isomorphic but not definitionally equal, and the separability statement for weakly
étale maps is already stated in the former form, so the datum is built there.

## References

* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open IsLocalRing Stacks.Henselian.EtaleLifting

universe u

/-- **A local ind-étale algebra maps to a strict henselization of its base.** If `B` is a local
ind-étale algebra over a local ring `A` and `C` is a henselization of `A` with separably closed
residue extension, then there is a local `A`-algebra map `B → C`. -/
theorem StacksDraft.exists_isLocalHom_algHom_of_indEtale
    {A B C L : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C] [Field L]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra (ResidueField A) L] [IsSepClosure (ResidueField A) L]
    [Algebra A C] [IsHenselization A L C]
    (hAB : StacksDraft.IndEtale A B) :
    ∃ g : B →ₐ[A] C, IsLocalHom (g : B →+* C) := by
  have : HenselianLocalRing C := IsHenselization.henselian (R := A) (L := L)
  have : IsLocalHom (algebraMap A C) := IsHenselization.isLocalHom (R := A) (L := L)
  have hp : maximalIdeal A = (maximalIdeal C).comap (algebraMap A C) :=
    (maximalIdeal_comap (algebraMap A C)).symm
  have hpq : maximalIdeal A = (maximalIdeal B).comap (algebraMap A B) :=
    (maximalIdeal_comap (algebraMap A B)).symm
  let : Algebra (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField :=
    (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B) hpq).toAlgebra
  let : Algebra (maximalIdeal A).ResidueField (ResidueField C) :=
    (residueFieldMapBase (maximalIdeal A) hp).toAlgebra
  have : Algebra.IsSeparable (maximalIdeal A).ResidueField (maximalIdeal B).ResidueField :=
    (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B
      (Algebra.weaklyEtale_of_ind_etale hAB) (maximalIdeal A) (maximalIdeal B) hpq).1
  have : IsSepClosed (ResidueField C) := by
    obtain ⟨alg, -, hsep, -⟩ :=
      IsHenselization.exists_residueFieldAlgebra (R := A) (L := L) (Rh := C)
    let := alg
    have := hsep inferInstance
    exact IsSepClosure.sep_closed (ResidueField A)
  let τ : (maximalIdeal B).ResidueField →ₐ[(maximalIdeal A).ResidueField] ResidueField C :=
    IsSepClosed.lift
  have hτ : (τ : (maximalIdeal B).ResidueField →+* ResidueField C).comp
      (residueFieldMapFib (maximalIdeal A) (maximalIdeal B) hpq)
      = residueFieldMapBase (maximalIdeal A) hp := τ.comp_algebraMap
  exact ⟨algHom hAB (maximalIdeal A) hp (maximalIdeal B) hpq _ hτ, ((local_hom_TFAE _).out 5 1).mp
    (comap_maximalIdeal_algHom hAB (maximalIdeal A) hp (maximalIdeal B) hpq _ hτ).symm⟩

/-- **A strict henselization of a local ring is one of every local ind-étale algebra over it.**
If `B` is a local ind-étale algebra over a local ring `A` and `C` is a henselization of `A` with
separably closed residue extension `L`, then `C` is a local `B`-algebra and a henselization of `B`
with residue extension `L`, which is again separably closed. -/
theorem StacksDraft.exists_isHenselization_of_indEtale_base
    {A B C L : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C] [Field L]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra (ResidueField A) L] [IsSepClosure (ResidueField A) L]
    [Algebra A C] [IsHenselization A L C]
    (hAB : StacksDraft.IndEtale A B) :
    ∃ (algB : Algebra B C) (algκ : Algebra (ResidueField B) L),
      letI := algB
      letI := algκ
      IsScalarTower A B C ∧ IsLocalHom (algebraMap B C) ∧
        IsSepClosure (ResidueField B) L ∧ IsHenselization B L C := by
  obtain ⟨g, hg⟩ := StacksDraft.exists_isLocalHom_algHom_of_indEtale (L := L) (C := C) hAB
  let algB : Algebra B C := (g : B →+* C).toAlgebra
  have htower : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have hlocal : IsLocalHom (algebraMap B C) := hg
  obtain ⟨algκ, hH, hsc⟩ :=
    StacksDraft.exists_isHenselization_of_indEtale (A := A) (B := B) (C := C) (L := L)
      (StacksDraft.indEtale_of_comp hAB (IsHenselization.ind_etale (R := A) (L := L) (Rh := C)))
  exact ⟨algB, algκ, htower, hlocal, hsc inferInstance, hH⟩

namespace AlgebraicGeometry

/-- A strict henselization `Ash` of the local ring of `X` at `f u`, for `f : U ⟶ X` étale, is
canonically a local algebra over the local ring of `U` at `u` and is a strict henselization of
it, with the same separably closed residue extension `L`. -/
theorem exists_isHenselization_stalk_of_etale
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] (u : U)
    (L : Type u) [Field L]
    [Algebra (ResidueField (X.presheaf.stalk (f u))) L]
    [IsSepClosure (ResidueField (X.presheaf.stalk (f u))) L]
    (Ash : Type u) [CommRing Ash] [IsLocalRing Ash]
    [Algebra (X.presheaf.stalk (f u)) Ash]
    [IsHenselization (X.presheaf.stalk (f u)) L Ash] :
    ∃ (algB : Algebra (U.presheaf.stalk u) Ash)
      (algκ : Algebra (ResidueField (U.presheaf.stalk u)) L),
      letI : Algebra (X.presheaf.stalk (f u)) (U.presheaf.stalk u) :=
        (f.stalkMap u).hom.toAlgebra
      letI := algB
      letI := algκ
      IsScalarTower (X.presheaf.stalk (f u)) (U.presheaf.stalk u) Ash ∧
        IsLocalHom (algebraMap (U.presheaf.stalk u) Ash) ∧
          IsSepClosure (ResidueField (U.presheaf.stalk u)) L ∧
            IsHenselization (U.presheaf.stalk u) L Ash := by
  let : Algebra (X.presheaf.stalk (f u)) (U.presheaf.stalk u) := (f.stalkMap u).hom.toAlgebra
  have : IsLocalHom (algebraMap (X.presheaf.stalk (f u)) (U.presheaf.stalk u)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  exact StacksDraft.exists_isHenselization_of_indEtale_base (L := L) (C := Ash)
    (indEtale_stalkMap_of_etale f u)

end AlgebraicGeometry

end
