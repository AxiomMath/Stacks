module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic.WellDefined
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen

/-!
# Short exact sequences of coherent triples

Morphisms of coherent triples and their composition (`CoherentTriple.Hom`,
`CoherentTriple.Hom.comp`), and short exact sequences of coherent triples
(`CoherentTriple.ShortExact`), with their stability under replacing the first or the third term
by an isomorphic one.

This file is part of
`StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic`; see there
for the overview and references.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

-- The complete-lattice structure on `F.Submodule` already exists upstream; it is made available
-- locally rather than re-declared, because an anonymous `local instance` with this type gets a
-- derived name that collides with the identical one in
-- `StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerComplement.Basic`.
attribute [local instance] SheafOfModules.Submodule.instCompleteLattice

/-! ### Short exact sequences of coherent triples -/

/-- **A morphism of coherent triples.** It consists of a morphism of the modules on the
punctured spectrum and a morphism of the modules on the closed fibre which agree, through the
two gluing isomorphisms, over the punctured closed fibre. -/
public structure CoherentTriple.Hom {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T S : CoherentTriple A f) where
  /-- The morphism of the modules on the punctured spectrum. -/
  onPunctured : T.F ⟶ S.F
  /-- The morphism of the modules on the closed fibre. -/
  onClosedFibre : T.F₀ ⟶ S.F₀
  /-- The two morphisms agree over the punctured closed fibre. -/
  compatible :
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map onPunctured ≫ S.alpha.hom =
      T.alpha.hom ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map onClosedFibre

/-- **A short exact sequence of coherent triples.** The category of coherent triples is additive
but not abelian, and a sequence is declared short exact when both of its component sequences --
on the punctured spectrum and on the closed fibre -- are short exact. -/
public structure CoherentTriple.ShortExact {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T S R : CoherentTriple A f} (φ : T.Hom S) (ψ : S.Hom R) : Prop where
  /-- The composite vanishes on the punctured spectrum. -/
  zero_punctured : φ.onPunctured ≫ ψ.onPunctured = 0
  /-- The composite vanishes on the closed fibre. -/
  zero_closedFibre : φ.onClosedFibre ≫ ψ.onClosedFibre = 0
  /-- The sequence of modules on the punctured spectrum is short exact. -/
  punctured : (ShortComplex.mk φ.onPunctured ψ.onPunctured zero_punctured).ShortExact
  /-- The sequence of modules on the closed fibre is short exact. -/
  closedFibre : (ShortComplex.mk φ.onClosedFibre ψ.onClosedFibre zero_closedFibre).ShortExact

/-! ### Composing morphisms of coherent triples -/

/-- **The composition of two morphisms of coherent triples.** The compatibility condition of the
composite is the two compatibility squares pasted. -/
public noncomputable def CoherentTriple.Hom.comp {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T S R : CoherentTriple A f} (φ : T.Hom S) (ψ : S.Hom R) : T.Hom R where
  onPunctured := φ.onPunctured ≫ ψ.onPunctured
  onClosedFibre := φ.onClosedFibre ≫ ψ.onClosedFibre
  compatible := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      ψ.compatible, ← Category.assoc, φ.compatible, Category.assoc]

/-- The punctured-spectrum member of a composite is the composite of the members. -/
public theorem CoherentTriple.Hom.comp_onPunctured {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S R : CoherentTriple A f} (φ : T.Hom S) (ψ : S.Hom R) :
    (φ.comp ψ).onPunctured = φ.onPunctured ≫ ψ.onPunctured := rfl

/-- The closed-fibre member of a composite is the composite of the members. -/
public theorem CoherentTriple.Hom.comp_onClosedFibre {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S R : CoherentTriple A f} (φ : T.Hom S) (ψ : S.Hom R) :
    (φ.comp ψ).onClosedFibre = φ.onClosedFibre ≫ ψ.onClosedFibre := rfl

/-- **A short exact sequence of coherent triples stays short exact when its third term is
replaced by an isomorphic one.** The replacement is a morphism of coherent triples both of whose
members are isomorphisms, and the new surjection is the old one composed with it.

This is the transport the second clause of `Stacks.Algebraization.HasHilbertInductionStep` needs:
the quotient the cokernel machinery produces in degree `n` is identified with the `n`-th twist of
one fixed triple, and the short exactness has to move along that identification. -/
public theorem CoherentTriple.ShortExact.compIso {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S R R' : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (h : CoherentTriple.ShortExact φ ψ) (θ : R.Hom R') [IsIso θ.onPunctured]
    [IsIso θ.onClosedFibre] : CoherentTriple.ShortExact φ (ψ.comp θ) where
  zero_punctured := by
    rw [CoherentTriple.Hom.comp_onPunctured, ← Category.assoc, h.zero_punctured, zero_comp]
  zero_closedFibre := by
    rw [CoherentTriple.Hom.comp_onClosedFibre, ← Category.assoc, h.zero_closedFibre, zero_comp]
  punctured := by
    refine ShortComplex.shortExact_of_iso ?_ h.punctured
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (asIso θ.onPunctured)
      (by simp) (by simp [CoherentTriple.Hom.comp_onPunctured])
  closedFibre := by
    refine ShortComplex.shortExact_of_iso ?_ h.closedFibre
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (asIso θ.onClosedFibre)
      (by simp) (by simp [CoherentTriple.Hom.comp_onClosedFibre])

/-- **A short exact sequence of coherent triples stays short exact when its first term is
replaced by an isomorphic one.** The replacement is a morphism of coherent triples both of whose
members are isomorphisms, and the new injection is the old one precomposed with it.

This is the companion of `Stacks.Algebraization.CoherentTriple.ShortExact.compIso` at the other
end of the sequence. It is what puts the degree-one sequence of the induction step of
[Stacks, Tag 0F27] in the shape the twisting consumes: the sequence the cokernel machinery
produces begins at the zeroth twist `T ⊗ L^{⊗ 0}`, while twisting by `L^{⊗ n}` has to begin at
`T` itself if the result is to begin at `T ⊗ L^{⊗ n}`. The replacement is then the degree-zero
identification `Stacks.Algebraization.CoherentTriple.twistZZeroHom`. -/
public theorem CoherentTriple.ShortExact.isoComp {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T T' S R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (h : CoherentTriple.ShortExact φ ψ) (θ : T'.Hom T) [IsIso θ.onPunctured]
    [IsIso θ.onClosedFibre] : CoherentTriple.ShortExact (θ.comp φ) ψ where
  zero_punctured := by
    rw [CoherentTriple.Hom.comp_onPunctured, Category.assoc, h.zero_punctured, comp_zero]
  zero_closedFibre := by
    rw [CoherentTriple.Hom.comp_onClosedFibre, Category.assoc, h.zero_closedFibre, comp_zero]
  punctured := by
    refine ShortComplex.shortExact_of_iso ?_ h.punctured
    exact ShortComplex.isoMk (asIso θ.onPunctured).symm (Iso.refl _) (Iso.refl _)
      (by simp [CoherentTriple.Hom.comp_onPunctured]) (by simp)
  closedFibre := by
    refine ShortComplex.shortExact_of_iso ?_ h.closedFibre
    exact ShortComplex.isoMk (asIso θ.onClosedFibre).symm (Iso.refl _) (Iso.refl _)
      (by simp [CoherentTriple.Hom.comp_onClosedFibre]) (by simp)

end Stacks.Algebraization

end
