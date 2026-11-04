module

public import StacksFrontier.RingTheory.Koszul.HomotopyCofiber
import all StacksFrontier.RingTheory.Koszul.HomotopyCofiber
public import StacksFrontier.RingTheory.Koszul.PowerLift.SingleTorsion
public import StacksFrontier.Homology.DerivedComplete.KoszulTensorVanishing
import all StacksFrontier.Homology.DerivedComplete.KoszulTensorVanishing

@[expose] public noncomputable section

/-!
# Morphisms from a Koszul complex into a complex with power-torsion cohomology

Let `A` be a commutative ring, let `f₁, …, f_r ∈ A`, let `g : A` and let `E` be an object of
`D(A)`. If every element of `H^j(E)` is annihilated by a power of `g` for every `j` in the window
`-r, …, 0` carrying the Koszul complex of the sequence, then every morphism in `D(A)` from that
Koszul complex to `E` is annihilated by a power of `g`.

The Koszul complex of a sequence of length `m + 1` is the mapping cone of multiplication by its
last entry on the Koszul complex of the first `m` entries ([Stacks, Tag 0629]), and the Koszul
complex of the empty sequence is the ring in degree `0`. So the statement follows from the base
case `Stacks.Koszul.PowerLift.homPowerTorsion_singleRing` by induction along those cones, using
that the property of having power-torsion Hom into `E` passes along distinguished triangles
(`Stacks.Koszul.PowerLift.HomPowerTorsion.of_distTriang₃`). Each cone shifts the window by one
degree, which is why the induction is run over all shifts of the Koszul complex at once.

This is the half of [Stacks, Tag 08E3] that controls `Hom(K, E)`. What it does not yet supply is
the compatibility of the cone presentation with the canonical map `A[0] ⟶ K` of
[Stacks, Tag 0BKC], which is what turns the control into the actual lifting statement.

## Main results

* `Stacks.Koszul.PowerLift.homPowerTorsion_koszul` — morphisms from the Koszul complex of a
  sequence into a complex whose cohomology is power torsion in the relevant degrees are power
  torsion.

## Implementation notes

The Koszul complex is the `ℕ`-indexed chain complex `Koszul.seqComplex`, re-indexed as a cochain
complex concentrated in degrees `-r, …, 0` along `ComplexShape.embeddingDownNat` and localized;
this is the same object as the terms of `AdicKoszul.canonicalKoszulPowerSystem`, in whose language
[Stacks, Tag 08E3] is stated.

Every statement carries a free `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` binder and mentions
`CategoryTheory.HasDerivedCategory.standard` nowhere, so the results are available at the locally
small model `ModuleCat.hasDerivedCategory`
(`StacksFrontier/AlgebraicGeometry/DerivedTilde/Basic.lean`) as well as at the standard one; this is
inherited from `StacksFrontier/RingTheory/Koszul/PowerLift/SingleTorsion.lean`, and the
triangle calculus it is built on
(`StacksFrontier/RingTheory/Koszul/PowerLift/HomTorsion.lean`) is model-free. The identification of
the Koszul complex of a snoc with a mapping cone is a statement about cochain complexes and so
carries no model at all.

Four ingredients already exist in the library as `private` declarations and are reused through
`import all` rather than reproved: the comparison between the explicit cone complex of
[Stacks, Tag 0628] and `HomologicalComplex.homotopyCofiber`, and the commutation of extension
with cone formation, both in `StacksFrontier/RingTheory/Koszul/HomotopyCofiber.lean`; and the
identification of the Koszul complex of the empty sequence with the ring in degree `0`, and the
commutation of extension with multiplication by a scalar, both in
`StacksFrontier/Homology/DerivedComplete/KoszulTensorVanishing.lean`.

## References

* [Stacks Project, Tag 08E3](https://stacks.math.columbia.edu/tag/08E3)
* [Stacks Project, Tag 0629](https://stacks.math.columbia.edu/tag/0629)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u w

namespace Stacks.Koszul.PowerLift

variable {A : Type u} [CommRing A]

/-- The Koszul complex of a finite sequence as a cochain complex in degrees `-r, …, 0`. -/
private abbrev koszulCochain {r : ℕ} (f : Fin r → A) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj (Koszul.seqComplex f)

/-- The Koszul complex of a finite sequence as an object of `D(A)`. -/
private abbrev koszulObj [HasDerivedCategory.{w} (ModuleCat.{u} A)] {r : ℕ} (f : Fin r → A) :
    DerivedCategory (ModuleCat.{u} A) :=
  DerivedCategory.Q.obj (koszulCochain f)

/-- The ring placed in cohomological degree `j`, as an object of `D(A)`. -/
private abbrev ringAt (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (j : ℤ) : DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) j).obj (ModuleCat.of A A)

/-! ### Adjoining one entry forms a mapping cone -/

/-- **Adjoining an entry to a sequence forms a mapping cone.** The cochain Koszul complex of
`Fin.snoc f a` is the mapping cone of multiplication by `a` on the cochain Koszul complex of `f`.
This is [Stacks, Tag 0629] after re-indexing. -/
private theorem exists_iso_koszulCochain_snoc {r : ℕ} (f : Fin r → A) (a : A) :
    Nonempty (koszulCochain (Fin.snoc f a) ≅
      CochainComplex.mappingCone (a • 𝟙 (koszulCochain f))) := by
  obtain ⟨e1⟩ := Koszul.seqComplex_snoc_iso_cone f a
  let e3 : Koszul.seqComplex (Fin.snoc f a) ≅
      HomologicalComplex.homotopyCofiber (a • 𝟙 (Koszul.seqComplex f)) :=
    e1 ≪≫ (Koszul.cofiberIsoCone.{u, u} (Koszul.seqComplex f) (a • 𝟙 _)).symm
  refine ⟨(ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).mapIso e3 ≪≫
    Koszul.extendHomotopyCofiberIso _ _ (a • 𝟙 (Koszul.seqComplex f)) ≪≫
    eqToIso ?_⟩
  rw [KoszulTensorVanishing.extendMap_smul_id]
  rfl

/-! ### The induction -/

private theorem homPowerTorsion_koszulObj_shift [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) :
    ∀ (r : ℕ) (f : Fin r → A) (m : ℤ),
      (∀ j : ℤ, -(r : ℤ) - m ≤ j → j ≤ -m → HomPowerTorsion g (ringAt A j) E) →
      HomPowerTorsion g ((koszulObj f)⟦m⟧) E := by
  intro r
  induction r with
  | zero =>
    intro f m hgen
    let e : koszulObj f ≅ ringAt A 0 := KoszulTensorVanishing.koszul_empty_iso_single f
    refine HomPowerTorsion.of_iso
      ((((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso m (-m) 0
            (by omega)).app (ModuleCat.of A A)).symm ≪≫
        ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) m).mapIso e).symm) ?_
    exact hgen (-m) (by omega) (by omega)
  | succ r ih =>
    intro f m hgen
    have hs : Fin.snoc (fun i : Fin r ↦ f i.castSucc) (f (Fin.last r)) = f := by
      ext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    have h₂ : HomPowerTorsion g ((koszulObj (fun i : Fin r ↦ f i.castSucc))⟦m⟧) E :=
      ih _ m (fun j hj₁ hj₂ ↦ hgen j (by omega) hj₂)
    have h₁' : HomPowerTorsion g ((koszulObj (fun i : Fin r ↦ f i.castSucc))⟦m + 1⟧) E :=
      ih _ (m + 1) (fun j hj₁ hj₂ ↦ hgen j (by omega) (by omega))
    have h₁ : HomPowerTorsion g
        (((koszulObj (fun i : Fin r ↦ f i.castSucc))⟦m⟧)⟦(1 : ℤ)⟧) E :=
      HomPowerTorsion.of_iso
        ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} A)) m 1 (m + 1) rfl).app
          (koszulObj (fun i : Fin r ↦ f i.castSucc))) h₁'
    obtain ⟨e⟩ := exists_iso_koszulCochain_snoc (fun i : Fin r ↦ f i.castSucc) (f (Fin.last r))
    rw [← hs]
    refine HomPowerTorsion.of_iso
      (((shiftFunctor _ m).mapIso (DerivedCategory.Q.mapIso e)).symm) ?_
    exact HomPowerTorsion.of_distTriang₃ _
      (Triangle.shift_distinguished _
        (DerivedCategory.mappingCone_triangle_distinguished
          (f (Fin.last r) • 𝟙 (koszulCochain (fun i : Fin r ↦ f i.castSucc)))) m)
      h₂ h₁

/-- **Morphisms from a Koszul complex into a complex with power-torsion cohomology are power
torsion.** Let `f₁, …, f_r ∈ A`, let `g : A` and let `E` be an object of `D(A)` all of whose
cohomology modules in degrees `-r, …, 0` are `g`-power torsion. Then every morphism in `D(A)`
from the Koszul complex of `f₁, …, f_r`, viewed in degrees `-r, …, 0`, to `E` is annihilated by
a power of `g`. -/
public theorem homPowerTorsion_koszul [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (g : A) (E : DerivedCategory (ModuleCat.{u} A)) {r : ℕ}
    (f : Fin r → A)
    (hE : ∀ j : ℤ, -(r : ℤ) ≤ j → j ≤ 0 →
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj E, ∃ k : ℕ, g ^ k • x = 0) :
    HomPowerTorsion g
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
          (Koszul.seqComplex f))) E := by
  have h := homPowerTorsion_koszulObj_shift g E r f 0
    (fun j hj₁ hj₂ ↦ homPowerTorsion_singleRing g j E (hE j (by omega) (by omega)))
  exact HomPowerTorsion.of_iso
    ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} A)) ℤ).app (koszulObj f)) h

end Stacks.Koszul.PowerLift

end
