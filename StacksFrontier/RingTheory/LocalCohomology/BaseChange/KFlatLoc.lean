module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.RingTheory.LocalCohomology.BaseChange.ExtendLoc

/-!
# Localizing a K-flat complex away from an element

Let `a` be an element of a commutative ring `A` and let `P` be a K-flat complex of
`A`-modules. Then the degreewise localization `P[1/a]` is again K-flat.

## Main definitions

* `Stacks.LocalCohomology.locComplexFunctor` — degreewise localization away from `a`, on
  complexes.

## Main results

* `Stacks.LocalCohomology.isColimitLocCoconeCx` — the colimit presentation on complexes.
* `Stacks.LocalCohomology.kFlat_locComplex` — localization preserves K-flatness.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Multiplication by `a`, as an endomorphism of a complex. -/
def smulHomCx (a : A) (P : CochainComplex (ModuleCat.{max u w} A) ℤ) : P ⟶ P where
  f n := smulHom a (P.X n)
  comm' i j _ := by
    ext m
    change (P.d i j).hom (a • m) = a • (P.d i j).hom m
    exact map_smul _ a m

/-- The sequence `P --a--> P --a--> ⋯` of multiplications by `a`, on complexes. -/
@[reducible]
def mulSeqCx (a : A) (P : CochainComplex (ModuleCat.{max u w} A) ℤ) :
    ℕ ⥤ CochainComplex (ModuleCat.{max u w} A) ℤ where
  obj _ := P
  map {i j} φ := smulHomCx (a ^ (j - i)) P
  map_id i := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    ext m
    change a ^ (i - i) • m = m
    rw [Nat.sub_self, pow_zero, one_smul]
  map_comp {i j k} φ ψ := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    ext m
    change a ^ (k - i) • m = a ^ (k - j) • (a ^ (j - i) • m)
    rw [← mul_smul, ← pow_add, Nat.sub_add_sub_cancel (leOfHom ψ) (leOfHom φ)]

/-- The transition map `n ⟶ n + 1` of `mulSeqCx a P` is multiplication by `a`. -/
lemma mulSeqCx_map_succ (a : A) (P : CochainComplex (ModuleCat.{max u w} A) ℤ) (n : ℕ) :
    (mulSeqCx.{u, w} a P).map (homOfLE (Nat.le_add_right n 1)) = smulHomCx a P := by
  change smulHomCx (a ^ (n + 1 - n)) P = _
  rw [Nat.add_sub_cancel_left, pow_one]

/-- Degreewise localization away from `a`, on complexes. -/
abbrev locComplexFunctor (a : A) :
    CochainComplex (ModuleCat.{max u w} A) ℤ ⥤ CochainComplex (ModuleCat.{max u w} A) ℤ :=
  (locFunctor.{u, w} a).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The `n`-th leg `m ↦ m/aⁿ` of the colimit presentation, on complexes. -/
def locLegCx (a : A) (P : CochainComplex (ModuleCat.{max u w} A) ℤ) (n : ℕ) :
    P ⟶ (locComplexFunctor.{u, w} a).obj P where
  f i := locLeg a (P.X i) n
  comm' i j _ := (locLeg_naturality.{u, w} a (P.d i j) n).symm

/-- The cocone exhibiting `P[1/a]` as the colimit of the multiplication-by-`a` sequence. -/
def locCoconeCx (a : A) (P : CochainComplex (ModuleCat.{max u w} A) ℤ) :
    Cocone (mulSeqCx.{u, w} a P) where
  pt := (locComplexFunctor.{u, w} a).obj P
  ι := NatTrans.ofSequence (F := mulSeqCx.{u, w} a P)
    (G := (Functor.const ℕ).obj ((locComplexFunctor.{u, w} a).obj P))
    (fun n ↦ locLegCx.{u, w} a P n) (fun n ↦ by
      refine Eq.trans ?_ (Category.comp_id (locLegCx.{u, w} a P n)).symm
      rw [mulSeqCx_map_succ]
      refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
      ext m
      exact locLeg_succ_smul a (P.X i) n m)

/-- The cocone `locCoconeCx a P` exhibits `P[1/a]` as the colimit of the
multiplication-by-`a` sequence. -/
def isColimitLocCoconeCx (a : A) (P : CochainComplex (ModuleCat.{max u w} A) ℤ) :
    IsColimit (locCoconeCx.{u, w} a P) :=
  HomologicalComplex.isColimitOfEval _ _ (fun i ↦ isColimitLocCocone.{u, w} a (P.X i))

/-- Localization away from an element preserves K-flatness. -/
lemma kFlat_locComplex (a : A) (P : CochainComplex (ModuleCat.{max u w} A) ℤ)
    (hP : CochainComplex.KFlat.{u, w} P) :
    CochainComplex.KFlat.{u, w} ((locComplexFunctor.{u, w} a).obj P) :=
  CochainComplex.KFlat.of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitLocCoconeCx.{u, w} a P))
    (CochainComplex.KFlat.kFlat_colimit (mulSeqCx.{u, w} a P) fun _ ↦ hP)

end Stacks.LocalCohomology

end
