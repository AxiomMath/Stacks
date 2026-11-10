module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Algebraic.MvPolynomial
public import Mathlib.RingTheory.QuasiFinite.Weakly
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.GoingUp
public import StacksFrontier.RingTheory.IntegralClosure.Basic

/-!
# Relative assassins under algebraic base change

The relative assassin of a pulled-back quasi-coherent module is always contained in the inverse
image of the original relative assassin. If the base-change morphism is locally quasi-finite,
or more generally induces algebraic extensions on all residue fields, this containment is an
equality.

## Main results

* `AlgebraicGeometry.relativeAssassin_pullback_subset_preimage` gives the unconditional
  containment.
* `AlgebraicGeometry.preimage_relativeAssassin_eq_pullback_of_locallyQuasiFinite` gives equality
  for a locally quasi-finite base change.
* `AlgebraicGeometry.preimage_relativeAssassin_eq_pullback_of_isAlgebraic_residueField` gives
  equality whenever all induced residue-field extensions are algebraic.

## Implementation notes

The base-changed scheme is the chosen pullback. The algebra structure on each residue field
upstairs is induced by the corresponding `Scheme.Hom.residueFieldMap`. The locally quasi-finite
hypothesis is expressed by the local finite-type and fibre-isolation classes, which together
are the pointwise condition of Tag 01TD.

## References

* [Stacks Project, Tag 05KL](https://stacks.math.columbia.edu/tag/05KL)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

private theorem specPoint_mem_component_of_integral {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.IsIntegral K A] (p : PrimeSpectrum A) :
    ∃ Z ∈ irreducibleComponents (PrimeSpectrum A), IsGenericPoint p Z := by
  have hmin : p.asIdeal ∈ minimalPrimes A := by
    rw [minimalPrimes_eq_minimals]
    exact ⟨p.isPrime, fun q _ hqp =>
      ((Algebra.IsIntegral.isMaximal_of_isPrime (k := K) (S := A) q).eq_of_le
        p.isPrime.ne_top hqp).symm.le⟩
  exact ⟨PrimeSpectrum.zeroLocus p.asIdeal,
    by rwa [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, p.isPrime.radical],
    isGenericPoint_def.mpr (PrimeSpectrum.closure_singleton p)⟩

private theorem tensor_inl_integral_of_isAlgebraic
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (T : Scheme.Pullback.Triplet f g)
    (h : letI := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField T.s) (S'.residueField T.y)) :
    letI := T.tensorInl.hom.toAlgebra
    Algebra.IsIntegral (X.residueField T.x) (T.tensor : Type u) := by
  let K : Type u := S.residueField T.s
  let A : Type u := X.residueField T.x
  let B : Type u := S'.residueField T.y
  let C := (T.tensor : Type u)
  let a : K →+* A := (((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x).hom)
  let b : K →+* B := (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom)
  let i : A →+* C := T.tensorInl.hom
  let j : B →+* C := T.tensorInr.hom
  let : Algebra K A := a.toAlgebra
  let : Algebra K B := b.toAlgebra
  let : Algebra A C := i.toAlgebra
  let : Algebra B C := j.toAlgebra
  let : Algebra K C := (i.comp a).toAlgebra
  have : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change (i.comp a) x = (j.comp b) x
    have hp : CommRingCat.ofHom a ≫ T.tensorInl = CommRingCat.ofHom b ≫ T.tensorInr := by
      simpa [a, b, Scheme.Pullback.Triplet.tensor, Scheme.Pullback.Triplet.tensorInl,
        Scheme.Pullback.Triplet.tensorInr] using
        (CategoryTheory.Limits.pushout.condition
          (f := CommRingCat.ofHom a) (g := CommRingCat.ofHom b))
    exact congrArg (fun φ : CommRingCat.Hom (CommRingCat.of K) T.tensor => φ.hom x) hp)
  have hpo : CategoryTheory.IsPushout
      (CommRingCat.ofHom a) (CommRingCat.ofHom b) T.tensorInl T.tensorInr := by
    simpa [K, A, B, a, b, Scheme.Pullback.Triplet.tensor,
      Scheme.Pullback.Triplet.tensorInl, Scheme.Pullback.Triplet.tensorInr,
      CommRingCat.of_carrier] using
      (CategoryTheory.IsPushout.of_hasPushout
        (CommRingCat.ofHom a) (CommRingCat.ofHom b))
  have hpo' : CategoryTheory.IsPushout
      (CommRingCat.ofHom (algebraMap K A))
      (CommRingCat.ofHom (algebraMap K B))
      (CommRingCat.ofHom (algebraMap A C))
      (CommRingCat.ofHom (algebraMap B C)) := by
    convert hpo using 1
  have : Algebra.IsPushout K A B C := (CommRingCat.isPushout_iff_isPushout).mp hpo'
  have : Algebra.IsPushout K B A C := (Algebra.IsPushout.comm K A B C).mp ‹_›
  have : Algebra.IsIntegral K B := Algebra.isAlgebraic_iff_isIntegral.mp h
  exact Algebra.IsPushout.isIntegral K A B C

private theorem residueField_algebraic_over_triplet_base
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (T : Scheme.Pullback.Triplet f g)
    (hg : ∀ y : S',
      letI := (g.residueFieldMap y).hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (g y)) (S'.residueField y)) :
    letI := ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom.toAlgebra
    Algebra.IsAlgebraic (S.residueField T.s) (S'.residueField T.y) := by
  let K : Type u := S.residueField T.s
  let K' : Type u := S.residueField (g T.y)
  let B : Type u := S'.residueField T.y
  let e : K ≃+* K' := (S.residueFieldCongr T.hy).symm.commRingCatIsoToRingEquiv
  let : Algebra K B :=
    (((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom).toAlgebra
  let : Algebra K' B := (g.residueFieldMap T.y).hom.toAlgebra
  have heq : (algebraMap K' B).comp (e : K →+* K') =
      ((RingEquiv.refl B : B ≃+* B) : B →+* B).comp (algebraMap K B) := by
    change (g.residueFieldMap T.y).hom.comp (e : K →+* K') =
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y).hom
    rw [show (e : K →+* K') = (S.residueFieldCongr T.hy).inv.hom from
      Iso.commRingCatIsoToRingEquiv_toRingHom (S.residueFieldCongr T.hy).symm,
      ← CommRingCat.hom_comp]
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq e (RingEquiv.refl B) heq).mp (hg T.y)

private theorem residueField_finite_of_locallyQuasiFinite
    {S' S : Scheme.{u}} (g : S' ⟶ S) [LocallyQuasiFinite g] (y : S') :
    letI := (g.residueFieldMap y).hom.toAlgebra
    Module.Finite (S.residueField (g y)) (S'.residueField y) := by
  let R : Type u := S.presheaf.stalk (g y)
  let A : Type u := S'.presheaf.stalk y
  let φ : R →+* A := (g.stalkMap y).hom
  let : Algebra R A := φ.toAlgebra
  have : Algebra.QuasiFinite R A :=
    RingHom.quasiFinite_algebraMap.mp (Scheme.Hom.quasiFiniteAt g y)
  let : Algebra R (IsLocalRing.ResidueField A) :=
    ((IsLocalRing.residue A).comp φ).toAlgebra
  let : Algebra A (IsLocalRing.ResidueField A) := (IsLocalRing.residue A).toAlgebra
  have : Algebra.QuasiFinite A (IsLocalRing.ResidueField A) :=
    Algebra.QuasiFinite.of_surjective_algHom (Algebra.ofId A _) IsLocalRing.residue_surjective
  have : IsScalarTower R A (IsLocalRing.ResidueField A) := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.QuasiFinite R (IsLocalRing.ResidueField A) := Algebra.QuasiFinite.trans R A _
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  have : IsScalarTower R (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq'
      (RingHom.ext fun x => (IsLocalRing.ResidueField.map_residue φ x).symm)
  have : Algebra.QuasiFinite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) :=
    Algebra.QuasiFinite.of_restrictScalars R _ _
  change Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A)
  exact Module.Finite.of_quasiFinite

private theorem specOfPoint_mem_irreducibleComponents_of_isAlgebraic
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (hg : ∀ s' : S',
      letI := (g.residueFieldMap s').hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s'))
    (x' : pullback (C := Scheme.{u}) f g) :
    ∃ Z ∈ irreducibleComponents (Spec (Scheme.Pullback.Triplet.ofPoint x').tensor),
      IsGenericPoint (Scheme.Pullback.SpecOfPoint x') Z := by
  let T := Scheme.Pullback.Triplet.ofPoint x'
  let : Algebra (X.residueField T.x) (T.tensor : Type u) := T.tensorInl.hom.toAlgebra
  have : Algebra.IsIntegral (X.residueField T.x) (T.tensor : Type u) :=
    tensor_inl_integral_of_isAlgebraic f g T (residueField_algebraic_over_triplet_base f g T hg)
  exact specPoint_mem_component_of_integral (K := X.residueField T.x)
    (A := (T.tensor : Type u)) (Scheme.Pullback.SpecOfPoint x')

/-- The inverse image of the relative assassin is the relative assassin of the pullback when all
residue-field extensions of `g` are algebraic. -/
private theorem preimage_relativeAssassin_eq_pullback_of_forall_isAlgebraic
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [LocallyOfFiniteType f]
    (hg : ∀ s' : S',
      letI := (g.residueFieldMap s').hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s')) :
    (pullback.fst (C := Scheme.{u}) f g) ⁻¹' Stacks.Divisors.relativeAssassin f F =
      Stacks.Divisors.relativeAssassin (pullback.snd (C := Scheme.{u}) f g)
        ((Scheme.Modules.pullback (pullback.fst (C := Scheme.{u}) f g)).obj F) := by
  ext x'
  rw [mem_relativeAssassin_pullback_iff]
  exact ⟨fun hx => ⟨hx, specOfPoint_mem_irreducibleComponents_of_isAlgebraic f g hg x'⟩,
    And.left⟩

/-- **Stacks Project, Tag 05KL.** After arbitrary base change, the relative assassin of the
pulled-back module is contained in the inverse image of the original relative assassin. -/
@[stacks 05KL "unconditional containment"]
public theorem relativeAssassin_pullback_subset_preimage
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [LocallyOfFiniteType f] :
    Stacks.Divisors.relativeAssassin (pullback.snd (C := Scheme.{u}) f g)
        ((Scheme.Modules.pullback (pullback.fst (C := Scheme.{u}) f g)).obj F) ⊆
      (pullback.fst (C := Scheme.{u}) f g) ⁻¹'
        Stacks.Divisors.relativeAssassin f F :=
  fun x' hx' => ((mem_relativeAssassin_pullback_iff f g F x').mp hx').1

/-- **Stacks Project, Tag 05KL.** A locally quasi-finite base change pulls the relative
assassin back exactly. -/
@[stacks 05KL "equality for locally quasi-finite base change"]
public theorem preimage_relativeAssassin_eq_pullback_of_locallyQuasiFinite
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [LocallyQuasiFinite g] :
    (pullback.fst (C := Scheme.{u}) f g) ⁻¹' Stacks.Divisors.relativeAssassin f F =
      Stacks.Divisors.relativeAssassin (pullback.snd (C := Scheme.{u}) f g)
        ((Scheme.Modules.pullback (pullback.fst (C := Scheme.{u}) f g)).obj F) := by
  have hg : ∀ s' : S',
      let := (g.residueFieldMap s').hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s') := by
    intro s'
    let := (g.residueFieldMap s').hom.toAlgebra
    have := residueField_finite_of_locallyQuasiFinite g s'
    exact Algebra.IsAlgebraic.of_finite _ _
  exact preimage_relativeAssassin_eq_pullback_of_forall_isAlgebraic f g F hg

/-- **Stacks Project, Tag 05KL.** If every residue-field extension induced by the base-change
morphism is algebraic, then it pulls the relative assassin back exactly. -/
@[stacks 05KL "equality for algebraic residue-field extensions"]
public theorem preimage_relativeAssassin_eq_pullback_of_isAlgebraic_residueField
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (F : X.Modules)
    [F.IsQuasicoherent] [LocallyOfFiniteType f]
    (hg : ∀ s' : S',
      letI := (g.residueFieldMap s').hom.toAlgebra
      Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s')) :
    (pullback.fst (C := Scheme.{u}) f g) ⁻¹' Stacks.Divisors.relativeAssassin f F =
      Stacks.Divisors.relativeAssassin (pullback.snd (C := Scheme.{u}) f g)
        ((Scheme.Modules.pullback (pullback.fst (C := Scheme.{u}) f g)).obj F) := by
  exact preimage_relativeAssassin_eq_pullback_of_forall_isAlgebraic f g F hg

end AlgebraicGeometry

end
