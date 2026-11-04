module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp

/-!
# Degrees of composite finite locally free morphisms

If `f : X ⟶ Y` is finite locally free of degree `r` and `g : Y ⟶ Z` is finite and flat, then the
rank function of `f ≫ g` is `r` times that of `g`. In particular a composite of finite locally
free morphisms of degrees `r` and `s` is finite locally free of degree `r * s`
([Stacks, Tag 02KC] together with multiplicativity of degrees).

## Main results

* `Stacks.Morphisms.finrank_comp_eq_mul`: `(f ≫ g).finrank z = r * g.finrank z`.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_comp`: degrees multiply under composition.

## Implementation notes

The rank function is compatible with base change, so the computation is done over the residue
field of a point of `Z`. There the target of `f` is the spectrum of a finite algebra `B` over a
field, which is Artinian and hence semilocal; the sections `C` of the source of `f` form a finite
flat `B`-module of constant rank `r`, hence a free one (Stacks Tag 02M9), and so
`dim C = r * dim B`. The argument is the one used
for Stacks 0B9I (addition).

## References

* [Stacks Project, Tag 02KC](https://stacks.math.columbia.edu/tag/02KC)
* [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.Morphisms

/-- Over a finite algebra `B` over a field `K`, a finite flat `B`-algebra whose fibres at the
maximal ideals all have dimension `n` has dimension `n * dim B` over `K`. -/
theorem finrank_eq_mul_of_finite_flat_constant_fiber_rank
    {K B C : Type u} [Field K] [CommRing B] [CommRing C]
    [Algebra K B] [Algebra B C] [Algebra K C] [IsScalarTower K B C]
    [Module.Finite K B] [Module.Finite B C] [Module.Flat B C] (n : ℕ)
    (h : ∀ p : MaximalSpectrum B, Module.finrank (B ⧸ p.1) ((B ⧸ p.1) ⊗[B] C) = n) :
    Module.finrank K C = n * Module.finrank K B := by
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B C n h
  let b' : Module.Basis (ULift.{u} (Fin n)) B C := b.reindex Equiv.ulift.symm
  calc
    Module.finrank K C = Module.finrank K (ULift.{u} (Fin n) →₀ B) :=
      (b'.repr.restrictScalars K).finrank_eq
    _ = n * Module.finrank K B := by
      rw [Module.finrank_finsupp (R := K) (M := B) (ι := ULift.{u} (Fin n))]
      simp

/-- The dimension of the fibre of a finite flat module at a maximal ideal is its rank at the
corresponding stalk. -/
private theorem finrank_quotient_tensor_eq_rankAtStalk'
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Flat R M] (P : Ideal R) [hP : P.IsMaximal] :
    Module.finrank (R ⧸ P) ((R ⧸ P) ⊗[R] M) =
      Module.rankAtStalk M (⟨P, hP.isPrime⟩ : PrimeSpectrum R) := by
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  rw [Module.rankAtStalk_eq, ← Module.finrank_baseChange (R := P.ResidueField)
    (S := R ⧸ P) (M' := (R ⧸ P) ⊗[R] M)]
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ P)
    P.ResidueField P.ResidueField M).finrank_eq

/-- Over the spectrum of a field, the rank of a finite flat morphism is the dimension of the
global sections of its source. -/
theorem finrank_eq_finrank_sections_of_specField {k : Type u} [Field k] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of k)) [IsFinite p] [Flat p] (x : Spec (.of k)) :
    p.finrank x =
      letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
      Module.finrank k Γ(Z, ⊤) := by
  have : IsAffine Z := isAffine_of_isAffineHom p
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  let := φ.hom.toAlgebra
  have heq : Z.isoSpec.inv ≫ p = Spec.map φ := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rw [← Scheme.Hom.finrank_comp_left_of_isIso Z.isoSpec.inv, heq]
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, ← heq]
    infer_instance
  have hflat : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, ← heq]
    infer_instance
  rw [Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat]
  show Module.rankAtStalk (R := k) Γ(Z, ⊤) x = _
  rw [Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- A finite locally free morphism of constant rank is finite and flat. -/
private theorem isFinite_and_flat_of_isFiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : ℕ) [IsFiniteLocallyFreeOfRank f r] : IsFinite f ∧ Flat f :=
  let ⟨h₁, h₂, _⟩ := (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r)
  ⟨h₁, h₂⟩

/-- The field case of `Stacks.Morphisms.finrank_comp_eq_mul`. -/
private theorem finrank_comp_eq_mul_of_specField {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Y) (a : Y ⟶ Spec (.of k)) (r : ℕ)
    [hpr : IsFiniteLocallyFreeOfRank p r] [IsFinite a] [Flat a]
    (x : Spec (.of k)) : (p ≫ a).finrank x = r * a.finrank x := by
  obtain ⟨_, _⟩ := isFinite_and_flat_of_isFiniteLocallyFreeOfRank p r
  have : IsAffine Y := isAffine_of_isAffineHom a
  have : IsAffine X := isAffine_of_isAffineHom p
  let B := Γ(Y, ⊤)
  let C := Γ(X, ⊤)
  let φ := (Scheme.ΓSpecIso (.of k)).inv ≫ a.appTop
  let ψ := p.appTop
  let χ := (Scheme.ΓSpecIso (.of k)).inv ≫ (p ≫ a).appTop
  let : Algebra k B := φ.hom.toAlgebra
  let : Algebra B C := ψ.hom.toAlgebra
  let : Algebra k C := χ.hom.toAlgebra
  have hχ : χ = φ ≫ ψ := by simp [χ, φ, ψ]
  have : IsScalarTower k B C := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hχ)
  have hfinB : φ.hom.Finite := RingHom.Finite.comp
    a.finite_appTop
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  have : Module.Finite k B := hfinB
  have : Module.Finite B C := p.finite_appTop
  have : Module.Flat B C := p.flat_appTop
  have hrank (q : PrimeSpectrum B) : Module.rankAtStalk (R := B) C q = r := by
    have sq : IsPullback X.isoSpec.inv (Spec.map ψ) p Y.isoSpec.inv :=
      IsPullback.of_horiz_isIso ⟨(Scheme.isoSpec_inv_naturality p).symm⟩
    have h := Scheme.Hom.finrank_of_isPullback _ _ _ _ sq q
    rw [Scheme.Hom.finrank_SpecMap_eq_finrank p.finite_appTop p.flat_appTop] at h
    exact h.trans ((isFiniteLocallyFreeOfRank_iff_forall_finrank_eq p r).mp hpr _)
  rw [finrank_eq_finrank_sections_of_specField, finrank_eq_finrank_sections_of_specField]
  exact finrank_eq_mul_of_finite_flat_constant_fiber_rank r fun q => by
    rw [finrank_quotient_tensor_eq_rankAtStalk', hrank]

/-- **Multiplicativity of the rank function.** If `f` is finite locally free of degree `r` and
`g` is finite and flat, then the rank of `f ≫ g` at every point is `r` times the rank of `g`. -/
theorem finrank_comp_eq_mul {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℕ)
    [IsFiniteLocallyFreeOfRank f r] [IsFinite g] [Flat g] (z : Z) :
    (f ≫ g).finrank z = r * g.finrank z := by
  obtain ⟨_, _⟩ := isFinite_and_flat_of_isFiniteLocallyFreeOfRank f r
  let i := Z.fromSpecResidueField z
  let g' := pullback.snd g i
  let f' := pullback.snd f (pullback.fst g i)
  have : IsFiniteLocallyFreeOfRank f' r :=
    IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_hasPullback f (pullback.fst g i))
  let x : Spec (Z.residueField z) := IsLocalRing.closedPoint (Z.residueField z)
  have hx : i x = z := Scheme.fromSpecResidueField_apply z x
  have : IsFinite g' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback g i)
    inferInstance
  have : Flat g' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback g i)
    inferInstance
  have h₁ := Scheme.Hom.finrank_of_isPullback _ _ _ _
    ((IsPullback.of_hasPullback f (pullback.fst g i)).paste_vert (IsPullback.of_hasPullback g i)) x
  have h₂ := Scheme.Hom.finrank_pullback_snd g i x
  rw [hx] at h₁ h₂
  rw [← h₁, ← h₂]
  exact @finrank_comp_eq_mul_of_specField _ _ _ _ f' g' r ‹_› ‹IsFinite g'› ‹Flat g'› x

/-- **Degrees multiply under composition.** A composite of finite locally free morphisms of
degrees `r` and `s` is finite locally free of degree `r * s`. -/
theorem isFiniteLocallyFreeOfRank_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : ℕ)
    [IsFiniteLocallyFreeOfRank f r] [hg : IsFiniteLocallyFreeOfRank g s] :
    IsFiniteLocallyFreeOfRank (f ≫ g) (r * s) := by
  have := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f r
  have := IsFiniteLocallyFreeOfRank.isFiniteLocallyFree g s
  obtain ⟨_, _⟩ := isFinite_and_flat_of_isFiniteLocallyFreeOfRank f r
  obtain ⟨_, _⟩ := isFinite_and_flat_of_isFiniteLocallyFreeOfRank g s
  refine (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq (f ≫ g) (r * s)).mpr fun z => ?_
  rw [finrank_comp_eq_mul f g r z, (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g s).mp hg z]

end Stacks.Morphisms

end
