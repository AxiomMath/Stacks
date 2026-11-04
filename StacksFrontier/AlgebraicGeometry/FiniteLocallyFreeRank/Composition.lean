module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Descent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.RankComp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.FiniteFibres
public import StacksFrontier.RingTheory.LocalRing.Module

/-!
# Composites of finite locally free morphisms

The degree of a finite locally free morphism is multiplicative in composites
(`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.comp`). Conversely the degree of the second factor can
be read off the other two: if `f` is finite locally free of positive degree `a`, `f ≫ g` is
finite locally free of degree `c`, and `g` is separated and locally of finite presentation, then
`g` is finite locally free of degree `c / a`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finrank_comp_of_isFiniteLocallyFreeOfRank`: the rank function of
  `f ≫ g` is `a` times the rank function of `g`, for `g` finite and flat.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_comp`: the degree of the second factor of a
  composite.

## Implementation notes

The second factor `g` is shown to be finite through Stacks Tag 02LS
(`AlgebraicGeometry.IsFinite.tfae_isProper_finite_preimage_singleton`): it is universally closed
because `f ≫ g` is and `f` is surjective (Stacks Tag 03GN), and its fibres are finite because
they are images of fibres of `f ≫ g`. It is flat because flatness descends along the faithfully
flat `f`. Its degree is then forced by the multiplicativity of the rank function.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open TensorProduct in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The rank at stalks is multiplicative in towers.** If `S` is a finite `R`-algebra and `T` is
a finite flat `S`-algebra of constant rank `a`, then the rank of `T` over `R` at a prime is `a`
times the rank of `S` there. Over the residue field `K` of the prime, the fibre `B = K ⊗[R] S` is
Artinian, so `B ⊗[S] T` is free of rank `a` over it, and `B ⊗[S] T` is the fibre of `T`. -/
private theorem rankAtStalk_eq_mul_of_isScalarTower {R S T : Type u} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.Finite R S] [Module.Flat R S] [Module.Finite S T] [Module.Flat S T] (a : ℕ)
    (h : ∀ q : PrimeSpectrum S, Module.rankAtStalk T q = a) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) T p = a * Module.rankAtStalk (R := R) S p := by
  have : Module.Finite R T := .trans S T
  have : Module.Flat R T := .trans R S T
  let K := p.asIdeal.ResidueField
  let B := K ⊗[R] S
  let C := B ⊗[S] T
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B C a fun P ↦ by
    let _ : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
    have hP : Module.finrank (B ⧸ P.asIdeal) ((B ⧸ P.asIdeal) ⊗[B] C) =
        Module.rankAtStalk C P.toPrimeSpectrum := by
      rw [Module.rankAtStalk_eq, ← Module.finrank_baseChange (R := P.asIdeal.ResidueField)
        (S := B ⧸ P.asIdeal) (M' := (B ⧸ P.asIdeal) ⊗[B] C)]
      exact (AlgebraTensorModule.cancelBaseChange B (B ⧸ P.asIdeal) P.asIdeal.ResidueField
        P.asIdeal.ResidueField C).finrank_eq
    rw [hP, Module.rankAtStalk_baseChange, h]
  have hC : Module.finrank K C = Module.rankAtStalk (R := R) T p := by
    rw [Module.rankAtStalk_eq]
    exact (Algebra.IsPushout.cancelBaseChange R K S B T).finrank_eq
  have hB : Module.finrank K B = Module.rankAtStalk (R := R) S p := by
    rw [Module.rankAtStalk_eq]
  rw [← hC, ← hB, (((b.reindex Equiv.ulift.symm).repr).restrictScalars K).finrank_eq,
    Module.finrank_finsupp]
  simp

namespace AlgebraicGeometry

/-- For a finite flat morphism of affine schemes, the rank function at a point is the rank of
the global sections map at the corresponding prime. -/
private theorem finrank_eq_ringHom_finrank_appTop {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Flat f] [IsFinite f] (s : S) :
    f.finrank s = f.appTop.hom.finrank (S.isoSpec.hom s) := by
  have hpb : IsPullback X.isoSpec.inv (Spec.map f.appTop) f S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by
      rw [← cancel_epi X.isoSpec.hom]
      simp only [Iso.hom_inv_id_assoc]
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun k ↦ k ≫ S.isoSpec.inv) (Scheme.isoSpec_hom_naturality f).symm⟩
  rw [← Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop,
    Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb]
  simp

/-- A morphism that is finite locally free of some degree is finite and flat. -/
private theorem isFinite_and_flat_of_isFiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f a] : IsFinite f ∧ Flat f := by
  obtain ⟨h1, h2, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree f a)
  exact ⟨h1, h2⟩

/-- The affine-target case of `Scheme.Hom.finrank_comp_of_isFiniteLocallyFreeOfRank`: on global
sections it is `rankAtStalk_eq_mul_of_isScalarTower`. -/
private theorem finrank_comp_of_isAffine {X Y Z : Scheme.{u}} [IsAffine Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) (a : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f a] [IsFinite f] [Flat f]
    [IsFinite g] [Flat g] (z : Z) : (f ≫ g).finrank z = a * g.finrank z := by
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : IsAffine X := isAffine_of_isAffineHom f
  let : Algebra Γ(Z, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(X, ⊤) := (f ≫ g).appTop.hom.toAlgebra
  have : IsScalarTower Γ(Z, ⊤) Γ(Y, ⊤) Γ(X, ⊤) := .of_algebraMap_eq' (by
    simp only [RingHom.algebraMap_toAlgebra, Scheme.Hom.comp_appTop, CommRingCat.hom_comp])
  have : Module.Finite Γ(Z, ⊤) Γ(Y, ⊤) := g.finite_appTop
  have : Module.Flat Γ(Z, ⊤) Γ(Y, ⊤) := g.flat_appTop
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  have : Module.Flat Γ(Y, ⊤) Γ(X, ⊤) := f.flat_appTop
  have hmod := (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine f a rfl).mp
    inferInstance
  rw [finrank_eq_ringHom_finrank_appTop, finrank_eq_ringHom_finrank_appTop]
  exact rankAtStalk_eq_mul_of_isScalarTower a
    (Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank a hmod) _

/-- The rank function of a composite `f ≫ g` with `f` finite locally free of degree `a` and `g`
finite and flat is `a` times the rank function of `g`. -/
theorem Scheme.Hom.finrank_comp_of_isFiniteLocallyFreeOfRank {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (a : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f a] [IsFinite g] [Flat g]
    (z : Z) : (f ≫ g).finrank z = a * g.finrank z := by
  obtain ⟨_, _⟩ := isFinite_and_flat_of_isFiniteLocallyFreeOfRank f a
  obtain ⟨y, hy⟩ := Z.affineCover.covers z
  let ι := Z.affineCover.f (Z.affineCover.idx z)
  have sq := (IsPullback.of_hasPullback f (pullback.fst g ι)).paste_vert
    (IsPullback.of_hasPullback g ι)
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd f (pullback.fst g ι)) a :=
    .of_isPullback (IsPullback.of_hasPullback f (pullback.fst g ι))
  rw [← hy, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ sq y,
    ← Scheme.Hom.finrank_pullback_snd g ι y]
  exact finrank_comp_of_isAffine _ _ a y

end AlgebraicGeometry

namespace Stacks.Morphisms

/-- **The degree of the second factor of a composite.** If `f` is finite locally free of
positive degree `a`, the composite `f ≫ g` is finite locally free of degree `c`, and `g` is
separated and locally of finite presentation, then `g` is finite locally free of degree `c / a`.

Over a nonempty base `a` divides `c` (each fibre degree of `f ≫ g` is `a` times one of `g`); over
an empty base every morphism is finite locally free of every degree, so no divisibility can be
asserted in general. -/
theorem isFiniteLocallyFreeOfRank_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {a c : ℕ} (ha : 0 < a) [IsFiniteLocallyFreeOfRank f a] [IsFiniteLocallyFreeOfRank (f ≫ g) c]
    [IsSeparated g] [LocallyOfFinitePresentation g] :
    IsFiniteLocallyFreeOfRank g (c / a) := by
  obtain ⟨_, _⟩ := isFinite_and_flat_of_isFiniteLocallyFreeOfRank f a
  obtain ⟨_, _⟩ := isFinite_and_flat_of_isFiniteLocallyFreeOfRank (f ≫ g) c
  have hfr := (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f a).mp inferInstance
  have : Surjective f := f.one_le_finrank_iff_surjective.mp fun y ↦ (hfr y).symm ▸ ha
  have : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  have hfib (z : Z) : (g ⁻¹' {z}).Finite := by
    rw [← Set.image_preimage_eq (g ⁻¹' {z}) f.surjective]
    exact ((f ≫ g).finite_preimage_singleton z).image f
  have : IsFinite g := by
    refine ((IsFinite.tfae_isProper_finite_preimage_singleton g).out 1 4).mpr ?_
    exact ⟨inferInstance, inferInstance, inferInstance, hfib⟩
  have : Flat g := flat_of_comp_of_surjective_flat f g
  have hc (z : Z) : c = a * g.finrank z := by
    rw [← Scheme.Hom.finrank_comp_of_isFiniteLocallyFreeOfRank f g a z]
    exact ((isFiniteLocallyFreeOfRank_iff_forall_finrank_eq (f ≫ g) c).mp inferInstance z).symm
  refine (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g (c / a)).mpr fun z ↦ ?_
  rw [hc z, Nat.mul_div_cancel_left _ ha]

end Stacks.Morphisms

end
