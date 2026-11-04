module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniqueness
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingDiagonal

/-!
# The derived endomorphisms of a relative dualizing complex

Let `R → A` be a flat ring map of finite presentation and let `K` be a relative dualizing complex
for `R → A` in the sense of [stacks 0E2C].  [stacks 0E2G] asserts that the canonical map
`A ⟶ RHom_A(K, K)` — the derived homothety `Dualizing.derivedHomothety` of [stacks 0A7C], taken
for the derived tensor--Hom adjunction of [stacks 0A63] — is an isomorphism.  This file proves it
in special cases and relative to a reference object.

## Main definitions

* `Dualizing.relativeHomothety`: the derived homothety `A ⟶ RHom_A(K, K)` at the derived
  tensor--Hom adjunction of [stacks 0A63].

## Main results

* `Dualizing.derivedHomothety_comp_homMap_of_iso`,
  `Dualizing.isIso_derivedHomothety_iff_of_iso_of_unitorNatural`: for a derived tensor--Hom
  adjunction with a tensor unit whose left unitor is natural, an isomorphism `e : K ≅ L` carries
  the derived homothety at `K` to the derived homothety at `L` along `RHom(e⁻¹, e)`; so
  invertibility at `K` and at `L` are equivalent.
* `Dualizing.isIso_relativeHomothety_iff_of_iso`: invertibility of `A ⟶ RHom_A(K, K)` depends
  only on the isomorphism class of `K`.
* `Dualizing.isIso_derivedHomothety_of_isRelativeDualizingComplex`: the conclusion of
  [stacks 0E2G] relative to a second relative dualizing complex at which the homothety is
  invertible, under the hypothesis `hdiag` of [stacks 0E2D].
* `Dualizing.isIso_derivedHomothety_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject`,
  `Dualizing.isIso_derivedHomothety_of_isRelativeDualizingComplex_of_isPerfect_baseChange`,
  `Dualizing.isIso_derivedHomothety_of_isRelativeDualizingComplex_of_torAmplitude`: the same with
  `hdiag` replaced by perfectness of the diagonal, perfectness of the two base changes, or a
  Tor-amplitude bound.
* `Dualizing.PolynomialPresentation.isIso_relativeHomothety_relativeDualizingComplex_of_flat`,
  `Dualizing.PolynomialPresentation.isIso_relativeHomothety_relativeDualizingComplex`: the
  conclusion of [stacks 0E2G] at the canonical relative dualizing complex `φ^!(R)`, the first for
  `A` perfect over the polynomial algebra of a presentation, the second for `R → A` flat.
* `Dualizing.PolynomialPresentation.isIso_relativeHomothety_of_isRelativeDualizingComplex_of_flat`
  and its three variants: the conclusion of [stacks 0E2G] for an arbitrary relative dualizing
  complex of a flat map of finite presentation of Noetherian rings, under the
  projection-compatibility hypotheses `hProjFib` and `hProjSelf`.

## References

* [Stacks Project, Tag 0E2G](https://stacks.math.columbia.edu/tag/0E2G)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2E](https://stacks.math.columbia.edu/tag/0E2E)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace Dualizing

open StacksDraft.DerivedHom

noncomputable section

/-! ### The transfer of the derived homothety along an isomorphism -/

section Abstract

universe u v w

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  (d : DerivedHomAdjunction R) (one : DerivedCategory (ModuleCat.{v} R))
  (lam : ∀ K : DerivedCategory (ModuleCat.{v} R), d.tensor.obj (one, K) ≅ K)

/-- **An isomorphism carries the derived homothety at its source to the one at its target.**
For `e : K ≅ L`, composing the derived homothety `1 ⟶ RHom(K, K)` with the derived Hom of `e`
in both variables — contravariantly by `e⁻¹` in the source, covariantly by `e` in the target —
gives the derived homothety `1 ⟶ RHom(L, L)`. -/
theorem derivedHomothety_comp_homMap_of_iso
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L) :
    derivedHomothety d one lam K ≫ d.hom.map (e.symm.op.prod e).hom =
      derivedHomothety d one lam L := by
  have hfactor : d.hom.map (e.symm.op.prod e).hom =
      d.hom.map (show (Opposite.op K, K) ⟶ (Opposite.op L, K) from (e.inv.op, 𝟙 K)) ≫
        d.hom.map (show (Opposite.op L, K) ⟶ (Opposite.op L, L) from
          (𝟙 (Opposite.op L), e.hom)) := by
    rw [← d.hom.map_comp]
    congr 1
    ext <;> simp
  apply (d.homEquiv one L L).injective
  calc d.homEquiv one L L (derivedHomothety d one lam K ≫ d.hom.map (e.symm.op.prod e).hom)
      = d.homEquiv one L K (derivedHomothety d one lam K ≫
          d.hom.map (show (Opposite.op K, K) ⟶ (Opposite.op L, K) from
            (e.inv.op, 𝟙 K))) ≫ e.hom := by
        rw [hfactor, ← Category.assoc]
        exact d.homEquiv_naturality_right e.hom _
    _ = (d.tensor.map (show (one, L) ⟶ (one, K) from (𝟙 one, e.inv)) ≫
          d.homEquiv one K K (derivedHomothety d one lam K)) ≫ e.hom :=
        congrArg (· ≫ e.hom) (d.homEquiv_dinaturality e.inv (derivedHomothety d one lam K))
    _ = ((lam L).hom ≫ e.inv) ≫ e.hom := by
        rw [derivedHomothety, AddEquiv.apply_symm_apply, hlam e.inv]
    _ = (lam L).hom := by simp
    _ = d.homEquiv one L L (derivedHomothety d one lam L) := by
        rw [derivedHomothety, AddEquiv.apply_symm_apply]

/-- **Invertibility of the derived homothety depends only on the isomorphism class of the
object**, for a derived tensor--Hom adjunction whose chosen left unitor is natural. -/
theorem isIso_derivedHomothety_iff_of_iso_of_unitorNatural
    (hlam : DerivedHomAdjunction.IsUnitorNatural d one lam)
    {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L) :
    IsIso (derivedHomothety d one lam K) ↔ IsIso (derivedHomothety d one lam L) := by
  rw [← derivedHomothety_comp_homMap_of_iso d one lam hlam e]
  exact (isIso_comp_right_iff _ _).symm

end Abstract

/-! ### Stacks 0E2G -/

section Relative

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The derived homothety `A ⟶ RHom_A(K, K)` of [stacks 0A7C] at the derived tensor--Hom
adjunction of [stacks 0A63], with the module universe of that adjunction instantiated at the
ring universe. -/
abbrev relativeHomothety (A : Type u) [CommRing A] (K : DerivedCategory (ModuleCat.{u} A)) :
    derivedTensorUnit.{u, 0} A ⟶
      (derivedHomAdjunctionOverRing.{u, 0} A).hom.obj (Opposite.op K, K) :=
  derivedHomothety (derivedHomAdjunctionOverRing.{u, 0} A) (derivedTensorUnit.{u, 0} A)
    (derivedTensorUnitLeft.{u, 0} A) K

/-- **Invertibility of `A ⟶ RHom_A(K, K)` depends only on the isomorphism class of `K`.** -/
theorem isIso_relativeHomothety_iff_of_iso (A : Type u) [CommRing A]
    {K L : DerivedCategory (ModuleCat.{u} A)} (e : K ≅ L) :
    IsIso (relativeHomothety A K) ↔ IsIso (relativeHomothety A L) :=
  isIso_derivedHomothety_iff_of_iso_of_unitorNatural _ _ _
    (derivedTensorUnitLeft_natural.{u, 0} A) e

/-- Invertibility of `A ⟶ RHom_A(K, K)` transfers along the existence of an isomorphism. -/
private theorem isIso_relativeHomothety_of_nonempty_iso (A : Type u) [CommRing A]
    {K ω : DerivedCategory (ModuleCat.{u} A)} (e : Nonempty (ω ≅ K))
    (h : IsIso (relativeHomothety A ω)) : IsIso (relativeHomothety A K) :=
  (isIso_relativeHomothety_iff_of_iso A e.some).1 h

/-- **The conclusion of [stacks 0E2G]**, relative to a reference relative dualizing complex.  Let
`R → A` be a flat ring map of finite presentation, let `K` and `ω` be relative dualizing
complexes for `R → A` satisfying the hypothesis `hdiag` of [stacks 0E2D], and suppose the
canonical map `A ⟶ RHom_A(ω, ω)` is an isomorphism.  Then so is `A ⟶ RHom_A(K, K)`. -/
theorem isIso_derivedHomothety_of_isRelativeDualizingComplex (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K ω : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hω : IsRelativeDualizingComplex R A ω)
    (hdiag :
      IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((diagonalDerivedExtension R A).obj K) ((diagonalDerivedExtension R A).obj ω)
          (diagonalObject R A)) ∧
        IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((diagonalDerivedExtension R A).obj ω) ((diagonalDerivedExtension R A).obj K)
          (diagonalObject R A)))
    (hhom : IsIso (relativeHomothety A ω)) :
    IsIso (relativeHomothety A K) :=
  isIso_relativeHomothety_of_nonempty_iso A
    (nonempty_iso_of_isRelativeDualizingComplex R A ω K hω hK hdiag) hhom

/-- **[stacks 0E2G] when the diagonal is perfect.** If the diagonal `A`, read as an object of
`D(A ⊗[R] A)` by restriction of scalars along the multiplication map, is perfect there, then
`A ⟶ RHom_A(K, K)` is an isomorphism for every relative dualizing complex `K`, as soon as it is
one at a single reference relative dualizing complex `ω`. -/
theorem isIso_derivedHomothety_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] (K ω : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hω : IsRelativeDualizingComplex R A ω)
    (hperf : StacksDraft.Perfect.IsPerfect (diagonalObject R A))
    (hhom : IsIso (relativeHomothety A ω)) :
    IsIso (relativeHomothety A K) :=
  isIso_relativeHomothety_of_nonempty_iso A
    (nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject R A ω K hω hK
      hperf) hhom

/-- **[stacks 0E2G] when the two base changes are perfect.** If the derived base changes of `K`
and of the reference complex `ω` along the left coprojection are perfect objects of
`D(A ⊗[R] A)`, then invertibility of `A ⟶ RHom_A(ω, ω)` gives invertibility of
`A ⟶ RHom_A(K, K)`. -/
theorem isIso_derivedHomothety_of_isRelativeDualizingComplex_of_isPerfect_baseChange
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] (K ω : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hω : IsRelativeDualizingComplex R A ω)
    (hKperf : StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj K))
    (hωperf : StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj ω))
    (hhom : IsIso (relativeHomothety A ω)) :
    IsIso (relativeHomothety A K) :=
  isIso_relativeHomothety_of_nonempty_iso A
    (nonempty_iso_of_isRelativeDualizingComplex_of_isPerfect_baseChange R A ω K hω hK hωperf
      hKperf) hhom

/-- **[stacks 0E2G] under the Tor-amplitude bound of [stacks 0ATK] (3).** If each of the two
derived base changes of `K` and of the reference complex `ω` along the left coprojection has Tor
amplitude bounded below over `A ⊗[R] A`, then invertibility of `A ⟶ RHom_A(ω, ω)` gives
invertibility of `A ⟶ RHom_A(K, K)`. -/
theorem isIso_derivedHomothety_of_isRelativeDualizingComplex_of_torAmplitude (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K ω : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) (hω : IsRelativeDualizingComplex R A ω) (a : ℤ)
    (hKtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N))))
    (hωtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj ω)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N))))
    (hhom : IsIso (relativeHomothety A ω)) :
    IsIso (relativeHomothety A K) :=
  isIso_relativeHomothety_of_nonempty_iso A
    (nonempty_iso_of_isRelativeDualizingComplex_of_torAmplitude R A ω K hω hK a hωtor
      hKtor) hhom

/-! ### Stacks 0E2G at the canonical relative dualizing complex -/

namespace PolynomialPresentation

/-- **The derived endomorphisms of `ω_{A/R} = φ^!(R)`.**  Let `φ : R → A` be a ring map with `R`
Noetherian, presented by `p`, and suppose `A` is perfect as a module over the polynomial algebra
of the presentation.  Then `A ⟶ RHom_A(φ^!(R), φ^!(R))` is an isomorphism, with `φ^!(R)` formed
at the module universe of the ring and the base ring written as itself rather than as its
universe lift. -/
theorem isIso_relativeHomothety_upperShriekFunctor_unit {R A : Type u} [CommRing R] [CommRing A]
    {f : R →+* A} [IsNoetherianRing R] (p : PolynomialPresentation f)
    (hperf : letI : Module p.Poly (ULift.{u} A) :=
        Module.compHom (ULift.{u} A) p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) (ULift.{u} A)) :
    IsIso (relativeHomothety A
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
  (isIso_relativeHomothety_iff_of_iso A
    (p.upperShriekFunctor.{u, 0}.mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (LinearEquiv.toModuleIso
          (ULift.moduleEquiv (R := R) (M := R) : ULift.{0} R ≃ₗ[R] R)).symm))).2
    (upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule.{u, 0} p hperf)

/-- **The conclusion of [stacks 0E2G] at the canonical relative dualizing complex.**  Let `R → A`
be a ring map with `R` Noetherian, presented by `p`, and suppose `A` is perfect over the
polynomial algebra of the presentation.  Then the canonical map `A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` is
an isomorphism for `ω_{A/R} = φ^!(R)`. -/
theorem isIso_relativeHomothety_relativeDualizingComplex_of_flat (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] [IsNoetherianRing R] (p : PolynomialPresentation (algebraMap R A))
    (hperf : letI : Module p.Poly (ULift.{u} A) :=
        Module.compHom (ULift.{u} A) p.toRingHom
      StacksDraft.Perfect.IsPerfectModule (R := p.Poly) (ULift.{u} A)) :
    IsIso (relativeHomothety A
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
  p.isIso_relativeHomothety_upperShriekFunctor_unit hperf

/-- **The conclusion of [stacks 0E2G] at the canonical relative dualizing complex of a flat
map.**  Let `R → A` be a flat homomorphism of finite type, presented by `p`, with `R` Noetherian.
Then `A ⟶ RHom_A(ω_{A/R}, ω_{A/R})` is an isomorphism for `ω_{A/R} = φ^!(R)`. -/
theorem isIso_relativeHomothety_relativeDualizingComplex (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [IsNoetherianRing R]
    (p : PolynomialPresentation (algebraMap R A)) :
    IsIso (relativeHomothety A
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
  p.isIso_relativeHomothety_upperShriekFunctor_unit
    (p.isPerfectModule_uLift_of_flat.{u, u} (RingHom.flat_algebraMap_iff.mpr inferInstance))

/-- **The conclusion of [stacks 0E2G] over a Noetherian base.**  Let `R → A` be a flat
homomorphism of finite presentation of Noetherian rings, presented by `p` and satisfying the
projection-compatibility hypotheses `hProjFib` and `hProjSelf`, and let `K` be a relative
dualizing complex for `R → A` satisfying, against `φ^!(R)`, the hypothesis `hdiag` of
[stacks 0E2D].  Then `A ⟶ RHom_A(K, K)` is an isomorphism. -/
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex_of_flat (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.FinitePresentation R A]
    [IsNoetherianRing R] [IsNoetherianRing A] (p : PolynomialPresentation (algebraMap R A))
    (hProjFib : ∀ t : PrimeSpectrum R, p.ProjectionCompatibility t.asIdeal.ResidueField)
    (hProjSelf : p.ProjectionCompatibility A)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hdiag :
      IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((diagonalDerivedExtension R A).obj K)
          ((diagonalDerivedExtension R A).obj (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
          (diagonalObject R A)) ∧
        IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
          ((diagonalDerivedExtension R A).obj (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))
          ((diagonalDerivedExtension R A).obj K) (diagonalObject R A))) :
    IsIso (relativeHomothety A K) :=
  isIso_derivedHomothety_of_isRelativeDualizingComplex R A K _ hK
    (p.relativeDualizingComplex_isRelativeDualizingComplex_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hProjFib hProjSelf)
    hdiag (isIso_relativeHomothety_relativeDualizingComplex R A p)

/-- **[stacks 0E2G] for a perfect diagonal.**  Under the hypotheses `hProjFib` and `hProjSelf`,
if the diagonal `A`, read in `D(A ⊗[R] A)` by restriction of scalars along the multiplication
map, is perfect there, then `A ⟶ RHom_A(K, K)` is an isomorphism for every relative dualizing
complex `K`. -/
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A))
    (hProjFib : ∀ t : PrimeSpectrum R, p.ProjectionCompatibility t.asIdeal.ResidueField)
    (hProjSelf : p.ProjectionCompatibility A)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hdiagPerf : StacksDraft.Perfect.IsPerfect (diagonalObject R A)) :
    IsIso (relativeHomothety A K) :=
  isIso_derivedHomothety_of_isRelativeDualizingComplex_of_isPerfect_diagonalObject R A K _ hK
    (p.relativeDualizingComplex_isRelativeDualizingComplex_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hProjFib hProjSelf)
    hdiagPerf (isIso_relativeHomothety_relativeDualizingComplex R A p)

/-- **[stacks 0E2G] for perfect base changes.**  Under the hypotheses `hProjFib` and
`hProjSelf`, if the derived base changes of `K` and of `ω_{A/R} = φ^!(R)` along the left
coprojection are perfect objects of `D(A ⊗[R] A)`, then `A ⟶ RHom_A(K, K)` is an isomorphism. -/
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex_of_isPerfect_baseChange
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A))
    (hProjFib : ∀ t : PrimeSpectrum R, p.ProjectionCompatibility t.asIdeal.ResidueField)
    (hProjSelf : p.ProjectionCompatibility A)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hKperf : StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj K))
    (hωperf : StacksDraft.Perfect.IsPerfect ((diagonalDerivedExtension R A).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) :
    IsIso (relativeHomothety A K) :=
  isIso_derivedHomothety_of_isRelativeDualizingComplex_of_isPerfect_baseChange R A K _ hK
    (p.relativeDualizingComplex_isRelativeDualizingComplex_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hProjFib hProjSelf)
    hKperf hωperf (isIso_relativeHomothety_relativeDualizingComplex R A p)

/-- **[stacks 0E2G] under the Tor-amplitude bound of [stacks 0ATK] (3).**  Under the hypotheses
`hProjFib` and `hProjSelf`, if each of the derived base changes of `K` and of
`ω_{A/R} = φ^!(R)` along the left coprojection has Tor amplitude bounded below over
`A ⊗[R] A`, then `A ⟶ RHom_A(K, K)` is an isomorphism. -/
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex_of_torAmplitude
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] [IsNoetherianRing R] [IsNoetherianRing A]
    (p : PolynomialPresentation (algebraMap R A))
    (hProjFib : ∀ t : PrimeSpectrum R, p.ProjectionCompatibility t.asIdeal.ResidueField)
    (hProjSelf : p.ProjectionCompatibility A)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K) (a : ℤ)
    (hKtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj K)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N))))
    (hωtor : ∀ (N : ModuleCat.{u} (A ⊗[R] A)) (i : ℤ), i < a →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] A)) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
              (A ⊗[R] A)).tensor.obj ((diagonalDerivedExtension R A).obj
                (p.upperShriekFunctor.{u, 0}.obj
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                    (ModuleCat.of R R))))).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj N)))) :
    IsIso (relativeHomothety A K) :=
  isIso_derivedHomothety_of_isRelativeDualizingComplex_of_torAmplitude R A K _ hK
    (p.relativeDualizingComplex_isRelativeDualizingComplex_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hProjFib hProjSelf)
    a hKtor hωtor (isIso_relativeHomothety_relativeDualizingComplex R A p)

end PolynomialPresentation

end Relative

end

end Dualizing

end
